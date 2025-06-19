# language

## dev setup

- download assembly and loader from https://github.com/riscv-collab/riscv-gnu-toolchain/releases
- download `riscv64-elf-ubuntu-24.04-gcc`
- run `riscv/riscv64-unknown-elf/bin/as -`
- assemble source to ELF object file `riscv/riscv64-unknown-elf/bin/as -o program.o program.s`
- link object file to ELF executable `riscv/riscv64-unknown-elf/bin/ld -o program.elf program.o`
- convert ELF to raw binary `riscv/riscv64-unknown-elf/bin/objcopy -O binary program.elf program.bin`
- when running in QEMU you will probably use the ELF executable.

## languages to take inspiration from

- https://lean-lang.org/
- https://www.rust-lang.org/
- https://ziglang.org/
- https://ocaml.org/
- https://ada-lang.io/
- https://www.modular.com/mojo
- https://www.python.org/

## things to make

1. A bare-metal OS running doom.
2. A bare-metal OS running a tor node.
3. A bare-metal OS running a web-server
4. A bare-metal OS running a level 1 hyper-visor, which can form the base of the serverless platform.

## onotation

`O(n * h^r * 2^b * 8^v)`

- `n`: Number of instructions.
- `h`: Number of harts.
- `r`: Number of racy instructions.
- `b`: Number of indeterminate branches.
- `v`: Number of unspecified variables.

This is the worst case and most program will be massively under it.

In a program with 10,000 instructions, 3 harts, 100 racy instructions, 100 indeterminte branches and 0 unpsecified variables we reach 6.5*10^81. This is impossible.

In a program with 10,000 instructions, 3 harts, 10 racy instructions, 10 indeterminate branches and 0 unspecified variables we reach 6.0*10^11. This is possible. The 10 racy instructions may be atomics to manage shared state.

## making it work in larger projects

To make it viable in larger projects there should be some configuration arguments:

- `racy-groups`: This should allow configuring the minimum size of sections evaluated for racyness. E.g. with 2 racy instructions a setting of 1 for a system with 2 harts would results in 4 evaluations of the first instruction and 16 evaluations of the 2nd instruction, while a setting of 2 would result in 4 evaluations of both instructions as these instructions would be merged to form a group of 2 instructions when evaluating racyness. This setting can massively reduce O'notation by assuming instructions which are very near are very unlikely to not be run sequentially, it is unlikely for race conditions to exist at this level and extremely unlikely for a race condition to be hit even if they exist (given we are talking about nanosecond times scales). This is of course an imperfect heuristic and you can definitely write programs that break this.
TODO I don't know how this would work with syscalls (on this specifically I don't care, as I'm only focussing on embedded and bare metal) and I think this issue will also apply to interrupts on bare metal.
- `seqeuntial`: Only explores 1 ordering of instructions, removing `h^r` from the onotation.
- `typed`: Requires all variables have types which can be immedately inferred, removing `8^v` from the onotation. For example `define x local u32` `y=x` works becuase `x` is fully defined and `y` is identical to `x`.
- `partial`: Allows partial exploration, doesn't remove untouched code, any `fail`s become like Zig exceptions returning unique error codes.

## borrow checking

Borrow checking just allows invalidating bad paths faster. This could be done by using a reference countered pointer then requiring on the reference count.

## updated run

There is a lot of work that is duplicated.

One area of this work is that as soon as an invalid configuration is found the entire configuration is discarded, then exploration begins again from the beginning re-treading much of the same path until reaching the same configuraiton with the last value as a different type.

Instead when an invalid configuration is encountered, all leaves should backtrace to the first occurence of the variable type we want to change. This way we can avoid re-treading the same path many times. This degree of optimization is so signficant it may even reduce the o'notation.

To accomplish this effectively each leaf node should contain a map of values to the verifiers nodes where the values where first encountered along this path. We then iterate through leaves, to the first occurences and deallocating all child nodes, any leaf nodes deallocated here should be added to a skip list so the next iteration can skip the leaf node if its already been deallocated.
The new leaves will then need to be enqued again.

In future it might be worth using a custom version of `NonNull` that counts the number of dereferences so this can be tracked as a performance metric.

## optimizing output

1. Remove untouched code.
2. Remove branches that never jump.
3. Remove writes to registers that are never read.
   Initially we should assume on syscalls all registers are read.
   Further optimization will require a mechanism to specify if a syscall read/writes certain reigsters.
4. Remove memory writes that are never read.
   This will require documenting volatile memory for mmio.

## assembly reference

keyword|assembly symbol
---|---
`fail` | `#!`
`unreachable` | `#?`
`define` | `#$`
`section` | `#@`
`lat` | `#&`

## optimizing

To optimize performance we can replace `ExplorererPath::queue` by immedately spawning a tokio spawn instead of when we would push an item to the queue.

We want a way to preserve deterministic ordering so tests can check ordering. Maybe there is a setting in tokio to only run 1 task at a time (or reduce parallelism in some other way)?

## logs with jaeger

Follow jaeger tutorial at https://tokio.rs/tokio/topics/tracing-next-steps.

## grafana loki for log monitoring

**this currently errors becuase god knows all this software has dogshit documentation that was only tested in 1 specific enviroment with a specific setup with a bunch of undocumented pre-existing settings**

From (https://grafana.com/grafana/download):

```bash
sudo apt-get install -y adduser libfontconfig1 musl
wget https://dl.grafana.com/enterprise/release/grafana-enterprise_11.2.0_amd64.deb
sudo dpkg -i grafana-enterprise_11.2.0_amd64.deb
```

Then `sudo systemctl enable grafana-server.service` to enable startup on start.

Then `sudo systemctl start grafana-server` to start, and `sudo systemctl status grafana-server` to view.

Config can be see with `sudo nano /etc/grafana/grafana.ini` the default port will be 3000 which will show as;

```
# The http port to use
;http_port = 3000
```

logs can be found at `/var/log/grafana`.

The default login will be username `admin` and password `admin`.

Go `+` in top right, click `import dashboard` enter the loki dashboard id (`13186`) from (`https://grafana.com/grafana/dashboards/13186-loki-dashboard/`).
Add loki datasource.


## cli args

- `list_depth`: How many layers of nested lists to explore during type exploration. The default is 0.
- `list_width`: How many items to explore in lists during type exploration. The default is 0.
- `union_depth`: How many layers of nested unions to explore during type exploration. The default is 0.

### placement

- global initialized data goes in `.data`
- global initialized read-only data goes in `.rodata`
- global uninitialized data goes in `.bss`
There should be an option (`tls`) whether to store `thread` locality in `.tdata` or `.data` (and `.tbss` or `.bss`) storing in TLS is safer as we can ensure thread isolation (atleast as much as possible) while using global `.data` is more memory efficient as it doesn't duplicate the data in threads where it is unused.
- thread initialized data goes in `.data`.
- thread uninitialized data goes in `.bss`.
- thread initialized read-only data goes in `.rodata`

Both global and thread have static lifetimes. There should be a `local` locality, that is stored on the stack to minimize runtime memory usage.

### racy-ness

thread local data is still stored in global memory so accesses are still racy. However the assumption only 1 thread accesses this data can massively speed up compile times as it means the majority of different orderings for loads/stores no longer need to be checked.

So there should be a cli argument about whether to evaluate racyness for thread local data.

### exploring lists and unions

Since there are an indefinite number of lists exploration needs to be constrained. This can be done with 2 variables `list_depth` and `list_width`.

Exploration of unions needs to be done with `union_depth` (the width is every possible type combinationthat doesn't nest unions more than `union_depth`).


### function args
When passing arms to functions they need to be flattened e.g.
```
my_fn(x,y[2],my_other_fn(z))
```
Becomes
```
x @ a
y[2] @ b
my_other_fn(z) @ c
my_fn(a,b,c)
```
Then when inlining `my_fn` we find and replace with `a`, `b` and `c`. This can yield consistent behavior since when using asm we know we are always given a label.

An alternative would be that we flatten fn arms and instead the `=` fn defined in core handles this flattening then `my_fn` is defined like
```
my_fn:
    a = in[0]
    b = in[1]
    c = in[2]
```
Where `in[0]` will be replaced with `x`, `in[1]` will be replaced with `y[2]` and `in[2]` will be replaced with `my_other_fn(z)`.

I prefer the second approach since it moves code to user space and allows deeper customization and passing unusual and possibly invalid code to functions if a user wants to define a function that does something special.

The second approach also preserves the purity of `@` doing nothing. In the first approach it must have runtime affects e.g. its essentially a mem copy for identifiers and literally but does nothing for functions (which is not consistent behavior).

The problem with the second approach is that if we want to make it truly generic it needs to pass the args as strings so it can support custom syntax (e.g. dot syntax `x.n`).
### other
The assembly layer is to simplify control flow and type evaluation. It will not be valid assembly. As it requires special type stuff.

When exploring types, we are looking for the initial type to treat variables as (before they are explicitly cast to a type). In this sense all variables act as unions, being the maximum size of all types they are cast as and being able to be cast to arbitrary types.

1. Virtual values (e.g. DATA_END)
2. Address space keyword (e.g. address 0x100 0x200 read write)
3. CSR handling (e.g. mhartid will each be different and one will be 0)
4. Interrupt handling (e.g. wfi) (need to learn more about how this works to figure this out)

## CLI arms

- Harts: Hart range to verify
- Segments: A list of ranges of memory addresses that are valid to access (and if they are volatile). When writing an OS this will cover all the physical memory will annotate MMIO as volatile (e.g. VGA character input). When writing g a userspace program this should be empty.
Need a keyword to annotate valid memory addresses with read and/or write 

## Formal verification
A system can have an arbitrary number of harts. This adds an indefinite dimension which is impossible to fully formally verify. So we restrict the number of harts that are evaluated to set value that can be modified via a setting in the compiler (e.g. 4).

Types must be know at compile time, so for each step forward in evaluating the paths for each number of harts the type state must be compatible.

```rust
struct FormalNode {
	// For each node
	harts: Vec<*mut Node>
}
struct Node {
	next: *mut Node
	prev: *mut Node
}
```

```rust
// We keep track of the position of all harts.
let front: Vec<*mut Node> = todo!();
```
Each AST node is
```rust
struct Node {
	next: Option<*mut Node>,
	prev: *mut Node
}
```
