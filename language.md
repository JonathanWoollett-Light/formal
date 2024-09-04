### cli args

- `list_depth`: How many layers of nested lists to explore during type exploration. The default is 0.
- `list_width`: How many items to explore in lists during type exploration. The default is 0.
- `union_depth`: How many layers of nested unions to explore during type exploration. The default is 0.
- `tls`: Whether to store thread local data in `.tdata` and `.tbss` or attempt to store in `.data` and `.bss`. The default is `true` (and this is the only current supported setting).

#### placement

- global initialized data goes in `.data`
- global initialized read-only data goes in `.rodata`
- global uninitialized data goes in `.bss`
There should be an option (`tls`) whether to store `thread` locality in `.tdata` or `.data` (and `.tbss` or `.bss`) storing in TLS is safer as we can ensure thread isolation (atleast as much as possible) while using global `.data` is more memory efficient as it doesn't duplicate the data in threads where it is unused.
- thread initialized data goes in `.data` or `.tdata`
- thread uninitialized data goes in `.bss` or `.tbss` (it could go in the stack but there's no point)
- thread initialized read-only data goes in `.rodata`

#### racy-ness

thread local data is still stored in global memory so accesses are still racy. However the assumption only 1 thread accesses this data can massively speed up compile times as it means the majority of different orderings for loads/stores no longer need to be checked.

So there should be a cli argument about whether to evaluate racyness for thread local data.

#### exploring lists and unions

Since there are an indefinite number of lists exploration needs to be constrained. This can be done with 2 variables `list_depth` and `list_width`.

Exploration of unions needs to be done with `union_depth` (the width is every possible type combinationthat doesn't nest unions more than `union_depth`).


#### function args
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
#### other
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
