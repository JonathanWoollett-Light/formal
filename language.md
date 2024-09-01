#### representing memory
The simplest memory is a strip
─│┌┐└┘

Every allocated item in memory has a virtual base

With maximum control of linker
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
