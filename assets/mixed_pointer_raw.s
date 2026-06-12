    # One instruction, two kinds of execution: iteration 1 stores through a
    # *pointer* into `value` (a recorded transition at offset 4); iteration 2
    # stores through a *raw address* into the `#@` region (invisible to the
    # transition records). Layout compaction must therefore pin the `sb` to its
    # original immediate and keep `value`'s padded layout - rewriting the
    # offset for the compacted pointer view would silently re-point the raw
    # store - see tests/mixed_pointer_raw.rs.
    #$ value global _
    la t1, value
    li t3, 0
    #@ 0x80100000 0x80100010 rw
_loop:
    sb t3, 4(t1)
    li t1, 0x80100000
    addi t3, t3, 1
    li t4, 2
    blt t3, t4, _loop
    #?
