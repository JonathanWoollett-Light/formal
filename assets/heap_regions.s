    # Heap accesses through `#@` region declarations. The first region is
    # declared with immediate bounds and accessed at a non-zero offset; the
    # second through registers, the way an allocator would declare each
    # allocation just before returning its pointer, and is exactly as wide as
    # the store that hits it.
    #@ 0x80100000 0x80100008 rw
    li t0, 0x80100000
    li t1, 42
    sw t1, 4(t0)
    lw t2, 4(t0)
    li t3, 0x80200000
    li t4, 0x80200004
    #@ t3 t4 rw
    sw t1, 0(t3)
    lw t5, 0(t3)
    #?
