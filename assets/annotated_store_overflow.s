    # A 4-byte `sw` into a variable annotated `u8`: the annotation removes the
    # type search, the store cannot fit, and the program is rejected as
    # `Invalid`.
    #$ value global u8
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    #?
