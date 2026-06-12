    # The store precedes the `#@` declaration in program order: regions take
    # effect when executed (declare-before-use), so the store hits undescribed
    # memory and the program is rejected as `Invalid`.
    li t0, 0x80100000
    li t1, 42
    sw t1, 0(t0)
    #@ 0x80100000 0x80100008 rw
    #?
