    # Only bytes 0 and 2 of the 4-byte list are accessed at runtime: the
    # verifier records exactly those ranges (the basis for dead-data trimming),
    # while `.bss` storage is still emitted at the full type size - bytes that
    # are merely *unaccessed* are never trimmed from live storage.
    #$ data _ [u8 u8 u8 u8]
    la t0, data
    li t1, 7
    sb t1, 0(t0)
    lb t2, 2(t0)
    #?
