    # The 4-byte store at offset 2 needs a type at least 6 bytes wide, so the
    # search rejects u8..i32 and lands on u64: the access offset participates
    # in type inference, and the recorded range covers exactly bytes 2..6.
    #$ value global _
    la t0, value
    li t1, 7
    sw t1, 2(t0)
    lw t2, 2(t0)
    #?
