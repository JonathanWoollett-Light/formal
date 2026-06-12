    # Reads the descriptor locality byte (offset 24) at runtime, so unlike
    # every other program the locality byte must survive in `.data`: dead-data
    # elimination removes only information that is never read at runtime.
    #$ x global u8
    #& t0, x
    li t5, 0
    lb t1, 24(t0)
    #?
