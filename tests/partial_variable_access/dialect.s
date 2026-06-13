    #$ data _ [u8 u8 u8 u8]
    la t0, data
    li t1, 7
    sb t1, 0(t0)
    lb t2, 2(t0)
    #?
