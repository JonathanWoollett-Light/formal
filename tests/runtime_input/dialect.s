    #$ arr thread [u32 u32 u32 u32]
    li a0, 12
    #~ a0
    li t2, 4
    rem a1, a0, t2
    la t3, arr
    mul t4, a1, t2
    add t5, t3, t4
    li a2, 7
    sw a2, 0(t5)
    li a0, 0
    li a7, 93
    ecall
    #?
