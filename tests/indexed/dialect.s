    #$ arr thread [u32 u32 u32 u32]
    la t0, arr
    li t2, 4
    li t1, 1
    mul t3, t1, t2
    add t4, t0, t3
    li t5, 10
    sw t5, 0(t4)
    li t1, 3
    mul t3, t1, t2
    add t4, t0, t3
    li t5, 30
    sw t5, 0(t4)
    li t1, 1
    mul t3, t1, t2
    add t4, t0, t3
    lw a1, 0(t4)
    li t1, 3
    mul t3, t1, t2
    add t4, t0, t3
    lw a2, 0(t4)
    add a1, a1, a2
    li a0, 40
    beq a1, a0, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
