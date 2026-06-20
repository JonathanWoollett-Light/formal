    #$ d thread [u32]
    la t0, d
    li t1, 100
    li t2, 7
    div t3, t1, t2
    li t4, 3
    div t3, t3, t4
    sw t3, 0(t0)
    lw t5, 0(t0)
    li a0, 4
    beq t5, a0, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
