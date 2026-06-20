    li t0, 6
    li t1, 7
    mul t2, t0, t1
    #$ acc global _
    la t3, acc
    sw t2, 0(t3)
    lw t4, 0(t3)
    li a0, 42
    beq t4, a0, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
