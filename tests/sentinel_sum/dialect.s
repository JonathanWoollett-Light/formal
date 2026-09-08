    #$ data thread [u32 u32 u32 u32 u32 u32 u32 u32]
    li a1, 4
    la t0, data
    li t1, 3
    #] t1, 0(t0)
    li t1, 1
    #] t1, 1(t0)
    li t1, 4
    #] t1, 2(t0)
    li t1, 1
    #] t1, 3(t0)
    li t1, 5
    #] t1, 4(t0)
    li t1, 9
    #] t1, 5(t0)
    li t1, 0
    #] t1, 6(t0)
    li a2, 0
    li a3, 0
    la t0, data
    #[ t1, 0(t0)
_l0:
    beqz t1, _l1
    add a2, a2, t1
    addi a3, a3, 1
    add t0, t0, a1
    #[ t1, 0(t0)
    j _l0
_l1:
    li t5, 23
    beq a2, t5, _l2
    #!
_l2:
    li t5, 6
    beq a3, t5, _l3
    #!
_l3:
    li a0, 0
    li a7, 93
    ecall
    #?
