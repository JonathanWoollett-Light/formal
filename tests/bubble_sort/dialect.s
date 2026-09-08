    #$ arr thread [u32 u32 u32 u32 u32 u32]
    li a1, 6
    li a2, 5
    li a5, 4
    la t0, arr
    li t1, 5
    #] t1, 0(t0)
    li t1, 2
    #] t1, 1(t0)
    li t1, 8
    #] t1, 2(t0)
    li t1, 1
    #] t1, 3(t0)
    li t1, 9
    #] t1, 4(t0)
    li t1, 3
    #] t1, 5(t0)
    li a0, 0
_l0:
    bge a0, a1, _l1
    li t0, 0
_l2:
    bge t0, a2, _l3
    mul t1, t0, a5
    la t2, arr
    add t2, t2, t1
    #[ a3, 0(t2)
    #[ a4, 1(t2)
    bge a4, a3, _l4
    #] a4, 0(t2)
    #] a3, 1(t2)
_l4:
    addi t0, t0, 1
    j _l2
_l3:
    addi a0, a0, 1
    j _l0
_l1:
    li t0, 0
_l5:
    bge t0, a2, _l6
    mul t1, t0, a5
    la t2, arr
    add t2, t2, t1
    #[ a3, 0(t2)
    #[ a4, 1(t2)
    bge a4, a3, _l7
    #!
_l7:
    addi t0, t0, 1
    j _l5
_l6:
    li a0, 0
    li a7, 93
    ecall
    #?
