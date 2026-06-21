    #$ arr thread [u32 u32 u32 u32 u32 u32]
    la t0, arr
    li t1, 3
    sw t1, 0(t0)
    li t1, 0
    sw t1, 4(t0)
    li t1, 5
    sw t1, 8(t0)
    li t1, 0
    sw t1, 12(t0)
    li t1, 0
    sw t1, 16(t0)
    li t1, 2
    sw t1, 20(t0)
    li a0, 0
    li a1, 0
    li a2, 6
    li a5, 4
_l0:
    bge a1, a2, _l1
    mul t1, a1, a5
    la t2, arr
    add t2, t2, t1
    lw t3, 0(t2)
    bnez t3, _l2
    addi a0, a0, 1
_l2:
    addi a1, a1, 1
    j _l0
_l1:
    li t4, 3
    beq a0, t4, _l3
    #!
_l3:
    li a0, 0
    li a7, 93
    ecall
    #?
