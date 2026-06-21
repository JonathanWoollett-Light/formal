    #$ arr thread [u32 u32 u32 u32 u32 u32]
    la t0, arr
    li t1, 1
    sw t1, 0(t0)
    li t1, 3
    sw t1, 4(t0)
    li t1, 5
    sw t1, 8(t0)
    li t1, 7
    sw t1, 12(t0)
    li t1, 9
    sw t1, 16(t0)
    li t1, 11
    sw t1, 20(t0)
    li a3, 7
    li a4, 0
    li a5, 4
    li a6, 2
    li a0, 0
    li a1, 5
_l0:
    blt a1, a0, _l1
    add a2, a0, a1
    div a2, a2, a6
    mul t1, a2, a5
    la t0, arr
    add t0, t0, t1
    lw t2, 0(t0)
    bne t2, a3, _l2
    addi a4, a2, 0
    addi a0, a1, 1
_l2:
    bge t2, a3, _l3
    addi a0, a2, 1
_l3:
    bge a3, t2, _l4
    addi a1, a2, -1
_l4:
    j _l0
_l1:
    li t3, 3
    beq a4, t3, _l5
    #!
_l5:
    li a0, 0
    li a7, 93
    ecall
    #?
