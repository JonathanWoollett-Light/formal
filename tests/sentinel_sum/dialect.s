    #$ data thread [u32 u32 u32 u32 u32 u32 u32 u32]
    li a1, 4
    la t0, data
    li t1, 3
    sw t1, 0(t0)
    li t1, 1
    sw t1, 4(t0)
    li t1, 4
    sw t1, 8(t0)
    li t1, 1
    sw t1, 12(t0)
    li t1, 5
    sw t1, 16(t0)
    li t1, 9
    sw t1, 20(t0)
    li t1, 0
    sw t1, 24(t0)
    li a2, 0
    li a3, 0
    la t0, data
    lw t1, 0(t0)
_l0:
    beqz t1, _l1
    add a2, a2, t1
    addi a3, a3, 1
    add t0, t0, a1
    lw t1, 0(t0)
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
