    #$ perm thread [u32 u32 u32 u32 u32]
    #$ work thread [u32 u32 u32 u32 u32]
    #$ cnt thread [u32 u32 u32 u32 u32]
    la t0, perm
    li t1, 0
    li t2, 5
_l0:
    beq t1, t2, _l1
    sw t1, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l0
_l1:
    la t0, cnt
    li t1, 0
    li t3, 0
_l2:
    beq t1, t2, _l3
    sw t3, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l2
_l3:
    li a5, 0
    li a6, 0
    li a7, 0
    li a4, 0
_l4:
    bnez a4, _l5
    la t0, perm
    la t1, work
    li t2, 0
    li t3, 5
_l6:
    beq t2, t3, _l7
    lw t4, 0(t0)
    sw t4, 0(t1)
    addi t0, t0, 4
    addi t1, t1, 4
    addi t2, t2, 1
    j _l6
_l7:
    li a0, 0
    la t0, work
    lw t1, 0(t0)
_l8:
    beqz t1, _l9
    la t2, work
    la t3, work
    li t4, 0
_l10:
    beq t4, t1, _l11
    addi t3, t3, 4
    addi t4, t4, 1
    j _l10
_l11:
    li t4, 0
    addi t5, t1, 0
_l12:
    bge t4, t5, _l13
    lw t1, 0(t2)
    lw a1, 0(t3)
    sw a1, 0(t2)
    sw t1, 0(t3)
    addi t2, t2, 4
    addi t3, t3, -4
    addi t4, t4, 1
    addi t5, t5, -1
    j _l12
_l13:
    addi a0, a0, 1
    lw t1, 0(t0)
    j _l8
_l9:
    bge a5, a0, _l14
    addi a5, a0, 0
_l14:
    addi t0, a0, 0
    bnez a7, _l15
_l16:
    beqz t0, _l17
    addi a6, a6, 1
    addi t0, t0, -1
    j _l16
_l17:
_l15:
    beqz a7, _l18
_l19:
    beqz t0, _l20
    addi a6, a6, -1
    addi t0, t0, -1
    j _l19
_l20:
_l18:
    addi t0, a7, 0
    li a7, 1
    beqz t0, _l21
    li a7, 0
_l21:
    li a4, 1
    li a3, 1
    li a2, 5
_l22:
    bge a3, a2, _l23
    la t0, perm
    lw t1, 0(t0)
    la t2, perm
    li t3, 0
_l24:
    bge t3, a3, _l25
    lw t4, 4(t2)
    sw t4, 0(t2)
    addi t2, t2, 4
    addi t3, t3, 1
    j _l24
_l25:
    sw t1, 0(t2)
    la t2, cnt
    li t3, 0
_l26:
    bge t3, a3, _l27
    addi t2, t2, 4
    addi t3, t3, 1
    j _l26
_l27:
    lw t4, 0(t2)
    addi t4, t4, 1
    sw t4, 0(t2)
    li t5, 1
    blt a3, t4, _l28
    li a4, 0
    addi a3, a2, 0
    li t5, 0
_l28:
    beqz t5, _l29
    li t3, 0
    sw t3, 0(t2)
    addi a3, a3, 1
_l29:
    j _l22
_l23:
    j _l4
_l5:
    li t0, 7
    beq a5, t0, _l30
    #!
_l30:
    li t0, 11
    beq a6, t0, _l31
    #!
_l31:
    li a0, 0
    li a7, 93
    ecall
    #?
