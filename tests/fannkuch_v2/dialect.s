    csrr t0, mhartid
    bnez t0, _l0
    #$ perm thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ work thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ cnt thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    li a2, 3
    #~ a2
    #(
    li a2, 3
    #)
    la t0, perm
    li t1, 0
_l1:
    beq t1, a2, _l2
    sw t1, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l1
_l2:
    la t0, cnt
    li t1, 0
    li t3, 0
_l3:
    beq t1, a2, _l4
    sw t3, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l3
_l4:
    li a5, 0
    li a6, 0
    li a7, 0
    li a4, 0
_l5:
    bnez a4, _l6
    la t0, perm
    la t1, work
    li t2, 0
_l7:
    beq t2, a2, _l8
    lw t4, 0(t0)
    sw t4, 0(t1)
    addi t0, t0, 4
    addi t1, t1, 4
    addi t2, t2, 1
    j _l7
_l8:
    li a0, 0
    la t0, work
    lw t1, 0(t0)
_l9:
    beqz t1, _l10
    la t2, work
    la t3, work
    li t4, 0
_l11:
    beq t4, t1, _l12
    addi t3, t3, 4
    addi t4, t4, 1
    j _l11
_l12:
    li t4, 0
    addi t5, t1, 0
_l13:
    bge t4, t5, _l14
    lw t1, 0(t2)
    lw a1, 0(t3)
    sw a1, 0(t2)
    sw t1, 0(t3)
    addi t2, t2, 4
    addi t3, t3, -4
    addi t4, t4, 1
    addi t5, t5, -1
    j _l13
_l14:
    addi a0, a0, 1
    lw t1, 0(t0)
    j _l9
_l10:
    bge a5, a0, _l15
    addi a5, a0, 0
_l15:
    addi t0, a0, 0
    bnez a7, _l16
_l17:
    beqz t0, _l18
    addi a6, a6, 1
    addi t0, t0, -1
    j _l17
_l18:
_l16:
    beqz a7, _l19
_l20:
    beqz t0, _l21
    addi a6, a6, -1
    addi t0, t0, -1
    j _l20
_l21:
_l19:
    addi t0, a7, 0
    li a7, 1
    beqz t0, _l22
    li a7, 0
_l22:
    li a4, 1
    li a3, 1
_l23:
    bge a3, a2, _l24
    la t0, perm
    lw t1, 0(t0)
    la t2, perm
    li t3, 0
_l25:
    bge t3, a3, _l26
    lw t4, 4(t2)
    sw t4, 0(t2)
    addi t2, t2, 4
    addi t3, t3, 1
    j _l25
_l26:
    sw t1, 0(t2)
    la t2, cnt
    li t3, 0
_l27:
    bge t3, a3, _l28
    addi t2, t2, 4
    addi t3, t3, 1
    j _l27
_l28:
    lw t4, 0(t2)
    addi t4, t4, 1
    sw t4, 0(t2)
    li t5, 1
    blt a3, t4, _l29
    li a4, 0
    addi a3, a2, 0
    li t5, 0
_l29:
    beqz t5, _l30
    li t3, 0
    sw t3, 0(t2)
    addi a3, a3, 1
_l30:
    j _l23
_l24:
    j _l5
_l6:
    addi t5, a6, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l31:
    beqz t5, _l32
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l31
_l32:
    li t3, 0x10000000
_l33:
    beqz a2, _l34
    lb t4, 0(t0)
    sb t4, 0(t3)
    addi t0, t0, 1
    addi a2, a2, -1
    j _l33
_l34:
    li t3, 0x10000000
    li t4, 10
    sb t4, 0(t3)
    addi t5, a5, 0
    #$ __local1 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local1
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l35:
    beqz t5, _l36
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l35
_l36:
    li t3, 0x10000000
_l37:
    beqz a2, _l38
    lb t4, 0(t0)
    sb t4, 0(t3)
    addi t0, t0, 1
    addi a2, a2, -1
    j _l37
_l38:
    li t3, 0x10000000
    li t4, 10
    sb t4, 0(t3)
_l0:
    wfi
    #?
