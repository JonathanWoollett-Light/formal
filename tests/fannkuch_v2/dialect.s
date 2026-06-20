    csrr t0, mhartid
    bnez t0, _l0
    #$ perm thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ work thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ cnt thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    li a2, 12
    #~ a2
    #(
    li a2, 3
    #)
    la t0, perm
    li t1, 0
    li t3, 12
_l1:
    beq t1, t3, _l2
    sw t1, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l1
_l2:
    la t0, cnt
    li t1, 0
    li t2, 0
_l3:
    beq t1, t3, _l4
    sw t2, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l3
_l4:
    la t0, work
    li t1, 0
_l5:
    beq t1, t3, _l6
    sw t2, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l5
_l6:
    li a5, 0
    li a6, 0
    li a7, 0
    li a4, 0
_l7:
    bnez a4, _l8
    la t0, perm
    la t1, work
    li t2, 0
_l9:
    beq t2, a2, _l10
    lw t4, 0(t0)
    sw t4, 0(t1)
    addi t0, t0, 4
    addi t1, t1, 4
    addi t2, t2, 1
    j _l9
_l10:
    li a0, 0
    la t0, work
    lw t1, 0(t0)
_l11:
    beqz t1, _l12
    la t2, work
    la t3, work
    li t4, 0
_l13:
    beq t4, t1, _l14
    addi t3, t3, 4
    addi t4, t4, 1
    j _l13
_l14:
    li t4, 0
    addi t5, t1, 0
_l15:
    bge t4, t5, _l16
    lw t1, 0(t2)
    lw a1, 0(t3)
    sw a1, 0(t2)
    sw t1, 0(t3)
    addi t2, t2, 4
    addi t3, t3, -4
    addi t4, t4, 1
    addi t5, t5, -1
    j _l15
_l16:
    addi a0, a0, 1
    lw t1, 0(t0)
    j _l11
_l12:
    bge a5, a0, _l17
    addi a5, a0, 0
_l17:
    addi t0, a0, 0
    bnez a7, _l18
_l19:
    beqz t0, _l20
    addi a6, a6, 1
    addi t0, t0, -1
    j _l19
_l20:
_l18:
    beqz a7, _l21
_l22:
    beqz t0, _l23
    addi a6, a6, -1
    addi t0, t0, -1
    j _l22
_l23:
_l21:
    addi t0, a7, 0
    li a7, 1
    beqz t0, _l24
    li a7, 0
_l24:
    li a4, 1
    li a3, 1
_l25:
    bge a3, a2, _l26
    la t0, perm
    lw t1, 0(t0)
    la t2, perm
    li t3, 0
_l27:
    bge t3, a3, _l28
    lw t4, 4(t2)
    sw t4, 0(t2)
    addi t2, t2, 4
    addi t3, t3, 1
    j _l27
_l28:
    sw t1, 0(t2)
    la t2, cnt
    li t3, 0
_l29:
    bge t3, a3, _l30
    addi t2, t2, 4
    addi t3, t3, 1
    j _l29
_l30:
    lw t4, 0(t2)
    addi t4, t4, 1
    sw t4, 0(t2)
    li t5, 1
    blt a3, t4, _l31
    li a4, 0
    addi a3, a2, 0
    li t5, 0
_l31:
    beqz t5, _l32
    li t3, 0
    sw t3, 0(t2)
    addi a3, a3, 1
_l32:
    j _l25
_l26:
    j _l7
_l8:
    addi a3, a2, 0
    addi t5, a6, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l33:
    beqz t5, _l34
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l33
_l34:
    li t3, 0x10000000
_l35:
    beqz a2, _l36
    lb t4, 0(t0)
    sb t4, 0(t3)
    addi t0, t0, 1
    addi a2, a2, -1
    j _l35
_l36:
    #$ __str0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __str0
    li t1, 10
    sb t1, 0(t0)
    li t1, 80
    sb t1, 1(t0)
    li t1, 102
    sb t1, 2(t0)
    li t1, 97
    sb t1, 3(t0)
    li t1, 110
    sb t1, 4(t0)
    li t1, 110
    sb t1, 5(t0)
    li t1, 107
    sb t1, 6(t0)
    li t1, 117
    sb t1, 7(t0)
    li t1, 99
    sb t1, 8(t0)
    li t1, 104
    sb t1, 9(t0)
    li t1, 101
    sb t1, 10(t0)
    li t1, 110
    sb t1, 11(t0)
    li t1, 40
    sb t1, 12(t0)
    li t1, 0
    sb t1, 13(t0)
    la a1, __str0
    lb t2, 0(a1)
    li t3, 0x10000000
_l37:
    beqz t2, _l38
    sb t2, 0(t3)
    addi a1, a1, 1
    lb t2, 0(a1)
    j _l37
_l38:
    addi t5, a3, 0
    #$ __local1 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local1
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l39:
    beqz t5, _l40
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l39
_l40:
    li t3, 0x10000000
_l41:
    beqz a2, _l42
    lb t4, 0(t0)
    sb t4, 0(t3)
    addi t0, t0, 1
    addi a2, a2, -1
    j _l41
_l42:
    #$ __str1 thread [u8 u8 u8 u8 u8]
    la t0, __str1
    li t1, 41
    sb t1, 0(t0)
    li t1, 32
    sb t1, 1(t0)
    li t1, 61
    sb t1, 2(t0)
    li t1, 32
    sb t1, 3(t0)
    li t1, 0
    sb t1, 4(t0)
    la a1, __str1
    lb t2, 0(a1)
    li t3, 0x10000000
_l43:
    beqz t2, _l44
    sb t2, 0(t3)
    addi a1, a1, 1
    lb t2, 0(a1)
    j _l43
_l44:
    addi t5, a5, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l45:
    beqz t5, _l46
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l45
_l46:
    li t3, 0x10000000
_l47:
    beqz a2, _l48
    lb t4, 0(t0)
    sb t4, 0(t3)
    addi t0, t0, 1
    addi a2, a2, -1
    j _l47
_l48:
    #$ __str2 thread [u8 u8]
    la t0, __str2
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str2
    lb t2, 0(a1)
    li t3, 0x10000000
_l49:
    beqz t2, _l50
    sb t2, 0(t3)
    addi a1, a1, 1
    lb t2, 0(a1)
    j _l49
_l50:
_l0:
    wfi
    #?
