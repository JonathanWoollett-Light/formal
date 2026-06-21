    #$ rank_counter global u32
    #$ done_counter global u32
    #$ cs_slots global [u32 u32]
    #$ max_global global u32
    #$ perm thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ work thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ cnt thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ myrank thread u32
    #$ blockc thread u32
    li a2, 12
    #~ a2
    #(
    li a2, 3
    #)
    la t0, perm
    li t1, 0
    li t3, 12
_l0:
    beq t1, t3, _l1
    sw t1, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l0
_l1:
    la t0, cnt
    li t1, 0
    li t2, 0
_l2:
    beq t1, t3, _l3
    sw t2, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l2
_l3:
    la t0, work
    li t1, 0
_l4:
    beq t1, t3, _l5
    sw t2, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l4
_l5:
    la t0, rank_counter
    li t1, 1
    amoadd.w a3, t1, (t0)
    la t0, myrank
    sw a3, 0(t0)
    la t0, blockc
    sw a3, 0(t0)
    li a5, 0
    li a6, 0
    la t0, blockc
    lw t0, 0(t0)
_l6:
    bge t0, a2, _l7
    la t1, blockc
    lw t1, 0(t1)
    la t0, perm
    li t2, 0
_l8:
    beq t2, a2, _l9
    add t3, t1, t2
    rem t4, t3, a2
    sw t4, 0(t0)
    addi t0, t0, 4
    addi t2, t2, 1
    j _l8
_l9:
    la t0, cnt
    li t2, 0
    li t3, 0
_l10:
    beq t2, a2, _l11
    sw t3, 0(t0)
    addi t0, t0, 4
    addi t2, t2, 1
    j _l10
_l11:
    li a7, 0
    li a4, 0
_l12:
    bnez a4, _l13
    la t0, perm
    la t1, work
    li t2, 0
_l14:
    beq t2, a2, _l15
    lw t4, 0(t0)
    sw t4, 0(t1)
    addi t0, t0, 4
    addi t1, t1, 4
    addi t2, t2, 1
    j _l14
_l15:
    li a0, 0
    la t0, work
    lw t1, 0(t0)
_l16:
    beqz t1, _l17
    la t2, work
    li t4, 4
    mul t3, t1, t4
    add t3, t2, t3
    li t4, 0
    addi t5, t1, 0
_l18:
    bge t4, t5, _l19
    lw t1, 0(t2)
    lw a1, 0(t3)
    sw a1, 0(t2)
    sw t1, 0(t3)
    addi t2, t2, 4
    addi t3, t3, -4
    addi t4, t4, 1
    addi t5, t5, -1
    j _l18
_l19:
    addi a0, a0, 1
    lw t1, 0(t0)
    j _l16
_l17:
    bge a5, a0, _l20
    addi a5, a0, 0
_l20:
    addi t0, a0, 0
    bnez a7, _l21
_l22:
    beqz t0, _l23
    addi a6, a6, 1
    addi t0, t0, -1
    j _l22
_l23:
_l21:
    beqz a7, _l24
_l25:
    beqz t0, _l26
    addi a6, a6, -1
    addi t0, t0, -1
    j _l25
_l26:
_l24:
    addi t0, a7, 0
    li a7, 1
    beqz t0, _l27
    li a7, 0
_l27:
    addi a1, a2, -1
    li a4, 1
    li a3, 1
_l28:
    bge a3, a1, _l29
    la t0, perm
    lw t1, 0(t0)
    la t2, perm
    li t3, 0
_l30:
    bge t3, a3, _l31
    lw t4, 4(t2)
    sw t4, 0(t2)
    addi t2, t2, 4
    addi t3, t3, 1
    j _l30
_l31:
    sw t1, 0(t2)
    la t2, cnt
    li t3, 0
_l32:
    bge t3, a3, _l33
    addi t2, t2, 4
    addi t3, t3, 1
    j _l32
_l33:
    lw t4, 0(t2)
    addi t4, t4, 1
    sw t4, 0(t2)
    li t5, 1
    blt a3, t4, _l34
    li a4, 0
    addi a3, a1, 0
    li t5, 0
_l34:
    beqz t5, _l35
    li t3, 0
    sw t3, 0(t2)
    addi a3, a3, 1
_l35:
    j _l28
_l29:
    j _l12
_l13:
    la t0, blockc
    lw t1, 0(t0)
    addi t1, t1, 2
    sw t1, 0(t0)
    addi t0, t1, 0
    j _l6
_l7:
    la t0, myrank
    lw t1, 0(t0)
    li t2, 4
    mul t3, t1, t2
    la t0, cs_slots
    add t0, t0, t3
    sw a6, 0(t0)
    la t0, max_global
    amomax.w t1, a5, (t0)
    la t0, done_counter
    li t1, 1
    fence rw, rw
    amoadd.w t2, t1, (t0)
    li a0, 1
    bne t2, a0, _l36
    fence rw, rw
    la t0, cs_slots
    lw a5, 0(t0)
    addi t0, t0, 4
    lw a6, 0(t0)
    add a5, a5, a6
    la t0, max_global
    lw a6, 0(t0)
    addi a3, a2, 0
    addi t5, a5, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l37:
    beqz t5, _l38
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l37
_l38:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
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
    li a2, 0
    lb t0, 0(a1)
_l39:
    beqz t0, _l40
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l39
_l40:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    addi t5, a3, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l41:
    beqz t5, _l42
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l41
_l42:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
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
    li a2, 0
    lb t0, 0(a1)
_l43:
    beqz t0, _l44
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l43
_l44:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    addi t5, a6, 0
    #$ __local4 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local4
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
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str2 thread [u8 u8]
    la t0, __str2
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str2
    li a2, 0
    lb t0, 0(a1)
_l47:
    beqz t0, _l48
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l47
_l48:
    li a0, 1
    la a1, __str2
    li a7, 64
    ecall
_l36:
    #?
