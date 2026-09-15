.global _start
_start:
    #$ starts thread [u32 u32 u32 u32]
    la t0, starts
    li t1, 2
    sw t1, 0(t0)  # #] t1, 0(t0)
    li t1, 1
    sw t1, 4(t0)  # #] t1, 1(t0)
    li t1, 15
    sw t1, 8(t0)  # #] t1, 2(t0)
    li t1, 8
    sw t1, 12(t0)  # #] t1, 3(t0)
    #$ ends thread [u32 u32 u32 u32]
    la t0, ends
    li t1, 6
    sw t1, 0(t0)  # #] t1, 0(t0)
    li t1, 3
    sw t1, 4(t0)  # #] t1, 1(t0)
    li t1, 18
    sw t1, 8(t0)  # #] t1, 2(t0)
    li t1, 10
    sw t1, 12(t0)  # #] t1, 3(t0)
    #$ outs thread [u32 u32 u32 u32]
    #$ oute thread [u32 u32 u32 u32]
    li a0, 4
    li a1, 4
    addi a4, a0, -1
    li a2, 0
_l0:
    bge a2, a0, _l1
    li a3, 0
_l2:
    bge a3, a4, _l3
    mul t1, a3, a1
    la t0, starts
    add t0, t0, t1
    lwu a5, 0(t0)  # #[ a5, 0(t0)
    lwu a6, 4(t0)  # #[ a6, 1(t0)
    bge a6, a5, _l4
    sw a6, 0(t0)  # #] a6, 0(t0)
    sw a5, 4(t0)  # #] a5, 1(t0)
    la t0, ends
    add t2, t0, t1
    lwu t3, 0(t2)  # #[ t3, 0(t2)
    lwu t4, 4(t2)  # #[ t4, 1(t2)
    sw t4, 0(t2)  # #] t4, 0(t2)
    sw t3, 4(t2)  # #] t3, 1(t2)
_l4:
    addi a3, a3, 1
    j _l2
_l3:
    addi a2, a2, 1
    j _l0
_l1:
    la t0, starts
    lwu a5, 0(t0)  # #[ a5, 0(t0)
    la t0, ends
    lwu a6, 0(t0)  # #[ a6, 0(t0)
    li a2, 0
    li a3, 1
_l5:
    bge a3, a0, _l6
    mul t1, a3, a1
    la t0, starts
    add t0, t0, t1
    lwu a7, 0(t0)  # #[ a7, 0(t0)
    la t0, ends
    add t0, t0, t1
    lwu t5, 0(t0)  # #[ t5, 0(t0)
    blt a6, a7, _l7
    addi a6, t5, 0
_l8:
_l7:
    bge a6, a7, _l9
    mul t1, a2, a1
    la t0, outs
    add t0, t0, t1
    sw a5, 0(t0)  # #] a5, 0(t0)
    la t0, oute
    add t0, t0, t1
    sw a6, 0(t0)  # #] a6, 0(t0)
    addi a2, a2, 1
    addi a5, a7, 0
    addi a6, t5, 0
_l9:
    addi a3, a3, 1
    j _l5
_l6:
    mul t1, a2, a1
    la t0, outs
    add t0, t0, t1
    sw a5, 0(t0)  # #] a5, 0(t0)
    la t0, oute
    add t0, t0, t1
    sw a6, 0(t0)  # #] a6, 0(t0)
    addi a2, a2, 1
    li t0, 3
    beq a2, t0, _l10
_l10:
    la t0, outs
    lwu t1, 0(t0)  # #[ t1, 0(t0)
    li t2, 1
    beq t1, t2, _l11
_l11:
    lwu t1, 4(t0)  # #[ t1, 1(t0)
    li t2, 8
    beq t1, t2, _l12
_l12:
    lwu t1, 8(t0)  # #[ t1, 2(t0)
    li t2, 15
    beq t1, t2, _l13
_l13:
    la t0, oute
    lwu t1, 0(t0)  # #[ t1, 0(t0)
    li t2, 6
    beq t1, t2, _l14
_l14:
    lwu t1, 4(t0)  # #[ t1, 1(t0)
    li t2, 10
    beq t1, t2, _l15
_l15:
    lwu t1, 8(t0)  # #[ t1, 2(t0)
    li t2, 18
    beq t1, t2, _l16
_l16:
    addi a4, a2, 0
    li a5, 4
    li a3, 0
_l17:
    bge a3, a4, _l18
    mul t1, a3, a5
    la t0, outs
    add t4, t0, t1
    lwu a6, 0(t4)  # #[ a6, 0(t4)
    addi t5, a6, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 2
    li t1, 10
    li a2, 0
    bnez t5, _l19
_l19:
_l20:
    beqz t5, _l21
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l20
_l21:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str0 thread [u8 u8]
    la t0, __str0
    li t1, 32
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str0
    li a2, 0
    lbu t0, 0(a1)  # #[ t0, 0(a1)
_l22:
    beqz t0, _l23
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l22
_l23:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    mul t1, a3, a5
    la t0, oute
    add t4, t0, t1
    lwu a6, 0(t4)  # #[ a6, 0(t4)
    addi t5, a6, 0
    #$ __local1 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local1
    addi t0, t0, 2
    li t1, 10
    li a2, 0
    bnez t5, _l24
_l24:
_l25:
    beqz t5, _l26
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l25
_l26:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str1 thread [u8 u8]
    la t0, __str1
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str1
    li a2, 0
    lbu t0, 0(a1)  # #[ t0, 0(a1)
_l27:
    beqz t0, _l28
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l27
_l28:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    addi a3, a3, 1
    j _l17
_l18:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
__local0:
    .zero 2
    .balign 8
__local1:
    .zero 2
    .balign 8
__str0:
    .zero 2
    .balign 8
__str1:
    .zero 2
    .balign 8
ends:
    .zero 16
    .balign 8
oute:
    .zero 12
    .balign 8
outs:
    .zero 12
    .balign 8
starts:
    .zero 16
