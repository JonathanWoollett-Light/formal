.global _start
_start:
    #$ perm thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ work thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ cnt thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    la t0, perm
    li a2, 5
    li t1, 0
_l0:
    beq t1, a2, _l1
    sw t1, 0(t0)
    addi t0, t0, 4
    addi t1, t1, 1
    j _l0
_l1:
    la t0, cnt
    li t1, 0
    li t3, 0
_l2:
    beq t1, a2, _l3
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
_l6:
    beq t2, a2, _l7
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
    li t4, 4
    mul t3, t1, t4
    add t3, t2, t3
    li t4, 0
    addi t5, t1, 0
_l10:
    bge t4, t5, _l11
    lw t1, 0(t2)
    lw a1, 0(t3)
    sw a1, 0(t2)
    sw t1, 0(t3)
    addi t2, t2, 4
    addi t3, t3, -4
    addi t4, t4, 1
    addi t5, t5, -1
    j _l10
_l11:
    addi a0, a0, 1
    lw t1, 0(t0)
    j _l8
_l9:
    bge a5, a0, _l12
    addi a5, a0, 0
_l12:
    addi t0, a0, 0
    bnez a7, _l13
_l14:
    beqz t0, _l15
    addi a6, a6, 1
    addi t0, t0, -1
    j _l14
_l15:
_l13:
    beqz a7, _l16
_l17:
    beqz t0, _l18
    addi a6, a6, -1
    addi t0, t0, -1
    j _l17
_l18:
_l16:
    addi t0, a7, 0
    li a7, 1
    beqz t0, _l19
    li a7, 0
_l19:
    li a4, 1
    li a3, 1
_l20:
    bge a3, a2, _l21
    la t0, perm
    lw t1, 0(t0)
    la t2, perm
    li t3, 0
_l22:
    bge t3, a3, _l23
    lw t4, 4(t2)
    sw t4, 0(t2)
    addi t2, t2, 4
    addi t3, t3, 1
    j _l22
_l23:
    sw t1, 0(t2)
    la t2, cnt
    li t3, 0
_l24:
    bge t3, a3, _l25
    addi t2, t2, 4
    addi t3, t3, 1
    j _l24
_l25:
    lw t4, 0(t2)
    addi t4, t4, 1
    sw t4, 0(t2)
    li t5, 1
    blt a3, t4, _l26
    li a4, 0
    addi a3, a2, 0
    li t5, 0
_l26:
    beqz t5, _l27
    li t3, 0
    sw t3, 0(t2)
    addi a3, a3, 1
_l27:
    j _l20
_l21:
    j _l4
_l5:
    addi a3, a2, 0
    addi t5, a6, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 2
    li t1, 10
    li a2, 0
_l28:
    beqz t5, _l29
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l28
_l29:
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
_l30:
    beqz t0, _l31
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l30
_l31:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    addi t5, a3, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 1
    li t1, 10
    li a2, 0
_l32:
    beqz t5, _l33
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l32
_l33:
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
_l34:
    beqz t0, _l35
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l34
_l35:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    addi t5, a5, 0
    #$ __local4 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local4
    addi t0, t0, 1
    li t1, 10
    li a2, 0
_l36:
    beqz t5, _l37
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l36
_l37:
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
_l38:
    beqz t0, _l39
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l38
_l39:
    li a0, 1
    la a1, __str2
    li a7, 64
    ecall
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
__local2:
    .zero 1
    .balign 8
__local4:
    .zero 1
    .balign 8
__str0:
    .zero 14
    .balign 8
__str1:
    .zero 5
    .balign 8
__str2:
    .zero 2
    .balign 8
cnt:
    .zero 20
    .balign 8
perm:
    .zero 20
    .balign 8
work:
    .zero 20
