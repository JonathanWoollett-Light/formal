.global _start
_start:
    li a2, 8
    li a0, 5
    add a1, a0, a0
    li t0, 10
    beq a1, t0, _l0
_l0:
    li a0, -2
    rem t3, a0, a2
    add t3, t3, a2
    rem a3, t3, a2
    li t0, 6
    beq a3, t0, _l1
_l1:
    li a0, 11
    rem t3, a0, a2
    add t3, t3, a2
    rem a4, t3, a2
    li t0, 3
    beq a4, t0, _l2
_l2:
    li a0, 42
    addi a5, a0, 0
    li t0, 42
    beq a5, t0, _l3
_l3:
    addi t5, a1, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 2
    li t1, 10
    li a2, 0
    bnez t5, _l4
_l4:
_l5:
    beqz t5, _l6
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l5
_l6:
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
_l7:
    beqz t0, _l8
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l7
_l8:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    addi t5, a3, 0
    #$ __local1 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local1
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    bnez t5, _l9
_l9:
_l10:
    beqz t5, _l11
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l10
_l11:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str1 thread [u8 u8]
    la t0, __str1
    li t1, 32
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str1
    li a2, 0
    lbu t0, 0(a1)  # #[ t0, 0(a1)
_l12:
    beqz t0, _l13
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l12
_l13:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    addi t5, a4, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    bnez t5, _l14
_l14:
_l15:
    beqz t5, _l16
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l15
_l16:
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
    lbu t0, 0(a1)  # #[ t0, 0(a1)
_l17:
    beqz t0, _l18
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l17
_l18:
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
__local1:
    .zero 1
    .balign 8
__local2:
    .zero 1
    .balign 8
__str0:
    .zero 2
    .balign 8
__str1:
    .zero 2
    .balign 8
__str2:
    .zero 2
