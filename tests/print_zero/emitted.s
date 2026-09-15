.global _start
_start:
    li t5, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    li t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
_l0:
_l1:
    beqz t5, _l2
_l2:
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
_l3:
    beqz t0, _l4
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l3
_l4:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    li t5, 42
    #$ __local1 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local1
    addi t0, t0, 2
    li t1, 10
    li a2, 0
    bnez t5, _l5
_l5:
_l6:
    beqz t5, _l7
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l6
_l7:
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
_l8:
    beqz t0, _l9
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l8
_l9:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    li t5, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    li t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
_l10:
_l11:
    beqz t5, _l12
_l12:
    addi a1, t0, 0
    li a0, 1
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
    .zero 1
    .balign 8
__local1:
    .zero 2
    .balign 8
__local2:
    .zero 1
    .balign 8
__str0:
    .zero 2
    .balign 8
__str1:
    .zero 2
