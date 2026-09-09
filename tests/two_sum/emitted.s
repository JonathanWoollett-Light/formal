.global _start
_start:
    #$ nums thread [u32 u32 u32 u32]
    la t0, nums
    li t1, 2
    sw t1, 0(t0)  # #] t1, 0(t0)
    li t1, 7
    sw t1, 4(t0)  # #] t1, 1(t0)
    li t1, 11
    sw t1, 8(t0)  # #] t1, 2(t0)
    li t1, 15
    sw t1, 12(t0)  # #] t1, 3(t0)
    li a0, 4
    li a1, 9
    li a2, 4
    li a3, 0
    li a4, 0
    li a5, 0
    li t0, 0
_l0:
    bge t0, a0, _l1
    mul t1, t0, a2
    la t2, nums
    add t2, t2, t1
    lwu a6, 0(t2)  # #[ a6, 0(t2)
    addi t3, t0, 1
_l2:
    bge t3, a0, _l3
    mul t4, t3, a2
    la t5, nums
    add t5, t5, t4
    lwu a7, 0(t5)  # #[ a7, 0(t5)
    add t5, a6, a7
    bne t5, a1, _l4
    addi a3, t0, 0
    addi a4, t3, 0
    li a5, 1
_l4:
    addi t3, t3, 1
    j _l2
_l3:
    addi t0, t0, 1
    j _l0
_l1:
    li t0, 1
    beq a5, t0, _l5
_l5:
    li t0, 0
    beq a3, t0, _l6
_l6:
    li t0, 1
    beq a4, t0, _l7
_l7:
    addi t5, a3, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    li t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
_l8:
_l9:
    beqz t5, _l10
_l10:
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
_l11:
    beqz t0, _l12
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l11
_l12:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    addi t5, a4, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    bnez t5, _l13
_l13:
_l14:
    beqz t5, _l15
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l14
_l15:
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
_l16:
    beqz t0, _l17
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l16
_l17:
    li a0, 1
    la a1, __str1
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
__local2:
    .zero 1
    .balign 8
__str0:
    .zero 2
    .balign 8
__str1:
    .zero 2
    .balign 8
nums:
    .zero 16
