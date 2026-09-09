.global _start
_start:
    #$ grid thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ stack thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    la t0, grid
    li t1, 1
    sw t1, 0(t0)  # #] t1, 0(t0)
    sw t1, 4(t0)  # #] t1, 1(t0)
    sw t1, 20(t0)  # #] t1, 5(t0)
    sw t1, 24(t0)  # #] t1, 6(t0)
    sw t1, 48(t0)  # #] t1, 12(t0)
    sw t1, 72(t0)  # #] t1, 18(t0)
    sw t1, 76(t0)  # #] t1, 19(t0)
    li t1, 0
    sw t1, 8(t0)  # #] t1, 2(t0)
    sw t1, 12(t0)  # #] t1, 3(t0)
    sw t1, 16(t0)  # #] t1, 4(t0)
    sw t1, 28(t0)  # #] t1, 7(t0)
    sw t1, 32(t0)  # #] t1, 8(t0)
    sw t1, 36(t0)  # #] t1, 9(t0)
    sw t1, 40(t0)  # #] t1, 10(t0)
    sw t1, 44(t0)  # #] t1, 11(t0)
    sw t1, 52(t0)  # #] t1, 13(t0)
    sw t1, 56(t0)  # #] t1, 14(t0)
    sw t1, 60(t0)  # #] t1, 15(t0)
    sw t1, 64(t0)  # #] t1, 16(t0)
    sw t1, 68(t0)  # #] t1, 17(t0)
    li a0, 20
    li a1, 4
    li a2, 5
    li a3, 0
    li a4, 0
    li a5, 0
_l0:
    bge a5, a0, _l1
    mul t1, a5, a1
    la t0, grid
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    beqz t2, _l2
    addi a3, a3, 1
    li t2, 0
    sw t2, 0(t0)  # #] t2, 0(t0)
    mul t1, a4, a1
    la t0, stack
    add t0, t0, t1
    sw a5, 0(t0)  # #] a5, 0(t0)
    addi a4, a4, 1
_l3:
    beqz a4, _l4
    addi a4, a4, -1
    mul t1, a4, a1
    la t0, stack
    add t0, t0, t1
    lwu a6, 0(t0)  # #[ a6, 0(t0)
    rem t4, a6, a2
    blt a6, a2, _l5
    sub a7, a6, a2
    mul t1, a7, a1
    la t0, grid
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    beqz t2, _l6
_l6:
_l5:
    add t5, a6, a2
    bge t5, a0, _l7
    mul t1, t5, a1
    la t0, grid
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    beqz t2, _l8
    li t2, 0
    sw t2, 0(t0)  # #] t2, 0(t0)
    mul t1, a4, a1
    la t0, stack
    add t0, t0, t1
    sw t5, 0(t0)  # #] t5, 0(t0)
    addi a4, a4, 1
_l8:
_l7:
    beqz t4, _l9
    addi a7, a6, -1
    mul t1, a7, a1
    la t0, grid
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    beqz t2, _l10
_l10:
_l9:
    addi t5, t4, 1
    beq t5, a2, _l11
    addi a7, a6, 1
    mul t1, a7, a1
    la t0, grid
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    beqz t2, _l12
    li t2, 0
    sw t2, 0(t0)  # #] t2, 0(t0)
    mul t1, a4, a1
    la t0, stack
    add t0, t0, t1
    sw a7, 0(t0)  # #] a7, 0(t0)
    addi a4, a4, 1
_l12:
_l11:
    j _l3
_l4:
_l2:
    addi a5, a5, 1
    j _l0
_l1:
    li t0, 3
    beq a3, t0, _l13
_l13:
    addi t5, a3, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
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
    #$ __str0 thread [u8 u8]
    la t0, __str0
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str0
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
    la a1, __str0
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
__str0:
    .zero 2
    .balign 8
grid:
    .zero 80
    .balign 8
stack:
    .zero 8
