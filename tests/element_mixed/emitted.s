.global _start
_start:
    #$ rec global [u8 u8 i16 u32 i32]
    la t0, rec
    li t1, 200
    sb t1, 0(t0)  # #] t1, 0(t0)
    li t1, -300
    sh t1, 1(t0)  # #] t1, 2(t0)
    li t1, 7
    sw t1, 3(t0)  # #] t1, 3(t0)
    li t1, -9
    sw t1, 7(t0)  # #] t1, 4(t0)
    lbu a0, 0(t0)  # #[ a0, 0(t0)
    li a1, 200
    beq a0, a1, _l0
_l0:
    lh a2, 1(t0)  # #[ a2, 2(t0)
    li a3, -300
    beq a2, a3, _l1
_l1:
    lwu a4, 3(t0)  # #[ a4, 3(t0)
    li a5, 7
    beq a4, a5, _l2
_l2:
    lw a6, 7(t0)  # #[ a6, 4(t0)
    li a7, -9
    beq a6, a7, _l3
_l3:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
rec:
    .zero 11
