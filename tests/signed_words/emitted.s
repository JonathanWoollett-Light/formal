.global _start
_start:
    #$ nums global [i32 i32 i32]
    la t0, nums
    li t1, -100
    sw t1, 0(t0)
    li t1, 50
    sw t1, 4(t0)
    li t1, -25
    sw t1, 8(t0)
    lw a0, 0(t0)
    lw a1, 4(t0)
    lw a2, 8(t0)
    add a0, a0, a1
    add a0, a0, a2
    li a3, -75
    beq a0, a3, _l0
_l0:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
nums:
    .zero 12
