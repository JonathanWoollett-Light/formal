.global _start
_start:
    #$ gap thread [u32]
    la t0, gap
    li t1, 100
    li t2, 30
    sub t3, t1, t2
    li t4, 8
    sub t5, t3, t4
    addi t1, t5, -12
    sw t1, 0(t0)
    lw t2, 0(t0)
    li a0, 50
    beq t2, a0, _l0
_l0:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
gap:
    .zero 4
