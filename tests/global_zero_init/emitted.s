.global _start
_start:
    #$ counter global u32
    la t0, counter
    lw t1, 0(t0)
    li a0, 0
    beq t1, a0, _l0
_l0:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
counter:
    .zero 4
