.global _start
_start:
    #$ value global _
    la t0, value
    li t1, 7
    sw t1, 0(t0)
    lw t2, 0(t0)
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 4
