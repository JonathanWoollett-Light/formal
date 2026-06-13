.global _start
_start:
    #$ value global _
    la t0, value
    li t1, 7
    sw t1, 0(t0)
    lw t2, 0(t0)
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 4
