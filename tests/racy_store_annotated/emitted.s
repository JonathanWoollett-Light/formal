.global _start
_start:
    #$ value global u32
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    lw t1, 0(t0)
    li t2, 0
    beq t1, t2, _l0
_l0:
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 4
