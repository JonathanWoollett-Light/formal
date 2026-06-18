.global _start
_start:
    #$ value global _
    la t0, value
    li t2, 0
    sw t2, 0(t0)
    lw t1, 0(t0)
    beq t1, t2, _l0
_l0:
    sw t2, 0(t0)
    lw t1, 0(t0)
    beq t1, t2, _l1
_l1:
    sw t2, 0(t0)
    lw t1, 0(t0)
    beq t1, t2, _l2
_l2:
    sw t2, 0(t0)
    lw t1, 0(t0)
    beq t1, t2, _l3
_l3:
    lw t1, 0(t0)
    beq t1, t2, _l4
_l4:
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 4
