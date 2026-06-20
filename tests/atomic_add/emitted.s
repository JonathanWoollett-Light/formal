.global _start
_start:
    #$ counter thread [u32]
    la t0, counter
    li t1, 5
    sw t1, 0(t0)
    li t3, 3
    amoadd.w t2, t3, (t0)
    li a0, 5
    beq t2, a0, _l0
_l0:
    lw t4, 0(t0)
    li a1, 8
    beq t4, a1, _l1
_l1:
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
