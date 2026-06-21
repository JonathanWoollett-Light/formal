.global _start
_start:
    #$ vals global [i16 i16 i16]
    la t0, vals
    li t1, -1000
    sh t1, 0(t0)
    li t1, 500
    sh t1, 2(t0)
    li t1, -200
    sh t1, 4(t0)
    lh a0, 0(t0)
    lh a1, 2(t0)
    lh a2, 4(t0)
    add a0, a0, a1
    add a0, a0, a2
    li a3, -700
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
vals:
    .zero 6
