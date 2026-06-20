.global _start
_start:
    #$ r thread [u32]
    la t0, r
    li t1, 17
    li t2, 5
    rem t3, t1, t2
    li t4, 100
    li t5, 7
    rem t4, t4, t5
    add t3, t3, t4
    sw t3, 0(t0)
    lw t1, 0(t0)
    li a0, 4
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
r:
    .zero 4
