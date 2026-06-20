.global _start
_start:
    #$ fact thread [u32]
    la t0, fact
    li t1, 1
    li t2, 2
    mul t1, t1, t2
    li t2, 3
    mul t1, t1, t2
    li t2, 4
    mul t1, t1, t2
    li t2, 5
    mul t1, t1, t2
    sw t1, 0(t0)
    lw t3, 0(t0)
    li a0, 120
    beq t3, a0, _l0
_l0:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
fact:
    .zero 4
