.global _start
_start:
    #$ total thread [u32]
    la t0, total
    li t1, 5
    li t2, 3
    add t3, t1, t2
    add t4, t3, t3
    add t5, t4, t1
    addi a1, t5, 100
    sw a1, 0(t0)
    lw t1, 0(t0)
    li a0, 121
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
total:
    .zero 4
