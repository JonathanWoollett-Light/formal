.global _start
_start:
    #$ arr thread [u32 u32 u32 u32]
    li a0, 12
    li t2, 4
    rem t3, a0, t2
    add t3, t3, t2
    rem a1, t3, t2
    mul t1, a1, t2
    la t0, arr
    add t5, t0, t1
    li a2, 7
    sw a2, 0(t5)  # #] a2, 0(t5)
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
arr:
    .zero 16
