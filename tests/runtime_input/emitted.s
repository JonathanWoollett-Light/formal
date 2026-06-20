.global _start
_start:
    #$ arr thread [u32 u32 u32 u32]
    li a0, 12
    li t2, 4
    rem a1, a0, t2
    la t3, arr
    mul t4, a1, t2
    add t5, t3, t4
    li a2, 7
    sw a2, 0(t5)
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
