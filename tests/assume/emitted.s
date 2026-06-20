.global _start
_start:
    #$ arr thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    li a0, 12
    li a2, 0
_l0:
    beq a2, a0, _l1
    li t3, 4
    mul t4, a2, t3
    la t5, arr
    add t5, t5, t4
    sw a2, 0(t5)
    addi a2, a2, 1
    j _l0
_l1:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
arr:
    .zero 20
