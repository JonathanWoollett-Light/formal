.global _start
_start:
    #@ 0x80100000 0x80100008 rw
    #$ arr thread [u32 u32 u32 u32]
    li t0, 0x80100000
    li t1, 12
    sw t1, 0(t0)
    lw a0, 0(t0)
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
