.global _start
_start:
    #$ x global u8
    la t0, __x_type  # #& t0, x
    li t5, 0
    lb t1, 0(t0)
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .data
__x_type:
    .byte 1

.section .bss
    .balign 8
x:
