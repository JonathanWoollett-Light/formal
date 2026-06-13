.global _start
_start:
    #$ value global u32
    la t0, __value_type  # #& t0, value
    li t5, 0
    ld t1, 0(t0)
__halt:
    wfi
    j __halt

.section .data
__value_type:
    .dword 4

.section .bss
    .balign 8
value:
