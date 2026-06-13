.global _start
_start:
    #$ x global u8
    la t0, __x_type  # #& t0, x
__halt:
    wfi
    j __halt

.section .data
__x_type:
    .zero 16                # never accessed at runtime (padding)
    .dword 0
    .byte 1

.section .bss
    .balign 8
x:
