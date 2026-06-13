.global _start
_start:
    #$ data _ [u8 u8 u8 u8]
    la t0, data
    li t1, 7
    sb t1, 0(t0)
    lb t2, 1(t0)
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
data:
    .zero 2
