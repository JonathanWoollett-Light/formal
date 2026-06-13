.global _start
_start:
    #$ value global _
    la t1, value
    li t3, 0
    #@ 0x80100000 0x80100010 rw
    li t4, 2
_l0:
    bge t3, t4, _l1
    sb t3, 4(t1)
    li t1, 0x80100000
    addi t3, t3, 1
    j _l0
_l1:
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 8
