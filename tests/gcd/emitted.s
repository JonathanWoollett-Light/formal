.global _start
_start:
    li a0, 48
    li a1, 36
_l0:
    beqz a1, _l1
    rem t0, a0, a1
    addi a0, a1, 0
    addi a1, t0, 0
    j _l0
_l1:
    li t3, 12
    beq a0, t3, _l2
_l2:
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt
