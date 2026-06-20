    li a0, 7
    li a1, 0
    li a2, 1
    li a3, 2
    li a4, 3
_l0:
    beq a0, a2, _l1
    rem t0, a0, a3
    bnez t0, _l2
    div a0, a0, a3
_l2:
    beqz t0, _l3
    mul a0, a0, a4
    add a0, a0, a2
_l3:
    add a1, a1, a2
    j _l0
_l1:
    li t5, 16
    beq a1, t5, _l4
    #!
_l4:
    li a0, 0
    li a7, 93
    ecall
    #?
