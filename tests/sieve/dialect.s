    #$ flags thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    li a1, 30
    li a0, 0
_l0:
    bge a0, a1, _l1
    la t0, flags
    add t0, t0, a0
    li t3, 0
    sb t3, 0(t0)
    addi a0, a0, 1
    j _l0
_l1:
    li a0, 2
_l2:
    bge a0, a1, _l3
    la t0, flags
    add t0, t0, a0
    lb t1, 0(t0)
    bnez t1, _l4
    add t2, a0, a0
_l5:
    bge t2, a1, _l6
    la t4, flags
    add t4, t4, t2
    li t3, 1
    sb t3, 0(t4)
    add t2, t2, a0
    j _l5
_l6:
_l4:
    addi a0, a0, 1
    j _l2
_l3:
    li a2, 0
    li a0, 2
_l7:
    bge a0, a1, _l8
    la t0, flags
    add t0, t0, a0
    lb t1, 0(t0)
    bnez t1, _l9
    addi a2, a2, 1
_l9:
    addi a0, a0, 1
    j _l7
_l8:
    li t5, 10
    beq a2, t5, _l10
    #!
_l10:
    li a0, 0
    li a7, 93
    ecall
    #?
