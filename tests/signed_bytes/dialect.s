    #$ deltas global [i8 i8 i8]
    la t0, deltas
    li t1, -5
    #] t1, 0(t0)
    li t1, 3
    #] t1, 1(t0)
    li t1, -1
    #] t1, 2(t0)
    #[ a0, 0(t0)
    #[ a1, 1(t0)
    #[ a2, 2(t0)
    add a0, a0, a1
    add a0, a0, a2
    li a3, -3
    beq a0, a3, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
