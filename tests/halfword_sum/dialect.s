    #$ vals global [u16 u16 u16]
    la t0, vals
    li t1, 1000
    #] t1, 0(t0)
    li t1, 2000
    #] t1, 1(t0)
    li t1, 3000
    #] t1, 2(t0)
    #[ a0, 0(t0)
    #[ a1, 1(t0)
    #[ a2, 2(t0)
    add a0, a0, a1
    add a0, a0, a2
    li a3, 6000
    beq a0, a3, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
