    #$ value global _
    la t0, value
    li t1, 300
    #] t1, 0(t0)
    #[ t2, 0(t0)
    li a0, 300
    beq t2, a0, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
