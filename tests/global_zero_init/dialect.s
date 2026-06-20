    #$ counter global u32
    la t0, counter
    lw t1, 0(t0)
    li a0, 0
    beq t1, a0, _l0
    #!
_l0:
    li a0, 0
    li a7, 93
    ecall
    #?
