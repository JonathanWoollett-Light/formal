    csrr t0, mhartid
    bnez t0, _l0
    li t1, 7
    li t2, 7
    beq t1, t2, _l1
    #!
_l1:
_l0:
    wfi
    #?
