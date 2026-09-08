    #$ welcome _ [u8 u8]
    csrr t0, mhartid
    bnez t0, _l0
    #& t1, welcome
    li t5, 0
    #[ t2, 0(t1)
_l0:
    beqz t0, _l1
    #& t1, welcome
    li t5, 0
    #[ t2, 2(t1)
_l1:
    wfi
    #?
