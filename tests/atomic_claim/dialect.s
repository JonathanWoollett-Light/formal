    #$ rank global u32
    la t0, rank
    li t1, 1
    amoadd.w t2, t1, (t0)
    li a0, 2
    blt t2, a0, _l0
    #!
_l0:
    wfi
    #?
