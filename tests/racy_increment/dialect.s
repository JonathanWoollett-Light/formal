    #$ value global _
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    lw t1, 0(t0)
    li t2, 4
    blt t1, t2, _l0
    #!
_l0:
    #?
