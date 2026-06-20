    #$ rank_counter global u32
    #$ done_counter global u32
    #$ slots global [u32 u32]
    #$ mine thread u32
    la t0, rank_counter
    li t1, 1
    amoadd.w a3, t1, (t0)
    la t0, mine
    addi a4, a3, 1
    sw a4, 0(t0)
    lw a5, 0(t0)
    li t5, 4
    mul t2, a3, t5
    la t0, slots
    add t0, t0, t2
    sw a5, 0(t0)
    la t0, done_counter
    li t1, 1
    amoadd.w t2, t1, (t0)
    li a0, 1
    bne t2, a0, _l0
    la t0, slots
    lw a5, 0(t0)
    addi t0, t0, 4
    lw a6, 0(t0)
    add a5, a5, a6
    li t3, 0x10000000
    addi t4, a5, 48
    sb t4, 0(t3)
_l0:
    wfi
    #?
