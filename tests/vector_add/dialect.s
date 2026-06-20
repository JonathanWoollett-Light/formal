    vsetivli t0, 4, e32, m1, ta, ma
    vmv.v.i v0, 1
    vmv.v.i v1, 2
    vadd.vv v2, v0, v1
    vmv.x.s a0, v2
    addi t5, a0, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
_l0:
    beqz t5, _l1
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l0
_l1:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
    #?
