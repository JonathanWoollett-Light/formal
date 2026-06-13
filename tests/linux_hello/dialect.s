    #$ __str0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __str0
    li t1, 72
    sb t1, 0(t0)
    li t1, 101
    sb t1, 1(t0)
    li t1, 108
    sb t1, 2(t0)
    li t1, 108
    sb t1, 3(t0)
    li t1, 111
    sb t1, 4(t0)
    li t1, 32
    sb t1, 5(t0)
    li t1, 87
    sb t1, 6(t0)
    li t1, 111
    sb t1, 7(t0)
    li t1, 114
    sb t1, 8(t0)
    li t1, 108
    sb t1, 9(t0)
    li t1, 100
    sb t1, 10(t0)
    li t1, 33
    sb t1, 11(t0)
    li t1, 10
    sb t1, 12(t0)
    li t1, 0
    sb t1, 13(t0)
    la a1, __str0
    li a2, 0
    lb t0, 0(a1)
_l0:
    beqz t0, _l1
    addi a2, a2, 1
    addi a1, a1, 1
    lb t0, 0(a1)
    j _l0
_l1:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
    #?
