    #$ __str0 thread [u8 u8 u8 u8]
    la t0, __str0
    li t1, 72
    sb t1, 0(t0)
    li t1, 105
    sb t1, 1(t0)
    li t1, 32
    sb t1, 2(t0)
    li t1, 0
    sb t1, 3(t0)
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
    #$ __print_buf thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __print_buf
    addi t0, t0, 20
    li t5, 42
    li t1, 10
    li a2, 0
_l2:
    beqz t5, _l3
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)
    addi a2, a2, 1
    j _l2
_l3:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
    #?
