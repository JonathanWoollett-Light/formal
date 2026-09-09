    #$ h thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    la t0, h
    li t1, 0
    #] t1, 0(t0)
    #] t1, 2(t0)
    #] t1, 5(t0)
    li t1, 1
    #] t1, 1(t0)
    #] t1, 4(t0)
    #] t1, 6(t0)
    #] t1, 9(t0)
    #] t1, 11(t0)
    li t1, 2
    #] t1, 3(t0)
    #] t1, 8(t0)
    #] t1, 10(t0)
    li t1, 3
    #] t1, 7(t0)
    li a0, 4
    li a2, 0
    li a3, 11
    li a4, 0
    li a5, 0
    li a6, 0
_l0:
    bge a2, a3, _l1
    mul t1, a2, a0
    la t0, h
    add t0, t0, t1
    #[ t2, 0(t0)
    mul t1, a3, a0
    la t0, h
    add t0, t0, t1
    #[ t3, 0(t0)
    bge t2, t3, _l2
    blt t2, a4, _l3
    addi a4, t2, 0
_l3:
    bge t2, a4, _l4
    sub t4, a4, t2
    add a6, a6, t4
_l4:
    addi a2, a2, 1
_l2:
    blt t2, t3, _l5
    blt t3, a5, _l6
    addi a5, t3, 0
_l6:
    bge t3, a5, _l7
    sub t4, a5, t3
    add a6, a6, t4
_l7:
    addi a3, a3, -1
_l5:
    j _l0
_l1:
    li t0, 6
    beq a6, t0, _l8
    #!
_l8:
    addi t5, a6, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
    bnez t5, _l9
    li t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
_l9:
_l10:
    beqz t5, _l11
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
    j _l10
_l11:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str0 thread [u8 u8]
    la t0, __str0
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str0
    li a2, 0
    #[ t0, 0(a1)
_l12:
    beqz t0, _l13
    addi a2, a2, 1
    addi a1, a1, 1
    #[ t0, 0(a1)
    j _l12
_l13:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
    #?
