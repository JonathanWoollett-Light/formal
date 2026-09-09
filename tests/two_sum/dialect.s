    #$ nums thread [u32 u32 u32 u32]
    la t0, nums
    li t1, 2
    #] t1, 0(t0)
    li t1, 7
    #] t1, 1(t0)
    li t1, 11
    #] t1, 2(t0)
    li t1, 15
    #] t1, 3(t0)
    #$ used thread [u32 u32 u32 u32 u32 u32 u32 u32]
    la t0, used
    li t1, 0
    #] t1, 0(t0)
    li t1, 0
    #] t1, 1(t0)
    li t1, 0
    #] t1, 2(t0)
    li t1, 0
    #] t1, 3(t0)
    li t1, 0
    #] t1, 4(t0)
    li t1, 0
    #] t1, 5(t0)
    li t1, 0
    #] t1, 6(t0)
    li t1, 0
    #] t1, 7(t0)
    #$ keys thread [u32 u32 u32 u32 u32 u32 u32 u32]
    la t0, keys
    li t1, 0
    #] t1, 0(t0)
    li t1, 0
    #] t1, 1(t0)
    li t1, 0
    #] t1, 2(t0)
    li t1, 0
    #] t1, 3(t0)
    li t1, 0
    #] t1, 4(t0)
    li t1, 0
    #] t1, 5(t0)
    li t1, 0
    #] t1, 6(t0)
    li t1, 0
    #] t1, 7(t0)
    #$ vals thread [u32 u32 u32 u32 u32 u32 u32 u32]
    la t0, vals
    li t1, 0
    #] t1, 0(t0)
    li t1, 0
    #] t1, 1(t0)
    li t1, 0
    #] t1, 2(t0)
    li t1, 0
    #] t1, 3(t0)
    li t1, 0
    #] t1, 4(t0)
    li t1, 0
    #] t1, 5(t0)
    li t1, 0
    #] t1, 6(t0)
    li t1, 0
    #] t1, 7(t0)
    li a0, 4
    li a1, 9
    li a2, 8
    li a3, 4
    li a4, 0
    li a5, 0
    li t4, 0
_l0:
    bge t4, a0, _l1
    mul t1, t4, a3
    la t0, nums
    add t0, t0, t1
    #[ a6, 0(t0)
    sub a7, a1, a6
    rem t3, a7, a2
    add t3, t3, a2
    rem t3, t3, a2
    li t5, 1
_l2:
    beqz t5, _l3
    mul t1, t3, a3
    la t0, used
    add t0, t0, t1
    #[ t2, 0(t0)
    bnez t2, _l4
    li t5, 0
_l4:
    beqz t2, _l5
    la t0, keys
    add t0, t0, t1
    #[ t2, 0(t0)
    bne t2, a7, _l6
    la t0, vals
    add t0, t0, t1
    #[ a4, 0(t0)
    addi a5, t4, 0
    li t5, 0
_l6:
_l5:
    beqz t5, _l7
    addi t3, t3, 1
    rem t3, t3, a2
_l7:
    j _l2
_l3:
    rem t3, a6, a2
    add t3, t3, a2
    rem t3, t3, a2
    li t5, 1
_l8:
    beqz t5, _l9
    mul t1, t3, a3
    la t0, used
    add t0, t0, t1
    #[ t2, 0(t0)
    bnez t2, _l10
    addi t2, t2, 1
    #] t2, 0(t0)
    la t0, keys
    add t0, t0, t1
    #] a6, 0(t0)
    la t0, vals
    add t0, t0, t1
    #] t4, 0(t0)
    li t5, 0
_l10:
    beqz t5, _l11
    addi t3, t3, 1
    rem t3, t3, a2
_l11:
    j _l8
_l9:
    addi t4, t4, 1
    j _l0
_l1:
    li t0, 0
    beq a4, t0, _l12
    #!
_l12:
    li t0, 1
    beq a5, t0, _l13
    #!
_l13:
    addi t5, a4, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
    bnez t5, _l14
    li t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
_l14:
_l15:
    beqz t5, _l16
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
    j _l15
_l16:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str0 thread [u8 u8]
    la t0, __str0
    li t1, 32
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str0
    li a2, 0
    #[ t0, 0(a1)
_l17:
    beqz t0, _l18
    addi a2, a2, 1
    addi a1, a1, 1
    #[ t0, 0(a1)
    j _l17
_l18:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    addi t5, a5, 0
    #$ __local2 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local2
    addi t0, t0, 20
    li t1, 10
    li a2, 0
    bnez t5, _l19
    li t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
_l19:
_l20:
    beqz t5, _l21
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
    j _l20
_l21:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str1 thread [u8 u8]
    la t0, __str1
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str1
    li a2, 0
    #[ t0, 0(a1)
_l22:
    beqz t0, _l23
    addi a2, a2, 1
    addi a1, a1, 1
    #[ t0, 0(a1)
    j _l22
_l23:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
    #?
