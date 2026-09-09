    #$ coins thread [u32 u32 u32]
    la t0, coins
    li t1, 1
    #] t1, 0(t0)
    li t1, 2
    #] t1, 1(t0)
    li t1, 5
    #] t1, 2(t0)
    #$ dp thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    li a0, 11
    li a1, 4
    li a2, 3
    li a3, 99
    la t0, dp
    li t1, 0
    #] t1, 0(t0)
    li t2, 1
_l0:
    blt a0, t2, _l1
    mul t1, t2, a1
    la t0, dp
    add t0, t0, t1
    #] a3, 0(t0)
    addi t2, t2, 1
    j _l0
_l1:
    li a4, 0
_l2:
    bge a4, a2, _l3
    mul t1, a4, a1
    la t0, coins
    add t0, t0, t1
    #[ a5, 0(t0)
    addi a6, a5, 0
_l4:
    blt a0, a6, _l5
    sub t1, a6, a5
    mul t2, t1, a1
    la t0, dp
    add t0, t0, t2
    #[ t3, 0(t0)
    addi t3, t3, 1
    mul t2, a6, a1
    la t0, dp
    add t0, t0, t2
    #[ t4, 0(t0)
    bge t3, t4, _l6
    #] t3, 0(t0)
_l6:
    addi a6, a6, 1
    j _l4
_l5:
    addi a4, a4, 1
    j _l2
_l3:
    mul t1, a0, a1
    la t0, dp
    add t0, t0, t1
    #[ a3, 0(t0)
    li t0, 3
    beq a3, t0, _l7
    #!
_l7:
    addi t5, a3, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 20
    li t1, 10
    li a2, 0
    bnez t5, _l8
    li t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
_l8:
_l9:
    beqz t5, _l10
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    #] t2, 0(t0)
    addi a2, a2, 1
    j _l9
_l10:
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
_l11:
    beqz t0, _l12
    addi a2, a2, 1
    addi a1, a1, 1
    #[ t0, 0(a1)
    j _l11
_l12:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
    #?
