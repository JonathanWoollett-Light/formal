    #$ arr global [i32 i32 i32 i32]
    #$ diff global [i32 i32 i32]
    la t0, arr
    li t1, 10
    sw t1, 0(t0)
    li t1, 7
    sw t1, 4(t0)
    li t1, 12
    sw t1, 8(t0)
    li t1, 4
    sw t1, 12(t0)
    li a5, 4
    li a0, 0
    li a1, 3
    li a2, 0
_l0:
    bge a0, a1, _l1
    mul t1, a0, a5
    la t2, arr
    add t2, t2, t1
    lw a3, 0(t2)
    lw a4, 4(t2)
    sub a4, a4, a3
    la t3, diff
    add t3, t3, t1
    sw a4, 0(t3)
    add a2, a2, a4
    addi a0, a0, 1
    j _l0
_l1:
    li a6, -6
    beq a2, a6, _l2
    #!
_l2:
    li a0, 0
    li a7, 93
    ecall
    #?
