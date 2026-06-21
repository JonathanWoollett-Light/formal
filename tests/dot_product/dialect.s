    #$ x global [i32 i32 i32]
    #$ y global [i32 i32 i32]
    la t0, x
    li t1, -1
    sw t1, 0(t0)
    li t1, 2
    sw t1, 4(t0)
    li t1, -3
    sw t1, 8(t0)
    la t0, y
    li t1, 4
    sw t1, 0(t0)
    li t1, -5
    sw t1, 4(t0)
    li t1, 6
    sw t1, 8(t0)
    li a0, 0
    li a1, 0
    li a2, 3
    li a5, 4
_l0:
    bge a1, a2, _l1
    mul t1, a1, a5
    la t2, x
    add t2, t2, t1
    la t3, y
    add t3, t3, t1
    lw a3, 0(t2)
    lw a4, 0(t3)
    mul a3, a3, a4
    add a0, a0, a3
    addi a1, a1, 1
    j _l0
_l1:
    li a6, -32
    beq a0, a6, _l2
    #!
_l2:
    li a0, 0
    li a7, 93
    ecall
    #?
