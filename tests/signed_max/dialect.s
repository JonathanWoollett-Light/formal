    #$ nums global [i32 i32 i32 i32 i32]
    la t0, nums
    li t1, -5
    sw t1, 0(t0)
    li t1, 3
    sw t1, 4(t0)
    li t1, -1
    sw t1, 8(t0)
    li t1, -8
    sw t1, 12(t0)
    li t1, 2
    sw t1, 16(t0)
    li a5, 4
    lw a0, 0(t0)
    li a1, 1
    li a2, 5
_l0:
    bge a1, a2, _l1
    mul t1, a1, a5
    la t2, nums
    add t2, t2, t1
    lw a3, 0(t2)
    bge a0, a3, _l2
    addi a0, a3, 0
_l2:
    addi a1, a1, 1
    j _l0
_l1:
    li t4, 3
    beq a0, t4, _l3
    #!
_l3:
    li a0, 0
    li a7, 93
    ecall
    #?
