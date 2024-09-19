.global _start
_start:
    #$ value global _
    la t0, value

    # Set to 0
    li t1, 0
    sw t1, (t0)

    # Do non-atomic addition
    lw t1, (t0)
    addi t1, t1, 1
    sw t1, (t0)

    # require value < 4
    lw t1, (t0)
    li t2, 4
    bge t1, t2, _invalid
    #?
_invalid:
    #!
