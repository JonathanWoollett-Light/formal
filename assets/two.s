.global _start
_start:
    # Do racy arithmetic with an undefined variable.
    la t0, value

    # Set to 0
    li t1, 0
    sw t1, (t0)

    # Do non-atomic addition
    lw t1, (t0)
    addi t1, t1, 1
    sw t1, (t0)
    
    # require value < 4
    # We compare the value to `4` and if less than jump over `#!` which
    # represents the `fail` keyword.
    lw t1, (t0)
    li t2, 4
    blt t1, t2, _okay
    #!
_okay:

    # Use hart 0 to output a message
    csrr t0, mhartid
    bnez t0, _wait
    la a0, welcome

_write_uart:
    li t1, 0x10000000
    lb t2, (a0)
    beqz t2, _wait
    sb t2, (t1)
    addi a0, a0, 1
    j _write_uart

_wait:
    wfi
    #?

.data
welcome:
.ascii "Hello, World!\n\0"
