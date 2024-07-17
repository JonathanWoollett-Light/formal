.global _start
_start:
    # Do some racy arithmetic
    la t0, value
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    # Output via vga
    csrr t0, mhartid
    bnez t0, _wait
    j _write_uart
    wfi
_write_uart:
    wfi
_wait:
    wfi
.data
    welcome: .ascii "Welcome to PseudOS\n\0"
    value: .word 0