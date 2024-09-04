.global _start
_start:
    # Do racy arithmetic with an undefined variable.
    # Use global locality so the load/stores are racy.
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
    # We compare the value to `4` and if less than jump over `#!` which
    # represents the `fail` keyword.
    lw t1, (t0)
    li t2, 4
    bge t1, t2, _invalid

    # Use hart 0 to output a message
    csrr t0, mhartid
    bnez t0, _wait

    #$ welcome _ u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8
    #                H  e  l  l  o  ,     W  o  r  l  d  !  \n 0
    # Type exploration doesn't explore list types since they are infinite, so
    # to define a list a user must define it manually.
    # In this case we leave the locality as unspecified which will default to `thread`.

    # Declare string
    # Get address of type structure
    lat t0, welcome

    # Check variable is list
    li t2, 8 # Load list type number
    ld t1, (t0) # Load type type number
    bne t1, t2, _invalid

    # Check list length
    addi t0, t0, 16 # Increment address to point at length
    ld t1, (t0) # Load length
    li t2, 15 # Load desired length
    bne t1, t2, _invalid

    # Check all values in list are u8
    addi t0, t0, -8 # Decrement address to point at list address
    ld t0, (t0) # Load list address

    li t5, 0 # Use t5 as the counter
_check_item:
    beq t5, t2, _no_items
    ld t3, (t0) # Load type of list item
    li t4, 0 # Load byte type number
    bne t3, t4, _invalid
    addi t0, t0, 24  # Increment list item address
    addi t5, t5, 1 # Increment the count
    branch _check_item # Keep iterating until no items left
_no_items:

    # Set string
    la t0, welcome
    li t1, 72 # 'H'
    sb t1, 0(t0)
    li t1, 101 # 'e'
    sb t1, 1(t0)
    li t1, 108 # 'l'
    sb t1, 2(t0)
    li t1, 108 # 'l'
    sb t1, 3(t0)
    li t1, 111 # 'o'
    sb t1, 4(t0)
    li t1, 44 # ','
    sb t1, 5(t0)
    li t1, 32 # ' '
    sb t1, 6(t0)
    li t1, 87 # 'W'
    sb t1, 7(t0)
    li t1, 111 # 'o'
    sb t1, 8(t0)
    li t1, 114 # 'r'
    sb t1, 9(t0)
    li t1, 108 # 'l'
    sb t1, 10(t0)
    li t1, 100 # 'd'
    sb t1, 11(t0)
    li t1, 32 # '!'
    sb t1, 12(t0)
    li t1, 10 # '\n'
    sb t1, 13(t0)
    li t1, 48 # '0'
    sb t1, 14(t0)

    # Output message
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
_invalid:
    #!
