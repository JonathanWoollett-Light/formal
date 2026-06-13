.global _start
_start:
    #$ value global _
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    lw t1, 0(t0)
    li t2, 4
    blt t1, t2, _l0
_l0:
    csrr t0, mhartid
    bnez t0, _l1
    #$ welcome _ [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __welcome_type  # #& t0, welcome
    li t2, 8
    ld t1, 0(t0)
    beq t1, t2, _l2
_l2:
    addi t0, t0, 16
    ld t1, 0(t0)
    li t2, 13
    beq t1, t2, _l3
_l3:
    addi t0, t0, -8
    ld t0, 0(t0)
    li t5, 0
_l4:
    beq t5, t2, _l5
    ld t3, 0(t0)
    li t4, 0
    beq t3, t4, _l6
_l6:
    addi t0, t0, 8
    addi t5, t5, 1
    j _l4
_l5:
    la t0, welcome
    li t1, 72
    sb t1, 0(t0)
    li t1, 101
    sb t1, 1(t0)
    li t1, 108
    sb t1, 2(t0)
    li t1, 108
    sb t1, 3(t0)
    li t1, 111
    sb t1, 4(t0)
    li t1, 32
    sb t1, 5(t0)
    li t1, 87
    sb t1, 6(t0)
    li t1, 111
    sb t1, 7(t0)
    li t1, 114
    sb t1, 8(t0)
    li t1, 108
    sb t1, 9(t0)
    li t1, 100
    sb t1, 10(t0)
    li t1, 33
    sb t1, 11(t0)
    li t1, 0
    sb t1, 12(t0)
    la a0, welcome
    li t1, 0x10000000
    lb t2, 0(a0)
_l7:
    beqz t2, _l8
    sb t2, 0(t1)
    addi a0, a0, 1
    lb t2, 0(a0)
    j _l7
_l8:
_l1:
    wfi
    j __halt  # unreachable (program end)
__halt:
    wfi
    j __halt

.section .data
__welcome_type:
    .dword 8                # List
    .dword __welcome_subtypes      # subtypes
    .dword 13                # length
__welcome_subtypes:
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0
    .dword 0

.section .bss
    .balign 8
value:
    .zero 4
    .balign 8
welcome:
    .zero 13
