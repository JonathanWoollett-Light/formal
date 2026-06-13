.global _start
_start:
    #$ welcome _ [u8 u8]
    csrr t0, mhartid
    bnez t0, _l0
    la t1, __welcome_type  # #& t1, welcome
    li t5, 0
    ld t2, 0(t1)
_l0:
    beqz t0, _l1
    la t1, __welcome_type  # #& t1, welcome
    li t5, 0
    ld t2, 8(t1)
_l1:
    wfi
    j __halt  # unreachable (program end)
__halt:
    wfi
    j __halt

.section .data
__welcome_type:
    .dword 8                # List
    .dword 2                # length
__welcome_subtypes:

.section .bss
    .balign 8
welcome:
