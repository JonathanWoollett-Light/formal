.global _start
_start:
    csrr tp, mhartid  # per-hart thread-local base
    li t0, 8
    mul tp, tp, t0
    #$ data _ [u8 u8 u8 u8]
    la t0, data
    add t0, t0, tp  # thread-local
    li t1, 7
    sb t1, 0(t0)
    lb t2, 1(t0)
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
data:
    .zero 2
    .zero 6
    .zero 8  # 1 more per-hart copies
