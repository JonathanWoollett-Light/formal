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
bge t1, t2, _invalid
csrr t0, mhartid
bnez t0, _wait
#$ welcome _ [u8 u8]
lat t0, welcome
li t2, 8
ld t1, 0(t0)
bne t1, t2, _invalid
addi t0, t0, 16
ld t1, 0(t0)
li t2, 2
bne t1, t2, _invalid
addi t0, t0, -8
ld t0, 0(t0)
li t5, 0
_check_item:
beq t5, t2, _no_items
ld t3, 0(t0)
li t4, 0
bne t3, t4, _invalid
addi t0, t0, 25
addi t5, t5, 1
branch _check_item
_no_items:
la t0, welcome
li t1, 72
sb t1, 0(t0)
li t1, 48
sb t1, 1(t0)
la a0, welcome
_write_uart:
li t1, 0x10000000
lb t2, 0(a0)
beqz t2, _wait
sb t2, 0(t1)
addi a0, a0, 1
j _write_uart
_wait:
wfi
#?
_invalid:
#!