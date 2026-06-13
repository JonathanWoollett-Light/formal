#@ 0x80100000 0x80100008 rw
li t0, 0x80100000
li t1, 42
sw t1, 4(t0)
lw t2, 4(t0)
li t3, 0x80200000
li t4, 0x80200004
#@ t3 t4 rw
sw t1, 0(t3)
lw t5, 0(t3)
