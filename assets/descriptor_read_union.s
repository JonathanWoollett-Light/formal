    # Hart 0 reads the descriptor type-number (bytes 0..8); hart 1 reads its
    # length (bytes 16..24). The accessed ranges are the union over all harts
    # and paths, so both fields survive in `.data` with padding between them.
    #$ welcome _ [u8 u8]
    csrr t0, mhartid
    bnez t0, _other
    #& t1, welcome
    li t5, 0
    ld t2, 0(t1)
    j _wait
_other:
    #& t1, welcome
    li t5, 0
    ld t2, 16(t1)
_wait:
    wfi
    #?
