    # Load from a raw (non-label) address with no `#@` region or configured
    # section describing it. Every memory access must be verifiable as safe,
    # so this program has no valid configuration: the verifier rejects it as
    # `Invalid` - see tests/eight.rs.
    li t0, 0x100
    li t2, 0
    lw t1, 0(t0)
    #?
