.global _start
_start:
    # Load from a raw (non-label) address. The verifier does not model raw
    # memory loads, so verifying this returns a `CompilerError::Unsupported`
    # rather than panicking - see tests/error.rs.
    li t0, 0x100
    li t2, 0
    lw t1, 0(t0)
    #?
