    # A `#@` region too small for the store that targets it: the 4-byte `sw`
    # needs bytes 0x80100000..0x80100004 but the region ends at 0x80100002,
    # so no declared region covers the access and the program is rejected as
    # `Invalid` - see tests/nine.rs.
    #@ 0x80100000 0x80100002 rw
    li t0, 0x80100000
    li t1, 42
    sw t1, 0(t0)
    #?
