    # Parsed only (not verified): tests/vague_access.rs drives record_access
    # and emit_executable directly, pinning that an access whose offset is only
    # known as a range fills its maximal span - no byte that *might* be
    # accessed at runtime can be elided from the generated data.
    #$ x global u8
    #& t0, x
