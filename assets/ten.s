    # A descriptor load whose only successor is `#?` (a path-terminal access).
    # Replays exclude the instruction being processed, so without the explicit
    # check-time record this load would never enter `accessed` and dead-data
    # elimination would elide the descriptor bytes the program still reads at
    # runtime - see tests/ten.rs.
    #$ value global u32
    #& t0, value
    li t5, 0
    ld t1, 0(t0)
    #?
