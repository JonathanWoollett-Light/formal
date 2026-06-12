    # Two `#$` defines disagree about the type of `value`: the second is
    # checked against the configured first, no configuration satisfies both,
    # and the program is rejected as `Invalid`.
    #$ value global u8
    #$ value global u16
    #?
