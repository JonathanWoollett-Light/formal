.global _start
_start:
    # Do racy arithmetic on a variables without a defined type.
    # Use global locality so the load/stores are racy.
    # It would otherwise default to thread local.
    #
    # Another way we could enforce locality would be loading the
    # type of `value` (with `#&`) then comparing the type locality
    # and jumping to `invalid` if the type were not thread local.
    #
    # The difference in these approaches is that `#$` is faster and
    # allows defining variables as types not explored. By default the
    # only way to specify a list or union type is with `#$` since these
    # paths are not otherwise explored (since there are an infinite number
    # of list and union type combinations). In essence `#$` = "this is" while
    # later checks are "if this is".
    #$ value global u32
    la t0, value

    # Set to 0
    li t1, 0
    sw t1, (t0)
    
    # require value = 0
    # We compare the value to `0` and if not equal jump to `#!` which
    # represents the `fail` keyword.
    lw t1, (t0)
    li t2, 0
    bne t1, t2, _invalid
    #?
_invalid:
    #!
