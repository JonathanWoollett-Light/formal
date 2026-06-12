    # `.global` parses but the verifier does not handle it (programs have no
    # explicit entry point - execution starts from the first line), so verifying
    # it returns a `CompilerError::Unsupported` rather than panicking - see
    # tests/unsupported_construct.rs.
    .global _start
    #?
