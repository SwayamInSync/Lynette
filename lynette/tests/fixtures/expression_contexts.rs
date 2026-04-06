use vstd::prelude::*;

verus! {

spec fn cond_a() -> bool { true }
spec fn cond_b() -> bool { true }
spec fn helper_spec() -> bool { true }

// Multiple spec_fns in one ensures clause
proof fn multi_ensures()
    ensures cond_a(),
            cond_b(),
{ }

// exec_fn using spec_fn in proof block
exec fn exec_with_proof_block() {
    proof {
        assert(cond_a());
    }
}

// Closure referencing spec_fn
spec fn closure_test() -> bool {
    let f = |x: int| helper_spec();
    f(1)
}

// While loop with invariant referencing spec_fn
exec fn loop_with_invariant() {
    let mut i: u64 = 0;
    while i < 10
        invariant cond_a(),
    {
        i = i + 1;
    }
}

// Assert referencing spec_fn
proof fn assert_test() {
    assert(cond_b());
}

} // verus!
