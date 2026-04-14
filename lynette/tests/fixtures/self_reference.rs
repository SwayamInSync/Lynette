use vstd::prelude::*;

verus! {

spec fn recursive_spec(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { recursive_spec((n - 1) as nat) }
}

// recursive_spec calls itself, so it should have itself in depends_on.
// self_ref_proof does NOT call itself, so it should NOT have itself in depends_on.
proof fn self_ref_proof()
    ensures true ==> true,
{
}

// --- Parameter shadowing: parameter named same as a spec_fn ---
// Should NOT list helper_spec as a self-dep even though param name matches.
spec fn helper_spec(x: int) -> int {
    x + 1
}

// `helper_spec` here is just a parameter name, not a call.
spec fn shadowed_param(helper_spec: int) -> int {
    helper_spec + 1
}

// --- Recursive spec fn that also depends on another spec fn ---
spec fn recursive_with_dep(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else { helper_spec(s.first()) + recursive_with_dep(s.drop_first()) }
}

// --- Non-recursive spec fn that mentions its own name only in a let binding ---
// (the let binding creates a variable, but `non_call_self_ref` also appears
// as a path expression on the RHS — should NOT self-dep since it's not a call)
spec fn non_call_self_ref(x: int) -> int {
    helper_spec(x)
}

// --- Impl method that calls itself recursively ---
struct MyStruct;

impl MyStruct {
    spec fn impl_recursive(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 0 } else { Self::impl_recursive((n - 1) as nat) }
    }

    spec fn impl_non_recursive(n: nat) -> nat {
        n + 1
    }
}

} // verus!
