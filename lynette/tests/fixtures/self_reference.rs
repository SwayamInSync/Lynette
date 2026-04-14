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
// Known limitation: `shadowed_param` will report a false-positive dependency
// on `helper_spec` because the parameter name matches the spec_fn name and
// cross-function dep detection operates on all path expressions.
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

// --- Non-recursive spec fn whose own name appears as a path but NOT as a call ---
// `non_call_self_ref` is referenced via a let binding (path expression), so it
// shows up in referenced_idents but NOT in call_target_idents. The self-dep
// filtering should therefore exclude it from its own depends_on list.
spec fn non_call_self_ref(x: int) -> int {
    let _shadow: int = if x > 0 { non_call_self_ref } else { 0 };
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
