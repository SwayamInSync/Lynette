use vstd::prelude::*;

verus! {

spec fn recursive_spec(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { recursive_spec((n - 1) as nat) }
}

// Should NOT have itself in depends_on
proof fn self_ref_proof()
    ensures true ==> true,
{
}

} // verus!
