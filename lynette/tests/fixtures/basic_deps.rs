use vstd::prelude::*;

verus! {

spec fn my_spec() -> bool { true }

spec fn other_spec() -> int { 42 }

proof fn my_proof()
    ensures my_spec(),
{
}

proof fn multi_dep_proof()
    ensures my_spec(),
            other_spec() > 0 ==> true,
{
}

proof fn no_dep_proof()
    ensures true ==> true,
{
}

spec fn spec_calls_spec() -> bool { my_spec() }

exec fn exec_no_dep() {
    let x: u64 = 1;
}

} // verus!
