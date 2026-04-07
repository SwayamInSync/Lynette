use vstd::prelude::*;

verus! {

mod inner {
    use vstd::prelude::*;

    pub open spec fn inner_spec() -> bool { true }

    pub proof fn inner_proof()
        ensures inner_spec(),
    { }
}

spec fn outer_spec() -> bool { true }

// outer_proof references outer_spec only
proof fn outer_proof()
    ensures outer_spec(),
{ }

} // verus!
