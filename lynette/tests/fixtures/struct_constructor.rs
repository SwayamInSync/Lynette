use vstd::prelude::*;

verus! {

// Struct constructor should NOT create false deps even if a spec_fn shares
// the name (different namespaces in Rust).
pub struct MyData {
    pub val: int,
}

spec fn MyData_spec() -> int { 42 }

spec fn unrelated_spec() -> bool { true }

// bar_maker uses struct literal MyData { val: 1 }.
// "MyData" is the struct path, NOT a function call.
// It should NOT depend on MyData_spec.
spec fn bar_maker() -> int {
    let d = MyData { val: 1 };
    d.val
}

// This one genuinely calls unrelated_spec.
proof fn real_dep()
    ensures unrelated_spec(),
{ }

} // verus!
