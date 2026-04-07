use vstd::prelude::*;

verus! {

pub struct Foo {
    pub x: int,
}

pub trait MyTrait {
    spec fn trait_spec(&self) -> bool;
}

impl MyTrait for Foo {
    open spec fn trait_spec(&self) -> bool { true }
}

impl Foo {
    pub open spec fn val(&self) -> int { 42 }

    // Uses self.val() — bare method call, same-impl
    pub proof fn uses_self_dot(&self)
        ensures self.val() >= 0 ==> true,
    { }

    // Uses Self::val — capital-S Self path
    pub proof fn uses_Self_qualified(&self)
        ensures Self::val(self) >= 0 ==> true,
    { }

    // Uses explicit Foo::val
    pub proof fn uses_Foo_qualified(&self)
        ensures Foo::val(self) >= 0 ==> true,
    { }

    // Uses trait spec via self.trait_spec()
    pub proof fn uses_trait_spec(&self)
        ensures self.trait_spec(),
    { }
}

} // verus!
