use vstd::prelude::*;

verus! {

pub struct Foo {
    pub x: int,
}

pub struct Bar {
    pub y: int,
}

impl Foo {
    pub open spec fn view(&self) -> int { self.x }

    pub proof fn foo_proof(&self)
        ensures self.view() >= 0 ==> true,
    { }
}

impl Bar {
    pub open spec fn view(&self) -> int { self.y }

    pub proof fn bar_proof(&self)
        ensures self.view() >= 0 ==> true,
    { }
}

// Free function — should depend on BOTH Foo::view and Bar::view
proof fn free_uses_view(a: Foo, b: Bar)
    ensures a.view() >= 0 ==> b.view() >= 0 ==> true,
{ }

} // verus!
