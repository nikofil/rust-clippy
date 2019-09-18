//run-rustfix

#![warn(clippy::must_use_unit)]
#![allow(clippy::unused_unit)]

#[must_use]
pub fn must_use_default() {}

#[must_use]
pub fn must_use_unit() -> () {}

#[must_use = "With note"]
pub fn must_use_with_note() {}

fn main() {
    must_use_default();
    must_use_unit();
    must_use_with_note();
}
