
use super::marker::Sized;

#[lang = "eq"]
pub trait PartialEq<Rhs: ?Sized = Self> {
    /// This method tests for `self` and `other` values to be equal, and is used
    /// by `==`.
    fn eq(&self, other: &Rhs) -> bool;

    /// This method tests for `!=`.
    #[inline]
    fn ne(&self, other: &Rhs) -> bool { !self.eq(other) }
}

pub trait Eq: PartialEq<Self> { }

#[lang = "ord"]
pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    // TODO:
}

