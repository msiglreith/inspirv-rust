
use super::marker::Sized;

pub trait Clone : Sized {
    fn clone(&self) -> Self;
}
