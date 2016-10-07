
use std_spirv::ops::Deref;

#[inspirv(interface)]
pub struct Attributes<T>(T);

impl<T> Deref for Attributes<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[inspirv(const_buffer)]
pub struct Cbuffer<T>(T);

impl<T> Deref for Cbuffer<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
