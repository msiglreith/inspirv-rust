
use super::clone::Clone;

#[lang = "sized"]
#[fundamental]
pub trait Sized { }

#[lang = "copy"]
pub trait Copy { }

#[lang = "sync"]
pub unsafe trait Sync {
    // Empty
}

unsafe impl Sync for .. { }
impl<T: ?Sized> !Sync for *const T { }
impl<T: ?Sized> !Sync for *mut T { }
