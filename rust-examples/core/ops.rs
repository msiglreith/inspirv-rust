use core::marker::Sized;

#[lang = "add"]
pub trait Add<RHS = Self> {
    type Output;
    fn add(self, rhs: RHS) -> Self::Output;
}

impl Add for u8 {
    type Output = u8;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: u8) -> Self::Output { self + rhs }
}

impl Add for u16 {
    type Output = u16;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: u16) -> Self::Output { self + rhs }
}

impl Add for u32 {
    type Output = u32;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: u32) -> Self::Output { self + rhs }
}

impl Add for u64 {
    type Output = u64;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: u64) -> Self::Output { self + rhs }
}

impl Add for usize {
    type Output = usize;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: usize) -> Self::Output { self + rhs }
}

impl Add for i8 {
    type Output = i8;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: i8) -> Self::Output { self + rhs }
}

impl Add for i16 {
    type Output = i16;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: i16) -> Self::Output { self + rhs }
}

impl Add for i32 {
    type Output = i32;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: i32) -> Self::Output { self + rhs }
}

impl Add for i64 {
    type Output = i64;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: i64) -> Self::Output { self + rhs }
}

impl Add for isize {
    type Output = isize;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: isize) -> Self::Output { self + rhs }
}

impl Add for f32 {
    type Output = f32;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: f32) -> Self::Output { self + rhs }
}

impl Add for f64 {
    type Output = f64;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add(self, rhs: f64) -> Self::Output { self + rhs }
}

#[lang = "sub"]
pub trait Sub<RHS=Self> {
    type Output;
    fn sub(self, rhs: RHS) -> Self::Output;
}

impl Sub for isize {
    type Output = isize;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn sub(self, rhs: isize) -> Self::Output { self - rhs }
}

#[lang = "mul"]
pub trait Mul<RHS=Self> {
    type Output;
    fn mul(self, rhs: RHS) -> Self::Output;
}

impl Mul for isize {
    type Output = isize;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn mul(self, rhs: isize) -> Self::Output { self * rhs }
}

#[lang = "div"]
pub trait Div<RHS=Self> {
    type Output;
    fn div(self, rhs: RHS) -> Self::Output;
}

impl Div for isize {
    type Output = isize;
    #[inline]
    #[inspirv(compiler_builtin)]
    fn div(self, rhs: isize) -> Self::Output { self / rhs }
}

#[lang = "add_assign"]
pub trait AddAssign<Rhs=Self> {
    fn add_assign(&mut self, Rhs);
}

impl AddAssign for u8 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: u8) { *self += other }
}

impl AddAssign for u16 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: u16) { *self += other }
}

impl AddAssign for u32 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: u32) { *self += other }
}

impl AddAssign for u64 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: u64) { *self += other }
}

impl AddAssign for usize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: usize) { *self += other }
}

impl AddAssign for i8 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: i8) { *self += other }
}

impl AddAssign for i16 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: i16) { *self += other }
}

impl AddAssign for i32 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: i32) { *self += other }
}

impl AddAssign for i64 {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: i64) { *self += other }
}

impl AddAssign for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn add_assign(&mut self, other: isize) { *self += other }
}

#[lang = "sub_assign"]
pub trait SubAssign<Rhs=Self> {
    fn sub_assign(&mut self, Rhs);
}

impl SubAssign for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn sub_assign(&mut self, other: isize) { *self -= other }
}

#[lang = "mul_assign"]
pub trait MulAssign<Rhs=Self> {
    fn mul_assign(&mut self, Rhs);
}

impl MulAssign for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn mul_assign(&mut self, other: isize) { *self *= other }
}

#[lang = "div_assign"]
pub trait DivAssign<Rhs=Self> {
    fn div_assign(&mut self, Rhs);
}

impl DivAssign for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn div_assign(&mut self, other: isize) { *self /= other }
}

#[lang = "eq"]
pub trait PartialEq<Rhs: ?Sized = Self> {
    #[inline]
    fn eq(&self, other: &Rhs) -> bool;

    #[inline]
    #[inspirv(compiler_builtin)]
    fn ne(&self, other: &Rhs) -> bool { !self.eq(other) }
}

impl PartialEq for isize {
    #[inline]
    #[inspirv(compiler_builtin)]
    fn eq(&self, other: &isize) -> bool { (*self) == (*other) }
    #[inline]
    #[inspirv(compiler_builtin)]
    fn ne(&self, other: &isize) -> bool { (*self) != (*other) }
}
