use syntax_pos::MultiSpan;
use rustc_errors::DiagnosticBuilder;
pub use rustc_errors::Level;

pub type PResult<'a, T> = Result<T, DiagnosticBuilder<'a>>;

pub trait DiagnosticBuilderExt {
    fn set_span<S: Into<MultiSpan>>(self, sp: S) -> Self;
}

impl<'a> DiagnosticBuilderExt for DiagnosticBuilder<'a> {
    fn set_span<S: Into<MultiSpan>>(mut self, sp: S) -> Self {
        self.span = sp.into();
        self
    }
}
