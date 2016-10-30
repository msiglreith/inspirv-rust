
use ops::{self, Add};

// TODO
impl Iterator for ops::Range<usize> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        if self.start < self.end {
            let new = self.start + 1;
            let prev = self.start;
            self.start = new;
            Some(prev)
        } else {
            None
        }
    }
}
