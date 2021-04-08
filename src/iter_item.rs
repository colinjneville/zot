#[derive(Debug)]
pub(crate) struct Item<T>(pub(crate) crate::zot::Zot<T>);

impl<T> Iterator for Item<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.take_first()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.0.len();
        (len, Some(len))
    }
}

impl<T> std::iter::DoubleEndedIterator for Item<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.take_last()
    }
}

impl<T> std::iter::ExactSizeIterator for Item<T> {}
impl<T> std::iter::FusedIterator for Item<T> {}
