/// A collection of exactly zero, one, or two `T` elements.
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Zot<T> {
    /// No value
    Zero,
    /// One value
    One(T),
    /// Two values
    Two(T, T),
}

/////////////////////////////////////////////////////////////////////////////
// Type implementation
/////////////////////////////////////////////////////////////////////////////

impl<T> Zot<T> {
    /////////////////////////////////////////////////////////////////////////
    // Querying the contained values
    /////////////////////////////////////////////////////////////////////////

    /// Returns `true` if the `Zot` is a [`Zero`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<u32>= zot::Zot::Zero;
    /// assert_eq!(x.is_zero(), true);
    ///
    /// let x: zot::Zot<u32>= zot::Zot::Two(2, 3);
    /// assert_eq!(x.is_zero(), false);
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_zero(&self) -> bool {
        match self {
            Zot::Zero => true,
            _ => false,
        }
    }

    /// Returns `true` if the `Zot` is a [`One`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<u32>= zot::Zot::One(2);
    /// assert_eq!(x.is_one(), true);
    ///
    /// let x: zot::Zot<u32>= zot::Zot::Two(2, 3);
    /// assert_eq!(x.is_one(), false);
    /// ```
    #[must_use = "if you intended to assert that this has a value, consider `.unwrap_one()` instead"]
    #[inline]
    pub const fn is_one(&self) -> bool {
        match self {
            Zot::One(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if the `Zot` is a [`Two`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<u32>= zot::Zot::Two(2, 3);
    /// assert_eq!(x.is_two(), true);
    ///
    /// let x: zot::Zot<u32>= zot::Zot::One(2);
    /// assert_eq!(x.is_two(), false);
    /// ```
    #[must_use = "if you intended to assert that this has a value, consider `.unwrap_two()` instead"]
    #[inline]
    pub const fn is_two(&self) -> bool {
        match self {
            Zot::Two(_, _) => true,
            _ => false,
        }
    }

    /// Returns `true` if at least one contained value equals the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<u32>= zot::Zot::One(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: zot::Zot<u32>= zot::Zot::One(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: zot::Zot<u32>= zot::Zot::Two(3, 2);
    /// assert_eq!(x.contains(&2), true);

    /// let x: zot::Zot<u32>= zot::Zot::Zero;
    /// assert_eq!(x.contains(&2), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains<U>(&self, v: &U) -> bool
    where U: PartialEq<T> {
        match self {
            Zot::Zero => false,
            Zot::One(v0) => v == v0,
            Zot::Two(v0, v1) => v == v0 || v == v1,
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Adapter for working with references
    /////////////////////////////////////////////////////////////////////////

    /// Converts from `&Zot<T>` to `Zot<&T>`.
    #[inline]
    pub const fn as_ref(&self) -> Zot<&T> {
        match *self {
            Zot::Zero => Zot::Zero,
            Zot::One(ref v0) => Zot::One(v0),
            Zot::Two(ref v0, ref v1) => Zot::Two(v0, v1),
        }
    }

    /// Converts from `&mut Zot<T>` to `Zot<&mut T>`.
    #[inline]
    pub fn as_mut(&mut self) -> Zot<&mut T> {
        match *self {
            Zot::Zero => Zot::Zero,
            Zot::One(ref mut v0) => Zot::One(v0),
            Zot::Two(ref mut v0, ref mut v1) => Zot::Two(v0, v1),
        }
    }

    /// Converts from [`Pin`]`<&Zot<T>>` to `Zot<`[`Pin`]`<&T>>`.
    #[inline]
    pub fn as_pin_ref(self: std::pin::Pin<&Self>) -> Zot<std::pin::Pin<&T>> {
        // SAFETY: `x` is guaranteed to be pinned because it comes from `self`
        // which is pinned.
        unsafe { std::pin::Pin::get_ref(self).as_ref().map(|x| std::pin::Pin::new_unchecked(x)) }
    }

    /// Converts from [`Pin`]`<&mut Zot<T>>` to `Zot<`[`Pin`]`<&mut T>>`.
    #[inline]
    pub fn as_pin_mut(self: std::pin::Pin<&mut Self>) -> Zot<std::pin::Pin<&mut T>> {
        // SAFETY: `get_unchecked_mut` is never used to move the `Zot` inside `self`.
        // `x` is guaranteed to be pinned because it comes from `self` which is pinned.
        unsafe { std::pin::Pin::get_unchecked_mut(self).as_mut().map(|x| std::pin::Pin::new_unchecked(x)) }
    }

    /////////////////////////////////////////////////////////////////////////
    // Getting to contained values
    /////////////////////////////////////////////////////////////////////////

    /// Returns the contained [`Zero`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is not [`Zero`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<&str>= zot::Zot::Zero;
    /// assert_eq!(x.expect_zero("fruits are healthy"), ());
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::One("value");
    /// x.expect_zero("fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    #[inline]
    pub fn expect_zero(self, msg: &str) -> () {
        match self {
            Zot::Zero => (),
            _ => expect_failed(msg),
        }
    }

    /// Returns the contained [`One`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is not [`One`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::One("value");
    /// assert_eq!(x.expect_one("fruits are healthy"), "value");
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::Two("value", "value");
    /// x.expect_one("fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    #[inline]
    pub fn expect_one(self, msg: &str) -> T {
        match self {
            Zot::One(value) => value,
            _ => expect_failed(msg),
        }
    }

    /// Returns the contained [`Two`] values as a `(T, T)`, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is not [`Two`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::Two("value", "value");
    /// assert_eq!(x.expect_two("fruits are healthy"), ("value", "value"));
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::One("value");
    /// x.expect_two("fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    #[inline]
    pub fn expect_two(self, msg: &str) -> (T, T) {
        match self {
            Zot::Two(value0, value1) => (value0, value1),
            _ => expect_failed(msg),
        }
    }

    /// Returns the contained [`Zero`] or [`One`] value as an `Option<T>`, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is [`Two`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::One("value");
    /// assert_eq!(x.expect_option("fruits are healthy"), Some("value"));
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::Two("value", "value");
    /// x.expect_option("fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    #[inline]
    pub fn expect_option(self, msg: &str) -> Option<T> {
        match self {
            Zot::Zero => None,
            Zot::One(v) => Some(v),
            Zot::Two(_, _) => expect_failed(msg),
        }
    }

    /// Returns the contained [`Zero`] value, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Instead, prefer to use pattern matching and handle the [`Zero`]
    /// case explicitly, or call [`unwrap_zero_or`], [`unwrap_zero_or_else`].
    ///
    /// [`unwrap_zero_or`]: zot::Zot::unwrap_zero_or
    /// [`unwrap_zero_or_else`]: zot::Zot::unwrap_zero_or_else
    ///
    /// # Panics
    ///
    /// Panics if the self value is not [`Zero`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<&str>= zot::Zot::Zero;
    /// assert_eq!(x.unwrap_zero(), ());
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::One("air");
    /// assert_eq!(x.unwrap_zero(), ()); // fails
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_zero(self) -> () {
        self.expect_zero("called unwrap_zero on a non-zero Zot")
    }

    /// Returns the contained [`One`] value, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Instead, prefer to use pattern matching and handle the [`One`]
    /// case explicitly, or call [`unwrap_one_or`], [`unwrap_one_or_else`].
    ///
    /// [`unwrap_one_or`]: zot::Zot::unwrap_one_or
    /// [`unwrap_one_or_else`]: zot::Zot::unwrap_one_or_else
    ///
    /// # Panics
    ///
    /// Panics if the self value is not [`One`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::One("air");
    /// assert_eq!(x.unwrap_one(), "air");
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::Two("air", "wind");
    /// assert_eq!(x.unwrap_one(), "air"); // fails
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_one(self) -> T {
        self.expect_one("called unwrap_one on a non-one Zot")
    }

    /// Returns the contained [`Two`] value as a `(T, T)`, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Instead, prefer to use pattern matching and handle the [`Two`]
    /// case explicitly, or call [`unwrap_two_or`], [`unwrap_two_or_else`].
    ///
    /// [`unwrap_two_or`]: zot::Zot::unwrap_two_or
    /// [`unwrap_two_or_else`]: zot::Zot::unwrap_two_or_else
    ///
    /// # Panics
    ///
    /// Panics if the self value is not [`Two`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::Two("air", "wind");
    /// assert_eq!(x.unwrap_two(), ("air", "wind"));
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::One("air");
    /// assert_eq!(x.unwrap_two(), ("air", "wind")); // fails
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_two(self) -> (T, T) {
        self.expect_two("called unwrap_two on a non-two Zot")
    }

    /// Returns the contained [`Zero`] or [`One`] value as an `Option<T>`, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Instead, prefer to use pattern matching and handle the [`Zero`]
    /// and [`One'] cases explicitly, or call [`unwrap_option_or`], [`unwrap_option_or_else`].
    ///
    /// [`unwrap_option_or`]: zot::Zot::unwrap_option_or
    /// [`unwrap_option_or_else`]: zot::Zot::unwrap_option_or_else
    ///
    /// # Panics
    ///
    /// Panics if the self value is not [`Zero`] or [`One`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::One("air");
    /// assert_eq!(x.unwrap_option(), Some("air"));
    /// ```
    ///
    /// ```{.should_panic}
    /// let x= zot::Zot::Two("air", "wind");
    /// assert_eq!(x.unwrap_option(), Some("air")); // fails
    /// ```
    pub fn unwrap_option(self) -> Option<T> {
        self.expect_option("called unwrap_option on a two Zot")
    }

    /// Returns the contained [`One`] value or a provided default.
    ///
    /// Arguments passed to `unwrap_one_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`unwrap_one_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`unwrap_one_or_else`]: zot::Zot::unwrap_one_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(zot::Zot::One("car").unwrap_one_or("bike"), "car");
    /// assert_eq!(zot::Zot::Zero.unwrap_one_or("bike"), "bike");
    /// ```
    #[inline]
    pub fn unwrap_one_or(self, default: T) -> T {
        match self {
            Zot::One(v0) => v0,
            _ => default,
        }
    }

    /// Returns the contained [`Two`] value as a `(T, T)` or a provided default.
    ///
    /// Arguments passed to `unwrap_two_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`unwrap_two_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`unwrap_two_or_else`]: zot::Zot::unwrap_two_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(zot::Zot::Two("car", "truck").unwrap_two_or(("bike", "pogo")), ("car", "truck"));
    /// assert_eq!(zot::Zot::Zero.unwrap_two_or(("bike", "pogo")), ("bike", "pogo"));
    /// ```
    #[inline]
    pub fn unwrap_two_or(self, default: (T, T)) -> (T, T) {
        match self {
            Zot::Two(v0, v1) => (v0, v1),
            _ => default,
        }
    }

    /// Returns the contained [`One`] value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```
    /// let k = 10;
    /// assert_eq!(zot::Zot::One(4).unwrap_one_or_else(|| 2 * k), 4);
    /// assert_eq!(zot::Zot::Zero.unwrap_one_or_else(|| 2 * k), 20);
    /// ```
    #[inline]
    pub fn unwrap_one_or_else<F: FnOnce() -> T>(self, f: F) -> T {
        match self {
            Zot::One(v0) => v0,
            _ => f(),
        }
    }

    /// Returns the contained [`Two`] value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```
    /// let k = 10;
    /// assert_eq!(zot::Zot::Two(4, 5).unwrap_two_or_else(|| (2 * k, 3 * k)), (4, 5));
    /// assert_eq!(zot::Zot::Zero.unwrap_two_or_else(|| (2 * k, 3 * k)), (20, 30));
    /// ```
    #[inline]
    pub fn unwrap_two_or_else<F: FnOnce() -> (T, T)>(self, f: F) -> (T, T) {
        match self {
            Zot::Two(v0, v1) => (v0, v1),
            _ => f(),
        }
    }

    pub fn first(&self) -> Option<&T> {
        match self {
            Zot::Zero => None,
            Zot::One(t0) |
            Zot::Two(t0, _) => Some(t0),
        }
    }

    pub fn first_mut(&mut self) -> Option<&mut T> {
        match self {
            Zot::Zero => None,
            Zot::One(t0) |
            Zot::Two(t0, _) => Some(t0),
        }
    }

    pub fn second(&self) -> Option<&T> {
        match self {
            Zot::Zero |
            Zot::One(_) => None,
            Zot::Two(_, t1) => Some(t1),
        }
    }

    pub fn second_mut(&mut self) -> Option<&mut T> {
        match self {
            Zot::Zero |
            Zot::One(_) => None,
            Zot::Two(_, t1) => Some(t1),
        }
    }

    pub fn last(&self) -> Option<&T> {
        match self {
            Zot::Zero => None,
            Zot::One(t0) => Some(t0),
            Zot::Two(_, t1) => Some(t1),
        }
    }

    pub fn last_mut(&mut self) -> Option<&mut T> {
        match self {
            Zot::Zero => None,
            Zot::One(t0) => Some(t0),
            Zot::Two(_, t1) => Some(t1),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Transforming contained values
    /////////////////////////////////////////////////////////////////////////

    /// Maps a `Zot<T>` to `Zot<U>` by applying a function to a contained values.
    #[inline]
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> Zot<U> {
        match self {
            Zot::Zero => Zot::Zero,
            Zot::One(t0) => Zot::One(f(t0)),
            Zot::Two(t0, t1) => Zot::Two(f(t0), f(t1)),
        }
    }

    /// Returns an iterator over the contained values.
    ///
    /// # Examples
    ///
    /// ```
    /// let x= zot::Zot::Two(4, 5);
    /// let mut iter = x.iter();
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&5));
    ///
    /// let x= zot::Zot::One(4);
    /// let mut iter = x.iter();
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub const fn iter(&self) -> Iter<'_, T> {
        Iter(crate::iter_item::Item(self.as_ref()))
    }

    /// Returns a mutable iterator over the contained values.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x= zot::Zot::One(4);
    /// match x.iter_mut().next() {
    ///     Some(v) => *v = 42,
    ///     None => {},
    /// }
    /// assert_eq!(x, zot::Zot::One(42));
    ///
    /// let mut x: zot::Zot<u32>= zot::Zot::Zero;
    /// assert_eq!(x.iter_mut().next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut(crate::iter_item::Item(self.as_mut()))
    }

    /////////////////////////////////////////////////////////////////////////
    // Misc
    /////////////////////////////////////////////////////////////////////////

    /// Takes the value out of the `Zot`, leaving a [`Zero`] in its place.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::One(2);
    /// let y = x.take();
    /// assert_eq!(x, zot::Zot::Zero);
    /// assert_eq!(y, zot::Zot::One(2));
    ///
    /// let mut x: zot::Zot<u32> = zot::Zot::Zero;
    /// let y = x.take();
    /// assert_eq!(x, zot::Zot::Zero);
    /// assert_eq!(y, zot::Zot::Zero);
    /// ```
    #[inline]
    pub fn take(&mut self) -> Zot<T> {
        std::mem::take(self)
    }

    /// Takes the first value out of the `Zot`, leaving only [`One`] if 
    /// there were initially two values, otherwise [`Zero`].
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::Two(2, 3);
    /// let y = x.take_first();
    /// assert_eq!(x, zot::Zot::One(3));
    /// assert_eq!(y, Some(2));
    ///
    /// let mut x: zot::Zot<u32> = zot::Zot::Zero;
    /// let y = x.take_first();
    /// assert_eq!(x, zot::Zot::Zero);
    /// assert_eq!(y, None);
    /// ```
    #[inline]
    pub fn take_first(&mut self) -> Option<T> {
        match std::mem::take(self) {
            Zot::Zero => None,
            Zot::One(v0) => Some(v0),
            Zot::Two(v0, v1) => {
                *self = Zot::One(v1);
                Some(v0)
            }
        }
    }

    /// Takes the second value out of the `Zot` if it is [`Two`], leaving 
    /// only [`One`], otherwise the `Zot` is unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::Two(2, 3);
    /// let y = x.take_second();
    /// assert_eq!(x, zot::Zot::One(2));
    /// assert_eq!(y, Some(3));
    ///
    /// let mut x: zot::Zot<u32> = zot::Zot::One(2);
    /// let y = x.take_second();
    /// assert_eq!(x, zot::Zot::One(2));
    /// assert_eq!(y, None);
    /// ```
    #[inline]
    pub fn take_second(&mut self) -> Option<T> {
        match std::mem::take(self) {
            Zot::Zero => None,
            Zot::One(v0) => {
                *self = Zot::One(v0);
                None
            }
            Zot::Two(v0, v1) => {
                *self = Zot::One(v0);
                Some(v1)
            }
        }
    }

    /// Takes the last value out of the `Zot`, leaving only [`One`] if 
    /// there were initially two values, otherwise [`Zero`].
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::Two(2, 3);
    /// let y = x.take_last();
    /// assert_eq!(x, zot::Zot::One(2));
    /// assert_eq!(y, Some(3));
    ///
    /// let mut x: zot::Zot<u32> = zot::Zot::Zero;
    /// let y = x.take_last();
    /// assert_eq!(x, zot::Zot::Zero);
    /// assert_eq!(y, None);
    /// ```
    #[inline]
    pub fn take_last(&mut self) -> Option<T> {
        match std::mem::take(self) {
            Zot::Zero => None,
            Zot::One(v0) => Some(v0),
            Zot::Two(v0, v1) => {
                *self = Zot::One(v0);
                Some(v1)
            }
        }
    }

    /// Replaces the actual value in the `Zot` by the value given in parameter,
    /// returning the old value,
    /// leaving a [`One`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::One(2);
    /// let old = x.replace_one(5);
    /// assert_eq!(x, zot::Zot::One(5));
    /// assert_eq!(old, zot::Zot::One(2));
    ///
    /// let mut x = zot::Zot::Zero;
    /// let old = x.replace_one(3);
    /// assert_eq!(x, zot::Zot::One(3));
    /// assert_eq!(old, zot::Zot::Zero);
    /// ```
    #[inline]
    pub fn replace_one(&mut self, value: T) -> Zot<T> {
        std::mem::replace(self, Zot::One(value))
    }

    /// Replaces the actual value in the `Zot` by the values given in parameter,
    /// returning the old value,
    /// leaving a [`Two`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::One(2);
    /// let old = x.replace_two(5, 6);
    /// assert_eq!(x, zot::Zot::Two(5, 6));
    /// assert_eq!(old, zot::Zot::One(2));
    ///
    /// let mut x = zot::Zot::Zero;
    /// let old = x.replace_two(3, 4);
    /// assert_eq!(x, zot::Zot::Two(3, 4));
    /// assert_eq!(old, zot::Zot::Zero);
    /// ```
    #[inline]
    pub fn replace_two(&mut self, first: T, second: T) -> Zot<T> {
        std::mem::replace(self, Zot::Two(first, second))
    }

    /// Replaces the first value in the `Zot` by the value given in parameter,
    /// returning the old value if present,
    /// leaving a [`One`] or [`Two`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::Two(2, 3);
    /// let old = x.replace_first(5);
    /// assert_eq!(x, zot::Zot::Two(5, 3));
    /// assert_eq!(old, Some(2));
    ///
    /// let mut x = zot::Zot::Zero;
    /// let old = x.replace_first(3);
    /// assert_eq!(x, zot::Zot::One(3));
    /// assert_eq!(old, None);
    /// ```
    #[inline]
    pub fn replace_first(&mut self, value: T) -> Option<T> {
        match self.take() {
            Zot::Zero => {
                *self = Zot::One(value);
                None
            },
            Zot::One(v0) => {
                *self = Zot::One(value);
                Some(v0)
            }
            Zot::Two(v0, v1) => {
                *self = Zot::Two(value, v1);
                Some(v0)
            }
        }
    }

    /// Replaces the last value in the `Zot` by the value given in parameter,
    /// returning the old value if present,
    /// leaving a [`One`] or [`Two`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Zot::Two(2, 3);
    /// let old = x.replace_last(5);
    /// assert_eq!(x, zot::Zot::Two(2, 5));
    /// assert_eq!(old, Some(3));
    ///
    /// let mut x = zot::Zot::Zero;
    /// let old = x.replace_last(3);
    /// assert_eq!(x, zot::Zot::One(3));
    /// assert_eq!(old, None);
    /// ```
    #[inline]
    pub fn replace_last(&mut self, value: T) -> Option<T> {
        match self.take() {
            Zot::Zero => {
                *self = Zot::One(value);
                None
            },
            Zot::One(v0) => {
                *self = Zot::One(value);
                Some(v0)
            }
            Zot::Two(v0, v1) => {
                *self = Zot::Two(v0, value);
                Some(v1)
            }
        }
    }

    /// Construct a `Zot` from two `Option`s.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<u32>= zot::Zot::from_options(None, Some(3));
    /// assert_eq!(x, zot::Zot::One(3));
    ///
    /// let x: zot::Zot<u32>= zot::Zot::from_options(Some(2), Some(3));
    /// assert_eq!(x, zot::Zot::Two(2, 3));
    /// ```
    pub fn from_options(a: Option<T>, b: Option<T>) -> Self {
        match a {
            Some(a) => match b {
                Some(b) => Zot::Two(a, b),
                None => Zot::One(a),
            }
            None => match b {
                Some(b) => Zot::One(b),
                None => Zot::Zero,
            }
        }
    }

    /// Returns the number of contained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Zot<u32>= zot::Zot::Two(7, 20);
    /// assert_eq!(x.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        match self {
            Zot::Zero => 0,
            Zot::One(_) => 1,
            Zot::Two(_, _) => 2,
        }
    }

    



    


    pub fn without_first(&self) -> Self
    where T: Clone {
        if let Zot::Two(_, t1) = self {
            Zot::One(t1.clone())
        } else {
            self.clone()
        }
    }

    pub fn without_second(&self) -> Self
    where T: Clone {
        if let Zot::Two(t0, _) = self {
            Zot::One(t0.clone())
        } else {
            self.clone()
        }
    }

    pub fn remove_second(self) -> Self 
    where T: Clone {
        if let Zot::Two(t0, _) = self {
            Zot::One(t0)
        } else {
            self
        }
    }

    

    
    
}

/////////////////////////////////////////////////////////////////////////////
// Trait implementations
/////////////////////////////////////////////////////////////////////////////

impl<T> From<Option<T>> for Zot<T> {
    fn from(t: Option<T>) -> Self {
        match t {
            Some(t) => Self::One(t),
            None => Self::Zero,
        }
    }
}

impl<T> From<T> for Zot<T> {
    fn from(t: T) -> Self {
        Self::One(t)
    }
}

impl<T> From<(T, T)> for Zot<T> {
    fn from(ts: (T, T)) -> Self {
        Self::Two(ts.0, ts.1)
    }
}

impl<T> From<(T, Option<T>)> for Zot<T> {
    fn from(ts: (T, Option<T>)) -> Self {
        let (t0, t1) = ts;
        match t1 {
            Some(t1) => Self::Two(t0, t1),
            None => Self::One(t0),
        }
    }
}

impl<T> From<(Option<T>, T)> for Zot<T> {
    fn from(ts: (Option<T>, T)) -> Self {
        match ts.0 {
            Some(t0) => Self::Two(t0, ts.1),
            None => Self::One(ts.1),
        }
    }
}

impl<T> From<(Option<T>, Option<T>)> for Zot<T> {
    /// Creates a `Zot` from two `Option`s.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Zot::from((None, Some(2)));
    /// assert_eq!(x, zot::Zot::One(2));
    ///
    /// let x = zot::Zot::from((Some(3), Some(4)));
    /// assert_eq!(x, zot::Zot::Two(3, 4));
    /// ```
    fn from(ts: (Option<T>, Option<T>)) -> Self {
        let (t0, t1) = ts;
        if let Some(t0) = t0 {
            (t0, t1).into()
        } else {
            t1.into()
        }
    }
}

impl<T> From<Zot<T>> for (Option<T>, Option<T>) {
    /// Convert a `Zot` into a tuple of `Option`s.
    /// If the second element of the tuple is `Some`,
    /// the first element will also be `Some`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: (Option<_>, Option<_>) = zot::Zot::One(2).into();
    /// assert_eq!(x, (Some(2), None));
    ///
    /// let x: (Option<_>, Option<_>) = zot::Zot::Two(2, 3).into();
    /// assert_eq!(x, (Some(2), Some(3)));
    ///
    /// let x: (Option<i32>, Option<_>) = zot::Zot::Zero.into();
    /// assert_eq!(x, (None, None));
    /// ```
    fn from(zot: Zot<T>) -> Self {
        match zot {
            Zot::Zero => (None, None),
            Zot::One(v0) => (Some(v0), None),
            Zot::Two(v0, v1) => (Some(v0), Some(v1)),
        }
    }
}

impl<T> From<Option<(T, Option<T>)>> for Zot<T> {
    fn from(ts: Option<(T, Option<T>)>) -> Self {
        if let Some((t0, t1)) = ts {
            if let Some(t1) = t1 {
                Zot::Two(t0, t1)
            } else {
                Zot::One(t0)
            }
        } else {
            Zot::Zero
        }
    }
}

impl<T> From<Zot<T>> for Option<(T, Option<T>)> {
    fn from(zot: Zot<T>) -> Self {
        match zot {
            Zot::Zero => None,
            Zot::One(v0) => Some((v0, None)),
            Zot::Two(v0, v1) => Some((v0, Some(v1))),
        }
    }
}

impl<T> From<crate::ot::Ot<T>> for Zot<T> {
    fn from(ot: crate::ot::Ot<T>) -> Self {
        match ot {
            crate::Ot::One(v0) => Zot::One(v0),
            crate::Ot::Two(v0, v1) => Zot::Two(v0, v1),
        }
    }
}

impl<'a, T> From<&'a Zot<T>> for Zot<&'a T> {
    /// Converts from `&Zot<T>` to `Zot<&T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// let s: zot::Zot<String> = zot::Zot::One(String::from("Hello, Rustaceans!"));
    /// let o: zot::Zot<usize> = zot::Zot::from(&s).map(|ss: &String| ss.len());
    ///
    /// println!("Can still print s: {:?}", s);
    ///
    /// assert_eq!(o, zot::Zot::One(18));
    /// ```
    fn from(o: &'a Zot<T>) -> Zot<&'a T> {
        o.as_ref()
    }
}

impl<'a, T> From<&'a mut Zot<T>> for Zot<&'a mut T> {
    /// Converts from `&mut Zot<T>` to `Zot<&mut T>`
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = zot::Zot::One(String::from("Hello"));
    /// let o: zot::Zot<&mut String> = zot::Zot::from(&mut s);
    ///
    /// match o {
    ///     zot::Zot::One(t) => *t = String::from("Hello, Rustaceans!"),
    ///     _ => (),
    /// }
    ///
    /// assert_eq!(s, zot::Zot::One(String::from("Hello, Rustaceans!")));
    /// ```
    fn from(o: &'a mut Zot<T>) -> Zot<&'a mut T> {
        o.as_mut()
    }
}

impl<T> Default for Zot<T> {
    /// Returns [`Zero`][zot::Zot::Zero].
    ///
    /// # Examples
    ///
    /// ```
    /// let z: zot::Zot<u32> = zot::Zot::default();
    /// assert!(z.is_zero());
    /// ```
    #[inline]
    fn default() -> Self {
        Zot::Zero
    }
}

/////////////////////////////////////////////////////////////////////////////
// The Zot Iterators
/////////////////////////////////////////////////////////////////////////////

impl<T> IntoIterator for Zot<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    /// Returns a consuming iterator any contained values.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Zot::Two("string", "text");
    /// let v: Vec<&str> = x.into_iter().collect();
    /// assert_eq!(v, ["string", "text"]);
    ///
    /// let x = zot::Zot::Zero;
    /// let v: Vec<&str> = x.into_iter().collect();
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(crate::iter_item::Item(self))
    }
}

impl<'a, T> IntoIterator for &'a Zot<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Zot<T> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[derive(Debug)]
pub struct Iter<'a, T>(crate::iter_item::Item<&'a T>);

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, T> std::iter::DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<'a, T> std::iter::ExactSizeIterator for Iter<'a, T> {}
impl<'a, T> std::iter::FusedIterator for Iter<'a, T> {}

#[derive(Debug)]
pub struct IterMut<'a, T>(crate::iter_item::Item<&'a mut T>);

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, T> std::iter::DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<'a, T> std::iter::ExactSizeIterator for IterMut<'a, T> {}
impl<'a, T> std::iter::FusedIterator for IterMut<'a, T> {}

#[derive(Debug)]
pub struct IntoIter<T>(crate::iter_item::Item<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T> std::iter::DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<T> std::iter::ExactSizeIterator for IntoIter<T> {}
impl<T> std::iter::FusedIterator for IntoIter<T> {}

// This is a separate function to reduce the code size of .expect_*() itself.
#[inline(never)]
#[cold]
#[track_caller]
fn expect_failed(msg: &str) -> ! {
    panic!("{}", msg)
}
