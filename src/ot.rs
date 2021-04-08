#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Ot<T> {
    One(T),
    Two(T, T),
}

/////////////////////////////////////////////////////////////////////////////
// Type implementation
/////////////////////////////////////////////////////////////////////////////

impl<T> Ot<T> {
    /////////////////////////////////////////////////////////////////////////
    // Querying the contained values
    /////////////////////////////////////////////////////////////////////////

    /// Returns `true` if the option is a [`One`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Ot<u32> = zot::Ot::One(2);
    /// assert_eq!(x.is_one(), true);
    ///
    /// let x: zot::Ot<u32> = zot::Ot::Two(2, 3);
    /// assert_eq!(x.is_one(), false);
    /// ```
    #[must_use = "if you intended to assert that this has two values, consider `.unwrap_one()` instead"]
    #[inline]
    pub const fn is_one(&self) -> bool {
        match self {
            Ot::One(_) => true,
            Ot::Two(_, _) => false,
        }
    }

    /// Returns `true` if the option is a [`Two`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Ot<u32> = zot::Ot::One(2);
    /// assert_eq!(x.is_two(), false);
    ///
    /// let x: zot::Ot<u32> = zot::Ot::Two(2, 3);
    /// assert_eq!(x.is_two(), true);
    /// ```
    #[must_use = "if you intended to assert that this has two values, consider `.unwrap_two()` instead"]
    #[inline]
    pub const fn is_two(&self) -> bool {
        match self {
            Ot::One(_) => false,
            Ot::Two(_, _) => true,
        }
    }

    /// Returns `true` if at least one contained value equals the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Ot<u32> = zot::Ot::One(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: zot::Ot<u32> = zot::Ot::One(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: zot::Ot<u32> = zot::Ot::Two(3, 2);
    /// assert_eq!(x.contains(&2), true);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains<U>(&self, v: &U) -> bool
    where U: PartialEq<T> {
        match self {
            Ot::One(v0) => v == v0,
            Ot::Two(v0, v1) => v == v0 || v == v1,
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Adapter for working with references
    /////////////////////////////////////////////////////////////////////////

    /// Converts from `&Ot<T>` to `Ot<&T>`.
    #[inline]
    pub const fn as_ref(&self) -> Ot<&T> {
        match *self {
            Ot::One(ref v0) => Ot::One(v0),
            Ot::Two(ref v0, ref v1) => Ot::Two(v0, v1),
        }
    }

    /// Converts from `&mut Option<T>` to `Option<&mut T>`.
    #[inline]
    pub fn as_mut(&mut self) -> Ot<&mut T> {
        match *self {
            Ot::One(ref mut v0) => Ot::One(v0),
            Ot::Two(ref mut v0, ref mut v1) => Ot::Two(v0, v1),
        }
    }

    /// Converts from [`Pin`]`<&Ot<T>>` to `Ot<`[`Pin`]`<&T>>`.
    #[inline]
    pub fn as_pin_ref(self: std::pin::Pin<&Self>) -> Ot<std::pin::Pin<&T>> {
        // SAFETY: `x` is guaranteed to be pinned because it comes from `self`
        // which is pinned.
        unsafe { std::pin::Pin::get_ref(self).as_ref().map(|x| std::pin::Pin::new_unchecked(x)) }
    }

    /// Converts from [`Pin`]`<&mut Ot<T>>` to `Ot<`[`Pin`]`<&mut T>>`.
    #[inline]
    pub fn as_pin_mut(self: std::pin::Pin<&mut Self>) -> Ot<std::pin::Pin<&mut T>> {
        // SAFETY: `get_unchecked_mut` is never used to move the `Ot` inside `self`.
        // `x` is guaranteed to be pinned because it comes from `self` which is pinned.
        unsafe { std::pin::Pin::get_unchecked_mut(self).as_mut().map(|x| std::pin::Pin::new_unchecked(x)) }
    }

    /////////////////////////////////////////////////////////////////////////
    // Getting to contained values
    /////////////////////////////////////////////////////////////////////////

    /// Returns the contained [`One`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a [`Two`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::One("value");
    /// assert_eq!(x.expect_one("fruits are healthy"), "value");
    /// ```
    ///
    /// ```{.should_panic}
    /// let x: zot::Ot<&str> = zot::Ot::Two("value", "value");
    /// x.expect_one("fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect_one(self, msg: &str) -> T {
        match self {
            Ot::One(value) => value,
            _ => expect_failed(msg),
        }
    }

    /// Returns the contained [`Two`] value as a `(T, T)`, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a [`One`] with a custom panic message provided by
    /// `msg`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::Two("value", "value");
    /// assert_eq!(x.expect_two("fruits are healthy"), ("value", "value"));
    /// ```
    ///
    /// ```{.should_panic}
    /// let x: zot::Ot<&str> = zot::Ot::One("value");
    /// x.expect_two("fruits are healthy"); // panics with `fruits are healthy`
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect_two(self, msg: &str) -> (T, T) {
        match self {
            Ot::Two(value0, value1) => (value0, value1),
            _ => expect_failed(msg),
        }
    }

    /// Returns the contained [`One`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals [`Two`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::One("air");
    /// assert_eq!(x.unwrap_one(), "air");
    /// ```
    ///
    /// ```{.should_panic}
    /// let x: zot::Ot<&str> = zot::Ot::Two("air", "air");
    /// assert_eq!(x.unwrap_one(), "air"); // fails
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_one(self) -> T {
        match self {
            Ot::One(v0) => v0,
            Ot::Two(_, _) => panic!("called `Ot::unwrap_one()` on a `Two` value"),
        }
    }

    /// Returns the contained [`Two`] value as a `(T, T)`, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the self value equals [`One`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::Two("air", "air");
    /// assert_eq!(x.unwrap_two(), ("air", "air"));
    /// ```
    ///
    /// ```{.should_panic}
    /// let x: zot::Ot<&str> = zot::Ot::One("air");
    /// assert_eq!(x.unwrap_two(), ("air", "air")); // fails
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_two(self) -> (T, T) {
        match self {
            Ot::One(_) => panic!("called `Ot::unwrap_two()` on a `One` value"),
            Ot::Two(v0, v1) => (v0, v1),
        }
    }

    /// Returns the contained [`One`] value or a provided default.
    ///
    /// Arguments passed to `unwrap_one_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`unwrap_one_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`unwrap_one_or_else`]: zot::Ot::unwrap_one_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(zot::Ot::One("car").unwrap_one_or("bike"), "car");
    /// assert_eq!(zot::Ot::Two("car", "train").unwrap_one_or("bike"), "bike");
    /// ```
    #[inline]
    pub fn unwrap_one_or(self, default: T) -> T {
        match self {
            Ot::One(v0) => v0,
            Ot::Two(_, _) => default,
        }
    }

    /// Returns the contained [`Two`] value as a `(T, T)` or a provided default.
    ///
    /// Arguments passed to `unwrap_two_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`unwrap_two_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`unwrap_two_or_else`]: zot::Ot::unwrap_two_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(zot::Ot::Two("car", "train").unwrap_two_or(("bike", "pogo")), ("car", "train"));
    /// assert_eq!(zot::Ot::One("car").unwrap_two_or(("bike", "pogo")), ("bike", "pogo"));
    /// ```
    #[inline]
    pub fn unwrap_two_or(self, default: (T, T)) -> (T, T) {
        match self {
            Ot::One(_) => default,
            Ot::Two(v0, v1) => (v0, v1),
        }
    }

    /// Returns the contained [`One`] value or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```
    /// let k = 10;
    /// assert_eq!(zot::Ot::One(4).unwrap_one_or_else(|| 2 * k), 4);
    /// assert_eq!(zot::Ot::Two(4, 5).unwrap_one_or_else(|| 2 * k), 20);
    /// ```
    #[inline]
    pub fn unwrap_one_or_else<F: FnOnce() -> T>(self, f: F) -> T {
        match self {
            Ot::One(v0) => v0,
            Ot::Two(_, _) => f(),
        }
    }

    /// Returns the contained [`Two`] value as a `(T, T)` or computes it from a closure.
    ///
    /// # Examples
    ///
    /// ```
    /// let k = 10;
    /// assert_eq!(zot::Ot::Two(4, 5).unwrap_two_or_else(|| (2 * k, 3 * k)), (4, 5));
    /// assert_eq!(zot::Ot::One(4).unwrap_two_or_else(|| (2 * k, 3 * k)), (20, 30));
    /// ```
    #[inline]
    pub fn unwrap_two_or_else<F: FnOnce() -> (T, T)>(self, f: F) -> (T, T) {
        match self {
            Ot::One(_) => f(),
            Ot::Two(v0, v1) => (v0, v1),
        }
    }

    /// Returns a `Result` with the contained [`One`] value or computes an Err from a closure.
    #[inline]
    pub fn ok_one_or_else<E, F: FnOnce(T, T) -> E>(self, f: F) -> Result<T, E> {
        match self {
            Ot::One(v0) => Ok(v0),
            Ot::Two(v0, v1) => Err(f(v0, v1)),
        }
    }

    /// Returns a `Result` with the contained [`Two`] value as a `(T, T)` or computes an Err from a closure.
    #[inline]
    pub fn ok_two_or_else<E, F: FnOnce(T) -> E>(self, f: F) -> Result<(T, T), E> {
        match self {
            Ot::One(v0) => Err(f(v0)),
            Ot::Two(v0, v1) => Ok((v0, v1)),
        }
    }

    pub fn first(&self) -> &T {
        match self {
            Ot::One(t0) |
            Ot::Two(t0, _) => t0,
        }
    }

    pub fn first_mut(&mut self) -> &mut T {
        match self {
            Ot::One(t0) |
            Ot::Two(t0, _) => t0,
        }
    }

    pub fn second(&self) -> Option<&T> {
        match self {
            Ot::One(_) => None,
            Ot::Two(_, t1) => Some(t1),
        }
    }

    pub fn second_mut(&mut self) -> Option<&mut T> {
        match self {
            Ot::One(_) => None,
            Ot::Two(_, t1) => Some(t1),
        }
    }

    pub fn last(&self) -> &T {
        self.second().unwrap_or(self.first())
    }

    pub fn last_mut(&mut self) -> &mut T {
        match self {
            Ot::One(t0) => t0,
            Ot::Two(_, t1) => t1,
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Transforming contained values
    /////////////////////////////////////////////////////////////////////////

    /// Maps an `Ot<T>` to `Ot<U>` by applying a function to a contained value.
    ///
    /// # Examples
    ///
    /// Converts an `Ot<`[`String`]`>` into an `Ot<`[`usize`]`>`, consuming the original:
    ///
    /// ```
    /// let ot_string = zot::Ot::Two(String::from("Hello, World!"), String::from("Goodbye, World!"));
    /// // `Ot::map` takes self *by value*, consuming `ot_string`
    /// let ot_len = ot_string.map(|s| s.len());
    ///
    /// assert_eq!(ot_len, zot::Ot::Two(13, 15));
    /// ```
    #[inline]
    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> Ot<U> {
        match self {
            Ot::One(v0) => Ot::One(f(v0)),
            Ot::Two(v0, v1) => Ot::Two(f(v0), f(v1)),
        }
    }

    /// Returns an iterator over the contained values.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::Two(4, 5);
    /// let mut iter = x.iter();
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&5));
    ///
    /// let x = zot::Ot::One(4);
    /// let mut iter = x.iter();
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub const fn iter(&self) -> Iter<'_, T> {
        let zot = match self {
            Ot::One(v0) => crate::zot::Zot::One(v0),
            Ot::Two(v0, v1) => crate::Zot::Two(v0, v1),
        };
        Iter(crate::iter_item::Item(zot))
    }

    /// Returns a mutable iterator over the contained values.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Ot::One(4);
    /// match x.iter_mut().next() {
    ///     Some(v) => *v = 42,
    ///     None => {},
    /// }
    /// assert_eq!(x, zot::Ot::One(42));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut(crate::iter_item::Item(self.as_mut().into()))
    }

    /////////////////////////////////////////////////////////////////////////
    // Misc
    /////////////////////////////////////////////////////////////////////////

    /// Replaces the actual value in the `Ot` by the value given in parameter,
    /// returning the old value,
    /// leaving a [`One`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Ot::One(2);
    /// let old = x.replace_one(5);
    /// assert_eq!(x, zot::Ot::One(5));
    /// assert_eq!(old, zot::Ot::One(2));
    ///
    /// let mut x = zot::Ot::Two(5, 6);
    /// let old = x.replace_one(3);
    /// assert_eq!(x, zot::Ot::One(3));
    /// assert_eq!(old, zot::Ot::Two(5, 6));
    /// ```
    #[inline]
    pub fn replace_one(&mut self, value: T) -> Ot<T> {
        std::mem::replace(self, Ot::One(value))
    }

    /// Replaces the actual value in the `Ot` by the values given in parameter,
    /// returning the old value,
    /// leaving a [`Two`] in its place without deinitializing either one.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Ot::One(2);
    /// let old = x.replace_two(5, 6);
    /// assert_eq!(x, zot::Ot::Two(5, 6));
    /// assert_eq!(old, zot::Ot::One(2));
    ///
    /// let mut x = zot::Ot::Two(5, 6);
    /// let old = x.replace_two(3, 4);
    /// assert_eq!(x, zot::Ot::Two(3, 4));
    /// assert_eq!(old, zot::Ot::Two(5, 6));
    /// ```
    #[inline]
    pub fn replace_two(&mut self, first: T, second: T) -> Ot<T> {
        std::mem::replace(self, Ot::Two(first, second))
    }

    /// Replaces the first value in the `Ot` by the value given in parameter,
    /// returning the old value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Ot::Two(2, 3);
    /// let old = x.replace_first(5);
    /// assert_eq!(x, zot::Ot::Two(5, 3));
    /// assert_eq!(old, 2);
    ///
    /// let mut x = zot::Ot::One(2);
    /// let old = x.replace_first(3);
    /// assert_eq!(x, zot::Ot::One(3));
    /// assert_eq!(old, 2);
    /// ```
    #[inline]
    pub fn replace_first(&mut self, value: T) -> T {
        match self {
            Ot::One(vfirst) |
            Ot::Two(vfirst, _) => {
                std::mem::replace(vfirst, value)
            }
        }
    }

    /// Replaces the last value in the `Ot` by the value given in parameter,
    /// returning the old value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = zot::Ot::Two(2, 3);
    /// let old = x.replace_last(5);
    /// assert_eq!(x, zot::Ot::Two(2, 5));
    /// assert_eq!(old, 3);
    ///
    /// let mut x = zot::Ot::One(2);
    /// let old = x.replace_last(3);
    /// assert_eq!(x, zot::Ot::One(3));
    /// assert_eq!(old, 2);
    /// ```
    #[inline]
    pub fn replace_last(&mut self, value: T) -> T {
        match self {
            Ot::One(vlast) |
            Ot::Two(_, vlast) => std::mem::replace(vlast, value),
        }
    }

    /// Returns the number of contained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Ot<u32> = zot::Ot::Two(7, 20);
    /// assert_eq!(x.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        match self {
            Ot::One(_) => 1,
            Ot::Two(_, _) => 2,
        }
    }

}

impl<T: Copy> Ot<&T> {
    /// Maps an `Ot<&T>` to an `Ot<T>` by copying the contents of the
    /// ot.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = 12;
    /// let ot_x = zot::Ot::One(&x);
    /// assert_eq!(ot_x, zot::Ot::One(&12));
    /// let copied = ot_x.copied();
    /// assert_eq!(copied, zot::Ot::One(12));
    /// ```
    pub fn copied(self) -> Ot<T> {
        self.map(|&t| t)
    }
}

impl<T: Copy> Ot<&mut T> {
    /// Maps an `Ot<&mut T>` to an `Ot<T>` by copying the contents of the
    /// ot.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = 12;
    /// let ot_x = zot::Ot::One(&mut x);
    /// assert_eq!(ot_x, zot::Ot::One(&mut 12));
    /// let copied = ot_x.copied();
    /// assert_eq!(copied, zot::Ot::One(12));
    /// ```
    pub fn copied(self) -> Ot<T> {
        self.map(|&mut t| t)
    }
}

impl<T: Clone> Ot<&T> {
    /// Maps an `Ot<&T>` to an `Ot<T>` by cloning the contents of the
    /// ot.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = 12;
    /// let ot_x = zot::Ot::One(&x);
    /// assert_eq!(ot_x, zot::Ot::One(&12));
    /// let cloned = ot_x.cloned();
    /// assert_eq!(cloned, zot::Ot::One(12));
    /// ```
    pub fn cloned(self) -> Ot<T> {
        self.map(|t| t.clone())
    }
}

impl<T: Clone> Ot<&mut T> {
    /// Maps an `Ot<&mut T>` to an `Ot<T>` by cloning the contents of the
    /// ot.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut x = 12;
    /// let ot_x = zot::Ot::One(&mut x);
    /// assert_eq!(ot_x, zot::Ot::One(&mut 12));
    /// let cloned = ot_x.cloned();
    /// assert_eq!(cloned, zot::Ot::One(12));
    /// ```
    pub fn cloned(self) -> Ot<T> {
        self.map(|t| t.clone())
    }
}

impl<T: std::ops::Deref> Ot<T> {
    /// Converts from `Ot<T>` (or `&Ot<T>`) to `Ot<&T::Target>`.
    ///
    /// Leaves the original Ot in-place, creating a new one with a reference
    /// to the original one, additionally coercing the contents via [`Deref`].
    ///
    /// # Examples
    ///
    /// ```
    /// let x: zot::Ot<String> = zot::Ot::One("hey".to_owned());
    /// assert_eq!(x.as_deref(), zot::Ot::One("hey"));
    /// ```
    pub fn as_deref(&self) -> Ot<&T::Target> {
        self.as_ref().map(|t| t.deref())
    }
}

/////////////////////////////////////////////////////////////////////////////
// Trait implementations
/////////////////////////////////////////////////////////////////////////////

impl<T> From<T> for Ot<T> {
    fn from(t: T) -> Self {
        Self::One(t)
    }
}

impl<T> From<(T, T)> for Ot<T> {
    fn from(ts: (T, T)) -> Self {
        Self::Two(ts.0, ts.1)
    }
}

impl<T> std::convert::TryFrom<Ot<T>> for (T, T) {
    type Error = crate::TryFromOtError;

    fn try_from(value: Ot<T>) -> Result<Self, Self::Error> {
        match value {
            Ot::One(_) => Err(Self::Error::InvalidElementCount),
            Ot::Two(v0, v1) => Ok((v0, v1)),
        }
    }
}

impl<T> From<(T, Option<T>)> for Ot<T> {
    /// Create an `Ot` from an element and an `Option`. Returns an `Ot::One`
    /// if the `Option` was `None`, otherwise `Ot::Two`.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::from((5, Some(2)));
    /// assert_eq!(x, zot::Ot::Two(5, 2));
    ///
    /// let x = zot::Ot::from((5, None));
    /// assert_eq!(x, zot::Ot::One(5));
    /// ```
    fn from(ts: (T, Option<T>)) -> Self {
        let (t0, t1) = ts;
        match t1 {
            Some(t1) => Ot::Two(t0, t1),
            None => Ot::One(t0),
        }
    }
}

impl<T> From<Ot<T>> for (T, Option<T>) {
    /// Convert the `Ot` into a tuple containing the first element and an `Option` 
    /// which contains the second value if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::from((5, Some(2)));
    /// assert_eq!(x, zot::Ot::Two(5, 2));
    /// 
    /// let x: zot::Ot<i32> = zot::Ot::from((5, None));
    /// assert_eq!(x, zot::Ot::One(5));
    /// ```
    fn from(ot: Ot<T>) -> Self {
        match ot {
            Ot::One(t0) => (t0, None),
            Ot::Two(t0, t1) => (t0, Some(t1)),
        }
    }
}

impl<'a, T> From<&'a Ot<T>> for Ot<&'a T> {
    /// Converts from `&Ot<T>` to `Ot<&T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// let s: zot::Ot<String> = zot::Ot::One(String::from("Hello, Rustaceans!"));
    /// let o: zot::Ot<usize> = zot::Ot::from(&s).map(|ss: &String| ss.len());
    ///
    /// println!("Can still print s: {:?}", s);
    ///
    /// assert_eq!(o, zot::Ot::One(18));
    /// ```
    fn from(o: &'a Ot<T>) -> Ot<&'a T> {
        o.as_ref()
    }
}

impl<'a, T> From<&'a mut Ot<T>> for Ot<&'a mut T> {
    /// Converts from `&mut Ot<T>` to `Ot<&mut T>`
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = zot::Ot::One(String::from("Hello"));
    /// let o: zot::Ot<&mut String> = zot::Ot::from(&mut s);
    ///
    /// match o {
    ///     zot::Ot::One(t) => *t = String::from("Hello, Rustaceans!"),
    ///     _ => (),
    /// }
    ///
    /// assert_eq!(s, zot::Ot::One(String::from("Hello, Rustaceans!")));
    /// ```
    fn from(o: &'a mut Ot<T>) -> Ot<&'a mut T> {
        o.as_mut()
    }
}

/////////////////////////////////////////////////////////////////////////////
// The Ot Iterators
/////////////////////////////////////////////////////////////////////////////

impl<T> IntoIterator for Ot<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    /// Returns a consuming iterator any contained values.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = zot::Ot::Two("string", "text");
    /// let v: Vec<&str> = x.into_iter().collect();
    /// assert_eq!(v, ["string", "text"]);
    ///
    /// let x = zot::Ot::One("string");
    /// let v: Vec<&str> = x.into_iter().collect();
    /// assert_eq!(v, ["string"]);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(crate::iter_item::Item(self.into()))
    }
}

impl<'a, T> IntoIterator for &'a Ot<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Ot<T> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

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

impl<'a, A> std::iter::ExactSizeIterator for Iter<'a, A> {}
impl<'a, A> std::iter::FusedIterator for Iter<'a, A> {}

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

impl<'a, A> std::iter::ExactSizeIterator for IterMut<'a, A> {}
impl<'a, A> std::iter::FusedIterator for IterMut<'a, A> {}

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

impl<A> std::iter::ExactSizeIterator for IntoIter<A> {}
impl<A> std::iter::FusedIterator for IntoIter<A> {}

// This is a separate function to reduce the code size of .expect_*() itself.
#[inline(never)]
#[cold]
#[track_caller]
fn expect_failed(msg: &str) -> ! {
    panic!("{}", msg)
}