//! A hash set implemented as a `HashMap` where the value is `()`.
//!
//! Check the module documentation for details on
//!
//! * the concept of `Value` ([Serialization and
//!   Deserialization](crate#serialization-and-deserialization), [Sized vs
//!   Unsized](crate#sized-vs-unsized)), and
//! * differences from the `std::collections::HashSet` API ([Ref and
//!   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
//!
//! # Examples
//!
//! See [`HashSet`](self::HashSet) for examples.
use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::io;

use crate::hash_map::HashMap;
use crate::storage::{BorrowStorage, Ref, SizedStorage, Storage, UnsizedStorage};
use crate::value::{Borrowed, SizedValue, Value, ValueBorrow};

/// A hash set implemented as a `HashMap` where the value is `()`.
///
/// The generic parameter `S` refers to an underlying storage, either
/// [`SizedStorage`](crate::storage::SizedStorage) or
/// [`UnsizedStorage`](crate::storage::UnsizedStorage), depending on the element
/// type.
///
/// Check the module documentation for details on
///
/// * the concept of `Value` ([Serialization and
///   Deserialization](crate#serialization-and-deserialization), [Sized vs
///   Unsized](crate#sized-vs-unsized)), and
/// * differences from the `std::collections::HashSet` API ([Ref and
///   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
///
/// # Examples
///
/// ```
/// use bonifacio::HashSet;
///
/// let mut books = HashSet::new_unsized();
///
/// books.insert("1984".to_string());
/// books.insert("The Lord of the Rings".to_string());
/// books.insert("On the Road".to_string());
///
/// if !books.contains("The Witcher") {
///     println!("There are {} books, but this one is not available", books.len());
/// }
///
/// assert!(books.remove("1984"));
///
/// for book in books.iter() {
///     println!("{}", book);
/// }
/// ```
pub struct HashSet<T, S, R = RandomState> {
    inner: HashMap<T, (), S, SizedStorage<()>, R>,
}

impl<T, S> HashSet<T, S>
where
    T: Hash + Eq,
    S: Storage<T>,
{
    /// Constructs a new, empty `HashSet<T, S>`, where `S` is type of the
    /// underlying storage.
    ///
    /// The type of the underlying storage must be specified explicitly since it
    /// can't be inferred automatically.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_new`](self::HashSet::try_new)
    /// if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// use bonifacio::{SizedStorage, UnsizedStorage};
    /// let set: HashSet<String, UnsizedStorage<_>> = HashSet::new();
    /// ```
    pub fn new() -> Self {
        Self::try_new().unwrap()
    }

    /// Constructs a new, empty `HashSet<T, S>`, where `S` is type of the
    /// underlying storage.
    ///
    /// The type of the underlying storage must be specified explicitly since it
    /// can't be inferred automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// use bonifacio::{SizedStorage, UnsizedStorage};
    /// let set: HashSet<String, UnsizedStorage<_>> = HashSet::try_new().expect("I/O error");
    /// ```
    pub fn try_new() -> io::Result<Self> {
        Ok(Self {
            inner: HashMap::try_new()?,
        })
    }
}

impl<T, S, R> HashSet<T, S, R>
where
    T: Hash + Eq,
    S: Storage<T>,
    R: BuildHasher,
{
    /// Constructs a new, empty `HashSet` with given hash builder to hash keys.
    ///
    /// The passed `hash_builder` must implement the
    /// [`BuildHasher`](std::hash::BuildHasher) trait for the hash map to be
    /// useful, see its documentation for details.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_with_hasher`](self::HashSet::try_with_hasher) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// use bonifacio::SizedStorage;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let state = RandomState::new();
    /// let mut set: HashSet<u32, SizedStorage<_>> = HashSet::with_hasher(state);
    /// ```
    pub fn with_hasher(hash_builder: R) -> Self {
        Self::try_with_hasher(hash_builder).unwrap()
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// set.insert("hello world".to_string());
    /// set.insert("bonifacio".to_string());
    /// assert_eq!(set.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Inserts a value into the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this key present, `false` is returned.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_insert`](self::HashSet::try_insert) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_sized();
    /// assert_eq!(set.insert(3), true);
    /// assert_eq!(set.insert(3), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.try_insert(value).unwrap()
    }

    /// Returns a [`Ref`](crate::storage::Ref) to a value equal to the given
    /// value, or `None` if the value is not present.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the set's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_get`](self::HashSet::try_get)
    /// if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.get("foo").as_deref(), Some(&"foo".to_string()));
    /// assert_eq!(set.get("bar"), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, value: &Q) -> Option<Ref<'_, T>>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_get(value).unwrap()
    }

    /// Removes a value from the set. Returns whether the value was present in
    /// the set.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the map's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_remove`](self::HashSet::try_remove) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.remove("foo"), true);
    /// assert_eq!(set.remove("foo"), false);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_remove(value).unwrap()
    }

    /// Returns `true` if the set contains given value.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the map's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_contains`](self::HashSet::try_contains) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.contains("foo"), true);
    /// assert_eq!(set.contains("bar"), false);
    /// ```
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_contains(value).unwrap()
    }

    /// Returns an iterator over values of the set in arbitrary order.
    ///
    /// # Panics
    ///
    /// `Iter::next` panics when an I/O error occurs. Use
    /// [`try_iter`](self::HashSet::try_iter) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// set.insert("hello world".to_string());
    /// set.insert("bonifacio".to_string());
    ///
    /// for value in set.iter() {
    ///     println!("{}", value);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T, S> {
        Iter {
            inner: self.try_iter(),
        }
    }

    /// Constructs a new, empty `HashSet` with given hash builder to hash keys.
    ///
    /// The passed `hash_builder` must implement the
    /// [`BuildHasher`](std::hash::BuildHasher) trait for the hash map to be
    /// useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// use bonifacio::SizedStorage;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let state = RandomState::new();
    /// let mut set: HashSet<u32, SizedStorage<_>> =
    ///     HashSet::try_with_hasher(state).expect("I/O error");
    /// ```
    pub fn try_with_hasher(hash_builder: R) -> io::Result<Self> {
        Ok(Self {
            inner: HashMap::try_with_hasher(hash_builder)?,
        })
    }

    /// Inserts a value into the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present,false`e` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_sized();
    /// assert_eq!(set.try_insert(3).expect("I/O error"), true);
    /// assert_eq!(set.try_insert(3).expect("I/O error"), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn try_insert(&mut self, value: T) -> io::Result<bool> {
        self.inner
            .try_insert(value, ())
            .map(|option| option.is_none())
    }

    /// Returns a [`Ref`](crate::storage::Ref) to a value equal to the given
    /// value, or `None` if the value is not present.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the set's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.try_get("foo").expect("I/O error").as_deref(), Some(&"foo".to_string()));
    /// assert_eq!(set.try_get("bar").expect("I/O error"), None);
    /// ```
    pub fn try_get<Q: ?Sized>(&self, value: &Q) -> io::Result<Option<Ref<'_, T>>>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.inner.try_get_key_value(value) {
            Ok(Some((value, _))) => Ok(Some(value)),
            Ok(None) => Ok(None),
            Err(err) => Err(err),
        }
    }

    /// Removes a value from the set. Returns whether the value was present in
    /// the set.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the map's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.try_remove("foo").expect("I/O error"), true);
    /// assert_eq!(set.try_remove("foo").expect("I/O error"), false);
    /// ```
    pub fn try_remove<Q: ?Sized>(&mut self, value: &Q) -> io::Result<bool>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.inner
            .try_remove(value)
            .map(|option| option.is_some())
    }

    /// Returns `true` if the set contains given value.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the map's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.try_contains("foo").expect("I/O error"), true);
    /// assert_eq!(set.try_contains("bar").expect("I/O error"), false);
    /// ```
    pub fn try_contains<Q: ?Sized>(&self, value: &Q) -> io::Result<bool>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.inner.try_contains_key(value)
    }

    /// Returns a checked variant of iterator over values of set map in
    /// arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// set.insert("hello world".to_string());
    /// set.insert("bonifacio".to_string());
    ///
    /// for value in set.try_iter().map(|r| r.expect("I/O error")) {
    ///     println!("{}", value);
    /// }
    /// ```
    pub fn try_iter(&self) -> TryIter<'_, T, S> {
        TryIter {
            inner: self.inner.try_keys(),
        }
    }
}

impl<T, S> HashSet<T, S>
where
    T: ValueBorrow + Hash + Eq,
    S: BorrowStorage<T>,
{
    /// Returns a [borrowed](crate::value::Borrowed) value corresponding to the
    /// given value, or `None` if the value is not present.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the map's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_borrow`](self::HashSet::try_borrow) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.borrow("foo").as_deref(), Some("foo"));
    /// ```
    pub fn borrow<Q: ?Sized>(&self, value: &Q) -> Option<Borrowed<'_, T>>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + PartialEq<T::Borrowed>,
    {
        self.try_borrow(value).unwrap()
    }

    /// Returns a [borrowed](crate::value::Borrowed) value corresponding to the
    /// given value, or `None` if the value is not present.
    ///
    /// The supplied value may be any [`Borrow`](std::borrow::Borrow) form of
    /// the map's value type, but [`Hash`](std::hash::Hash) and
    /// [`Eq`](std::cmp::Eq) on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// assert_eq!(set.try_borrow("foo").expect("I/O error").as_deref(), Some("foo"));
    /// ```
    pub fn try_borrow<Q: ?Sized>(&self, value: &Q) -> io::Result<Option<Borrowed<'_, T>>>
    where
        T: Borrow<Q>,
        Q: Hash + Eq + PartialEq<T::Borrowed>,
    {
        self.inner.try_borrow_key(value)
    }
}

impl<T> HashSet<T, UnsizedStorage<T>>
where
    T: Value + Hash + Eq,
{
    /// Constructs a new, empty `HashSet<T, UnsizedStorage<T>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_unsized`](self::HashSet::try_new_unsized) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_unsized();
    /// set.insert("foo".to_string());
    /// ```
    pub fn new_unsized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `HashSet<T, UnsizedStorage<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::try_new_unsized().expect("I/O error");
    /// set.insert("foo".to_string());
    /// ```
    pub fn try_new_unsized() -> io::Result<Self> {
        Self::try_new()
    }
}

impl<T> HashSet<T, SizedStorage<T>>
where
    T: SizedValue + Hash + Eq,
{
    /// Constructs a new, empty `HashSet<T, SizedStorage<T>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_sized`](self::HashSet::try_new_sized) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::new_sized();
    /// set.insert(3);
    /// ```
    pub fn new_sized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `HashSet<T, SizedStorage<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashSet;
    /// let mut set = HashSet::try_new_sized().expect("I/O error");
    /// set.insert(3);
    /// ```
    pub fn try_new_sized() -> io::Result<Self> {
        Self::try_new()
    }
}

/// An immutable iterator over the values of the set in arbitrary order,
/// propagating I/O errors.
///
/// This struct is created by the [`try_iter`](self::HashSet::try_iter) method
/// on [`HashSet`](self::HashSet).
///
/// # Examples
///
/// ```
/// # use bonifacio::HashSet;
/// let mut set = HashSet::new_unsized();
/// set.insert("foo".to_string());
/// set.insert("hello world".to_string());
/// set.insert("bonifacio".to_string());
///
/// for value in set.try_iter().map(|r| r.expect("I/O error")) {
///     println!("{}", value);
/// }
/// ```
pub struct TryIter<'a, T, S> {
    inner: crate::hash_map::TryKeys<'a, T, (), S, SizedStorage<()>>,
}

impl<'a, T, S> Iterator for TryIter<'a, T, S>
where
    T: Hash + Eq,
    S: Storage<T>,
{
    type Item = io::Result<Ref<'a, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// An immutable iterator over the values of the set in arbitrary order,
/// panicking on I/O errors.
///
/// This struct is created by the [`iter`](self::HashSet::iter) method on
/// [`HashSet`](self::HashSet).
///
/// # Panics
///
/// `Iter::next` panics when an I/O error occurs. Use
/// [`try_iter`](self::HashSet::try_iter) if this is unacceptable.
///
/// # Examples
///
/// ```
/// # use bonifacio::HashSet;
/// let mut set = HashSet::new_unsized();
/// set.insert("foo".to_string());
/// set.insert("hello world".to_string());
/// set.insert("bonifacio".to_string());
///
/// for value in set.iter() {
///     println!("{}", value);
/// }
/// ```
pub struct Iter<'a, T, S> {
    inner: TryIter<'a, T, S>,
}

impl<'a, T, S> Iterator for Iter<'a, T, S>
where
    T: Hash + Eq,
    S: Storage<T>,
{
    type Item = Ref<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Result::unwrap)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::BuildHasherDefault;

    use proptest::prelude::*;

    use crate::storage::UnsizedStorage;

    type TestHasher = BuildHasherDefault<DefaultHasher>;

    fn new_string_set() -> super::HashSet<String, UnsizedStorage<String>, TestHasher> {
        super::HashSet::with_hasher(TestHasher::default())
    }

    #[derive(Debug, Clone)]
    enum Action {
        Insert(String),
        Get(String),
        Remove(String),
    }

    fn test_random(actions: impl Iterator<Item = Action>) {
        let mut our_set = new_string_set();
        let mut std_set = std::collections::HashSet::<String>::new();

        for action in actions {
            match action {
                Action::Insert(key) => {
                    assert_eq!(our_set.insert(key.clone()), std_set.insert(key));
                }
                Action::Get(key) => {
                    assert_eq!(our_set.get(&key).as_deref(), std_set.get(&key));
                }
                Action::Remove(key) => {
                    assert_eq!(our_set.remove(&key), std_set.remove(&key));
                }
            }
        }

        assert_eq!(our_set.len(), std_set.len());

        for key in our_set.iter() {
            assert!(std_set.contains(&*key));
        }

        for key in std_set.iter() {
            assert!(our_set.contains(key));
        }
    }

    fn limit_key(key_num: usize) -> String {
        // We need to create keys that have some probability that they are
        // contained in the map.
        format!("{}", key_num % 50)
    }

    fn action_strategy() -> impl Strategy<Value = Action> {
        prop_oneof![
            any::<usize>().prop_map(limit_key).prop_map(Action::Insert),
            any::<usize>().prop_map(limit_key).prop_map(Action::Get),
            any::<usize>().prop_map(limit_key).prop_map(Action::Remove),
        ]
    }

    proptest! {
        #[test]
        fn random(actions in proptest::collection::vec(action_strategy(), 1..500)) {
            test_random(actions.into_iter());
        }
    }
}
