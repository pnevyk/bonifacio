//! A hash map in simple textbook implementation with linear probing.
//!
//! Check the module documentation for details on
//!
//! * the concept of `Value` ([Serialization and
//!   Deserialization](crate#serialization-and-deserialization), [Sized vs
//!   Unsized](crate#sized-vs-unsized)), and
//! * differences from the `std::collections::HashMap` API ([Ref and
//!   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
//!
//! # Examples
//!
//! See [`HashMap`](self::HashMap) for examples.

use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};
use std::io;
use std::marker::PhantomData;
use std::mem;

use crate::storage::{
    BorrowStorage, Ref, RefMut, SizedStorage, Storage, UnsizedStorage, INITIAL_CAPACITY,
};
use crate::value::{Borrowed, SizedValue, Value, ValueBorrow};

const LOAD_FACTOR_THRESHOLD: f32 = 0.75;

/// A hash map in simple textbook implementation with linear probing.
///
/// The generic parameters `KS` and `VS` refer to underlying storages, either
/// [`SizedStorage`](crate::storage::SizedStorage) or
/// [`UnsizedStorage`](crate::storage::UnsizedStorage), depending on the key and
/// element types, respectively.
///
/// Check the module documentation for details on
///
/// * the concept of `Value` ([Serialization and
///   Deserialization](crate#serialization-and-deserialization), [Sized vs
///   Unsized](crate#sized-vs-unsized)), and
/// * differences from the `std::collections::HashMap` API ([Ref and
///   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
///
/// # Examples
///
/// ```
/// use bonifacio::HashMap;
///
/// let mut ratings = HashMap::new_unsized_sized();
///
/// ratings.insert("1984".to_string(), 4.19);
/// ratings.insert("The Lord of the Rings".to_string(), 4.5);
/// ratings.insert("On the Road".to_string(), 3.62);
///
/// if !ratings.contains_key("The Witcher") {
///     println!("There are {} books, but this one is not available", ratings.len());
/// }
///
/// assert!(ratings.remove("1984").unwrap() > 4.0);
///
/// match ratings.get("On The Road") {
///     Some(rating) => println!("Rating: {}", rating),
///     None => println!("No rating"),
/// }
///
/// for (book, rating) in ratings.iter() {
///     println!("{}: {}", book, rating);
/// }
/// ```
pub struct HashMap<K, V, KS, VS, R = RandomState> {
    entries: SizedStorage<EntryType>,
    keys: KS,
    values: VS,
    ty: PhantomData<(K, V)>,
    len: usize,
    buckets: usize,
    tombstones: usize,
    hash_builder: R,
}

impl<K, V, KS, VS> HashMap<K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    /// Constructs a new, empty `HashMap<K, V, KS, VS>`, where `KS` is type of
    /// the underlying storage for keys and `VS` is type of the underlying
    /// storage for values.
    ///
    /// The type of the underlying storages must be specified explicitly since
    /// they can't be inferred automatically.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_new`](self::HashMap::try_new)
    /// if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// use bonifacio::{SizedStorage, UnsizedStorage};
    /// let map: HashMap<String, f32, UnsizedStorage<_>, SizedStorage<_>> = HashMap::new();
    /// ```
    pub fn new() -> Self {
        Self::try_new().unwrap()
    }

    /// Constructs a new, empty `HashMap<K, V, KS, VS>`, where `KS` is type of
    /// the underlying storage for keys and `VS` is type of the underlying
    /// storage for values.
    ///
    /// The type of the underlying storages must be specified explicitly since
    /// they can't be inferred automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// use bonifacio::{SizedStorage, UnsizedStorage};
    /// let map: HashMap<String, f32, UnsizedStorage<_>, SizedStorage<_>> =
    ///     HashMap::try_new().expect("I/O error");
    /// ```
    pub fn try_new() -> io::Result<Self> {
        Self::new_inner(1024, INITIAL_CAPACITY, INITIAL_CAPACITY, RandomState::new())
    }
}

impl<K, V, KS, VS, R> HashMap<K, V, KS, VS, R>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
    R: BuildHasher,
{
    /// Constructs a new, empty `HashMap` with given hash builder to hash keys.
    ///
    /// The passed `hash_builder` must implement the
    /// [`BuildHasher`](std::hash::BuildHasher) trait for the hash map to be
    /// useful, see its documentation for details.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_with_hasher`](self::HashMap::try_with_hasher) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// use bonifacio::SizedStorage;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let state = RandomState::new();
    /// let mut map: HashMap<u32, u32, SizedStorage<_>, SizedStorage<_>> = HashMap::with_hasher(state);
    /// ```
    pub fn with_hasher(hash_builder: R) -> Self {
        Self::try_with_hasher(hash_builder).unwrap()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the
    /// [`std::collections`](std::collections#insert-and-complex-keys) for more.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_insert`](self::HashMap::try_insert) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.insert(3, "foo".to_string());
    /// assert_eq!(map.len(), 1);
    ///
    /// assert_eq!(map.insert(3, "bar".to_string()).as_deref(), Some("foo"));
    /// assert_eq!(map.get(&3).as_deref(), Some(&"bar".to_string()));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.try_insert(key, value).unwrap()
    }

    /// Returns the key-value pair corresponding to given key.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_get_key_value`](self::HashMap::try_get_key_value) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    ///
    /// let key_value = map.get_key_value("foo").unwrap();
    /// assert_eq!(&*key_value.0, "foo");
    /// assert_eq!(&*key_value.1, &3);
    /// assert_eq!(map.get_key_value("bar"), None);
    /// ```
    pub fn get_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(Ref<'_, K>, Ref<'_, V>)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_get_key_value(key).unwrap()
    }

    /// Returns a [`Ref`](crate::storage::Ref) to a value corresponding to given
    /// key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_get`](self::HashMap::try_get)
    /// if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.get("foo").as_deref(), Some(&3));
    /// assert_eq!(map.get("bar"), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<Ref<'_, V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_get(key).unwrap()
    }

    /// Returns a [`RefMut`](crate::storage::RefMut) to a value corresponding to
    /// the key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_get_mut`](self::HashMap::try_get_mut) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    ///
    /// if let Some(elem) = map.get_mut("foo").as_deref_mut() {
    ///     *elem = 42;
    /// }
    ///
    /// assert_eq!(map.get("foo").as_deref(), Some(&42));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<RefMut<'_, V, VS>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_get_mut(key).unwrap()
    }

    /// Removes a key from the map, returning the value at the key, or `None` if
    /// the key was not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_remove`](self::HashMap::try_remove) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.remove("foo"), Some(3));
    /// assert_eq!(map.remove("foo"), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_remove(key).unwrap()
    }

    /// Returns `true` if the map contains a value for given key.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_contains_key`](self::HashMap::try_contains_key) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.contains_key("foo"), true);
    /// assert_eq!(map.contains_key("bar"), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_contains_key(key).unwrap()
    }

    /// Returns an iterator over key-value pairs of the map in arbitrary order.
    ///
    /// # Panics
    ///
    /// `Iter::next` panics when an I/O error occurs. Use
    /// [`try_iter`](self::HashMap::try_iter) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    ///
    /// for (key, value) in map.iter() {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V, KS, VS> {
        Iter {
            inner: RawIter::from_parts(&self.entries, &self.keys, &self.values),
        }
    }

    /// Returns an iterator over keys of the map in arbitrary order.
    ///
    /// # Panics
    ///
    /// `Keys::next` panics when an I/O error occurs. Use
    /// [`try_keys`](self::HashMap::try_keys) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    ///
    /// for key in map.keys() {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V, KS, VS> {
        Keys {
            inner: self.try_keys(),
        }
    }

    /// Returns an iterator over values of the map in arbitrary order.
    ///
    /// # Panics
    ///
    /// `Values::next` panics when an I/O error occurs. Use
    /// [`try_values`](self::HashMap::try_values) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    ///
    /// for value in map.values() {
    ///     println!("value: {}", value);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, K, V, KS, VS> {
        Values {
            inner: self.try_values(),
        }
    }

    /// Constructs a new, empty `HashMap` with given hash builder to hash keys.
    ///
    /// The passed `hash_builder` must implement the
    /// [`BuildHasher`](std::hash::BuildHasher) trait for the hash map to be
    /// useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// use bonifacio::SizedStorage;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let state = RandomState::new();
    /// let mut map: HashMap<u32, u32, SizedStorage<_>, SizedStorage<_>> =
    ///     HashMap::try_with_hasher(state).expect("I/O error");
    /// ```
    pub fn try_with_hasher(hash_builder: R) -> io::Result<Self> {
        Self::new_inner(1024, INITIAL_CAPACITY, INITIAL_CAPACITY, hash_builder)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the
    /// [`std::collections`](std::collections#insert-and-complex-keys) for more.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.try_insert(3, "foo".to_string()).expect("I/O error");
    /// assert_eq!(map.len(), 1);
    ///
    /// assert_eq!(map.try_insert(3, "bar".to_string()).expect("I/O error").as_deref(), Some("foo"));
    /// assert_eq!(map.get(&3).as_deref(), Some(&"bar".to_string()));
    /// ```
    pub fn try_insert(&mut self, key: K, value: V) -> io::Result<Option<V>> {
        self.grow_maybe()?;

        let (index, entry) = self.scan_with_hash(self.make_hash(&key)).find_empty(&key)?;

        let (previous, new_bucket) = if entry == EntryType::Occupied {
            (Some(self.values.get(index)?), false)
        } else {
            if let Some((index, _)) = self.scan_with_index(index + 1).find_key(&key)? {
                self.entries.set(index, &EntryType::Tombstone)?;
                self.tombstones += 1;
                (Some(self.values.get(index)?), false)
            } else {
                (None, true)
            }
        };

        self.entries.set(index, &EntryType::Occupied)?;
        self.values.set(index, &value)?;

        // The key is not updated when the insert replaces an existing element.
        if entry != EntryType::Occupied {
            self.keys.set(index, &key)?;
        }

        if new_bucket {
            self.len += 1;
        }

        if entry == EntryType::Tombstone {
            self.tombstones -= 1;
        }

        Ok(previous)
    }

    /// Returns the key-value pair corresponding to given key.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    ///
    /// let key_value = map.try_get_key_value("foo").expect("I/O error").unwrap();
    /// assert_eq!(&*key_value.0, "foo");
    /// assert_eq!(&*key_value.1, &3);
    /// assert_eq!(map.try_get_key_value("bar").expect("I/O error"), None);
    /// ```
    pub fn try_get_key_value<Q: ?Sized>(
        &self,
        key: &Q,
    ) -> io::Result<Option<(Ref<'_, K>, Ref<'_, V>)>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        if let Some((index, key)) = self.scan_with_hash(self.make_hash(key)).find_key(key)? {
            Ok(Some((Ref::from_raw(key), self.values.get_ref(index)?)))
        } else {
            Ok(None)
        }
    }

    /// Returns a [`Ref`](crate::storage::Ref) to a value corresponding to given
    /// key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.try_get("foo").expect("I/O error").as_deref(), Some(&3));
    /// assert_eq!(map.try_get("bar").expect("I/O error"), None);
    /// ```
    pub fn try_get<Q: ?Sized>(&self, key: &Q) -> io::Result<Option<Ref<'_, V>>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.try_get_key_value(key) {
            Ok(Some((_, value))) => Ok(Some(value)),
            Ok(None) => Ok(None),
            Err(err) => Err(err),
        }
    }

    /// Returns a [`RefMut`](crate::storage::RefMut) to a value corresponding to
    /// the key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    ///
    /// if let Some(elem) = map.try_get_mut("foo").expect("I/O error").as_deref_mut() {
    ///     *elem = 42;
    /// }
    ///
    /// assert_eq!(map.get("foo").as_deref(), Some(&42));
    /// ```
    pub fn try_get_mut<Q: ?Sized>(&mut self, key: &Q) -> io::Result<Option<RefMut<'_, V, VS>>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        if let Some((index, _)) = self.scan_with_hash(self.make_hash(key)).find_key(key)? {
            Ok(Some(self.values.get_mut(index)?))
        } else {
            Ok(None)
        }
    }

    /// Removes a key from the map, returning the value at the key, or `None` if
    /// the key was not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.try_remove("foo").expect("I/O error"), Some(3));
    /// assert_eq!(map.try_remove("foo").expect("I/O error"), None);
    /// ```
    pub fn try_remove<Q: ?Sized>(&mut self, key: &Q) -> io::Result<Option<V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        if let Some((index, _)) = self.scan_with_hash(self.make_hash(key)).find_key(key)? {
            self.entries.set(index, &EntryType::Tombstone)?;
            self.len -= 1;
            self.tombstones += 1;
            Ok(Some(self.values.get(index)?))
        } else {
            Ok(None)
        }
    }

    /// Returns `true` if the map contains a value for given key.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.try_contains_key("foo").expect("I/O error"), true);
    /// assert_eq!(map.try_contains_key("bar").expect("I/O error"), false);
    /// ```
    pub fn try_contains_key<Q: ?Sized>(&self, key: &Q) -> io::Result<bool>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        Ok(self
            .scan_with_hash(self.make_hash(key))
            .find_key(key)?
            .is_some())
    }

    /// Returns a checked variant of iterator over key-value pairs of the map in
    /// arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    ///
    /// for (key, value) in map.try_iter().map(|r| r.expect("I/O error")) {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
    pub fn try_iter(&self) -> TryIter<'_, K, V, KS, VS> {
        TryIter {
            inner: RawIter::from_parts(&self.entries, &self.keys, &self.values),
        }
    }

    /// Returns a checked variant of iterator over keys of the map in arbitrary
    /// order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    ///
    /// for key in map.try_keys().map(|r| r.expect("I/O error")) {
    ///     println!("key: {}", key);
    /// }
    /// ```
    pub fn try_keys(&self) -> TryKeys<'_, K, V, KS, VS> {
        TryKeys {
            inner: self.try_iter(),
        }
    }

    /// Returns a checked variant of iterator over values of the map in
    /// arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 1);
    /// map.insert("hello world".to_string(), 2);
    /// map.insert("bonifacio".to_string(), 3);
    ///
    /// for value in map.try_values().map(|r| r.expect("I/O error")) {
    ///     println!("value: {}", value);
    /// }
    /// ```
    pub fn try_values(&self) -> TryValues<'_, K, V, KS, VS> {
        TryValues {
            inner: self.try_iter(),
        }
    }

    fn new_inner(
        buckets: usize,
        keys_capacity: usize,
        values_capacity: usize,
        hash_builder: R,
    ) -> io::Result<Self> {
        let mut keys = KS::new(keys_capacity)?;
        let mut values = VS::new(values_capacity)?;

        unsafe {
            keys.reserve(buckets)?;
            values.reserve(buckets)?;
        }

        let mut entries = SizedStorage::new(buckets)?;

        for i in 0..buckets {
            entries.set(i, &EntryType::Vacant)?;
        }

        Ok(Self {
            entries,
            keys,
            values,
            ty: PhantomData,
            len: 0,
            buckets,
            tombstones: 0,
            hash_builder,
        })
    }

    fn grow_maybe(&mut self) -> io::Result<()> {
        let load_factor = (self.len + self.tombstones) as f32 / (self.buckets as f32);

        if load_factor > LOAD_FACTOR_THRESHOLD {
            self.buckets = 2 * self.buckets;
            self.len = 0;
            self.tombstones = 0;

            let entries = mem::replace(&mut self.entries, SizedStorage::new(self.buckets)?);

            let keys_len = 2 * self.keys.byte_len();
            let keys = mem::replace(&mut self.keys, KS::new(keys_len)?);

            let values_len = 2 * self.values.byte_len();
            let values = mem::replace(&mut self.values, VS::new(values_len)?);

            unsafe {
                self.keys.reserve(self.buckets)?;
                self.values.reserve(self.buckets)?;
            }

            for i in 0..self.buckets {
                self.entries.set(i, &EntryType::Vacant)?;
            }

            for item in RawIter::from_parts(&entries, &keys, &values) {
                let (key, value) = item?;
                self.try_insert(key, value)?;
            }
        }

        Ok(())
    }

    fn make_hash<Q: ?Sized>(&self, key: &Q) -> u64
    where
        Q: Hash,
    {
        let mut state = self.hash_builder.build_hasher();
        key.hash(&mut state);
        state.finish()
    }

    fn scan_with_hash(&self, hash: u64) -> EntryScan<'_, K, KS> {
        EntryScan::with_hash(hash, &self.entries, &self.keys)
    }

    fn scan_with_index(&self, index: usize) -> EntryScan<'_, K, KS> {
        EntryScan::with_index(index, &self.entries, &self.keys)
    }
}

impl<K, V, KS, VS> HashMap<K, V, KS, VS>
where
    K: Hash + Eq,
    V: ValueBorrow,
    KS: Storage<K>,
    VS: BorrowStorage<V>,
{
    /// Returns the key-value pair corresponding to given key, where the value
    /// is in [`borrowed`](crate::value::Borrowed) form, or `None` if the key is
    /// not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_borrow_key_value`](self::HashMap::try_borrow_key_value) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.insert(3, "foo".to_string());
    ///
    /// let key_value = map.borrow_key_value(&3);
    /// assert_eq!(key_value.map(|kv| kv.1).as_deref(), Some("foo"));
    /// ```
    pub fn borrow_key_value<Q: ?Sized>(&self, key: &Q) -> Option<(Ref<'_, K>, Borrowed<'_, V>)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_borrow_key_value(key).unwrap()
    }

    /// Returns a [borrowed](crate::value::Borrowed) value corresponding to
    /// given key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_borrow`](self::HashMap::try_borrow) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.insert(3, "foo".to_string());
    /// assert_eq!(map.borrow(&3).as_deref(), Some("foo"));
    /// ```
    pub fn borrow<Q: ?Sized>(&self, key: &Q) -> Option<Borrowed<'_, V>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.try_borrow(key).unwrap()
    }

    /// Returns the key-value pair corresponding to given key, where the value
    /// is in [`borrowed`](crate::value::Borrowed) form, or `None` if the key is
    /// not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.insert(3, "foo".to_string());
    ///
    /// let key_value = map.try_borrow_key_value(&3).expect("I/O error");
    /// assert_eq!(key_value.map(|kv| kv.1).as_deref(), Some("foo"));
    /// ```
    pub fn try_borrow_key_value<Q: ?Sized>(
        &self,
        key: &Q,
    ) -> io::Result<Option<(Ref<'_, K>, Borrowed<'_, V>)>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        if let Some((index, key)) = self.scan_with_hash(self.make_hash(key)).find_key(key)? {
            Ok(Some((Ref::from_raw(key), self.values.borrow(index)?)))
        } else {
            Ok(None)
        }
    }

    /// Returns a [borrowed](crate::value::Borrowed) value corresponding to
    /// given key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.insert(3, "foo".to_string());
    /// assert_eq!(map.try_borrow(&3).expect("I/O error").as_deref(), Some("foo"));
    /// ```
    pub fn try_borrow<Q: ?Sized>(&self, key: &Q) -> io::Result<Option<Borrowed<'_, V>>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        match self.try_borrow_key_value(key) {
            Ok(Some((_, value))) => Ok(Some(value)),
            Ok(None) => Ok(None),
            Err(err) => Err(err),
        }
    }
}

impl<K, V, KS, VS> HashMap<K, V, KS, VS>
where
    K: ValueBorrow + Hash + Eq,
    KS: BorrowStorage<K>,
    VS: Storage<V>,
{
    /// Returns a [borrowed](crate::value::Borrowed) form of the key
    /// corresponding to given key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_borrow_key`](self::HashMap::try_borrow_key) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.borrow_key("foo").as_deref(), Some("foo"));
    /// ```
    pub fn borrow_key<Q: ?Sized>(&self, key: &Q) -> Option<Borrowed<'_, K>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + PartialEq<K::Borrowed>,
    {
        self.try_borrow_key(key).unwrap()
    }

    /// Returns a [borrowed](crate::value::Borrowed) form of the key
    /// corresponding to given key, or `None` if the key is not present.
    ///
    /// The supplied key may be any [`Borrow`](std::borrow::Borrow) form of the
    /// map's key type, but [`Hash`](std::hash::Hash) and [`Eq`](std::cmp::Eq)
    /// on the borrowed form *must* match those for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// assert_eq!(map.try_borrow_key("foo").expect("I/O error").as_deref(), Some("foo"));
    /// ```
    pub fn try_borrow_key<Q: ?Sized>(&self, key: &Q) -> io::Result<Option<Borrowed<'_, K>>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + PartialEq<K::Borrowed>,
    {
        if let Some((_, key)) = self.scan_with_hash(self.make_hash(key)).borrow_key(key)? {
            Ok(Some(key))
        } else {
            Ok(None)
        }
    }
}

impl<K, V> HashMap<K, V, UnsizedStorage<K>, UnsizedStorage<V>>
where
    K: Value + Hash + Eq,
    V: Value,
{
    /// Constructs a new, empty `HashMap<K, V, UnsizedStorage<K>,
    /// UnsizedStorage<V>>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_unsized`](self::HashMap::try_new_unsized) if this is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized();
    /// map.insert("hello world".to_string(), "foo".to_string());
    /// ```
    pub fn new_unsized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `HashMap<K, V, UnsizedStorage<K>,
    /// UnsizedStorage<V>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::try_new_unsized().expect("I/O error");
    /// map.insert("hello world".to_string(), "foo".to_string());
    /// ```
    pub fn try_new_unsized() -> io::Result<Self> {
        Self::try_new()
    }
}

impl<K, V> HashMap<K, V, SizedStorage<K>, SizedStorage<V>>
where
    K: SizedValue + Hash + Eq,
    V: SizedValue,
{
    /// Constructs a new, empty `HashMap<K, V, SizedStorage<K>,
    /// SizedStorage<V>>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_sized`](self::HashMap::try_new_sized) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized();
    /// map.insert(1, 3.14);
    /// ```
    pub fn new_sized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `HashMap<K, V, SizedStorage<K>,
    /// SizedStorage<V>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::try_new_sized().expect("I/O error");
    /// map.insert(1, 3.14);
    /// ```
    pub fn try_new_sized() -> io::Result<Self> {
        Self::try_new()
    }
}

impl<K, V> HashMap<K, V, SizedStorage<K>, UnsizedStorage<V>>
where
    K: SizedValue + Hash + Eq,
    V: Value,
{
    /// Constructs a new, empty `HashMap<K, V, SizedStorage<K>,
    /// UnsizedStorage<V>>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_sized_unsized`](self::HashMap::try_new_sized_unsized) if this
    /// is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_sized_unsized();
    /// map.insert(3, "foo".to_string());
    /// ```
    pub fn new_sized_unsized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `HashMap<K, V, SizedStorage<K>,
    /// UnsizedStorage<V>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::try_new_sized_unsized().expect("I/O error");
    /// map.insert(3, "foo".to_string());
    /// ```
    pub fn try_new_sized_unsized() -> io::Result<Self> {
        Self::try_new()
    }
}

impl<K, V> HashMap<K, V, UnsizedStorage<K>, SizedStorage<V>>
where
    K: Value + Hash + Eq,
    V: SizedValue,
{
    /// Constructs a new, empty `HashMap<K, V, UnsizedStorage<K>,
    /// SizedStorage<V>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::try_new_unsized_sized().expect("I/O error");
    /// map.insert("foo".to_string(), 3);
    /// ```
    pub fn try_new_unsized_sized() -> io::Result<Self> {
        Self::try_new()
    }

    /// Constructs a new, empty `HashMap<K, V, UnsizedStorage<K>,
    /// SizedStorage<V>>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_unsized_sized`](self::HashMap::try_new_unsized_sized) if this
    /// is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::HashMap;
    /// let mut map = HashMap::new_unsized_sized();
    /// map.insert("foo".to_string(), 3);
    /// ```
    pub fn new_unsized_sized() -> Self {
        Self::new()
    }
}

#[derive(PartialEq, Eq)]
enum EntryType {
    Vacant,
    Occupied,
    Tombstone,
}

impl Value for EntryType {
    fn to_bytes(&self, buf: &mut Vec<u8>) {
        let byte = match self {
            EntryType::Vacant => 0,
            EntryType::Occupied => 1,
            EntryType::Tombstone => 2,
        };

        buf.push(byte)
    }

    fn from_bytes(buf: &[u8]) -> Self {
        match buf[0] {
            0 => EntryType::Vacant,
            1 => EntryType::Occupied,
            2 => EntryType::Tombstone,
            _ => unreachable!(),
        }
    }
}

impl SizedValue for EntryType {
    fn size() -> usize {
        1
    }
}

struct EntryScan<'a, K, KS> {
    entries: &'a SizedStorage<EntryType>,
    keys: &'a KS,
    ty: PhantomData<K>,
    index: usize,
}

impl<'a, K, KS> EntryScan<'a, K, KS>
where
    K: Eq,
    KS: Storage<K>,
{
    pub fn with_hash(hash: u64, entries: &'a SizedStorage<EntryType>, keys: &'a KS) -> Self {
        Self {
            entries,
            keys,
            ty: PhantomData,
            index: hash as usize % entries.len(),
        }
    }

    pub fn with_index(index: usize, entries: &'a SizedStorage<EntryType>, keys: &'a KS) -> Self {
        Self {
            entries,
            keys,
            ty: PhantomData,
            index: index % entries.len(),
        }
    }

    pub fn find_key<Q: ?Sized>(&mut self, key: &Q) -> io::Result<Option<(usize, K)>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.find_key_with(|scan, index| {
            let occupied_key = scan.keys.get(index)?;

            if key == occupied_key.borrow() {
                Ok(Some(occupied_key))
            } else {
                Ok(None)
            }
        })
    }

    pub fn find_empty(&mut self, key: &K) -> io::Result<(usize, EntryType)> {
        loop {
            match self.entries.get(self.index)? {
                entry @ EntryType::Vacant | entry @ EntryType::Tombstone => {
                    return Ok((self.index, entry));
                }
                entry @ EntryType::Occupied => {
                    let occupied_key = self.keys.get(self.index)?;

                    if key == &occupied_key {
                        return Ok((self.index, entry));
                    } else {
                        self.update_index();
                    }
                }
            }
        }
    }

    fn find_key_with<F, R>(&mut self, compare: F) -> io::Result<Option<(usize, R)>>
    where
        F: Fn(&mut Self, usize) -> io::Result<Option<R>>,
    {
        loop {
            match self.entries.get(self.index)? {
                EntryType::Vacant => {
                    // Not found.
                    return Ok(None);
                }
                EntryType::Occupied => match compare(self, self.index)? {
                    Some(result) => return Ok(Some((self.index, result))),
                    None => self.update_index(),
                },
                EntryType::Tombstone => {
                    // Continue.
                    self.update_index();
                }
            }
        }
    }

    fn update_index(&mut self) {
        // Linear probing.
        self.index = (self.index + 1) % self.entries.len()
    }
}

impl<'a, K, KS> EntryScan<'a, K, KS>
where
    K: Eq + ValueBorrow,
    KS: BorrowStorage<K>,
{
    pub fn borrow_key<Q: ?Sized>(&mut self, key: &Q) -> io::Result<Option<(usize, Borrowed<'a, K>)>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + PartialEq<K::Borrowed>,
    {
        self.find_key_with(|scan, index| {
            let occupied_key = scan.keys.borrow(index)?;

            if key == (*occupied_key).borrow() {
                Ok(Some(occupied_key))
            } else {
                Ok(None)
            }
        })
    }
}

struct RawIter<'a, K, V, KS, VS> {
    entries: &'a SizedStorage<EntryType>,
    keys: &'a KS,
    values: &'a VS,
    ty: PhantomData<(K, V)>,
    current: usize,
}

impl<'a, K, V, KS, VS> RawIter<'a, K, V, KS, VS> {
    pub fn from_parts(entries: &'a SizedStorage<EntryType>, keys: &'a KS, values: &'a VS) -> Self {
        Self {
            entries,
            keys,
            values,
            ty: PhantomData,
            current: 0,
        }
    }
}

impl<'a, K, V, KS, VS> Iterator for RawIter<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = io::Result<(K, V)>;

    fn next(&mut self) -> Option<Self::Item> {
        macro_rules! ok {
            ($result:expr) => {
                match $result {
                    Ok(value) => value,
                    Err(err) => return Some(Err(err)),
                }
            };
        }

        while self.current < self.entries.len() {
            if ok!(self.entries.get(self.current)) == EntryType::Occupied {
                let key = ok!(self.keys.get(self.current));
                let value = ok!(self.values.get(self.current));
                self.current += 1;
                return Some(Ok((key, value)));
            } else {
                self.current += 1;
            }
        }

        None
    }
}

/// An immutable iterator over the key-value pairs of the map in arbitrary
/// order, propagating I/O errors.
///
/// This struct is created by the [`try_iter`](self::HashMap::try_iter) method
/// on [`HashMap`](self::HashMap).
///
/// # Examples
///
/// ```
/// # use bonifacio::HashMap;
/// let mut map = HashMap::new_unsized_sized();
/// map.insert("foo".to_string(), 1);
/// map.insert("hello world".to_string(), 2);
/// map.insert("bonifacio".to_string(), 3);
///
/// for (key, value) in map.try_iter().map(|r| r.expect("I/O error")) {
///     println!("{}: {}", key, value);
/// }
/// ```
pub struct TryIter<'a, K, V, KS, VS> {
    inner: RawIter<'a, K, V, KS, VS>,
}

impl<'a, K, V, KS, VS> Iterator for TryIter<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = io::Result<(Ref<'a, K>, Ref<'a, V>)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|result| result.map(|(key, value)| (Ref::from_raw(key), Ref::from_raw(value))))
    }
}

/// An immutable iterator over the key-value pairs of the map in arbitrary
/// order, panicking on I/O errors.
///
/// This struct is created by the [`iter`](self::HashMap::iter) method on
/// [`HashMap`](self::HashMap).
///
/// # Panics
///
/// `Iter::next` panics when an I/O error occurs. Use
/// [`try_iter`](self::HashMap::try_iter) if this is unacceptable.
///
/// # Examples
///
/// ```
/// # use bonifacio::HashMap;
/// let mut map = HashMap::new_unsized_sized();
/// map.insert("foo".to_string(), 1);
/// map.insert("hello world".to_string(), 2);
/// map.insert("bonifacio".to_string(), 3);
///
/// for (key, value) in map.iter() {
///     println!("{}: {}", key, value);
/// }
/// ```
pub struct Iter<'a, K, V, KS, VS> {
    inner: RawIter<'a, K, V, KS, VS>,
}

impl<'a, K, V, KS, VS> Iterator for Iter<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = (Ref<'a, K>, Ref<'a, V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(Result::unwrap)
            .map(|(key, value)| (Ref::from_raw(key), Ref::from_raw(value)))
    }
}

/// An immutable iterator over the keys of the map in arbitrary order,
/// propagating I/O errors.
///
/// This struct is created by the [`try_keys`](self::HashMap::try_keys) method
/// on [`HashMap`](self::HashMap).
///
/// # Examples
///
/// ```
/// # use bonifacio::HashMap;
/// let mut map = HashMap::new_unsized_sized();
/// map.insert("foo".to_string(), 1);
/// map.insert("hello world".to_string(), 2);
/// map.insert("bonifacio".to_string(), 3);
///
/// for key in map.try_keys().map(|r| r.expect("I/O error")) {
///     println!("key: {}", key);
/// }
/// ```
pub struct TryKeys<'a, K, V, KS, VS> {
    inner: TryIter<'a, K, V, KS, VS>,
}

impl<'a, K, V, KS, VS> Iterator for TryKeys<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = io::Result<Ref<'a, K>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((key, _)) => Some(Ok(key)),
            Err(err) => Some(Err(err)),
        }
    }
}

/// An immutable iterator over the keys of the map in arbitrary order, panicking
/// on I/O errors.
///
/// This struct is created by the [`keys`](self::HashMap::keys) method on
/// [`HashMap`](self::HashMap).
///
/// # Panics
///
/// `Keys::next` panics when an I/O error occurs. Use
/// [`try_keys`](self::HashMap::try_keys) if this is unacceptable.
///
/// # Examples
///
/// ```
/// # use bonifacio::HashMap;
/// let mut map = HashMap::new_unsized_sized();
/// map.insert("foo".to_string(), 1);
/// map.insert("hello world".to_string(), 2);
/// map.insert("bonifacio".to_string(), 3);
///
/// for key in map.keys() {
///     println!("key: {}", key);
/// }
/// ```
pub struct Keys<'a, K, V, KS, VS> {
    inner: TryKeys<'a, K, V, KS, VS>,
}

impl<'a, K, V, KS, VS> Iterator for Keys<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = Ref<'a, K>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Result::unwrap)
    }
}

/// An immutable iterator over the values of the map in arbitrary order,
/// propagating I/O errors.
///
/// This struct is created by the [`try_values`](self::HashMap::try_values)
/// method on [`HashMap`](self::HashMap).
///
/// # Examples
///
/// ```
/// # use bonifacio::HashMap;
/// let mut map = HashMap::new_unsized_sized();
/// map.insert("foo".to_string(), 1);
/// map.insert("hello world".to_string(), 2);
/// map.insert("bonifacio".to_string(), 3);
///
/// for value in map.try_values().map(|r| r.expect("I/O error")) {
///     println!("value: {}", value);
/// }
/// ```
pub struct TryValues<'a, K, V, KS, VS> {
    inner: TryIter<'a, K, V, KS, VS>,
}

impl<'a, K, V, KS, VS> Iterator for TryValues<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = io::Result<Ref<'a, V>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((_, value)) => Some(Ok(value)),
            Err(err) => Some(Err(err)),
        }
    }
}

/// An immutable iterator over the values of the map in arbitrary order,
/// panicking on I/O errors.
///
/// This struct is created by the [`values`](self::HashMap::values) method on
/// [`HashMap`](self::HashMap).
///
/// # Panics
///
/// `Values::next` panics when an I/O error occurs. Use
/// [`try_values`](self::HashMap::try_values) if this is unacceptable.
///
/// # Examples
///
/// ```
/// # use bonifacio::HashMap;
/// let mut map = HashMap::new_unsized_sized();
/// map.insert("foo".to_string(), 1);
/// map.insert("hello world".to_string(), 2);
/// map.insert("bonifacio".to_string(), 3);
///
/// for value in map.values() {
///     println!("value: {}", value);
/// }
/// ```
pub struct Values<'a, K, V, KS, VS> {
    inner: TryValues<'a, K, V, KS, VS>,
}

impl<'a, K, V, KS, VS> Iterator for Values<'a, K, V, KS, VS>
where
    K: Hash + Eq,
    KS: Storage<K>,
    VS: Storage<V>,
{
    type Item = Ref<'a, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Result::unwrap)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{BuildHasherDefault, Hash, Hasher};

    use proptest::prelude::*;

    use crate::storage::UnsizedStorage;

    type TestHasher = BuildHasherDefault<DefaultHasher>;

    fn new_string_string_map(
    ) -> super::HashMap<String, String, UnsizedStorage<String>, UnsizedStorage<String>, TestHasher>
    {
        super::HashMap::with_hasher(TestHasher::default())
    }

    #[test]
    fn basic() {
        let mut map = new_string_string_map();

        assert!(map.insert(String::from("0"), String::from("foo")).is_none());
        assert!(map.insert(String::from("1"), String::from("bar")).is_none());

        assert_eq!(map.get("0").as_deref(), Some(&String::from("foo")));

        assert_eq!(
            map.insert(String::from("0"), String::from("baz")),
            Some(String::from("foo"))
        );
        assert_eq!(map.get("0").as_deref(), Some(&String::from("baz")));

        assert_eq!(map.remove("0"), Some(String::from("baz")));
        assert!(map.get("0").is_none());

        assert!(map.insert(String::from("0"), String::from("quo")).is_none());
        assert_eq!(map.get("0").as_deref(), Some(&String::from("quo")));
    }

    #[test]
    fn insert_behavior_on_equal_key() {
        struct Key {
            key: u64,
            hidden: u64,
        }

        impl PartialEq for Key {
            fn eq(&self, other: &Self) -> bool {
                self.key == other.key
            }
        }

        impl Eq for Key {}

        impl Hash for Key {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.key.hash(state);
            }
        }

        use crate::{
            tools::{StructDeserializer, StructSerializer},
            Value,
        };

        impl Value for Key {
            fn to_bytes(&self, buf: &mut Vec<u8>) {
                StructSerializer::new(buf)
                    .field(&self.key)
                    .field(&self.hidden)
                    .finish();
            }

            fn from_bytes(bytes: &[u8]) -> Self {
                let deserializer = StructDeserializer::new(bytes);
                unsafe {
                    Key {
                        key: deserializer.field(0),
                        hidden: deserializer.field(1),
                    }
                }
            }
        }

        let mut map = super::HashMap::new_unsized_sized();

        assert!(map.insert(Key { key: 3, hidden: 0 }, 1).is_none());
        assert_eq!(map.insert(Key { key: 3, hidden: 1 }, 2), Some(1));
        let pair = map.iter().next();
        // The key should not have been be updated.
        assert_eq!(pair.map(|p| p.0.hidden), Some(0));
    }

    #[test]
    fn proptest_trophy1() {
        let mut map = new_string_string_map();

        assert_eq!(map.insert(String::from("12"), String::from("")), None);
        assert_eq!(map.insert(String::from("35"), String::from("")), None);
        assert_eq!(map.remove("12"), Some(String::from("")));
        assert_eq!(
            map.insert(String::from("35"), String::from("")),
            Some(String::from(""))
        );
    }

    #[test]
    fn proptest_trophy2() {
        let mut map = new_string_string_map();

        assert_eq!(map.insert(String::from("30"), String::from("")), None);
        assert_eq!(
            map.insert(String::from("30"), String::from("")),
            Some(String::from(""))
        );
        assert_eq!(map.len(), 1);
    }

    #[derive(Debug, Clone)]
    enum Action {
        Insert((String, String)),
        Get(String),
        Remove(String),
    }

    fn test_random(actions: impl Iterator<Item = Action>) {
        let mut our_map = new_string_string_map();
        let mut std_map = std::collections::HashMap::<String, String>::new();

        for action in actions {
            match action {
                Action::Insert((key, value)) => {
                    assert_eq!(
                        our_map.insert(key.clone(), value.clone()),
                        std_map.insert(key, value)
                    );
                }
                Action::Get(key) => {
                    assert_eq!(our_map.get(&key).as_deref(), std_map.get(&key));
                }
                Action::Remove(key) => {
                    assert_eq!(our_map.remove(&key), std_map.remove(&key));
                }
            }
        }

        assert_eq!(our_map.len(), std_map.len());

        for (key, value) in our_map.iter() {
            assert_eq!(Some(&*value), std_map.get(&*key));
        }

        for (key, value) in std_map.iter() {
            assert_eq!(Some(value), our_map.get(key).as_deref());
        }
    }

    fn limit_key(key_num: usize) -> String {
        // We need to create keys that have some probability that they are
        // contained in the map.
        format!("{}", key_num % 50)
    }

    fn action_strategy() -> impl Strategy<Value = Action> {
        prop_oneof![
            any::<(usize, String)>()
                .prop_map(|(key, value)| (limit_key(key), value))
                .prop_map(Action::Insert),
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
