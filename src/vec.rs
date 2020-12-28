//! A `Vec`-like container that stores the elements in a file instead of memory.
//!
//! Check the module documentation for details on
//!
//! * the concept of `Value` ([Serialization and
//!   Deserialization](crate#serialization-and-deserialization), [Sized vs
//!   Unsized](crate#sized-vs-unsized)), and
//! * differences from the `std::vec::Vec` API ([Ref and
//!   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
//!
//! # Examples
//!
//! See [`Vec`](self::Vec) for examples.
use std::io;
use std::marker::PhantomData;

use crate::storage::{
    BorrowStorage, Ref, RefMut, SizedStorage, Storage, UnsizedStorage, INITIAL_CAPACITY,
};
use crate::value::{Borrowed, SizedValue, Value, ValueBorrow};

/// A `Vec`-like container that stores the elements in a file instead of memory.
///
/// The generic parameter `S` refers to an underlying storage, either
/// [`SizedStorage`](crate::storage::SizedStorage) or
/// [`UnsizedStorage`](crate::storage::UnsizedStorage), depending on the element
/// type. Do not confuse it with allocator generic type `A` in `std::Vec<T, A>`.
///
/// Check the module documentation for details on
///
/// * the concept of `Value` ([Serialization and
///   Deserialization](crate#serialization-and-deserialization), [Sized vs
///   Unsized](crate#sized-vs-unsized)), and
/// * differences from the `std::vec::Vec` API ([Ref and
///   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
///
/// # Examples
///
/// ```
/// use bonifacio::Vec;
///
/// let mut vec = Vec::new_sized();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec.get(0).as_deref(), Some(&1));
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// *vec.get_mut(0).unwrap() = 7;
/// assert_eq!(vec.get(0).as_deref(), Some(&7));
///
/// for x in vec.iter() {
///     println!("{}", x);
/// }
/// ```
///
/// The constructors postfixed with `_sized` and `_unsized` are for convenience,
/// to specify what underlying storage will be used. Otherwise, it is necessary
/// to write the storage type explicitly since it can't be inferred.
///
/// ```
/// # use bonifacio::Vec;
/// use bonifacio::SizedStorage;
/// let mut vec: Vec<_, SizedStorage<_>> = Vec::new();
/// vec.push(1);
/// ```
pub struct Vec<T, S> {
    storage: S,
    ty: PhantomData<T>,
}

impl<T, S> Vec<T, S>
where
    S: Storage<T>,
{
    fn with_capacity_inner(capacity: usize) -> io::Result<Self> {
        // harrow requires non-zero length.
        let capacity = if capacity == 0 {
            INITIAL_CAPACITY
        } else {
            capacity
        };

        Ok(Self {
            storage: S::new(capacity)?,
            ty: PhantomData,
        })
    }

    /// Constructs a new, empty `Vec<T, S>`, where `S` is type of the underlying
    /// storage.
    ///
    /// The type of the underlying storage must be specified explicitly since it
    /// can't be inferred automatically.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_new`](self::Vec::try_new) if
    /// this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// use bonifacio::SizedStorage;
    /// let vec: Vec<u32, SizedStorage<_>> = Vec::new();
    /// ```
    pub fn new() -> Self {
        Self::try_new().unwrap()
    }

    /// Returns the number of elements in the vector, also referred to as its
    /// "length".
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_unsized();
    /// vec.push("foo".to_string());
    /// vec.push("hello world".to_string());
    /// vec.push("bonifacio".to_string());
    /// assert_eq!(vec.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.storage.len()
    }

    /// Returns the number of **bytes** that the vector can hold without
    /// resizing the underlying file. The number of elements depends on their
    /// size in serialized representation.
    ///
    /// # Examples
    ///
    /// The granularity of this value is determined by
    /// [`harrow::granularity`](harrow::granularity).
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_unsized();
    /// assert_eq!(vec.byte_capacity(), harrow::granularity());
    ///
    /// vec.push((0..harrow::granularity()).map(|_| 'B').collect::<String>());
    /// assert_eq!(vec.byte_capacity(), harrow::granularity());
    ///
    /// vec.push("B".to_string());
    /// assert_eq!(vec.byte_capacity(), 2 * harrow::granularity());
    /// ```
    pub fn byte_capacity(&self) -> usize {
        self.storage.byte_capacity()
    }

    /// Returns a [`Ref`](crate::storage::Ref) to an element at position
    /// `index`, or `None` if the index is out of bounds.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_get`](self::Vec::try_get) if
    /// this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// assert_eq!(vec.get(0).as_deref(), Some(&1));
    /// assert_eq!(vec.get(1), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<Ref<'_, T>> {
        self.try_get(index).unwrap()
    }

    /// Returns a [`RefMut`](crate::storage::RefMut) to an element at position
    /// `index`, or `None` if the index is out of bounds.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_get_mut`](self::Vec::try_get_mut) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    ///
    /// if let Some(elem) = vec.get_mut(0).as_deref_mut() {
    ///     *elem = 42;
    /// }
    ///
    /// assert_eq!(vec.get(0).as_deref(), Some(&42));
    /// assert_eq!(vec.get(1), None);
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<RefMut<'_, T, S>> {
        self.try_get_mut(index).unwrap()
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_push`](self::Vec::try_push)
    /// if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.get(1).as_deref(), Some(&2));
    /// ```
    pub fn push(&mut self, value: T) {
        self.try_push(value).unwrap()
    }

    /// Removes the last element from the vector and returns it, or `None` if it
    /// is empty.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_pop`](self::Vec::try_pop) if
    /// this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.pop(), Some(2));
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.try_pop().unwrap()
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or when an I/O error occurs. Use
    /// [`try_insert`](self::Vec::try_insert) if panicking on I/O error is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.insert(0, 2);
    /// assert_eq!(vec.get(0).as_deref(), Some(&2));
    /// ```
    pub fn insert(&mut self, index: usize, value: T) {
        self.try_insert(index, value).unwrap()
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or when an I/O error occurs. Use
    /// [`try_remove`](self::Vec::try_remove) if panicking on I/O error is
    /// unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.remove(0), 1);
    /// assert_eq!(vec.get(0).as_deref(), Some(&2));
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        self.try_remove(index).unwrap()
    }

    /// Returns an iterator over elements of the vector.
    ///
    /// # Panics
    ///
    /// `Iter::next` panics when an I/O error occurs. Use
    /// [`try_iter`](self::Vec::try_iter) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let mut iterator = vec.iter();
    /// assert_eq!(iterator.next().as_deref(), Some(&1));
    /// assert_eq!(iterator.next().as_deref(), Some(&2));
    /// assert_eq!(iterator.next().as_deref(), Some(&3));
    /// assert!(iterator.next().is_none());
    /// ```
    pub fn iter(&self) -> Iter<'_, T, S> {
        Iter {
            inner: self.try_iter(),
        }
    }

    /// Constructs a new, empty `Vec<T, S>`, where `S` is type of the underlying
    /// storage.
    ///
    /// The type of the underlying storage must be specified explicitly since it
    /// can't be inferred automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// use bonifacio::SizedStorage;
    /// let vec: Vec<u32, SizedStorage<_>> = Vec::try_new().expect("I/O error");
    /// ```
    pub fn try_new() -> io::Result<Self> {
        Self::with_capacity_inner(INITIAL_CAPACITY)
    }

    /// Returns a [`Ref`](crate::storage::Ref) to an element at position
    /// `index`, or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// assert_eq!(vec.try_get(0).expect("I/O error").as_deref(), Some(&1));
    /// assert_eq!(vec.try_get(1).expect("I/O error"), None);
    /// ```
    pub fn try_get(&self, index: usize) -> io::Result<Option<Ref<'_, T>>> {
        if index >= self.storage.len() {
            Ok(None)
        } else {
            self.storage.get_ref(index).map(Some)
        }
    }

    /// Returns a [`RefMut`](crate::storage::RefMut) to an element at position
    /// `index`, or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    ///
    /// if let Some(elem) = vec.try_get_mut(0).expect("I/O error").as_deref_mut() {
    ///     *elem = 42;
    /// }
    ///
    /// assert_eq!(vec.get(0).as_deref(), Some(&42));
    /// assert_eq!(vec.get(1), None);
    /// ```
    pub fn try_get_mut(&mut self, index: usize) -> io::Result<Option<RefMut<'_, T, S>>> {
        if index >= self.storage.len() {
            Ok(None)
        } else {
            self.storage.get_mut(index).map(Some)
        }
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.try_push(1).expect("I/O error");
    /// vec.try_push(2).expect("I/O error");
    /// assert_eq!(vec.get(1).as_deref(), Some(&2));
    /// ```
    pub fn try_push(&mut self, value: T) -> io::Result<()> {
        self.storage.set(self.storage.len(), &value)
    }

    /// Removes the last element from the vector and returns it, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.try_pop().expect("I/O error"), Some(2));
    /// ```
    pub fn try_pop(&mut self) -> io::Result<Option<T>> {
        if self.len() == 0 {
            Ok(None)
        } else {
            self.storage.remove(self.len() - 1).map(Some)
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.try_insert(0, 2).expect("I/O error");
    /// assert_eq!(vec.get(0).as_deref(), Some(&2));
    /// ```
    pub fn try_insert(&mut self, index: usize, value: T) -> io::Result<()> {
        self.storage.insert(index, &value)
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.try_remove(0).expect("I/O error"), 1);
    /// assert_eq!(vec.get(0).as_deref(), Some(&2));
    /// ```
    pub fn try_remove(&mut self, index: usize) -> io::Result<T> {
        self.storage.remove(index)
    }

    /// Returns a checked variant of iterator over elements of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let mut iterator = vec.try_iter();
    /// assert_eq!(iterator.next().map(|r| r.expect("I/O error")).as_deref(), Some(&1));
    /// assert_eq!(iterator.next().map(|r| r.expect("I/O error")).as_deref(), Some(&2));
    /// assert_eq!(iterator.next().map(|r| r.expect("I/O error")).as_deref(), Some(&3));
    /// assert!(iterator.next().is_none());
    /// ```
    pub fn try_iter(&self) -> TryIter<'_, T, S> {
        TryIter {
            inner: self,
            current: 0,
        }
    }
}

impl<T, S> Vec<T, S>
where
    T: ValueBorrow,
    S: BorrowStorage<T>,
{
    /// Returns a [borrowed](crate::value::Borrowed) value of en element at
    /// position `index`, or `None` if the index is out of bounds.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_borrow`](self::Vec::try_borrow) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_unsized();
    /// vec.push("foo".to_string());
    /// assert_eq!(vec.borrow(0).as_deref(), Some("foo"));
    /// ```
    pub fn borrow(&self, index: usize) -> Option<Borrowed<'_, T>> {
        self.try_borrow(index).unwrap()
    }

    /// Returns a [borrowed](crate::value::Borrowed) value of en element at
    /// position `index`, or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_unsized();
    /// vec.push("foo".to_string());
    /// assert_eq!(vec.try_borrow(0).expect("I/O error").as_deref(), Some("foo"));
    /// ```
    pub fn try_borrow(&self, index: usize) -> io::Result<Option<Borrowed<'_, T>>> {
        if index >= self.storage.len() {
            Ok(None)
        } else {
            self.storage.borrow(index).map(Some)
        }
    }
}

impl<T> Vec<T, UnsizedStorage<T>>
where
    T: Value,
{
    /// Constructs a new, empty `Vec<T, UnsizedStorage<T>>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_unsized`](self::Vec::try_new_unsized) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_unsized();
    /// vec.push("foo".to_string());
    /// ```
    pub fn new_unsized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `Vec<T, UnsizedStorage<T>>` with a particular
    /// capacity. The capacity is specified **in number of bytes**, since the
    /// size of elements is unknown.
    ///
    /// The capacity is actually rounded to closest higher value that is
    /// divisible by [`harrow::granularity()`](harrow::granularity). The vector
    /// will be able to hold exactly this number of bytes of serialized elements
    /// without resizing the underlying file.
    ///
    /// Zero capacity is not supported. The lowest possible non-zero capacity
    /// will be used instead.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_with_capacity_unsized`](self::Vec::try_with_capacity_unsized) if
    /// this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec: Vec<String, _> = Vec::with_capacity_unsized(harrow::granularity() + 1);
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.byte_capacity(), 2 * harrow::granularity());
    /// ```
    pub fn with_capacity_unsized(capacity: usize) -> Self {
        Self::try_with_capacity_unsized(capacity).unwrap()
    }

    /// Constructs a new, empty `Vec<T, UnsizedStorage<T>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::try_new_unsized().expect("I/O error");
    /// vec.push("foo".to_string());
    /// ```
    pub fn try_new_unsized() -> io::Result<Self> {
        Self::try_new()
    }

    /// Constructs a new, empty `Vec<T, UnsizedStorage<T>>` with a particular
    /// capacity. The capacity is specified **in number of bytes**, since the
    /// size of elements is unknown.
    ///
    /// The capacity is actually rounded to closest higher value that is
    /// divisible by [`harrow::granularity()`](harrow::granularity). The vector
    /// will be able to hold exactly this number of bytes of serialized elements
    /// without resizing the underlying file.
    ///
    /// Zero capacity is not supported. The lowest possible non-zero capacity
    /// will be used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec: Vec<String, _> = Vec::try_with_capacity_unsized(harrow::granularity() + 1).expect("I/O error");
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.byte_capacity(), 2 * harrow::granularity());
    /// ```
    pub fn try_with_capacity_unsized(capacity: usize) -> io::Result<Self> {
        Self::with_capacity_inner(capacity)
    }
}

impl<T> Vec<T, SizedStorage<T>>
where
    T: SizedValue,
{
    /// Constructs a new, empty `Vec<T, SizedStorage<T>>`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_new_sized`](self::Vec::try_new_sized) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::new_sized();
    /// vec.push(1);
    /// ```
    pub fn new_sized() -> Self {
        Self::new()
    }

    /// Constructs a new, empty `Vec<T, SizedStorage<T>>` with a particular
    /// capacity. The capacity is specified in **number of elements**, since the
    /// size of elements is known.
    ///
    /// The capacity is actually rounded such that the capacity in number of
    /// bytes is the closest higher value that is divisible by
    /// [`harrow::granularity()`](harrow::granularity). The vector will be able
    /// to hold exactly this number of bytes of serialized elements without
    /// resizing the underlying file.
    ///
    /// Zero capacity is not supported. The lowest possible non-zero capacity
    /// will be used instead.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_with_capacity_sized`](self::Vec::try_with_capacity_sized) if this
    /// is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec: Vec<u32, _> =
    ///     Vec::with_capacity_sized(harrow::granularity() / std::mem::size_of::<u32>() + 1);
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.byte_capacity(), 2 * harrow::granularity());
    /// assert_eq!(vec.capacity(), 2 * harrow::granularity() / std::mem::size_of::<u32>());
    /// ```
    pub fn with_capacity_sized(capacity: usize) -> Self {
        Self::try_with_capacity_sized(capacity).unwrap()
    }

    /// Returns the number of elements that the vector can hold without resizing
    /// the underlying file.
    ///
    /// This value depends on the granularity of the underlying storage, based
    /// on [`harrow::granularity`](harrow::granularity).
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec: Vec<u32, _> = Vec::new();
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.byte_capacity(), harrow::granularity());
    /// assert_eq!(vec.capacity(), harrow::granularity() / std::mem::size_of::<u32>());
    /// ```
    pub fn capacity(&self) -> usize {
        self.byte_capacity() / T::size()
    }

    /// Constructs a new, empty `Vec<T, SizedStorage<T>>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec = Vec::try_new_sized().expect("I/O error");
    /// vec.push(1);
    /// ```
    pub fn try_new_sized() -> io::Result<Self> {
        Self::try_new()
    }

    /// Constructs a new, empty `Vec<T, SizedStorage<T>>` with a particular
    /// capacity. The capacity is specified in **number of elements**, since the
    /// size of elements is known.
    ///
    /// The capacity is actually rounded such that the capacity in number of
    /// bytes is the closest higher value that is divisible by
    /// [`harrow::granularity()`](harrow::granularity). The vector will be able
    /// to hold exactly this number of bytes of serialized elements without
    /// resizing the underlying file.
    ///
    /// Zero capacity is not supported. The lowest possible non-zero capacity
    /// will be used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::Vec;
    /// let mut vec: Vec<u32, _> =
    ///     Vec::try_with_capacity_sized(harrow::granularity() / std::mem::size_of::<u32>() + 1)
    ///     .expect("I/O error");
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.byte_capacity(), 2 * harrow::granularity());
    /// assert_eq!(vec.capacity(), 2 * harrow::granularity() / std::mem::size_of::<u32>());
    /// ```
    pub fn try_with_capacity_sized(capacity: usize) -> io::Result<Self> {
        Self::with_capacity_inner(capacity * T::size())
    }
}

/// An immutable iterator over the contents of the vector, panicking on I/O
/// errors.
///
/// This struct is created by the [`iter`](self::Vec::iter) method on
/// [`Vec`](self::Vec).
///
/// # Panics
///
/// `Iter::next` panics when an I/O error occurs. Use
/// [`try_iter`](self::Vec::try_iter) if this is unacceptable.
///
/// # Examples
///
/// ```
/// use bonifacio::Vec;
///
/// let mut vec = Vec::new_sized();
/// vec.push(1);
/// vec.push(2);
/// vec.push(3);
///
/// for elem in vec.iter() {
///     println!("{}", elem);
/// }
/// ```
pub struct Iter<'a, T, S> {
    inner: TryIter<'a, T, S>,
}

impl<'a, T, S> Iterator for Iter<'a, T, S>
where
    S: Storage<T>,
{
    type Item = Ref<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Result::unwrap)
    }
}

/// An immutable iterator over the contents of the vector, propagating I/O
/// errors.
///
/// This struct is created by the [`try_iter`](self::Vec::try_iter) method on
/// [`Vec`](self::Vec).
///
/// # Examples
///
/// ```
/// use bonifacio::Vec;
///
/// let mut vec = Vec::new_sized();
/// vec.push(1);
/// vec.push(2);
/// vec.push(3);
///
/// for elem in vec.try_iter() {
///     println!("{}", elem.expect("I/O error"));
/// }
/// ```
pub struct TryIter<'a, T, S> {
    inner: &'a Vec<T, S>,
    current: usize,
}

impl<'a, T, S> Iterator for TryIter<'a, T, S>
where
    S: Storage<T>,
{
    type Item = io::Result<Ref<'a, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == self.inner.len() {
            None
        } else {
            let current = self.current;
            self.current += 1;
            Some(self.inner.try_get(current).map(Option::unwrap))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::storage::UnsizedStorage;
    use proptest::prelude::*;

    #[test]
    fn basic() {
        let mut vec = super::Vec::<String, UnsizedStorage<String>>::new();

        vec.push(String::from("foo"));
        vec.push(String::from("bar"));

        assert_eq!(vec.get(0).as_deref(), Some(&String::from("foo")));

        assert_eq!(vec.remove(0), String::from("foo"));
        assert_eq!(vec.get(0).as_deref(), Some(&String::from("bar")));

        vec.insert(0, String::from("baz"));
        assert_eq!(vec.get(0).as_deref(), Some(&String::from("baz")));

        assert_eq!(vec.pop(), Some(String::from("bar")));
    }

    #[derive(Debug, Clone)]
    enum Action {
        Push(String),
        Get(usize),
        Insert((usize, String)),
        Pop,
    }

    fn test_random(actions: impl Iterator<Item = Action>) {
        let mut our_vec = super::Vec::<String, UnsizedStorage<String>>::new();
        let mut std_vec = Vec::<String>::new();

        for action in actions {
            match action {
                Action::Push(value) => {
                    assert_eq!(our_vec.push(value.clone()), std_vec.push(value));
                }
                Action::Get(index) => {
                    assert_eq!(our_vec.get(index).as_deref(), std_vec.get(index));
                }
                Action::Insert((index, value)) => {
                    // Insert functions panic when index > len.
                    if index <= std_vec.len() {
                        assert_eq!(
                            our_vec.insert(index, value.clone()),
                            std_vec.insert(index, value)
                        );
                    }
                }
                Action::Pop => {
                    assert_eq!(our_vec.pop(), std_vec.pop());
                }
            }
        }

        assert_eq!(our_vec.len(), std_vec.len());

        for (lhs, rhs) in our_vec.iter().zip(std_vec.iter()) {
            assert_eq!(lhs.as_ref(), rhs);
        }
    }

    fn limit_index(index: usize) -> usize {
        // The whole domain of usize is unnecessarily large, we need to focus on
        // the subset whose values have reasonable probability to be valid in
        // the sequence of the actions. But we of course need values that can
        // exceed the length of a Vec.
        index % 50
    }

    fn action_strategy() -> impl Strategy<Value = Action> {
        prop_oneof![
            any::<String>().prop_map(Action::Push),
            any::<usize>().prop_map(limit_index).prop_map(Action::Get),
            any::<(usize, String)>()
                .prop_map(|(index, value)| (limit_index(index), value))
                .prop_map(Action::Insert),
            Just(Action::Pop),
        ]
    }

    proptest! {
        #[test]
        fn random(actions in proptest::collection::vec(action_strategy(), 1..500)) {
            test_random(actions.into_iter());
        }
    }
}
