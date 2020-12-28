use std::env;
use std::fmt;
use std::io;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::path::PathBuf;

use harrow::FileMut;
use uuid::Uuid;

use crate::value::{Borrowed, SizedValue, Value, ValueBorrow};

// The actually size of allocated file will be extended to the size of virtual
// memory alignment requirements on the current operating system. This is done
// automatically by harrow::FileMut.
pub const INITIAL_CAPACITY: usize = 1;

/// A contiguous-like memory holding values of generic type `T`, although no
/// restrictions are put on the internal implementation.
///
/// The storage is composed of the underlying file, length and capacity (similar
/// as `Vec` does). Capacity should be automatically extended when new values do
/// not fit. It is not specified in what units the capacity is, be it bytes,
/// number of items, or whatever.
pub trait Storage<T>: Sized {
    /// Initializes the storage with given capacity and zero length.
    fn new(capacity: usize) -> io::Result<Self>;

    /// Returns properly initialized value of type `T` stored at given index.
    ///
    /// # Errors
    ///
    /// A trait implementation should return any I/O error encountered.
    ///
    /// # Panics
    ///
    /// A trait implementation is free to panic when passed index is out of
    /// bounds of the current storage.
    fn get(&self, index: usize) -> io::Result<T>;

    /// Replaces or appends to the end given value at specified index.
    ///
    /// If `index` < `len`, the operation is replacement. If `index` == `len`,
    /// the operation is appending and the storage length must be incremented by
    /// one.
    ///
    /// # Errors
    ///
    /// A trait implementation should return any I/O error encountered.
    ///
    /// # Panics
    ///
    /// A trait implementation is free to panic when passed index is out of
    /// bounds of the current storage.
    fn set(&mut self, index: usize, value: &T) -> io::Result<()>;

    /// Inserts given value at specified index, moving all subsequent values to
    /// the right.
    ///
    /// The storage length must be incremented by one.
    ///
    /// # Errors
    ///
    /// A trait implementation should return any I/O error encountered.
    ///
    /// # Panics
    ///
    /// A trait implementation is free to panic when passed index is out of
    /// bounds of the current storage.
    fn insert(&mut self, index: usize, value: &T) -> io::Result<()>;

    /// Removes a value at specified index, moving all subsequent values to the
    /// left.
    ///
    /// The storage length must be decremented by one.
    ///
    /// # Errors
    ///
    /// A trait implementation should return any I/O error encountered.
    ///
    /// # Panics
    ///
    /// A trait implementation is free to panic when passed index is out of
    /// bounds of the current storage.
    fn remove(&mut self, index: usize) -> io::Result<T>;

    /// Returns the number of items in the storage.
    fn len(&self) -> usize;

    /// Returns the total number of bytes occupied by items in the storage.
    fn byte_len(&self) -> usize;

    /// Returns the number of bytes that the storage can hold without resizing
    /// the underlying file.
    fn byte_capacity(&self) -> usize;

    /// Reserves the capacity without properly initializing values of type `T`
    /// in free space. The capacity is specified in number of items.
    ///
    /// # Safety
    ///
    /// The caller must ensure that every value must be properly initialized
    /// with [`set`](self::Storage::set) before it is accessed using
    /// [`get`](self::Storage::get), [`get_ref`](self::Storage::get_ref), or
    /// [`get_mut`](self::Storage::get_mut).
    ///
    /// # Errors
    ///
    /// A trait implementation should return any I/O error encountered.
    unsafe fn reserve(&mut self, capacity: usize) -> io::Result<()>;

    /// Returns properly initialized value of type `T` stored at given index,
    /// wrapped in [`Ref`](self::Ref).
    ///
    /// For more details, see [`get`](self::Storage::get).
    fn get_ref(&self, index: usize) -> io::Result<Ref<'_, T>> {
        let value = match self.get(index) {
            Ok(value) => value,
            Err(err) => return Err(err),
        };

        Ok(Ref::from_raw(value))
    }

    /// Returns properly initialized value of type `T` stored at given index,
    /// wrapped in [`RefMut`](self::RefMut).
    ///
    /// For more details, see [`get`](self::Storage::get).
    fn get_mut(&mut self, index: usize) -> io::Result<RefMut<'_, T, Self>> {
        let value = match self.get(index) {
            Ok(value) => value,
            Err(err) => return Err(err),
        };

        Ok(RefMut::from_raw(value, self, index))
    }
}

/// Extends the [`Storage`](self::Storage) trait to support types implementing
/// [`ValueBorrow`](crate::value::ValueBorrow) trait.
pub trait BorrowStorage<T: ValueBorrow>: Storage<T> {
    /// Returns a reference to properly initialized value of type `T` stored at
    /// given index.
    ///
    /// # Errors
    ///
    /// A trait implementation should return any I/O error encountered.
    ///
    /// # Panics
    ///
    /// A trait implementation is free to panic when passed index is out of
    /// bounds of the current storage.
    fn borrow(&self, index: usize) -> io::Result<Borrowed<'_, T>>;
}

/// A [`Storage`](self::Storage) implementation for types implementing
/// [`Value`](crate::value::Value) trait.
pub struct UnsizedStorage<T> {
    data: FileMut,
    // TODO: Store this information in FileMut as well and use usize for
    // pointers' offset and length.
    off: Vec<ptr::Ptr>,
    buf: Vec<u8>,
    ty: PhantomData<T>,
    tail: usize,
    garbage: usize,
    byte_len: usize,
}

impl<T: Value> UnsizedStorage<T> {
    fn get_at(&self, ptr: &ptr::Ptr) -> io::Result<T> {
        Ok(T::from_bytes(
            self.data.view_range(ptr.offset()..ptr.end())?.as_slice(),
        ))
    }

    fn defrag_maybe(&mut self) -> io::Result<()> {
        const DEFRAG_THRESHOLD: f32 = 0.25;

        // NOTE: self.mem.len() returns the size of allocated memory by
        // FileMut, not the size of the valid data inside the storage. But to
        // use it makes sense as well as if the latter was true.
        let ratio = (self.garbage as f32) / (self.data.len() as f32);

        if ratio > DEFRAG_THRESHOLD {
            // NOTE: In-place defragmentation is possible, but would be more
            // complicated. Let's keep it simple for now.
            let mut new_mem = FileMut::new(temp_path(), self.data.len())?;
            let mut new_off = Vec::new();

            self.tail = 0;
            for ptr in self.off.iter() {
                new_mem.write_at(
                    self.data.view_range(ptr.offset()..ptr.end())?.as_slice(),
                    self.tail,
                )?;
                new_off.push(ptr::Ptr::new(self.tail, ptr.len())?);
                self.tail += ptr.len();
            }

            self.data = new_mem;
            self.off = new_off;
            self.garbage = 0;
            self.byte_len = self.tail;
        }

        Ok(())
    }

    #[cfg(test)]
    pub fn tail(&self) -> usize {
        self.tail
    }
}

impl<T: Value> Storage<T> for UnsizedStorage<T> {
    fn new(capacity: usize) -> io::Result<Self> {
        let mem = FileMut::new(temp_path(), capacity)?;

        Ok(Self {
            data: mem,
            off: Vec::new(),
            buf: Vec::new(),
            ty: PhantomData,
            tail: 0,
            garbage: 0,
            byte_len: 0,
        })
    }

    fn get(&self, index: usize) -> io::Result<T> {
        let ptr = match self.off.get(index) {
            Some(ptr) => ptr,
            None => panic!("index out of bounds"),
        };

        self.get_at(ptr)
    }

    fn set(&mut self, index: usize, value: &T) -> io::Result<()> {
        self.buf.clear();
        value.to_bytes(&mut self.buf);
        let len = self.buf.len();

        let ptr = if index == self.off.len() {
            self.byte_len += len;
            ptr::Ptr::new(self.tail, len)?
        } else if index < self.off.len() {
            let ptr = self.off[index];
            self.byte_len = self.byte_len + len - ptr.len();

            if ptr.len() < len {
                self.garbage += ptr.len();
                let offset = self.tail;
                ptr::Ptr::new(offset, len)?
            } else {
                self.garbage += ptr.len() - len;
                ptr::Ptr::new(ptr.offset(), len)?
            }
        } else {
            panic!("index out of bounds");
        };

        if ptr.end() > self.data.len() {
            let new_len = std::cmp::max(2 * self.data.len(), ptr.end());
            self.data.resize(new_len)?;
        }

        self.data.write_at(self.buf.as_slice(), ptr.offset())?;

        if index == self.off.len() {
            self.off.push(ptr);
        } else {
            self.off[index] = ptr;
        }

        self.tail = std::cmp::max(self.tail, ptr.end());

        self.defrag_maybe()?;

        Ok(())
    }

    fn insert(&mut self, index: usize, value: &T) -> io::Result<()> {
        if index > self.off.len() {
            panic!("index out of bounds");
        }

        let ptr = ptr::Ptr::new(self.tail, 0)?;
        self.off.insert(index, ptr);

        self.set(index, value)
    }

    fn remove(&mut self, index: usize) -> io::Result<T> {
        if index >= self.off.len() {
            panic!("index out of bounds");
        }

        // NOTE: If index < off.len() - 1, then this will create a hole in the
        // file. This is safe, although it creates garbage data in the file.
        // However, since we implement defragmentation, this is not a serious
        // issue.
        let ptr = self.off.remove(index);

        if ptr.end() == self.tail {
            self.tail -= ptr.len();
        } else {
            self.garbage += ptr.len();
        }

        self.byte_len -= ptr.len();
        self.get_at(&ptr)
    }

    fn len(&self) -> usize {
        self.off.len()
    }

    fn byte_len(&self) -> usize {
        self.byte_len
    }

    fn byte_capacity(&self) -> usize {
        self.data.len()
    }

    unsafe fn reserve(&mut self, capacity: usize) -> io::Result<()> {
        for _ in 0..capacity {
            self.off.push(ptr::Ptr::new(0, 0).unwrap());
        }

        Ok(())
    }
}

impl<T: ValueBorrow> BorrowStorage<T> for UnsizedStorage<T> {
    fn borrow(&self, index: usize) -> io::Result<Borrowed<'_, T>> {
        let ptr = match self.off.get(index) {
            Some(ptr) => ptr,
            None => panic!("index out of bounds"),
        };

        self.data
            .view_range(ptr.offset()..ptr.end())
            .map(Borrowed::new)
    }
}

/// A [`Storage`](self::Storage) implementation for types implementing
/// [`SizedValue`](crate::value::SizedValue) trait.
pub struct SizedStorage<T> {
    data: FileMut,
    buf: Vec<u8>,
    ty: PhantomData<T>,
    len: usize,
}

impl<T: SizedValue> SizedStorage<T> {
    fn range(&self, index: usize) -> (usize, usize) {
        let start = index * T::size();
        let end = start + T::size();
        (start, end)
    }

    fn check_get_bounds(&self, index: usize) {
        if index >= self.len {
            panic!("index out of bounds");
        }
    }

    fn check_set_bounds(&self, index: usize) {
        if index > self.len {
            panic!("index out of bounds");
        }
    }

    fn get_at(&self, index: usize) -> io::Result<T> {
        let (offset, end) = self.range(index);
        Ok(T::from_bytes(self.data.view_range(offset..end)?.as_slice()))
    }
}

impl<T: SizedValue> Storage<T> for SizedStorage<T> {
    fn new(capacity: usize) -> io::Result<Self> {
        let mem = FileMut::new(temp_path(), capacity)?;

        Ok(Self {
            data: mem,
            buf: Vec::new(),
            ty: PhantomData,
            len: 0,
        })
    }

    fn get(&self, index: usize) -> io::Result<T> {
        self.check_get_bounds(index);
        self.get_at(index)
    }

    fn set(&mut self, index: usize, value: &T) -> io::Result<()> {
        self.check_set_bounds(index);

        self.buf.clear();
        value.to_bytes(&mut self.buf);
        assert!(self.buf.len() == T::size());

        let (offset, end) = self.range(index);
        if end > self.data.len() {
            self.data.resize(2 * self.data.len())?;
        }

        self.data.write_at(self.buf.as_slice(), offset)?;

        if index == self.len {
            self.len += 1;
        }

        Ok(())
    }

    fn insert(&mut self, index: usize, value: &T) -> io::Result<()> {
        self.check_set_bounds(index);

        let (offset, end) = self.range(index);
        let tail = self.byte_len() - offset;

        if end + tail > self.data.len() {
            self.data.resize(2 * self.data.len())?;
        }

        // Create a hole.
        self.data.copy_within(offset, end, tail)?;

        // If index == self.len, the length is incremented in SizedStorage::set.
        if index < self.len {
            self.len += 1;
        }

        self.set(index, value)
    }

    fn remove(&mut self, index: usize) -> io::Result<T> {
        self.check_get_bounds(index);

        let value = self.get_at(index)?;

        let (dst, src) = self.range(index);
        self.data.copy_within(src, dst, self.len * T::size() - dst)?;

        self.len -= 1;

        Ok(value)
    }

    fn len(&self) -> usize {
        self.len
    }

    fn byte_len(&self) -> usize {
        self.len * T::size()
    }

    fn byte_capacity(&self) -> usize {
        self.data.len()
    }

    unsafe fn reserve(&mut self, capacity: usize) -> io::Result<()> {
        let n_bytes = capacity * T::size();

        if n_bytes > self.data.len() {
            self.data.resize(n_bytes)?;
        }

        self.len = capacity;

        Ok(())
    }
}

impl<T: ValueBorrow + SizedValue> BorrowStorage<T> for SizedStorage<T> {
    fn borrow(&self, index: usize) -> io::Result<Borrowed<'_, T>> {
        self.check_get_bounds(index);
        let (offset, end) = self.range(index);
        self.data.view_range(offset..end).map(Borrowed::new)
    }
}

/// A shared-reference wrapper around initialized value.
///
/// See [crate](crate) documentation for more details.
pub struct Ref<'a, T> {
    value: T,
    lifetime: PhantomData<&'a ()>,
}

impl<'a, T> Ref<'a, T> {
    pub(crate) fn from_raw(value: T) -> Self {
        Self {
            value,
            lifetime: PhantomData,
        }
    }
}

impl<'a, T> Deref for Ref<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'a, T> AsRef<T> for Ref<'a, T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<'a, T> PartialEq for Ref<'a, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<'a, T> PartialEq<T> for Ref<'a, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == other
    }
}

impl<'a, T> fmt::Debug for Ref<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ref({:?})", self.value)
    }
}

impl<'a, T> fmt::Display for Ref<'a, T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

/// An exclusive-reference wrapper around initialized value.
///
/// See [crate](crate) documentation for more details.
pub struct RefMut<'a, T, S>
where
    S: Storage<T>,
{
    storage: &'a mut S,
    index: usize,
    value: T,
}

impl<'a, T, S> RefMut<'a, T, S>
where
    S: Storage<T>,
{
    pub(crate) fn from_raw(value: T, storage: &'a mut S, index: usize) -> Self {
        Self {
            storage,
            index,
            value,
        }
    }
}

impl<'a, T, S> Deref for RefMut<'a, T, S>
where
    S: Storage<T>,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'a, T, S> DerefMut for RefMut<'a, T, S>
where
    S: Storage<T>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<'a, T, S> Drop for RefMut<'a, T, S>
where
    S: Storage<T>,
{
    fn drop(&mut self) {
        self.storage
            .set(self.index, &self.value)
            .expect("persisting mutated value failed");
    }
}

impl<'a, T, S> AsRef<T> for RefMut<'a, T, S>
where
    S: Storage<T>,
{
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<'a, T, S> AsMut<T> for RefMut<'a, T, S>
where
    S: Storage<T>,
{
    fn as_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<'a, T, S> PartialEq for RefMut<'a, T, S>
where
    T: PartialEq,
    S: Storage<T>,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<'a, T, S> PartialEq<T> for RefMut<'a, T, S>
where
    T: PartialEq,
    S: Storage<T>,
{
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == other
    }
}

impl<'a, T, S> fmt::Debug for RefMut<'a, T, S>
where
    T: fmt::Debug,
    S: Storage<T>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RefMut({:?})", self.value)
    }
}

impl<'a, T, S> fmt::Display for RefMut<'a, T, S>
where
    T: fmt::Display,
    S: Storage<T>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

pub fn temp_path() -> PathBuf {
    let name = format!("{}", Uuid::new_v4());
    let mut path = env::temp_dir().join(name);
    path.set_extension("bnfcio");
    path
}

mod ptr {
    use std::fmt;
    use std::io;

    const BITS_LEN: u64 = 20;
    const BITS_OFFSET: u64 = 64 - BITS_LEN;
    const MASK_LEN: u64 = 0xfffff;

    // Leftmost 44 bits store the offset and rightmost 20 bits store the length.
    // This imposes these limits: maximum total size of the storage is
    // 1.7592186e+13 bytes ~ 17 TB (plus the size of the last item) and maximum
    // size of a single value is 1_048_576 bytes ~ 1 MB.
    #[derive(Clone, Copy)]
    pub struct Ptr(u64);

    impl Ptr {
        pub fn new(offset: usize, len: usize) -> Result<Self, PtrError> {
            if offset > max(BITS_OFFSET) as usize {
                return Err(PtrError::TotalSize(offset));
            }

            if len > max(BITS_LEN) {
                return Err(PtrError::ItemSize(len));
            }

            let bits = (offset as u64) << BITS_LEN | (len as u64);
            Ok(Ptr(bits))
        }

        pub fn offset(&self) -> usize {
            (self.0 >> BITS_LEN) as usize
        }

        pub fn len(&self) -> usize {
            (self.0 & MASK_LEN) as usize
        }

        pub fn end(&self) -> usize {
            self.offset() + self.len()
        }
    }

    const fn max(n_bits: u64) -> usize {
        (1u64 << n_bits) as usize - 1
    }

    impl fmt::Debug for Ptr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Ptr")
                .field("offset", &self.offset())
                .field("len", &self.len())
                .field("end", &self.end())
                .finish()
        }
    }

    #[derive(Debug)]
    pub enum PtrError {
        TotalSize(usize),
        ItemSize(usize),
    }

    impl fmt::Display for PtrError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                PtrError::TotalSize(offset) => {
                    write!(f, "maximum total size of storage exceeded: requested offset is {} while the maximum is {}", offset, max(BITS_OFFSET))
                }
                PtrError::ItemSize(len) => {
                    write!(f, "maximum size of an item exceeded: requested len is {} while the maximum is {}", len, max(BITS_LEN))
                }
            }
        }
    }

    impl std::error::Error for PtrError {}

    impl From<PtrError> for io::Error {
        fn from(err: PtrError) -> Self {
            io::Error::new(io::ErrorKind::Other, err)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn should_panic<F: FnOnce() -> R + std::panic::UnwindSafe, R: std::fmt::Debug>(
        body: F,
        message: &str,
    ) {
        let result = std::panic::catch_unwind(body).map_err(|m| m.downcast::<&str>().unwrap());

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), Box::new(message));
    }

    mod unsized_storage {
        use super::*;

        #[test]
        fn basic_sized() {
            let mut storage = UnsizedStorage::<u32>::new(1).unwrap();
            storage.set(0, &1).unwrap();
            storage.set(1, &2).unwrap();

            assert_eq!(storage.get(0).unwrap(), 1);
            assert_eq!(storage.get(1).unwrap(), 2);
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);

            storage.set(0, &3).unwrap();
            assert_eq!(storage.get(0).unwrap(), 3);
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);

            storage.insert(0, &4).unwrap();
            assert_eq!(storage.get(0).unwrap(), 4);
            assert_eq!(storage.get(1).unwrap(), 3);
            assert_eq!(storage.get(2).unwrap(), 2);
            assert_eq!(storage.len(), 3);
            assert_eq!(storage.byte_len(), 12);

            storage.remove(1).unwrap();
            assert_eq!(storage.get(0).unwrap(), 4);
            assert_eq!(storage.get(1).unwrap(), 2);
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);
        }

        #[test]
        fn basic_unsized_same_size() {
            let mut storage = UnsizedStorage::<String>::new(1).unwrap();
            storage.set(0, &String::from("1")).unwrap();
            storage.set(1, &String::from("2")).unwrap();

            assert_eq!(storage.get(0).unwrap(), String::from("1"));
            assert_eq!(storage.get(1).unwrap(), String::from("2"));
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 2);

            storage.set(0, &String::from("3")).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("3"));
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 2);

            storage.insert(0, &String::from("4")).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("4"));
            assert_eq!(storage.get(1).unwrap(), String::from("3"));
            assert_eq!(storage.get(2).unwrap(), String::from("2"));
            assert_eq!(storage.len(), 3);
            assert_eq!(storage.byte_len(), 3);

            storage.remove(1).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("4"));
            assert_eq!(storage.get(1).unwrap(), String::from("2"));
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 2);
        }

        #[test]
        fn unsized_various_sizes() {
            let mut storage = UnsizedStorage::<String>::new(1).unwrap();

            storage.set(0, &String::from("foo")).unwrap();
            storage.set(1, &String::from("hello")).unwrap();

            assert_eq!(storage.get(0).unwrap(), String::from("foo"));
            assert_eq!(storage.get(1).unwrap(), String::from("hello"));
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);

            storage.set(0, &String::from("world")).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("world"));
            assert_eq!(storage.get(1).unwrap(), String::from("hello"));
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 10);

            storage.insert(0, &String::from("bonifacio")).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("bonifacio"));
            assert_eq!(storage.len(), 3);
            assert_eq!(storage.byte_len(), 19);

            storage.set(0, &String::from("a")).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("a"));
            assert_eq!(storage.len(), 3);
            assert_eq!(storage.byte_len(), 11);

            storage.remove(1).unwrap();
            assert_eq!(storage.get(0).unwrap(), String::from("a"));
            assert_eq!(storage.get(1).unwrap(), String::from("hello"));
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 6);
        }

        #[test]
        fn ref_storage() {
            let mut storage = UnsizedStorage::<String>::new(1).unwrap();

            storage.set(0, &String::from("foo")).unwrap();
            assert_eq!(&*storage.borrow(0).unwrap(), "foo");
        }

        #[test]
        fn defragmentation() {
            let mut storage = UnsizedStorage::<String>::new(1).unwrap();

            let mut happened = false;
            let mut last_tail = 0;

            for i in 0..1000 {
                let value = (0..i).map(|_| ' ').collect::<String>();
                storage.set(0, &value).unwrap();

                if storage.tail() < last_tail {
                    happened = true;
                }

                last_tail = storage.tail();
            }

            assert!(happened);
        }

        #[test]
        fn reserve() {
            let mut storage = UnsizedStorage::<String>::new(1).unwrap();

            unsafe {
                storage.reserve(10).unwrap();
            }

            storage.set(9, &String::from("hello")).unwrap();
            storage.set(3, &String::from("world")).unwrap();
            assert_eq!(storage.get(9).unwrap(), String::from("hello"));
            assert_eq!(storage.get(3).unwrap(), String::from("world"));
            assert_eq!(storage.len(), 10);
            assert_eq!(storage.byte_len(), 10);
        }

        #[test]
        fn bounds_checking() {
            should_panic(
                || {
                    let mut storage = UnsizedStorage::<String>::new(1).unwrap();
                    storage.set(1, &String::from("1")).unwrap();
                },
                "index out of bounds",
            );

            should_panic(
                || {
                    let mut storage = UnsizedStorage::<String>::new(1).unwrap();
                    storage.set(0, &String::from("1")).unwrap();
                    storage.get(1).unwrap();
                },
                "index out of bounds",
            );

            should_panic(
                || {
                    let mut storage = UnsizedStorage::<String>::new(1).unwrap();
                    storage.insert(1, &String::from("1")).unwrap();
                },
                "index out of bounds",
            );

            should_panic(
                || {
                    let mut storage = UnsizedStorage::<String>::new(1).unwrap();
                    storage.set(0, &String::from("1")).unwrap();
                    storage.remove(1).unwrap();
                },
                "index out of bounds",
            );
        }
    }

    mod sized_storage {
        use super::*;

        #[test]
        fn basic_sized() {
            let mut storage = SizedStorage::<u32>::new(1).unwrap();
            storage.set(0, &1).unwrap();
            storage.set(1, &2).unwrap();

            assert_eq!(storage.get(0).unwrap(), 1);
            assert_eq!(storage.get(1).unwrap(), 2);
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);

            storage.set(0, &3).unwrap();
            assert_eq!(storage.get(0).unwrap(), 3);
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);

            storage.insert(0, &4).unwrap();
            assert_eq!(storage.get(0).unwrap(), 4);
            assert_eq!(storage.get(1).unwrap(), 3);
            assert_eq!(storage.get(2).unwrap(), 2);
            assert_eq!(storage.len(), 3);
            assert_eq!(storage.byte_len(), 12);

            storage.remove(1).unwrap();
            assert_eq!(storage.get(0).unwrap(), 4);
            assert_eq!(storage.get(1).unwrap(), 2);
            assert_eq!(storage.len(), 2);
            assert_eq!(storage.byte_len(), 8);
        }

        #[test]
        fn reserve() {
            let mut storage = SizedStorage::<u32>::new(1).unwrap();

            unsafe {
                storage.reserve(10).unwrap();
            }

            storage.set(9, &13).unwrap();
            storage.set(3, &42).unwrap();
            assert_eq!(storage.get(9).unwrap(), 13);
            assert_eq!(storage.get(3).unwrap(), 42);
            assert_eq!(storage.len(), 10);
            assert_eq!(storage.byte_len(), 40);
        }

        #[test]
        fn bounds_checking() {
            should_panic(
                || {
                    let mut storage = SizedStorage::<u32>::new(1).unwrap();
                    storage.set(1, &1).unwrap();
                },
                "index out of bounds",
            );

            should_panic(
                || {
                    let mut storage = SizedStorage::<u32>::new(1).unwrap();
                    storage.set(0, &1).unwrap();
                    storage.get(1).unwrap();
                },
                "index out of bounds",
            );

            should_panic(
                || {
                    let mut storage = SizedStorage::<u32>::new(1).unwrap();
                    storage.insert(1, &1).unwrap();
                },
                "index out of bounds",
            );

            should_panic(
                || {
                    let mut storage = SizedStorage::<u32>::new(1).unwrap();
                    storage.set(0, &1).unwrap();
                    storage.remove(1).unwrap();
                },
                "index out of bounds",
            );
        }
    }
}
