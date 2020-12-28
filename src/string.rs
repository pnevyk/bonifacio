//! A `String`-like container that stores the contents in a file instead of
//! memory.
//!
//! Check the module documentation for details on
//!
//! * the concept of `Value` ([Serialization and
//!   Deserialization](crate#serialization-and-deserialization), [Sized vs
//!   Unsized](crate#sized-vs-unsized)), and
//! * differences from the `std::string::String` API ([Ref and
//!   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
//!
//! # Examples
//!
//! See [`String`](self::String) for examples.
use std::convert::TryFrom;
use std::fmt;
use std::io;
use std::ops::Deref;
use std::str::Utf8Error;

use harrow::FileMut;

use crate::storage::{temp_path, INITIAL_CAPACITY};

use unicode::CharScan;

/// A `String`-like container that stores the contents in a file instead of
/// memory.
///
/// Check the module documentation for details on
///
/// * the concept of `Value` ([Serialization and
///   Deserialization](crate#serialization-and-deserialization), [Sized vs
///   Unsized](crate#sized-vs-unsized)), and
/// * differences from the `std::string::String` API ([Ref and
///   RefMut](crate#ref-and-refmut), [I/O Errors](crate#io-errors)).
///
/// # Examples
///
/// ```
/// use bonifacio::String;
/// use std::convert::TryFrom;
///
/// let mut hello = String::try_from("Hello ").expect("I/O error");
/// hello.push_str("world! ");
/// hello.push('♥');
///
/// assert_eq!(hello.len(), 16); // in bytes
/// assert_eq!(hello.chars().count(), 14); // in chars
///
/// // `as_str()` creates a virtual mapping for the entire string,
/// // regardless of its size. You should generally avoid it.
/// assert_eq!(hello.as_str(), "Hello world! ♥");
/// ```
pub struct String {
    data: FileMut,
    len: usize,
    buf: Vec<u8>,
}

impl String {
    /// Creates a new, empty `String`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use [`try_new`](self::String::try_new)
    /// if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let string = String::new();
    /// ```
    pub fn new() -> Self {
        Self::try_new().unwrap()
    }

    /// Creates a new, empty `String` with a particular capacity (in bytes).
    ///
    /// The capacity is actually rounded to closest higher value that is
    /// divisible by [`harrow::granularity()`](harrow::granularity). The string
    /// will be able to hold exactly this number of bytes without resizing the
    /// underlying file.
    ///
    /// Zero capacity is not supported. The lowest possible non-zero capacity
    /// will be used instead.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_with_capacity`](self::String::try_with_capacity) if this is
    /// unacceptable.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let string = String::with_capacity(harrow::granularity() + 1);
    /// assert_eq!(string.len(), 0);
    /// assert_eq!(string.capacity(), 2 * harrow::granularity());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self::try_with_capacity(capacity).unwrap()
    }

    /// Converts a standard vector of bytes to a `String`.
    ///
    /// Not all byte vectors are valid strings: `String` requires that it is
    /// valid UTF-8. `from_utf8` checks to ensure that this property is
    /// satisfied.
    ///
    /// If you are sure tha the byte vector is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an *unsafe*
    /// version of this function, `try_from_utf8_unchecked`, which has the same
    /// behavior, except it propagates an I/O error if one occurs, but skips the
    /// check.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_from_utf8`](self::String::try_from_utf8) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let heart = [226, 153, 165].to_vec();
    ///
    /// // We are sure that the bytes are valid, thus we unwrap.
    /// let heart = String::from_utf8(heart).unwrap();
    /// assert_eq!(heart.as_str(), "♥");
    ///
    /// let invalid = [0, 153, 165].to_vec();
    ///
    /// let invalid = String::from_utf8(invalid);
    /// assert!(invalid.is_err());
    /// ```
    pub fn from_utf8(bytes: Vec<u8>) -> Result<Self, Utf8Error> {
        std::str::from_utf8(&bytes)?;
        let mut string = Self::with_capacity(bytes.len());
        string.data.write_at(&bytes, 0).unwrap();
        string.len += bytes.len();

        Ok(string)
    }

    /// Converts a standard vector of bytes to a `String` without checking that
    /// the string contains valid UTF-8.
    ///
    /// See the safe variant [`try_from_utf8`](self::String::try_from_utf8) for
    /// more details. There also exists another safe variant,
    /// [`from_utf8`](self::String::from_utf8), which panics on I/O errors.
    ///
    /// This method returns the I/O error if one occurs and there is no unsafe
    /// sibling that unwraps the `std::io::Result` internally, as the need of
    /// wrapping the call in an `unsafe` block is already some noise so the
    /// additional call to `unwrap` is not considered an inconvenient.
    ///
    /// # Safety
    ///
    /// It must be guaranteed that the bytes passed to it are valid UTF-8. If
    /// this constraint is violated, it may cause memory unsafety issues with
    /// future users of the created `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let heart = [226, 153, 165].to_vec();
    ///
    /// let heart = unsafe { String::try_from_utf8_unchecked(heart).expect("I/O error") };
    /// assert_eq!(heart.as_str(), "♥");
    /// ```
    pub unsafe fn try_from_utf8_unchecked(bytes: Vec<u8>) -> io::Result<Self> {
        let mut string = Self::try_with_capacity(bytes.len())?;
        string.data.write_at(&bytes, 0)?;
        string.len += bytes.len();

        Ok(string)
    }

    /// Returns the length of the `String` in **bytes**, not
    /// [`char`](std::char)s nor graphemes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// use std::convert::TryFrom;
    ///
    /// let foo = String::try_from("foo").expect("I/O error");
    /// assert_eq!(foo.len(), 3);
    /// assert_eq!(foo.chars().count(), 3);
    ///
    /// let fancy_foo = String::try_from("ƒoo").expect("I/O error");
    /// assert_eq!(fancy_foo.len(), 4);
    /// assert_eq!(fancy_foo.chars().count(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the capacity of the `String` in **bytes**, not
    /// [`char`](std::char)s nor graphemes.
    ///
    /// This value depends on the granularity of the underlying storage, based
    /// on [`harrow::granularity`](harrow::granularity).
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let string = String::with_capacity(harrow::granularity() + 1);
    /// assert_eq!(string.capacity(), 2 * harrow::granularity());
    /// ```
    pub fn capacity(&self) -> usize {
        self.data.len()
    }

    /// Returns [`AsStr`](self::AsStr) wrapper which can be used to obtain a
    /// `&str` reference to the string.
    ///
    /// The reason for using a wrapper instead of `&str` directly is the same as
    /// for using [`Ref`](crate::storage::Ref) in other collections. See [Ref
    /// and RefMut](crate#ref-and-refmut) for more details.
    ///
    /// Keep in mind that calling this function allocates a new virtual mapping
    /// for the entire string, regardless of its size. This may cause troubles
    /// for hge strings.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_as_str`](self::String::try_as_str) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push_str("Hello world!");
    ///
    /// let as_str = string.as_str();
    /// let as_ref: &str = as_str.as_ref();
    /// assert_eq!(as_str, "Hello world!");
    /// ```
    pub fn as_str(&self) -> AsStr<'_> {
        AsStr(self.data.view(0, self.len).unwrap())
    }

    /// Returns [`AsBytes`](self::AsBytes) wrapper which can be used to obtain a
    /// slice of bytes, `&[u8]`, of the string.
    ///
    /// The reason for using a wrapper instead of `&[u8]` directly is the same
    /// as for using [`Ref`](crate::storage::Ref) in other collections. See [Ref
    /// and RefMut](crate#ref-and-refmut) for more details.
    ///
    /// Keep in mind that calling this function allocates a new virtual mapping
    /// for the entire string, regardless of its size. This may cause troubles
    /// for hge strings.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_as_bytes`](self::String::try_as_bytes) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push_str("Hello");
    ///
    /// let as_bytes = string.as_bytes();
    /// let as_ref: &[u8] = as_bytes.as_ref();
    /// assert_eq!(as_bytes, &[72, 101, 108, 108, 111][..]);
    /// ```
    pub fn as_bytes(&self) -> AsBytes<'_> {
        self.try_as_bytes().unwrap()
    }

    /// Appends a char to the end of the string.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_push`](self::String::try_push) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push('a');
    /// string.push('b');
    /// string.push('c');
    ///
    /// assert_eq!(string.as_str(), "abc");
    /// ```
    pub fn push(&mut self, ch: char) {
        self.try_push(ch).unwrap()
    }

    /// Appends a string slice to the end of the string.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs. Use
    /// [`try_push_str`](self::String::try_push_str) if this is unacceptable.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push_str("Hello ");
    /// string.push_str("world!");
    ///
    /// assert_eq!(string.as_str(), "Hello world!");
    /// ```
    pub fn push_str(&mut self, string: &str) {
        self.try_push_str(string).unwrap()
    }

    /// Checks whether the byte at position `index` is the first byte in a UTF-8
    /// code point sequence or the end of the string.
    ///
    /// The start and end of the string (when `index == self.len()`) are
    /// considered to be boundaries.
    ///
    /// Returns `false` if the index is greater than `self.len()`.
    ///
    /// # Panics
    ///
    /// Panics when an I/O error occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// use std::convert::TryFrom;
    /// let string = String::try_from("Löwe 老虎 Léopard").expect("I/O error");
    ///
    /// assert!(string.is_char_boundary(0));
    /// // start of `老`
    /// assert!(string.is_char_boundary(6));
    /// assert!(string.is_char_boundary(string.len()));
    /// assert!(!string.is_char_boundary(string.len() + 1));
    ///
    /// // second byte of `ö`
    /// assert!(!string.is_char_boundary(2));
    ///
    /// // third byte of `老`
    /// assert!(!string.is_char_boundary(8));
    /// ```
    pub fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 || index == self.len() {
            true
        } else if index > self.len() {
            false
        } else {
            CharScan::from(self.as_bytes(), index)
                .next()
                .unwrap()
                .is_ok()
        }
    }

    /// Returns an iterator over [`char`](std::char)s of the string.
    ///
    /// # Panics
    ///
    /// `String::chars` and `Chars::next` panic when an I/O error occurs.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push_str("ƒoo");
    ///
    /// assert_eq!(string.chars().count(), 3);
    ///
    /// let mut chars = string.chars();
    ///
    /// assert_eq!(chars.next(), Some('ƒ'));
    /// assert_eq!(chars.next(), Some('o'));
    /// assert_eq!(chars.next(), Some('o'));
    /// assert_eq!(chars.next(), None);
    /// ```
    pub fn chars(&self) -> Chars<'_> {
        Chars {
            inner: CharScan::new(self.as_bytes()),
        }
    }

    /// Creates a new, empty `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let string = String::try_new().expect("I/O error");
    /// ```
    pub fn try_new() -> io::Result<Self> {
        Self::try_with_capacity(INITIAL_CAPACITY)
    }

    /// Creates a new, empty `String` with a particular capacity (in bytes).
    ///
    /// The capacity is actually rounded to closest higher value that is
    /// divisible by [`harrow::granularity()`](harrow::granularity). The string
    /// will be able to hold exactly this number of bytes without resizing the
    /// underlying file.
    ///
    /// Zero capacity is not supported. The lowest possible non-zero capacity
    /// will be used instead.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let string = String::try_with_capacity(harrow::granularity() + 1).expect("I/O error");
    /// assert_eq!(string.len(), 0);
    /// assert_eq!(string.capacity(), 2 * harrow::granularity());
    /// ```
    pub fn try_with_capacity(capacity: usize) -> io::Result<Self> {
        // harrow requires non-zero length.
        let capacity = if capacity == 0 {
            INITIAL_CAPACITY
        } else {
            capacity
        };

        Ok(Self {
            data: FileMut::new(temp_path(), capacity)?,
            len: 0,
            buf: Vec::new(),
        })
    }

    /// Converts a standard vector of bytes to a `String`.
    ///
    /// Not all byte vectors are valid strings: `String` requires that it is
    /// valid UTF-8. `try_from_utf8` checks to ensure that this property is
    /// satisfied.
    ///
    /// If you are sure tha the byte vector is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an *unsafe*
    /// version of this function, `try_from_utf8_unchecked`, which has the same
    /// behavior but skips the check.
    ///
    /// # Errors
    ///
    /// There are two types of possible errors: an I/O error and invalid UTF-8.
    /// The latter is returned in the form of the former, with
    /// `std::io::ErrorKind::InvalidInput` kind and the underlying
    /// `std::str::Utf8Error` as the argument.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let heart = [226, 153, 165].to_vec();
    ///
    /// let heart = String::try_from_utf8(heart).expect("I/O error");
    /// assert_eq!(heart.as_str(), "♥");
    ///
    /// let invalid = [0, 153, 165].to_vec();
    ///
    /// let invalid = String::try_from_utf8(invalid);
    /// assert!(invalid.is_err());
    /// ```
    pub fn try_from_utf8(bytes: Vec<u8>) -> io::Result<Self> {
        std::str::from_utf8(&bytes)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
        let mut string = Self::try_with_capacity(bytes.len())?;
        string.data.write_at(&bytes, 0)?;
        string.len += bytes.len();

        Ok(string)
    }

    /// Returns [`AsStr`](self::AsStr) wrapper which can be used to obtain a
    /// `&str` reference to the string.
    ///
    /// The reason for using a wrapper instead of `&str` directly is the same as
    /// for using [`Ref`](crate::storage::Ref) in other collections. See [Ref
    /// and RefMut](crate#ref-and-refmut) for more details.
    ///
    /// Keep in mind that calling this function allocates a new virtual mapping
    /// for the entire string, regardless of its size. This may cause troubles
    /// for hge strings.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push_str("Hello world!");
    ///
    /// let as_str = string.try_as_str().expect("I/O error");
    /// let as_ref: &str = as_str.as_ref();
    /// assert_eq!(as_str, "Hello world!");
    /// ```
    pub fn try_as_str(&self) -> io::Result<AsStr<'_>> {
        let view = self.data.view(0, self.len)?;
        std::str::from_utf8(view.as_slice())
            .map_err(|error| io::Error::new(io::ErrorKind::Other, error))?;
        Ok(AsStr(view))
    }

    /// Returns [`AsBytes`](self::AsBytes) wrapper which can be used to obtain a
    /// slice of bytes, `&[u8]`, of the string.
    ///
    /// The reason for using a wrapper instead of `&[u8]` directly is the same
    /// as for using [`Ref`](crate::storage::Ref) in other collections. See [Ref
    /// and RefMut](crate#ref-and-refmut) for more details.
    ///
    /// Keep in mind that calling this function allocates a new virtual mapping
    /// for the entire string, regardless of its size. This may cause troubles
    /// for hge strings.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.push_str("Hello");
    ///
    /// let as_bytes = string.try_as_bytes().expect("I/O error");
    /// let as_ref: &[u8] = as_bytes.as_ref();
    /// assert_eq!(as_bytes, &[72, 101, 108, 108, 111][..]);
    /// ```
    pub fn try_as_bytes(&self) -> io::Result<AsBytes<'_>> {
        self.data.view(0, self.len).map(AsBytes)
    }

    /// Appends a char to the end of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.try_push('a').expect("I/O error");
    /// string.try_push('b').expect("I/O error");
    /// string.try_push('c').expect("I/O error");
    ///
    /// assert_eq!(string.as_str(), "abc");
    /// ```
    pub fn try_push(&mut self, ch: char) -> io::Result<()> {
        self.grow_maybe(ch.len_utf8())?;

        self.buf.resize(ch.len_utf8(), 0);
        ch.encode_utf8(&mut self.buf);
        self.data.write_at(self.buf.as_slice(), self.len)?;
        self.len += ch.len_utf8();
        Ok(())
    }

    /// Appends a string slice to the end of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bonifacio::String;
    /// let mut string = String::new();
    /// string.try_push_str("Hello ").expect("I/O error");
    /// string.try_push_str("world!").expect("I/O error");
    ///
    /// assert_eq!(string.as_str(), "Hello world!");
    /// ```
    pub fn try_push_str(&mut self, string: &str) -> io::Result<()> {
        self.grow_maybe(string.len())?;

        self.data.write_at(string.as_bytes(), self.len)?;
        self.len += string.len();
        Ok(())
    }

    fn grow_maybe(&mut self, additional: usize) -> io::Result<()> {
        if self.len() + additional > self.data.len() {
            self.data.resize(2 * self.len())?;
        }

        Ok(())
    }
}

impl TryFrom<&str> for String {
    type Error = io::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let mut string = String::try_with_capacity(value.len())?;
        string.data.write_at(value.as_bytes(), 0)?;
        string.len += value.len();

        Ok(string)
    }
}

/// An iterator over [`char`](std::char)s of the string.
///
/// This struct is created by the [`chars`](self::String::chars) method on
/// [`String`](self::String).
///
/// # Panics
///
/// `Chars::next` panics when an I/O error occurs.
///
/// # Examples
///
/// ```
/// # use bonifacio::String;
/// let mut string = String::new();
/// string.push_str("ƒoo");
///
/// assert_eq!(string.chars().count(), 3);
///
/// let mut chars = string.chars();
///
/// assert_eq!(chars.next(), Some('ƒ'));
/// assert_eq!(chars.next(), Some('o'));
/// assert_eq!(chars.next(), Some('o'));
/// assert_eq!(chars.next(), None);
/// ```
pub struct Chars<'a> {
    inner: CharScan<'a>,
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Result::unwrap)
    }
}

mod unicode {
    use std::fmt;

    use super::AsBytes;

    pub struct CharScan<'a> {
        bytes: AsBytes<'a>,
        offset: usize,
    }

    impl<'a> CharScan<'a> {
        pub fn new(bytes: AsBytes<'a>) -> Self {
            Self { bytes, offset: 0 }
        }

        pub fn from(bytes: AsBytes<'a>, offset: usize) -> Self {
            Self { bytes, offset }
        }
    }

    impl<'a> Iterator for CharScan<'a> {
        type Item = Result<char, FromUtf8Error>;

        fn next(&mut self) -> Option<Self::Item> {
            if self.offset < self.bytes.len() {
                let ch = match parse_char(&self.bytes[self.offset..]) {
                    Some(ch) => ch,
                    None => {
                        return Some(Err(FromUtf8Error {
                            bytes: self.bytes.to_owned(),
                            valid_up_to: self.offset,
                        }))
                    }
                };
                self.offset += ch.len_utf8();
                Some(Ok(ch))
            } else {
                None
            }
        }
    }

    #[derive(Debug)]
    pub struct FromUtf8Error {
        bytes: Vec<u8>,
        valid_up_to: usize,
    }

    impl fmt::Display for FromUtf8Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "invalid utf-8 sequence at position {}", self.valid_up_to)
        }
    }

    impl std::error::Error for FromUtf8Error {}

    pub fn parse_char(bytes: &[u8]) -> Option<char> {
        let width = char_width(bytes[0])?;

        if width <= bytes.len() {
            let mut buf = [0; 4];

            buf[0] = bytes[0];
            for i in 1..width {
                buf[i] = bytes[i];
            }

            std::str::from_utf8(&buf[..width]).ok()?.chars().next()
        } else {
            None
        }
    }

    fn char_width(first_byte: u8) -> Option<usize> {
        // https://tools.ietf.org/html/rfc3629
        if first_byte & 0x80 == 0 {
            Some(1)
        } else if first_byte & 0xe0 == 0xc0 {
            Some(2)
        } else if first_byte & 0xf0 == 0xe0 {
            Some(3)
        } else if first_byte & 0xf8 == 0xf0 {
            Some(4)
        } else {
            None
        }
    }
}

/// A wrapper which can be used to obtain a slice of bytes, `&[u8]`, of the
/// string.
///
/// This struct is created by the [`try_as_bytes`](self::String::try_as_bytes)
/// and [`as_bytes`](self::String::as_bytes) methods on
/// [`String`](self::String).
///
/// # Examples
///
/// ```
/// # use bonifacio::String;
/// let mut string = String::new();
/// string.push_str("Hello");
///
/// let as_bytes = string.as_bytes();
/// let as_ref: &[u8] = as_bytes.as_ref();
/// assert_eq!(as_bytes, &[72, 101, 108, 108, 111][..]);
/// ```
pub struct AsBytes<'a>(harrow::ViewRef<'a>);

impl AsRef<[u8]> for AsStr<'_> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl Deref for AsBytes<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.0.as_slice()
    }
}

impl fmt::Debug for AsBytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AsBytes({:?})", self.0.as_slice())
    }
}

impl PartialEq for AsBytes<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_slice() == other.0.as_slice()
    }
}

impl<'a> PartialEq<&'a [u8]> for AsBytes<'a> {
    fn eq(&self, other: &&'a [u8]) -> bool {
        self.0.as_slice() == *other
    }
}

impl PartialEq<Vec<u8>> for AsBytes<'_> {
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.0.as_slice() == other.as_slice()
    }
}

impl PartialEq<[u8]> for AsBytes<'_> {
    fn eq(&self, other: &[u8]) -> bool {
        self.0.as_slice() == other
    }
}

impl Eq for AsBytes<'_> {}

/// A wrapper which can be used to obtain a `&str` reference to the string.
///
/// This struct is created by the [`try_as_str`](self::String::try_as_str) and
/// [`as_str`](self::String::as_str) methods on [`String`](self::String).
///
/// # Examples
///
/// ```
/// # use bonifacio::String;
/// let mut string = String::new();
/// string.push_str("Hello world!");
///
/// let as_str = string.as_str();
/// let as_ref: &str = as_str.as_ref();
/// assert_eq!(as_str, "Hello world!");
/// ```
pub struct AsStr<'a>(harrow::ViewRef<'a>);

impl AsStr<'_> {
    fn as_str(&self) -> &str {
        // SAFETY: If the user asks for a checked version, the validity of the
        // unicode encoding is checked in `try_as_str`.
        unsafe { std::str::from_utf8_unchecked(self.0.as_slice()) }
    }
}

impl AsRef<str> for AsStr<'_> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Deref for AsStr<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl fmt::Debug for AsStr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AsStr({:?})", self.as_str())
    }
}

impl fmt::Display for AsStr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl PartialEq for AsStr<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<'a> PartialEq<&'a str> for AsStr<'a> {
    fn eq(&self, other: &&'a str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<std::string::String> for AsStr<'_> {
    fn eq(&self, other: &std::string::String) -> bool {
        self.as_str() == other.as_str()
    }
}

impl PartialEq<str> for AsStr<'_> {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl Eq for AsStr<'_> {}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    #[derive(Debug, Clone)]
    enum Action {
        PushStr(String),
        Push(char),
        CharBoundary(usize),
    }

    fn test_random_ops(actions: impl Iterator<Item = Action>) {
        let mut our_str = super::String::new();
        let mut std_str = String::new();

        for action in actions {
            match action {
                Action::PushStr(value) => {
                    our_str.push_str(&value);
                    std_str.push_str(&value);
                }
                Action::Push(value) => {
                    our_str.push(value);
                    std_str.push(value);
                }
                Action::CharBoundary(index) => {
                    if index < std_str.len() {
                        assert_eq!(
                            our_str.is_char_boundary(index),
                            std_str.is_char_boundary(index)
                        );
                    }
                }
            }
        }

        assert_eq!(our_str.len(), std_str.len());
        assert_eq!(our_str.as_str(), std_str.as_str());
    }

    fn limit_index(index: usize) -> usize {
        // The whole domain of usize is unnecessarily large, we need to focus on
        // the subset whose values have reasonable probability to be valid in
        // the sequence of the actions.
        index % 50
    }

    fn action_strategy() -> impl Strategy<Value = Action> {
        prop_oneof![
            any::<String>().prop_map(Action::PushStr),
            any::<char>().prop_map(Action::Push),
            any::<usize>()
                .prop_map(limit_index)
                .prop_map(Action::CharBoundary),
        ]
    }

    proptest! {
        #[test]
        fn random_ops(actions in proptest::collection::vec(action_strategy(), 1..500)) {
            test_random_ops(actions.into_iter());
        }

        #[test]
        fn random_bytes(bytes in proptest::collection::vec(any::<u8>(), 0..1000)) {
            assert_eq!(super::String::from_utf8(bytes.clone()).is_ok(), String::from_utf8(bytes).is_ok());
        }
    }
}
