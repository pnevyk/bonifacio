//! A module providing tools for serialization and deserialization. This should
//! be eventually replaced by a custom derive macro.
//!
//! # Examples
//!
//! Use [`StructSerializer`](self::StructSerializer) and
//! [`StructDeserializer`](self::StructDeserializer) for structs.
//!
//! ```
//! use bonifacio::Value;
//! use bonifacio::tools::{StructDeserializer, StructSerializer};
//!
//! #[derive(Debug, Clone, PartialEq)]
//! struct Foo {
//!     string: String,
//!     number: u64,
//! }
//!
//! impl Value for Foo {
//!     fn to_bytes(&self, buf: &mut Vec<u8>) {
//!         StructSerializer::new(buf)
//!             .field(&self.string)
//!             .field(&self.number)
//!             .finish();
//!     }
//!
//!     fn from_bytes(bytes: &[u8]) -> Self {
//!         let deserializer = StructDeserializer::new(bytes);
//!         unsafe {
//!             Foo {
//!                 string: deserializer.field(0),
//!                 number: deserializer.field(1),
//!             }
//!         }
//!     }
//! }
//!
//! let foo = Foo {
//!     string: "bar".to_string(),
//!     number: 3,
//! };
//! let mut vec = bonifacio::Vec::new_unsized();
//! vec.push(foo.clone());
//! assert_eq!(&*vec.get(0).unwrap(), &foo);
//! ```
//!
//! Use [`EnumSerializer`](self::EnumSerializer) and
//! [`EnumDeserializer`](self::EnumDeserializer) for enums.
//!
//! ```
//! use bonifacio::Value;
//! use bonifacio::tools::{EnumDeserializer, EnumSerializer};
//!
//! #[derive(Debug, Clone, PartialEq)]
//! enum Foo {
//!     Pair(String, u64),
//!     Unit,
//! }
//!
//! impl Value for Foo {
//!     fn to_bytes(&self, buf: &mut Vec<u8>) {
//!         let serializer = EnumSerializer::new(buf);
//!         match self {
//!             Foo::Pair(string, number) => {
//!                 serializer.variant(0).field(string).field(number).finish()
//!             }
//!             Foo::Unit => serializer.variant(1).finish(),
//!         }
//!     }
//!
//!     fn from_bytes(bytes: &[u8]) -> Self {
//!         let deserializer = EnumDeserializer::new(bytes);
//!         match deserializer.variant() {
//!             0 => {
//!                 let deserializer = deserializer.data();
//!                 unsafe { Foo::Pair(deserializer.field(0), deserializer.field(1)) }
//!             }
//!             1 => Foo::Unit,
//!             _ => unreachable!(),
//!         }
//!     }
//! }
//!
//! let foo = Foo::Pair("bar".to_string(), 3);
//! let mut vec = bonifacio::Vec::new_unsized();
//! vec.push(foo.clone());
//! assert_eq!(&*vec.get(0).unwrap(), &foo);
//! ```

use std::convert::TryInto;

use crate::value::Value;

/// A serializer of a struct to bytes.
///
/// The deserialization should be done with
/// [`StructDeserializer`](self::StructDeserializer).
///
/// # Examples
///
/// See [module](self) documentation for a full example.
pub struct StructSerializer<'a> {
    buf: &'a mut Vec<u8>,
    sizes: Vec<usize>,
}

impl<'a> StructSerializer<'a> {
    /// Creates a new serializer that will output the bytes into given `buf`.
    pub fn new(buf: &'a mut Vec<u8>) -> Self {
        Self {
            buf,
            sizes: Vec::new(),
        }
    }

    /// Appends a field value to the internal buffer of bytes.
    ///
    /// The call order on the fields is important for
    /// [`StructDeserializer::field`](self::StructDeserializer::field).
    #[must_use = "finish must be called after all fields are serialized"]
    pub fn field<T: Value>(mut self, value: &T) -> Self {
        let len = self.buf.len();
        value.to_bytes(&mut self.buf);
        self.sizes.push(self.buf.len() - len);
        self
    }

    /// Adds a header necessary for correct deserialization.
    pub fn finish(self) {
        // Append the header.

        // Sizes of individual fields.
        for size in self.sizes.iter() {
            self.buf.extend_from_slice(&size.to_ne_bytes());
        }

        // Number of fields.
        self.buf.extend_from_slice(&self.sizes.len().to_ne_bytes());
    }
}

/// A deserializer of a struct from bytes.
///
/// The serialization should be done with
/// [`StructSerializer`](self::StructSerializer).
///
/// # Examples
///
/// See [module](self) documentation for a full example.
pub struct StructDeserializer<'a> {
    bytes: &'a [u8],
    cum_sizes: Vec<usize>,
}

impl<'a> StructDeserializer<'a> {
    /// Creates a new deserializer that will parse the struct's fields from
    /// given `bytes`.
    pub fn new(bytes: &'a [u8]) -> Self {
        let len = bytes.len();
        let usize_size = std::mem::size_of::<usize>();
        let n_fields = usize::from_ne_bytes(bytes[len - usize_size..len].try_into().unwrap());

        let header_start = len - n_fields * usize_size - usize_size;
        let mut cum_sizes = Vec::new();
        let mut cum = 0;

        for i in 0..n_fields {
            let start = header_start + i * usize_size;
            let size = usize::from_ne_bytes(bytes[start..start + usize_size].try_into().unwrap());

            cum += size;
            cum_sizes.push(cum);
        }

        Self { bytes, cum_sizes }
    }

    /// Reconstructs a field value from the internal slice of bytes.
    ///
    /// The `index` must respect the order of calling
    /// [`StructSerializer::field`](self::StructSerializer::field) when
    /// serializing the struct.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `index` (as determined by the order of
    /// `StructSerializer::field` calls) really corresponds to a field of type
    /// `T`.
    pub unsafe fn field<T: Value>(&self, index: usize) -> T {
        assert!(index < self.cum_sizes.len());
        let (start, end) = if index == 0 {
            (0, self.cum_sizes[0])
        } else {
            (self.cum_sizes[index - 1], self.cum_sizes[index])
        };

        T::from_bytes(&self.bytes[start..end])
    }
}

/// A serializer of an enum to bytes.
///
/// The deserialization should be done with
/// [`EnumDeserializer`](self::EnumDeserializer).
///
/// # Examples
///
/// See [module](self) documentation for a full example.
pub struct EnumSerializer<'a> {
    buf: &'a mut Vec<u8>,
}

impl<'a> EnumSerializer<'a> {
    /// Creates a new serializer that will output the bytes into given `buf`.
    pub fn new(buf: &'a mut Vec<u8>) -> Self {
        Self { buf }
    }

    /// Specifies a discriminant that determines the variant of an enum and
    /// returns [`StructSerializer`](self::StructSerializer) which should be
    /// used to encode the data of this variant.
    ///
    /// If the variant does not hold any data, just call
    /// [`finish`](self::StructSerializer::finish).
    pub fn variant(self, discriminant: usize) -> StructSerializer<'a> {
        self.buf.extend_from_slice(&discriminant.to_ne_bytes());
        StructSerializer::new(self.buf)
    }
}

/// A deserializer of an enum from bytes.
///
/// The serialization should be done with
/// [`EnumSerializer`](self::EnumSerializer).
///
/// # Examples
///
/// See [module](self) documentation for a full example.
pub struct EnumDeserializer<'a> {
    bytes: &'a [u8],
}

impl<'a> EnumDeserializer<'a> {
    /// Creates a new deserializer that will parse the enums's data from given
    /// `bytes`.
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    /// Reconstructs the discriminant of an enum that is used to determine the
    /// variant.
    ///
    /// Returned discriminant value corresponds to the value specified in
    /// [`EnumSerializer::variant`](self::EnumSerializer::variant).
    pub fn variant(&self) -> usize {
        let usize_size = std::mem::size_of::<usize>();
        usize::from_ne_bytes(self.bytes[0..usize_size].try_into().unwrap())
    }

    /// Returns a [`StructDeserializer`](self::StructDeserializer) that is used
    /// to deserialize the data of the variant, if there is any.
    pub fn data(&self) -> StructDeserializer {
        let usize_size = std::mem::size_of::<usize>();
        StructDeserializer::new(&self.bytes[usize_size..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_basic() {
        #[derive(Debug, Clone, PartialEq)]
        struct Foo {
            string: String,
            number: u64,
        }

        impl Value for Foo {
            fn to_bytes(&self, buf: &mut Vec<u8>) {
                StructSerializer::new(buf)
                    .field(&self.string)
                    .field(&self.number)
                    .finish();
            }

            fn from_bytes(bytes: &[u8]) -> Self {
                let deserializer = StructDeserializer::new(bytes);
                unsafe {
                    Foo {
                        string: deserializer.field(0),
                        number: deserializer.field(1),
                    }
                }
            }
        }

        let foo = Foo {
            string: "bar".to_string(),
            number: 3,
        };
        let mut bytes = Vec::new();
        foo.to_bytes(&mut bytes);
        let foo2 = Foo::from_bytes(bytes.as_slice());
        assert_eq!(foo, foo2);
    }

    #[test]
    fn enum_basic() {
        #[derive(Debug, Clone, PartialEq)]
        enum Foo {
            Pair(String, u64),
            Unit,
        }

        impl Value for Foo {
            fn to_bytes(&self, buf: &mut Vec<u8>) {
                let serializer = EnumSerializer::new(buf);
                match self {
                    Foo::Pair(string, number) => {
                        serializer.variant(0).field(string).field(number).finish()
                    }
                    Foo::Unit => serializer.variant(1).finish(),
                }
            }

            fn from_bytes(bytes: &[u8]) -> Self {
                let deserializer = EnumDeserializer::new(bytes);
                match deserializer.variant() {
                    0 => {
                        let deserializer = deserializer.data();
                        unsafe { Foo::Pair(deserializer.field(0), deserializer.field(1)) }
                    }
                    1 => Foo::Unit,
                    _ => unreachable!(),
                }
            }
        }

        let foo = Foo::Pair("bar".to_string(), 3);
        let mut bytes = Vec::new();
        foo.to_bytes(&mut bytes);
        let foo2 = Foo::from_bytes(bytes.as_slice());
        assert_eq!(foo, foo2);
    }
}
