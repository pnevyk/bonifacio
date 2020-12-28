use std::convert::TryInto;
use std::fmt;
use std::mem;
use std::ops::Deref;

/// A trait that specifies how an element type is serialized and deserialized.
pub trait Value {
    /// Serializes self into a vector of bytes `buf`.
    fn to_bytes(&self, buf: &mut Vec<u8>);

    /// Deserializes a value from bytes.
    ///
    /// It is guaranteed that the bytes were produced by associated
    /// [`Value::to_bytes`](self::Value::to_bytes).
    fn from_bytes(bytes: &[u8]) -> Self;
}

/// A trait that is implemented for types whose byte representation has fixed
/// size.
pub trait SizedValue: Value + Sized {
    /// Returns the size of the byte representation for any value of the type.
    ///
    /// The default implementation is using [`std::mem::size_of<T>`] function.
    /// It is not appropriate when the non-primitive type uses padding due to
    /// memory alignment requirement (see
    /// [size_of](https://doc.rust-lang.org/nightly/std/mem/fn.size_of.html#size-of-structs)
    /// docs for explanation), because this padding in unnecessary for
    /// serialization into the file and thus should be avoided. In that case,
    /// the value from `SizedValue::size` is different than from
    /// `std::mem::size_of`.
    fn size() -> usize {
        mem::size_of::<Self>()
    }
}

/// A trait for getting "borrowed" variants of stored types that do not need to
/// do a heap allocation.
pub trait ValueBorrow: Value {
    /// An associated borrowed type of the stored value type.
    type Borrowed: ?Sized;

    /// Reinterprets the bytes as the borrowed type.
    fn from_bytes_borrowed(bytes: &[u8]) -> &Self::Borrowed;
}

/// A wrapper providing access to borrowed type of `T: ValueBorrow` while
/// holding the virtual mapping to the "borrowed" bytes.
///
/// # Examples
///
/// ```
/// use bonifacio::{Borrowed, Vec};
///
/// let mut vec = Vec::new_unsized();
/// vec.push("♥".to_string());
///
/// let borrowed: Borrowed<'_, String> = vec.borrow(0).unwrap();
/// let as_ref: &str = borrowed.as_ref();
/// assert_eq!(borrowed.len(), 3);
/// assert_eq!(borrowed.chars().count(), 1);
/// ```
pub struct Borrowed<'a, T: ValueBorrow> {
    // We need to store the view so it lives during the lifetime of Borrowed.
    #[allow(dead_code)]
    view: harrow::ViewRef<'a>,
    borrowed: &'a T::Borrowed,
}

impl<'a, T: ValueBorrow> Borrowed<'a, T> {
    pub(crate) fn new(view: harrow::ViewRef<'a>) -> Self {
        // SAFETY: We store the view along with the borrowed value. So the view
        // is not dropped until the Borrowed value is not dropped.
        let borrowed = T::from_bytes_borrowed(unsafe { view.as_slice_dangling() });
        Self { view, borrowed }
    }
}

impl<T: ValueBorrow> AsRef<T::Borrowed> for Borrowed<'_, T> {
    fn as_ref(&self) -> &T::Borrowed {
        &self.borrowed
    }
}

impl<T: ValueBorrow> Deref for Borrowed<'_, T> {
    type Target = T::Borrowed;

    fn deref(&self) -> &Self::Target {
        &self.borrowed
    }
}

impl<T: ValueBorrow> fmt::Debug for Borrowed<'_, T>
where
    T::Borrowed: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Borrowed({:?})", self.borrowed)
    }
}

impl<T: ValueBorrow> fmt::Display for Borrowed<'_, T>
where
    T::Borrowed: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.borrowed)
    }
}

mod impls {
    use super::*;

    impl Value for String {
        fn to_bytes(&self, buf: &mut Vec<u8>) {
            buf.extend_from_slice(self.as_bytes());
        }

        fn from_bytes(bytes: &[u8]) -> Self {
            String::from_utf8(bytes.to_owned()).unwrap()
        }
    }

    impl ValueBorrow for String {
        type Borrowed = str;

        fn from_bytes_borrowed(bytes: &[u8]) -> &Self::Borrowed {
            std::str::from_utf8(bytes).unwrap()
        }
    }

    impl Value for () {
        fn to_bytes(&self, _buf: &mut Vec<u8>) {}

        fn from_bytes(_bytes: &[u8]) -> Self {
            ()
        }
    }

    impl SizedValue for () {}

    macro_rules! impl_number {
        ($num_ty:ty) => {
            impl Value for $num_ty {
                fn to_bytes(&self, buf: &mut Vec<u8>) {
                    buf.extend_from_slice(&self.to_le_bytes());
                }

                fn from_bytes(bytes: &[u8]) -> Self {
                    Self::from_le_bytes(bytes.try_into().unwrap())
                }
            }

            impl SizedValue for $num_ty {}
        };
    }

    impl_number!(i8);
    impl_number!(i16);
    impl_number!(i32);
    impl_number!(i64);

    impl_number!(u8);
    impl_number!(u16);
    impl_number!(u32);
    impl_number!(u64);

    impl_number!(isize);
    impl_number!(usize);

    impl_number!(f32);
    impl_number!(f64);
}
