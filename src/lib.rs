//! A set of standard collections, backed by a file instead of memory. Intended
//! for use when facing huge amount of data.
//!
//! Pronounced as /boniˈfaːtʃo/ or /ˈbonɪfaːt͡s aɪ oʊ/.
//!
//! Available collections (so far with minimum-viable-product API):
//!
//! * [`Vec`](crate::Vec)
//! * [`String`](crate::String)
//! * [`HashMap`](crate::HashMap)
//! * [`HashSet`](crate::HashSet)
//!
//! In spite of following the API of the standard library in the collections,
//! there is yet no guarantee for stability of the other APIs in the crate.
//!
//! Uses [harrow](https://crates.io/crates/harrow) crate under the hood. See its
//! documentation for platform support and **safety** guarantees. TL;DR:
//! Consider this highly experimental.
//!
//! Dual-licensed under MIT and [UNLICENSE](https://unlicense.org/). Feel free
//! to use it, contribute or spread the word.
//!
//! API documentation of collections is to large extent based on or even reused
//! from the documentation of Rust's [standard
//! library](https://doc.rust-lang.org/std/index.html), which is dual-licensed
//! under MIT and Apache License (Version 2.0). See
//! [here](https://github.com/rust-lang/rust#license) for details.
//!
//! # Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! bonifacio = "0.1"
//! ```
//!
//! Either shadow the standard collections via `use` or keep them in `bonifacio`
//! namespace. Then work with the collections in (mostly) standard way as you
//! are used to.
//!
//! ```
//! let mut vec = bonifacio::Vec::new_unsized();
//! vec.push("Hello world!".to_string());
//! assert_eq!(vec.len(), 1);
//!
//! use bonifacio::HashSet;
//! let mut set = HashSet::new_sized();
//! set.insert(3);
//! assert!(set.contains(&3));
//! ```
//!
//! # Roadmap
//!
//! * Implement more of the standard API on the collections
//! * Add support for more types that is possible to store in the collections
//!   * Provide a *derive* macro to conveniently integrate custom element types
//!   * Support types implementing `serde` traits
//! * Improve ergonomics by implementing standard traits
//! * Implement other collections (`VecDeque`, `BinaryHeap`, `BTreeMap`,
//!   `BTreeSet`)
//!
//! Contributions are welcome!
//!
//! # Serialization and Deserialization
//!
//! Because the elements of collections are stored in a file as bytes, there
//! must be a safe way how to encode the elements to bytes and reconstruct them
//! back again. This necessity unfortunately limits the set of types that can be
//! possibly stored in *bonifacio* collections.
//!
//! For this purpose, there is a trait [`Value`](crate::value::Value), defined
//! as follows:
//!
//! ```no_run
//! pub trait Value {
//!     fn to_bytes(&self, buf: &mut Vec<u8>);
//!     fn from_bytes(bytes: &[u8]) -> Self;
//! }
//! ```
//!
//! Any type implementing this trait serializes itself to `buf` vector,
//! reconstructs itself from `bytes` slice. Both serialization and
//! deserialization must be **infallible** - no error should ever occur. That is
//! why there is no way how to indicate an error through some `Result`. It is
//! guaranteed that `from_bytes` always gets data that were produced by
//! `to_bytes`.
//!
//! Another limitation of the file-backed storage is that it can only support
//! types that own their contents (for example, `String` is possible, but `&str`
//! is not). The reason is that when getting an element, the data must be read
//! from the file. That is, the serialized form of an element does not live in a
//! memory, so there is no way how to just borrow it.
//!
//! The actual implementation uses virtually mapped buffers from which a slice
//! of bytes can be obtained, and this is why `Value::from_bytes` works on
//! `&[u8]`. Such buffer lives however only for the lifetime inside body of a
//! getter, so the slice must be materialized when reconstructing the element.
//! Keeping the virtual mappings in memory would contradict the purpose of this
//! library to store huge collections without exhausting the memory. The
//! rationale for passing `&[u8]` instead of `Vec<u8>` to `from_bytes` is that
//! the serialized form can hold some metadata for deserialization, which do not
//! need to be materialized.
//!
//! Nonetheless, there is a way how to obtain slice-like types without the need
//! of materializing the bytes. See [Borrowed values](#borrowed-values) section
//! for details.
//!
//! See the [list](crate::value::Value#foreign-impls) of currently supported
//! element types. Use [`tools`](crate::tools) module to implement the `Value`
//! trait for custom types.
//!
//! # Sized vs Unsized
//!
//! In *bonifacio*, the notion of *sized* and *unsized* is different from that
//! in [standard
//! library](https://doc.rust-lang.org/nightly/std/marker/trait.Sized.html).
//! Here, sized types are those that can be serialized into bytes such that the
//! number of bytes is always the same (e.g., numbers), while unsized are types
//! that do not hold this number-of-bytes guarantee (e.g., standard `String`).
//!
//! Notice that [`std::String`](std::string::String) is considered unsized in
//! *bonifacio*, because it can be arbitrarily long, but it is `Sized` in
//! standard Rust sense, because it is represented simply by a heap allocation
//! pointer, length and capacity.
//!
//! Trait-wise, both sized and unsized types implement
//! [`Value`](crate::value::Value), while sized ones implement
//! [`SizedValue`](crate::value::SizedValue) on top of that.
//!
//! # `Ref` and `RefMut`
//!
//! This library tries to mirror the API of the standard library as much as
//! possible. However, due to implementation consequences of the file-backed
//! storage, when getting items we acquire owned instances of the types instead
//! of references.
//!
//! To avoid misuse (or rather confusing behavior) and get closer to the
//! standard API, the collections return [`Ref<'_, T>`](crate::Ref) in place of
//! `&T` and [`RefMut<'_, T>`](crate::RefMut) in place of `&mut T`. These
//! wrappers implement appropriate standard traits (like `Deref` and `DerefMut`)
//! to mimic expected API and behavior.
//!
//! Actually, the type declaration of `RefMut` requires additional generic type
//! for the used underlying storage, since it needs to write-back the changes
//! made on the value when the reference goes out of scope.
//!
//! # Borrowed values
//!
//! For many types that own its contents there exists an associated slice-like
//! type representing a borrowed variant (example pairs are `String` and `str`
//! or `PathBuf` and `Path`). While *bonifacio* collections cannot return a
//! simple reference to a type, as explained in the previous section, there is a
//! trait [`ValueBorrow`](crate::value::ValueBorrow) that enables to simply wrap
//! a slice of bytes into the appropriate slice-like type without the need of
//! doing heap allocation as it is the case for `Value::from_bytes`.
//!
//! This is possible only thanks to virtually mapped buffers that are allocated
//! for a part of the file. In this "borrowing" mechanism, the ownership of
//! these mappings is moved to type [`Borrowed`](crate::value::Borrowed), which
//! offers ways how to access the slice-like type through `ValueBorrow` trait.
//! Keep in mind, however, that keeping many of these `Borrowed` wrappers from
//! different parts of the underlying files causes an increased use of the
//! memory, because the mappings live in the memory in the end.
//!
//! # Efficiency
//!
//! Obviously, *bonifacio* generally cannot compete with in-memory
//! implementations. The goal here is to provide a decent substitute when the
//! data are too huge to use an in-memory approach. That does not mean that
//! there should be no focus on making *bonifacio* as fast as possible.
//!
//! Currently, a simple benchmark of `Vec` (available in `benches/` directory)
//! shows the slowdown compared to `std::Vec` is somewhat from 2x up to
//! something like 500x, depending on the element type and operations.
//! Efficiency of `HashMap` and `HashSet` is likely worse due to simplicity of
//! their implementation.
//!
//! An interesting case is when many `insert` and `remove` operations are
//! performed on `Vec` of an [unsized](#sized-vs-unsized) type like `String`.
//! The *bonifacio* vector can be actually faster than the standard one in these
//! circumstances. But it is not a fair comparison, because *bonifacio* does not
//! do the memory shifts on `insert` and `remove` for unsized types, as the
//! contiguity of the vector is only faked in this case.
//!
//! # I/O Errors
//!
//! Since collections in this library are backed by a file and not
//! heap-allocated memory, I/O errors can happen. However, until the storage is
//! pushed to its extremes, the errors can be perhaps considered as unlikely.
//!
//! To reduce the friction when using provided API, every fallible method comes
//! in two variants: *checked* (prefixed with `try_`) and *faithful* (named
//! exactly as in the standard library). Checked methods propagate every I/O
//! error encountered, while faithful simply unwrap the `Result`s.
//!
//! It is up to the user's consideration which variant they will use.
//!
//! # Name
//!
//! Sometimes, one encounters documents of such big size that they can't be
//! stored in a personal library (think operational memory). In these cases,
//! they need to be stored in a large archive (think files). Who else in such
//! circumstances could possibly provide a better help than [Baldassarre
//! Bonifacio](https://en.wikipedia.org/wiki/Baldassarre_Bonifacio) (think this
//! crate), an Italian bishop and scholar known for his work *De archivis liber
//! singularis* (published 1632), the first known treatise on the management of
//! archives.

#![doc(html_root_url = "https://docs.rs/bonifacio/0.1.0")]
#![deny(missing_docs)]

pub mod hash_map;
pub mod hash_set;
mod storage;
pub mod string;
pub mod tools;
mod value;
pub mod vec;

pub use storage::{BorrowStorage, Ref, RefMut, SizedStorage, Storage, UnsizedStorage};
pub use value::{Borrowed, SizedValue, Value, ValueBorrow};

pub use hash_map::HashMap;
pub use hash_set::HashSet;
pub use string::String;
pub use vec::Vec;
