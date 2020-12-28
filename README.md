# Bonifacio

> /boniˈfaːtʃo/ or /ˈbonɪfaːt͡s aɪ oʊ/

A set of standard collections, backed by a file instead of memory. Intended for
use when facing huge amount of data.

Available collections (so far with minimum-viable-product API):

* `Vec`
* `String`
* `HashMap`
* `HashSet`

In spite of following the API of the standard library in the collections, there
is yet no guarantee for stability of the other APIs in the crate.

Uses [harrow](https://crates.io/crates/harrow) crate under the hood. See its
documentation for platform support and **safety** guarantees. TL;DR: Consider
this highly experimental.

## [Documentation](https://docs.rs/bonifacio)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bonifacio = "0.1"
```

Either shadow the standard collections via `use` or keep them in `bonifacio`
namespace. Then work with the collections in (mostly) standard way as you are
used to.

```rust
let mut vec = bonifacio::Vec::new_unsized();
vec.push("Hello world!".to_string());
assert_eq!(vec.len(), 1);

use bonifacio::HashSet;
let mut set = HashSet::new_sized();
set.insert(3);
assert!(set.contains(&3));
```

## Roadmap

* Implement more of the standard API on the collections
* Add support for more types that is possible to store in the collections
  * Provide a *derive* macro to conveniently integrate custom element types
  * Support types implementing `serde` traits
* Improve ergonomics by implementing standard traits
* Implement other collections (`VecDeque`, `BinaryHeap`, `BTreeMap`, `BTreeSet`)

Contributions are welcome!

## Name

Sometimes, one encounters documents of such big size that they can't be stored
in a personal library (think operational memory). In these cases, they need to
be stored in a large archive (think files). Who else in such circumstances could
possibly provide a better help than [Baldassarre
Bonifacio](https://en.wikipedia.org/wiki/Baldassarre_Bonifacio) (think this
crate), an Italian bishop and scholar known for his work *De archivis liber
singularis* (published 1632), the first known treatise on the management of
archives.

## License

Dual-licensed under [MIT](LICENSE) and [UNLICENSE](UNLICENSE). Feel free to use
it, contribute or spread the word.

API documentation of collections is to large extent based on or even reused from
the documentation of Rust's [standard
library](https://doc.rust-lang.org/std/index.html), which is dual-licensed under
MIT and Apache License (Version 2.0). See
[here](https://github.com/rust-lang/rust#license) for details.
