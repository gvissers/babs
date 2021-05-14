# babs

The aim of `babs` is to write a performant, full-fledged, safe, big integer crate for Rust, avoiding
unsafe code whenever possible.[[1]](#unsafe) Big integers in `babs` are stored as an array of digits
that implement the `Digit` trait; nearly all methods in `babs` are generic with respect to the
underlying digit type.

## Status

Currently, `babs` supports unsigned integers and the basic operations on them (comparisons and
arithmetic operations). Several algorithms for multiplication (long, Karatsuba, Toom-3)
and division (long, Burnikel-Ziegler) have been implemented. The current plan is to add bitwise
operations on unsigned integers next, and add support for signed integers at a later stage.
Implementing an FFT based multiplication scheme (e.g. the Schönhage-Strassen algorithm) is under
investigation. Furthermore, documentation and test coverage could use some improvement.

## What kind of name is `babs`!?

When thinking of big numbers, "billions and billions" comes to mind very quickly. And although
"billions and billions" can be represented by a single `u32`, it sounds like an awful lot, so the
name stuck and got abbreviated to `babs`.

<a name="unsafe">[1]</a>: currently, babs does not use any unsafe code at all. This may change if the
performance benefits of an unsafe function justify the cost of using it, but we endeavour to avoid
this.
