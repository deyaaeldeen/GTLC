[![Build Status](https://travis-ci.org/deyaaeldeen/GTLC.svg?branch=master)](https://travis-ci.org/deyaaeldeen/GTLC)

gtlc is an interpreter implemented in Haskell for gradually typed lambda calculus with basic types and mutable references and is tested using QuickCheck. The main goal of the project is to explore ideas for efficient compilation of mutable references in GTLC.

#Introduction
> Gradual typing is a technical approach to integrating static and dynamic typing within a single language that puts the programmer in control of which regions of code are statically or dynamically typed, and enables the gradual migration of code between the two typing disciplines.

[Siek, Jeremy G., et al. "Refined Criteria for Gradual Typing."]

This project is still a work in progress and builds on ideas from the following papers:

Siek, Jeremy G., and Walid Taha. "Gradual typing for functional languages." Scheme and Functional Programming Workshop. Vol. 6. 2006.

Siek, Jeremy, Ronald Garcia, and Walid Taha. "Exploring the design space of higher-order casts." Programming Languages and Systems. Springer Berlin Heidelberg, 2009. 17-31.

Herman, David, Aaron Tomb, and Cormac Flanagan. "Space-efficient gradual typing." Higher-Order and Symbolic Computation 23.2 (2010): 167-189.

Siek, Jeremy G., et al. "Monotonic References for Efficient Gradual Typing." European Symposium on Programming. 2015.

#Build

```bash
cabal configure --enable-tests && cabal build && cabal test
```

#Installation

```bash
cabal install
```

#Usage

There is no parser yet, but you can invoke ghci like this:

```bash
ghci test/Test -isrc
```

then, run the function

```haskell
test
```

to generate 10000 random program instances, typecheck them, evaluate them, typecheck the result and make sure the former type is the same as the later type, i.e. tries to prove type preservation.
