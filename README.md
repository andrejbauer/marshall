# Marshall

Marshall is a programming language for exact real arithmetic based on ideas from
[Abstract Stone Duality (ASD)](http://www.paultaylor.eu/ASD/) and the
construction of the [Dedekind reals in
ASD](http://www.paultaylor.eu/ASD/analysis#dedras). See also Andrej Bauer's talk
on [Efficient computations with Dedekind
reals](http://math.andrej.com/2008/08/24/efficient-computation-with-dedekind-reals/). 

The main idea of Marshall is that a real number `x` is given as a Dedekind cut,
i.e., as a pair of predicates describing which numbers are smaller than `x` and
which ones larger. For example, the `sqrt` function is defined in Marshall as

    let sqrt =
      fun a : real =>
        cut x
          left  (x < 0 \/ x * x < a)
          right (x > 0 /\ x * x > a)

See `example.asd` for more examples.

## Prerequisites

To compile Marshall you will need [Ocaml](http://www.ocaml.org/), version 4.12 or later,
the OCaml [dune](https://dune.build) build system, the
[menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator, and the large number library [num](https://github.com/ocaml/num/). The best way to
obtain these is to use the OCaml package manager [opam](https://opam.ocaml.org). Once
you have got OPAM going, run

    opam install dune menhir num

Optionally, you may install the `rlwrap` or `ledit` command-line editing wrappers.
Marshall will use them automatically in the interactive mode.

## Compilation

Compilation should run smoothly or not at all. Type

    dune build

If all goes well, an executable `marshall.exe` will appear in the main directory.

## Examples

There are examples in the `example` subdirectory. It may be instructive to look at
`prelude.asd`.

## A small Haskell implementation

In `etc/haskell` you can find a small Haskell implementation of real numbers that
somewhat follows the ideas of Marshall. It was implemented as part of a graduate course on
computable topology in 2009 at the Faculty of Computer Science and Informatics, University
of Ljubljana. Of particular help might be the notes `etc/haskell/notes.tex`.

## Compiling with MPFR

In theory Marshall can be compiled with the MPFR library, but the current configuration
is not set up to use it. If you manage to do it in a nice way, please contact us.
Here are some obsolete instruction that may or may not work:

1. Install `mpfr` through OPAM, as well as its dependencies.
2. Add `mpfr` as a dependency to `dune-project`.
3. Change `src/main.ml` so that it uses the MPFR interval arithmetic instead of `Big_num`.
