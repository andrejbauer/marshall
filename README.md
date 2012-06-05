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

To compile Marshall you will need [Ocaml](http://www.ocaml.org/), version 3.12 and
the [menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator.

Both are available through standard packaging systems on Linux distributions, and
on MacOS X via [macports](http://www.macports.org/). If you embark on compiling
Ocaml on your own, consider [GODI](http://godi.camlcity.org/godi/index.html) instead.

## Compilation

Compilation should run smoothly or not at all. Type

    ./configure
    make

The `configure` command accepts standard autoconf options, see `configure --help`.
The compiled executable is called `marshall` and you can run it in place.

## Installation

To install Marshall type

    make install

## Command-line editing

If you install the `rlwrap` or `ledit` command-line wrapper, Marshall will use them
automatically.

## Examples

There are examples in the `example` subdirectory. It may be instructive to look at
`prelude.asd`.

## A small Haskell implementation

In `etc/haskell` you can find a small Haskell implementation of real numbers that
somewhat follows the ideas of Marshall. It was implemented as part of a graduate course on
computable topology in 2009 at the Faculty of Computer Science and Informatics, University
of Ljubljana. Of particular help might be the notes `etc/haskell/notes.tex`.

## Compiling with MPFR

In theory Marshall can be compiled with the MPFR library, but this requires extra work.
At the moment MPFR is not used by autoconf. Here are some obsolete instruction that may
or may not work.

0. You need the prerequisites listed above.

1. You need the usual building tools, such as subversion, make, and gcc. Under Microsoft
Windows you can get those by installing [Cygwin](http://www.cygwin.com/).

3. You need [camlidl](http://caml.inria.fr/camlidl/), which is available in GODI
as well.

4. You need [MPFR](http://www.mpfr.org/), or through your package manager.

5. You need [mlgmpidl](http://mlxxxidl.gforge.inria.fr/mlgmpidl/index.html). You should get
the latest subversion version which includes some patches that we
submitted. Check out mlgmpidl from subversion:

    svn checkout svn://scm.gforge.inria.fr/svn/mlxxxidl/mlgmpidl

(Just in case, this repostitory includes the patch in `mpfr.idl.patch`. But you
should not have to apply it if you get mlgmpidl from subversion.) Proceed with
installation of mlgmpidl.

6. TODO How to "register" it with ocamlfind?

7. To compile the bytecode version with Mpfr library, type in the `src` subdirectory

    ocamlbuild -use-ocamlfind marshall_mpfr.byte

To compile bytecode, native, and the documentation, type in the `src` subdirectory

    ocamlbuild -use-ocamlfind all.otarget
