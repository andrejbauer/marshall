(lang dune 3.4)
(name marshall)
(version dev)
(generate_opam_files true)
(using menhir 2.1)
(source
 (github andrejbauer/marshall))

(authors "Andrej Bauer" "Ivo List" "Paul Taylor")

(maintainers "Andrej Bauer")

(license BSD-2-Clause)

(package
 (name marshall)
 (synopsis "A programming language for computation with Dedekind reals")
 (description "Marshall is a programming language for exact real arithmetic based on ideas from Abstract Stone Duality (ASD) and the construction of the Dedekind reals in ASD.")
 (depends
    ocaml
    dune
    menhir
    mpfr)
)

