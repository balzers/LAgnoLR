[![type check](https://github.com/balzers/LAgnoLR/actions/workflows/build.yml/badge.svg)](https://github.com/balzers/LAgnoLR/actions/workflows/build.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2506.10026-b31b1b.svg)](https://arxiv.org/abs/2506.10026)

The project has been tested with Coq 8.20.1.

# Instructions for Typechecking

1. Install `opam` (skip if you already have it): follow the instructions at <https://opam.ocaml.org/doc/Install.html>.

2. Install the appropriate version of `std++` (skip if you already have it) and Coq:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stdpp.1.12.0
```

3. Typecheck the code:

```bash
bash gen_makefile.sh
make -f CoqMakefile
```

The end of the output is expected to be

```
Closed under the global context
Closed under the global context
```

They correspond to the last two lines in `theory.v`:

```coq
Print Assumptions fundamental.
Print Assumptions TToRecv_terminates.
```

The first line prints the assumptions of the FTLR (Theorem 22), and the second line prints
the theorem that the bit-flipping example inhabits the logical relation (Theorem 12).
