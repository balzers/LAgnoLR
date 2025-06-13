The project has been tested with Coq 8.20.1.

# Instructions for Typechecking

1. Install `opam` (skip if you already have it): follow the instructions at <https://opam.ocaml.org/doc/Install.html>.

2. Install dev version of `std++` (skip if you already have it) and Coq:

```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-stdpp
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
