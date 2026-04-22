# UnderLogicAndType

Rocq formalization accompanying the POPL 2027 paper
*"Underapproximate Types"* (Choice Logic and Choice Types).

## Dependencies

| Package | Version |
|---------|---------|
| [Rocq](https://rocq-prover.org/) | 9.1.0 |
| [rocq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) | dev.2026-01-23 |
| [coq-hammer](https://github.com/lukaszcz/coqhammer) | 1.3.2+9.1 |

## Setup

The recommended way is via [opam](https://opam.ocaml.org/).

```bash
# Create a dedicated switch (once)
opam switch create with-rocq-1 ocaml-base-compiler
eval $(opam env --switch=with-rocq-1)

# Add the Rocq and Iris opam repositories
opam repo add rocq-released https://github.com/rocq-archive/opam-rocq-archive/releases/download/0.0.1/rocq-released-repo.tar.gz
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam/-/raw/master/index

# Install dependencies
opam install rocq-core.9.1.0 rocq-stdpp.dev.2026-01-23 coq-hammer.1.3.2+9.1
```

## Building

```bash
# Generate the Makefile (only needed once, or after editing _CoqProject)
rocq makefile -f _CoqProject -o Makefile.coq

# Build all files
make
```

If `rocq` is not on your PATH, prefix with the switch's bin directory:

```bash
PATH=$(opam var bin --switch=with-rocq-1):$PATH make
```

## File overview

| File | Contents |
|------|----------|
| `theories/Prelude.v` | Imports and shared setup |
| `theories/MapFilterDom.v` | Auxiliary lemmas: `dom` vs `filter` on `gmap` |
| `theories/Substitution.v` | Substitutions, compatibility, restriction, fibers |
| `theories/Resource.v` | Resources, resource operations, partial order |
| `theories/ChoiceAlgebra.v` | Abstract choice algebra; concrete `World` instance |
| `theories/ChoiceLogic.v` | Formula syntax and satisfaction relation |
| `theories/ChoiceLogicProps.v` | Key theorems about the logic |
