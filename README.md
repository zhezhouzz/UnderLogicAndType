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

## Repository structure

The formalization is split into four libraries with a linear dependency order:

```
ChoiceAlgebra → ChoiceLogic → ChoiceType
                               ↑
                            CoreLang
```

Each library lives under `<Library>/theories/`.

### `ChoiceAlgebra/` — The algebraic layer

Substitutions, resources, and the abstract choice algebra.

| File | Contents |
|------|----------|
| `Prelude.v` | Shared setup (stdpp, Hammer) |
| `MapFilterDom.v` | Auxiliary lemmas: `dom` vs `filter` on `gmap` |
| `Substitution.v` | Substitutions, compatibility, restriction, fibers |
| `Resource.v` | Resources (worlds), resource operations, partial order |
| `ChoiceAlgebra.v` | Abstract choice algebra class; concrete `World` instance |

### `ChoiceLogic/` — The logic layer

Formula syntax and the satisfaction relation, built on top of `ChoiceAlgebra`.

| File | Contents |
|------|----------|
| `Prelude.v` | Re-exports all of `ChoiceAlgebra` |
| `LogicQualifier.v` | Logic-level qualifier atoms (`lqual`) and `logic_qualifier_denote` |
| `Formula.v` | Formula syntax (`FAtom`, `FStar`, `FFib`, …) and `res_models` |
| `ChoiceLogicProps.v` | Key theorems (modality monotonicity, closure, collapse, adjunction) |

### `CoreLang/` — The programming language

A call-by-value λ-calculus with primitives and pattern matching,
in locally-nameless representation.

| File | Contents |
|------|----------|
| `Prelude.v` | LN infrastructure: `Open`, `Close`, `SubstV`, `Stale`, `Lc` typeclasses |
| `Syntax.v` | Syntax of values and terms; `open`, `close`, `subst`, `lc` |
| `BasicTyping.v` | Simple type system (`⊢ᵥ`, `⊢ₑ`) |
| `SmallStep.v` | Small-step operational semantics (`→*`) |
| `Properties.v` | Type safety and basic metatheory |

### `ChoiceType/` — The type system

Choice types layered on top of `CoreLang` and `ChoiceLogic`.

| File | Contents |
|------|----------|
| `Prelude.v` | Instantiates `ChoiceLogic` with `atom`/`value` from `CoreLang` |
| `Qualifier.v` | Type-level shallow qualifiers (`type_qualifier`); interpretation `qual_interp` |
| `Syntax.v` | Choice type syntax (`choice_ty`, `ctx`); erasure, lifting, substitution |
| `Denotation.v` | Type denotation `⟦τ⟧ e` and context denotation `⟦Γ⟧` as formulas |
| `Typing.v` | Single typing judgment `Γ ⊢ e ⋮ τ` |
| `Soundness.v` | Fundamental theorem and corollaries (safety, coverage, refinement, incorrectness) |
