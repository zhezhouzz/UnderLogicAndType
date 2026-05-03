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

The formalization is split into five libraries with the following dependency
shape:

```
ChoicePrelude → ChoiceAlgebra → ChoiceLogic
      │                              │
      └────────────→ CoreLang ───────┘
                         │
                         v
                    ChoiceType
```

Most libraries live under `<Library>/theories/`; `ChoicePrelude/` is a small
top-level shared prelude.

### `ChoicePrelude/` — Shared prelude

Common infrastructure shared by the algebra, logic, and language layers:
the concrete `atom` type, finite atom sets, freshness helpers, `Stale`, and
the abstract `ValueSig` interface used by `ChoiceAlgebra` and `ChoiceLogic`.

### `ChoiceAlgebra/` — The algebraic layer

Stores, resources, and the abstract choice algebra.

| File | Contents |
|------|----------|
| `Prelude.v` | Shared setup (stdpp, Hammer) |
| `MapFilterDom.v` | Auxiliary lemmas: `dom` vs `filter` on `gmap` |
| `Store.v` | Stores, compatibility, restriction, fibers |
| `Resource.v` | Resources (worlds), resource operations, partial order |
| `ChoiceAlgebra.v` | Abstract choice algebra class; `WfWorld` instance |

### `ChoiceLogic/` — The logic layer

Formula syntax and the satisfaction relation, built on top of `ChoiceAlgebra`.

| File | Contents |
|------|----------|
| `Prelude.v` | Re-exports `ChoiceAlgebra` and `ChoicePrelude` |
| `LogicQualifier.v` | Logic-level qualifier atoms (`lqual`) and `logic_qualifier_denote` |
| `Formula.v` | Formula syntax (`FAtom`, `FStar`, `FFib`, …) and `res_models` |
| `ChoiceLogicProps.v` | Key theorems (modality monotonicity, closure, collapse, adjunction) |

### `CoreLang/` — The programming language

A call-by-value λ-calculus with primitives and pattern matching,
in locally-nameless representation.

The Rocq syntax intentionally represents recursive functions slightly
differently from the paper's surface presentation.  Instead of giving `vfix`
two binders for the ordinary argument and recursive self reference, the
formalization uses `vfix Tf vf`, where `vf` is a value with one binder for the
ordinary argument.  After that binder is opened, `vf` is expected to be a
function that accepts the recursive self reference.  This HATs-style encoding
keeps the locally-nameless treatment of `vfix` to one direct binder while
preserving the intended recursive-call behavior.  Sanity checks against the
paper should treat this as an encoding choice rather than a literal syntax
match.

| File | Contents |
|------|----------|
| `Prelude.v` | LN infrastructure: `Open`, `Close`, `SubstV`, `Stale`, `Lc` typeclasses |
| `Syntax.v` | Syntax of values and terms; `open`, `close`, `subst`, `lc` |
| `BasicTyping.v` | Simple type system (`⊢ᵥ`, `⊢ₑ`) |
| `SmallStep.v` | Small-step operational semantics (`→*`) |
| `Properties.v` | Type safety and basic metatheory |

### `ChoiceType/` — The type system

Choice types layered on top of `CoreLang` and `ChoiceLogic`.

Dependent choice types and qualifiers use an atom-only opening discipline:
locally-nameless bound variables in type refinements are opened with a fresh
`atom`, not an arbitrary `value`.  Accordingly, the function-application
typing rules only apply directly to arguments of the form `vfvar x`; an
arbitrary value argument can first be named with `tlete` and then applied via
that atom.  This is a formalization choice that keeps qualifier opening aligned
with store-based lookup while preserving expressiveness through let-binding.

| File | Contents |
|------|----------|
| `Prelude.v` | Instantiates `ChoiceLogic` with `atom`/`value` from `CoreLang` |
| `Qualifier.v` | Type-level shallow qualifiers (`type_qualifier`); interpretation `qual_interp` |
| `Syntax.v` | Choice type syntax (`choice_ty`, `ctx`); erasure, lifting, substitution |
| `Denotation.v` | Type denotation `⟦τ⟧ e` and context denotation `⟦Γ⟧` as formulas |
| `Typing.v` | Single typing judgment `Γ ⊢ e ⋮ τ` |
| `Soundness.v` | Fundamental theorem and corollaries (safety, coverage, refinement, incorrectness) |
