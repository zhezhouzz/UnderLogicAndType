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

The formalization is split into several libraries with the following dependency
shape:

```
ChoicePrelude ──→ ChoiceAlgebra ──→ ChoiceLogic ──┐
      │                                            │
      └────────────────→ CoreLang ────────────────┤
                                                    v
                                               ChoiceType

CoreLang.Syntax ──→ LocallyNameless.Classes
LocallyNameless ──→ CoreLang / ChoiceType instance and proof files
```

Most libraries live under `<Library>/theories/`.  `ChoicePrelude/` and
`LocallyNameless/` are top-level support libraries.  `ChoicePrelude` does not
depend on `CoreLang`; it only provides abstract infrastructure such as `atom`,
`aset`, `ValueSig`, stores, and freshness helpers.  `LocallyNameless` contains
reusable LN tactics plus parameterized LN typeclasses.  The typeclass file
currently imports `CoreLang.Syntax` for value-specific substitution classes;
payload-independent opening is still parameterized so qualifiers can open with
atoms while CoreLang opens with values.

### `ChoicePrelude/` — Shared prelude

Common infrastructure shared by the algebra, logic, and language layers.
It contains no program syntax and no dependency on `CoreLang`.

| File | Contents |
|------|----------|
| `Prelude.v` | `atom`, finite atom sets, freshness helpers, `Stale`, and `ValueSig` |
| `MapFilterDom.v` | Reusable `dom`/`filter` lemmas for finite maps |
| `Store.v` | Polymorphic map operations, atom-keyed stores, restriction, compatibility, and renaming |

### `ChoiceAlgebra/` — The algebraic layer

Resources and the abstract choice algebra.  Store operations live in
`ChoicePrelude/Store.v`, so this layer no longer carries a store wrapper.

| File | Contents |
|------|----------|
| `Prelude.v` | Re-exports the shared prelude |
| `Resource.v` | Resources (worlds), resource operations, partial order |
| `ChoiceAlgebra.v` | Abstract choice algebra class; `WfWorld` instance |

Examples live in `ChoiceAlgebra/examples/`.

### `ChoiceLogic/` — The logic layer

Formula syntax and the satisfaction relation, built on top of `ChoiceAlgebra`.
The logic layer is deliberately independent of `CoreLang`: program expressions
are embedded into formulas later, by `ChoiceType`, through logic qualifier
atoms.

| File | Contents |
|------|----------|
| `Prelude.v` | Re-exports `ChoiceAlgebra` and `ChoicePrelude` |
| `LogicQualifier.v` | Logic-level qualifier atoms and `logic_qualifier_denote` |
| `Formula.v` | Formula syntax (`FAtom`, `FForall`, `FExists`, `FFib`, …), formula renaming, and `res_models` |
| `ChoiceLogicProps.v` | Key theorems (modality monotonicity, closure, collapse, adjunction) |

Examples live in `ChoiceLogic/examples/`.

### `LocallyNameless/` — Proof support

Small Ltac support and reusable typeclasses for locally-nameless metatheory.

| File | Contents |
|------|----------|
| `Classes.v` | Parameterized LN theorem classes; opening payloads are abstract (`value` for CoreLang, `atom` for qualifiers/types) |
| `Tactics.v` | Lightweight locally-nameless proof automation |

## Naming Representation

The formalization intentionally uses two different binding representations in
different layers.

### Core language and choice types: locally nameless

`CoreLang` terms and values use the standard locally-nameless (LN)
representation: free variables are `atom`s and binders are represented by
natural-number bound variables.  `ChoiceType` also uses LN for dependent
choice types and type qualifiers, because dependent refinements need to refer
to the result coordinate bound by a type former.

This representation is good for syntax with real binders:

- opening and closing are structural;
- alpha-equivalence is handled by bound indices rather than by named
  substitution;
- dependent type bodies such as the codomain of `CTArrow` can be opened with a
  fresh atom using the usual `{0 ~> x}` operation.

The main cost is bookkeeping around open/close operations.  In particular,
type qualifiers may be non-closed while they sit under a binder, so
`ChoiceType/theories/Qualifier.v` keeps explicit bound-variable metadata.

### Choice logic: explicit names with cofinite semantics

`ChoiceLogic` formulas use explicit atom binders:

```coq
FForall x p
FExists x p
FFib x p
```

The atom `x` in `FForall x p` is only a syntactic representative.  The
satisfaction relation gives it a cofinite interpretation: to model a universal
or existential formula, the representative is renamed to every sufficiently
fresh atom outside a finite avoidance set.  This is implemented by
`formula_rename_atom` and exposed by the smart constructor/spec
`fresh_forall`.

This design was chosen after weighing two alternatives.

Using LN for formulas would make binders more standard, but it would also force
formula opening to reach into every embedded atom.  Since type denotation needs
program expressions such as `tapp y x` to depend on formula binders, an LN
formula representation would either make `ChoiceLogic` depend directly on
`CoreLang`, or require shifting embedded `tm`/`value` syntax whenever a new
formula binder is introduced.  That substantially complicates the logic layer.

Using explicit names keeps `ChoiceLogic` independent from `CoreLang` and keeps
logic qualifier atoms shallow.  Program expressions are converted to logic
qualifier atoms only in `ChoiceType/theories/Denotation.v`.  The cost is that
we must define named renaming for stores, worlds, qualifiers, and formulas, and
we use cofinite semantics to recover the intended alpha-invariant behavior of
quantifiers.

In short:

- Core language binders and choice-type binders use LN, where structural
  opening is the right tool.
- Choice-logic binders use explicit atoms plus cofinite renaming, preserving a
  clean dependency boundary between logic and programs.
- Type denotation bridges the two worlds by choosing syntactic binder
  representatives with `fresh_forall`; these names are not semantically
  privileged, because formula satisfaction immediately interprets them through
  cofinite renaming.

### `CoreLang/` — The programming language

A deterministic call-by-value λ-calculus with unary primitive operations and
boolean pattern matching, in locally-nameless representation.

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
| `SmallStep.v` | Deterministic small-step operational semantics (`→*`) |
| `Sugar.v` | Small deterministic derived forms used by examples |
| `Properties.v` | Basic metatheory entry points |
| `LocallyNamelessProps.v` | Locally-nameless lemmas for values and terms |
| `LocallyNamelessExtra.v` | Additional LN lemmas imported from earlier developments |
| `LocallyNamelessInstances.v` | CoreLang instances for the shared LN classes |
| `BasicTypingProps.v` | Basic typing lemmas |
| `OperationalProps.v` | Operational semantics lemmas |

### `ChoiceType/` — Choice types and denotation

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
| `Prelude.v` | Imports `CoreLang` and `ChoiceLogic`; fixes ChoiceType notations to CoreLang `value`s |
| `Qualifier.v` | Type-level shallow qualifiers (`type_qualifier`); interpretation `qual_interp` |
| `QualifierBridge.v` | Lifting closed type qualifiers into logic qualifier atoms |
| `QualifierInstances.v` | Type-qualifier instances for the shared LN classes |
| `Syntax.v` | Choice type syntax (`choice_ty`, `ctx`); erasure, lifting, atom opening/swap |
| `Sugar.v` | Derived type forms such as over/under/precise refinements and unary primop types |
| `LocallyNamelessInstances.v` | Choice-type instances for the shared LN classes |
| `BasicTyping.v` | Basic domain/LN checks for qualifiers, types, and tree-like contexts |
| `Denotation.v` | Type denotation `⟦τ⟧ e` and context denotation `⟦Γ⟧` as formulas |

### `ChoiceTyping/` — Unstable typing layer

The paper-level typing infrastructure is kept outside `ChoiceType` while its
definitions are still changing.  `ChoiceType` retains `BasicTyping.v` because
denotation is expected to depend on basic domain/LN well-scopedness.

The current declarative rules follow the paper's bunched presentation more
closely:

- every typing constructor carries an explicit `choice_typing_wf` side
  condition for the conclusion, packaging context/type well-formedness together
  with erased Core basic typing;
- constants have precise refinement types, i.e. the intersection of over and
  under refinements at the same qualifier;
- primitive operations remain unary, their arguments must be variables, their
  argument types are over-approximate, and their result types are precise;
- there is no separate `T-AppOpD`, because the over-approximate argument type
  is the uniform interface for primitive application;
- `T-Let` and `T-LetD` use the standard additive and separating bunched forms,
  without the older context-hole/`ToOver` premise;
- boolean `tmatch` is split into three rules: both branches reachable, true
  only, and false only.  Unreachable branches are still required to be
  well-typed after erasure, but they do not contribute a ChoiceTyping
  context/type branch.

| File | Contents |
|------|----------|
| `WellFormed.v` | Well-formedness and nonemptiness judgments |
| `Auxiliary.v` | Context-level helper relations such as subtype context lifting |
| `PrimOpContext.v` | Unary primitive-operation signatures and well-formedness |
| `Typing.v` | Single typing judgment `Γ ⊢ e ⋮ τ` |
| `Soundness.v` | Fundamental theorem and corollaries (safety, coverage, refinement, incorrectness) |
