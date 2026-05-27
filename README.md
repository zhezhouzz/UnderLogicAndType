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
ChoiceBase ──→ ChoicePrelude ──→ ChoiceAlgebra ──→ ChoiceLogic
    │               │                  │                │
    │               └──────────────────┴────────────────┤
    │                                                    v
    └────────→ CoreLang ─────────→ ChoiceTypeLanguage ──→ ChoiceBasicDenotation
                                                                  │
                                                                  v
                                                              Denotation
                                                                  │
                                                                  v
                                                             ChoiceTyping

LocallyNameless supports CoreLang, ChoiceTypeLanguage, and the denotation
proof files.
```

Most libraries live under `<Library>/theories/`.  `ChoicePrelude/` and
`LocallyNameless/` are top-level support libraries.  The current route splits
the old monolithic choice-type layer into three pieces:
`ChoiceTypeLanguage` for syntax and LN well-formedness,
`ChoiceBasicDenotation` for basic store/world/term atoms, and `Denotation` for
the recursive choice-type denotation.

### `ChoicePrelude/` — Shared prelude

Common infrastructure shared by the algebra, logic, and language layers.
It contains no program syntax and no dependency on `CoreLang`.

| File | Contents |
|------|----------|
| `Prelude.v` | `atom`, finite atom sets, freshness helpers, `Stale`, swap/rekey classes, and `ValueSig` |
| `Store*.v` | Polymorphic `StoreA` infrastructure, atom/lvar specializations, restriction, compatibility, and bind/rekey operations |

### `ChoiceAlgebra/` — The algebraic layer

Resources and the abstract choice algebra.  Store operations live in
`ChoicePrelude/Store.v`, so this layer no longer carries a store wrapper.

| File | Contents |
|------|----------|
| `Resource*.v` | `WorldA`/`WfWorldA`, resource restriction, algebraic order, sum/product, fiber extensions, and atom-specialized interfaces |
| `ResourceNotation.v` / `ResourceTactics.v` | Proof-facing notation and focused resource tactics |

### `ChoiceLogic/` — The logic layer

Formula syntax and the satisfaction relation, built on top of `ChoiceAlgebra`.
The logic layer is deliberately independent of `CoreLang`: program expressions
are embedded into formulas later, by `ChoiceBasicDenotation`, through logic
qualifier atoms.

| File | Contents |
|------|----------|
| `LogicQualifier.v` | Dependent-domain logic qualifier atoms over lvar-keyed worlds |
| `Formula*.v` | Formula syntax (`FAtom`, `FForall`, `FFibVars`, over/under, separating connectives), opening, scope, and `res_models` |
| `FormulaTactics.v` | Small formula-normalization tactics |

### `LocallyNameless/` — Proof support

Small Ltac support and reusable typeclasses for locally-nameless metatheory.

| File | Contents |
|------|----------|
| `Classes.v` | Parameterized LN theorem classes; opening payloads are abstract (`value` for CoreLang, `atom` for qualifiers/types) |
| `Tactics.v` | Lightweight locally-nameless proof automation |

## Naming Representation

The formalization intentionally uses two different binding representations in
different layers.

### Core language, choice types, and logic formulas: locally nameless

`CoreLang` terms and values use the standard locally-nameless (LN)
representation: free variables are `atom`s and binders are represented by
natural-number bound variables.  `ChoiceTypeLanguage` and `ChoiceLogic` now use
the same discipline for type/qualifier/formula binders.  Free logical
variables are `LVFree x`; bound coordinates are `LVBound k`.

This representation is good for syntax with real binders:

- opening and closing are structural;
- alpha-equivalence is handled by bound indices rather than by named
  substitution;
- dependent type bodies such as the codomain of `CTArrow` can be opened with a
  fresh atom using the usual `{0 ~> x}` operation.

The main cost is bookkeeping around open/close operations.  In particular,
type qualifiers may be non-closed while they sit under a binder, so
`ChoiceTypeLanguage/theories/Qualifier.v` keeps the qualifier domain explicitly.
Logic qualifiers are also dependent-domain predicates over lvar-keyed worlds.
Opening a qualifier or formula swaps `LVBound k` with `LVFree x`; the semantic
predicate swaps the incoming lworld back before interpreting it.

In short:

- Core language binders use LN with `value` payloads.
- Choice-type, qualifier, and formula binders use LN with `atom` payloads.
- Type denotation bridges terms and formulas by embedding totality, result,
  basic-typing, and qualifier predicates as shallow logic atoms.

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
| `BasicTypingProps.v` | Basic typing lemmas |
| `OperationalProps.v` | Operational semantics lemmas |

### `ChoiceTypeLanguage/` — Choice type syntax and LN metatheory

Choice type syntax layered on top of `CoreLang`, but without semantic
denotation.

Dependent choice types and qualifiers use an atom-only opening discipline:
locally-nameless bound variables in type refinements are opened with a fresh
`atom`, not an arbitrary `value`.  Accordingly, the function-application
typing rules only apply directly to arguments of the form `vfvar x`; an
arbitrary value argument can first be named with `tlete` and then applied via
that atom.  This is a formalization choice that keeps qualifier opening aligned
with store-based lookup while preserving expressiveness through let-binding.

| File | Contents |
|------|----------|
| File family | Contents |
|-------------|----------|
| `Qualifier.v` | Dependent-domain type qualifiers over lvar-keyed stores |
| `Syntax*.v` | Choice type and context syntax, erasure, lifting, lvar/fv/open facts |
| `LtyEnv*.v` / `Env.v` | Lvar-keyed type environments, atom projection, typed binder insertion |
| `WellFormed.v` / `Interface.v` | Basic qualifier/type/context well-scopedness API |
| `Notation.v` / `Sugar.v` | Public syntax notation and small derived type forms |

### `ChoiceBasicDenotation/` — Basic semantic atoms

Store/world typing, expression totality/result atoms, and the formulas that
embed CoreLang basic typing and type-qualifier semantics into `ChoiceLogic`.

| File family | Contents |
|-------------|----------|
| `StoreTyping.v` | `storeA_has_type`, `worldA_has_type`, typed extensions, and `basic_world_formula` |
| `Term*.v` | Expression evaluation, totality, result extensions, and tlet operational bridges |
| `Qualifier.v` | Interpreting type qualifiers as logic qualifiers over lworlds |
| `BasicTypingFormula.v` | Logic atoms for choice-type well-formedness and CoreLang basic typing |
| `Notation.v` / `Interface.v` | Value-specialized aliases and public re-export |

### `Denotation/` — Recursive choice-type denotation

The gas-indexed denotation `denot_ty_lvar_gas`, the atom-context wrapper
`denot_ty`, context denotation, and the current direct TLet proof.

| File family | Contents |
|-------------|----------|
| `TypeDenotation*.v` | Recursive denotation plus lvar/fv/open/saturation lemmas |
| `Context.v` | Context denotation and denotation instances |
| `TLetSupport.v` / `TLet.v` | Shared TLet support tactics and the TLet introduction theorem |
| `Notation.v` | Denotation-level notation (`m ⊨ φ`, `φ ⊫ ψ`, value-specialized aliases) |

### `ChoiceTyping/` — Paper-level typing layer

The paper-level typing infrastructure sits above the syntax and denotation
layers.  It imports `Denotation` directly instead of going through the old
ChoiceType denotation stack.

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
| `TLetDirect.v` / `TLetDenotation.v` | Direct bridge from the typing TLet case to `Denotation.TLet` |
| `SoundnessDirect.v` / `Soundness.v` | Current soundness entry points on the new denotation route |
