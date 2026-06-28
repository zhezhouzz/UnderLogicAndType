# UnderLogicAndType

Rocq formalization for the context-logic/context-type development behind
*Underapproximate Types*.

The current `main` branch is tagged `first-complete-proof`: this is the first
version where the direct Fundamental theorem and denotational soundness
theorem are fully proved for the current core system.

## Status

- Primitive operations are supplied by an explicit context `Φ : primop_ctx`.
  The abstract soundness theorem assumes `wf_primop_ctx Φ`; the current
  graph-based instance is `concrete_Φ` with theorem `concrete_Φ_wf`.  The
  concrete primitive context includes deterministic graph-precise operators
  `eq0`, `plus1`, and `minus1`, plus nondeterministic generators `boolGen` and
  `natGen`.
- The main typing judgment is `has_context_type Φ Σ Γ e τ`.
- The Fundamental theorem is:

  ```coq
  Theorem Fundamental Φ :
    wf_primop_ctx Φ ->
    forall Σ Γ e τ,
      has_context_type Φ Σ Γ e τ ->
    ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
  ```

  The concrete wrapper is `concrete_Fundamental` in
  `ContextTyping/theories/SoundnessConcrete.v`.

- The closed-program denotational soundness theorem is:

  ```coq
  Theorem denotational_soundness Φ :
    wf_primop_ctx Φ ->
    forall e τ,
      has_context_type Φ ∅ CtxEmpty e τ ->
    forall x,
      exists mres,
        closed_result_world_of e x mres /\
        mres ⊨ ty_denote ({[x := erase_ty τ]}) τ (tret (vfvar x)).
  ```

  The concrete wrapper is `concrete_denotational_soundness`.

- FixD is not part of the compiled system.

## Dependencies

| Package | Version |
|---------|---------|
| [Rocq](https://rocq-prover.org/) | 9.1.0 |
| [rocq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) | dev.2026-01-23 |
| [coq-hammer](https://github.com/lukaszcz/coqhammer) | 1.3.2+9.1 |

## Setup

The recommended setup uses opam:

```bash
opam switch create with-rocq-1 ocaml-base-compiler
eval $(opam env --switch=with-rocq-1)

opam repo add rocq-released https://github.com/rocq-archive/opam-rocq-archive/releases/download/0.0.1/rocq-released-repo.tar.gz
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam/-/raw/master/index

opam install rocq-core.9.1.0 rocq-stdpp.dev.2026-01-23 coq-hammer.1.3.2+9.1
```

## Building

Generate the makefile after changing `_CoqProject`:

```bash
rocq makefile -f _CoqProject -o Makefile
```

Build everything:

```bash
make
```

During proof work, prefer focused checks with a 50 second timeout:

```bash
timeout 50s make ContextTyping/theories/Soundness.vo
timeout 50s make Denotation/theories/Context.vo
```

For slow or unclear proof failures, run the corresponding Rocq command with
`-time` rather than repeatedly extending timeouts.

## Repository Structure

The dependency shape is:

```text
ContextBase -> ContextStore -> ContextAlgebra -> ContextLogic
      \             \              \              \
       \             \--------------\--------------\
        v                                           v
      CoreLang -> ContextTypeLanguage -> ContextBasicDenotation
                                                   |
                                                   v
                                               Denotation
                                                   |
                                                   v
                                             ContextTyping
```

### Core Libraries

- `ContextBase`: atoms, logical variables, finite sets, and shared tactics.
- `ContextStore`: polymorphic store operations and atom/lvar specializations.
- `ContextAlgebra`: worlds, resources, restriction, fibers, product, sum, and
  result/fiber extensions.
- `ContextLogic`: formula syntax, binder-aware `FBWand`, satisfaction, Kripke
  monotonicity, and reviewer-facing BI compatibility facts.

### Language and Denotation

- `CoreLang`: call-by-value language with nondeterministic primitive results,
  locally nameless syntax, basic typing, small-step semantics, and
  instantiation.  The current base types include `Unit`, `Bool`, `Nat`, `Tree`,
  and fixed `List` values over Rocq's `list nat`.
- `ContextTypeLanguage`: context types, contexts, qualifiers, erasure,
  locally nameless opening, and well-formedness.
- `ContextBasicDenotation`: basic semantic atoms for stores, worlds, term
  totality/results, qualifier formulas, and relevant environments.
- `Denotation`: recursive context-type denotation, context denotation,
  result-equivalence transport, TLet support, constants, and primitive
  operation support.
- `ContextTyping`: primitive-operation signatures and instances, context
  typing rules, the parameterized direct Fundamental proof, and concrete
  soundness wrappers.

## Proof Engineering Conventions

- Normalize at proof boundaries: unfold and simplify erasure, relevant
  environments, `ctx_erasure_under`, `lty_env_open_one`, and formula/type opens
  before extracting helper lemmas.
- Qualifier top is domain-indexed.  Use `qual_top_on D` or the standard
  `qual_top` notation for the result binder domain; do not use an empty-support
  top qualifier.  Empty support would make underapproximate coverage vacuous.
- `CTOver` and `CTUnder` result bodies are typed: the qualifier atom is paired
  with the result slot's basic typing formula, so `CTUnder b qual_top` covers
  all and only values of base type `b`.
- Keep helper statements semantic and short. If a premise contains only
  syntactic noise, normalize earlier or move the fact to the lower layer.
- Prefer existing `better_*` solvers for set/store side conditions. For slow
  hotspots, use a small local deterministic tactic or a lower-level lemma.
- Avoid anonymous `admit` and avoid long chains of one-use `assert`/`pose`
  facts. Generalize repeated proof patterns into lower-layer lemmas.
- If timing diagnostics repeat, stop after four rounds and reassess the proof
  shape or split the file.

## Notes

Durable explanations should live either in Rocq comments near the
definitions/theorems they justify, or in this README when they affect
repository-level workflow.  Temporary analysis files should not be committed.
