# Proof README

This file is a proof-oriented guide to the checked `main` branch.  It is meant
to complement `README.md`: the main README explains how to build the project,
while this document explains how the proof is organized and where to look when
checking or modifying a theorem.

The current proof has no `Admitted.`/`admit.` in compiled Rocq files on
`main`.  The top-level results are in
`ContextTyping/theories/Soundness.v`.

## Implementation/Paper Alignment Notes

This repository intentionally differs from the paper presentation in a few
places.  Keep these in mind when comparing statements.

- Primitive operations are parameterized in the abstract proof.  The concrete
  checked instance is `concrete_Φ`, proved well formed by `concrete_Φ_wf`.
- The core semantics is nondeterministic-ready.  In particular, `boolGen` and
  `natGen` are concrete generator primitives with `Unit` arguments.
- Concrete primitive result types are graph precise.  Deterministic primitives
  use their exact input/output graph; generators use graph qualifiers whose
  graphs enumerate all boolean or natural results.
- Qualifier top is not empty-support top.  `qual_top_on D` carries an explicit
  support domain, and the usual `qual_top` notation observes the result binder.
  This is necessary because an empty-support qualifier would impose no
  result-slot constraint.
- The type denotation for `CTOver b φ` and `CTUnder b φ` interprets the result
  refinement in the typed carrier for `b`: the result body is
  `FOver`/`FUnder` of `FAnd (FAtom φ) result_basic_typing_formula`.
  Consequently `CTUnder b qual_top` covers all values of base type `b`, not all
  syntactic values.
- The implementation has additional infrastructure compared with the paper,
  including `FPersist`/`CTPersist`, `FExists`, result-first Arrow/Wand
  denotation, and fixed tree/list support in the core language.

## Quick Checks

Use focused checks while editing:

```sh
timeout 50s make TIMED=1 Denotation/theories/TypeDenote.vo
timeout 50s make TIMED=1 Denotation/theories/TypeEquiv.vo
timeout 50s make TIMED=1 ContextTyping/theories/Soundness.vo
```

Full validation:

```sh
timeout 180s make TIMED=1
rg -n "Admitted\.|admit\." -g '*.v' .
```

If a proof becomes slow, rerun the failing `.vo` build with Rocq `-time` and
locate the expensive sentence before rewriting the proof.

## Top-Level Theorems

All abstract soundness theorems live inside `Section WithPrimopContext` in
`ContextTyping/theories/Soundness.v`, parameterized by a primitive-operation
context `Φ` and a proof `wf_primop_ctx Φ`.

The direct Fundamental theorem is:

```coq
Theorem Fundamental (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) :
  has_context_type Φ Σ Γ e τ ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
```

The closed-program denotational soundness theorem is:

```coq
Theorem denotational_soundness e τ :
  has_context_type Φ ∅ CtxEmpty e τ ->
  forall x,
    exists mres : WfWorldT,
      closed_result_world_of e x mres /\
      mres ⊨ ty_denote ({[x := erase_ty τ]} : gmap atom ty) τ
        (tret (vfvar x)).
```

The concrete primitive context is supplied in
`ContextTyping/theories/PrimOpConcreteContext.v`; the concrete wrappers are:

```coq
Theorem concrete_Fundamental Σ Γ e τ : ...
Theorem concrete_denotational_soundness e τ : ...
```

## Dependency Shape

The proof is intentionally layered.  When possible, fix a failed proof at the
lowest layer that states the missing fact cleanly.

```text
ContextBase
  -> ContextStore
  -> ContextAlgebra
  -> ContextLogic
  -> CoreLang
  -> ContextTypeLanguage
  -> ContextBasicDenotation
  -> Denotation
  -> ContextTyping
```

The most common mistake while editing is to prove a store, resource, syntax,
or open-normalization fact in `Soundness`.  If the statement does not mention a
typing derivation, it usually belongs lower.

## Lemma Families

The following inventory follows the same style as the paper proof appendix:
first the reusable semantic lemmas, then the denotation transport lemmas, then
the Fundamental cases.

### Formula And Resource Semantics

Files:

- `ContextAlgebra/theories/Resource*.v`
- `ContextLogic/theories/FormulaSemantics.v`
- `ContextLogic/theories/FormulaConnectives.v`
- `ContextLogic/theories/FormulaConnectivesHigher.v`
- `ContextLogic/theories/FormulaFiberwise.v`
- `ContextLogic/theories/FormulaWorldExtension.v`

Key facts:

- `res_models_kripke`, `res_models_projection`,
  `res_models_minimal_on`: Kripke/projection principles for formulas.
- `res_models_star_iff`, `res_models_plus_iff`,
  `res_models_fbwand_*`: BI-style connectives and bounded wand.
- `res_models_forall_*`: locally-nameless quantified formula rules.
- `res_models_persist_*` and `persistent_formula_*`: logic-level
  persistency.
- `fiberwise_joinable_on_*`: aggregation of fiber-local proofs back to a
  whole world for the formula fragments that support it.

These lemmas deliberately distinguish three notions that are easy to conflate:
resource subset, projection/Kripke order, and fiber equality on an observation
set.

### Atoms And Basic Denotation

Files:

- `ContextQualifier/theories/Qualifier.v`
- `ContextLogic/theories/FormulaAtom.v`
- `ContextBasicDenotation/theories/Term*.v`
- `ContextBasicDenotation/theories/BasicTyping*.v`
- `ContextBasicDenotation/theories/Qualifier.v`
- `ContextBasicDenotation/theories/RelevantEnv.v`

Key facts:

- `FAtom q` is the only exact store-level qualifier atom.
- `FFiberAtom q` is sugar for `FFibVars (qual_vars q) (FAtom q)`.
- `res_models_atom_exact_iff` and
  `res_models_FFiberAtom_store_iff` expose atom semantics.
- `expr_total_formula`, `expr_result_formula_at`, and
  `expr_result_extension_witness` connect operational results to worlds.
- `RelevantEnv.v` controls the environment restriction used by type
  denotation.

This layer is the right place for facts about term result graphs, result
extensions, basic typing formulas, and qualifier formulas.

### Type Denotation

Files:

- `Denotation/theories/TypeDenote.v`
- `Denotation/theories/ResultFirstOpen.v`
- `Denotation/theories/DenotationSetMapFacts.v`

The central definition is:

```coq
Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT := ...
```

Each denotation starts with:

```coq
FAnd (ty_guard_formula (relevant_env Σ τ e) τ e) ...
```

The guard proves well-formedness of the context type, a basic world, erased
basic typing of the term, and totality of the term.  The recursive body uses
the result-first shape for result-sensitive types:

- `CTOver` / `CTUnder`: quantify over a result slot and then check the opened
  over/under body.  The body is typed: `over_result_body b φ` and
  `under_result_body b φ` combine the refinement atom with
  `result_basic_typing_formula b`.
- `CTSum`: quantify over a result slot and split the result resource with
  `FPlus`.
- `CTArrow` / `CTWand`: first quantify over the function result, then check
  `arrow_value_denote_gas_with` or `wand_value_denote_gas_with` for `ret f`.
- `CTPersist`: quantify over the value result and wrap the inner denotation in
  `FPersist`.

Important support lemmas:

- `formula_open_env_ty_denote_gas`
- `ty_denote_gas_env_agree_on`
- `ty_denote_gas_lvars_subset`
- `ty_denote_gas_fv_subset`
- `ty_denote_gas_scope_of_guard`

Normalize opens, relevant environments, and inserted environments before using
or stating higher-level helper lemmas.

### Term Transport, Result Extension, And Let

Files:

- `Denotation/theories/TypeEquivCore.v`
- `Denotation/theories/TypeEquivTerm*.v`
- `Denotation/theories/TypeEquivFiber*.v`
- `Denotation/theories/TypeEquivBody.v`
- `Denotation/theories/TypeEquivArrow.v`
- `Denotation/theories/TypeEquivWand.v`
- `Denotation/theories/TypeEquivTLet.v`
- `Denotation/theories/TypeEquiv.v`

These files prove that denotation is stable under the term transformations
used by typing rules:

- `ty_denote_gas_tm_equiv`: ordinary term equivalence transport.
- `ty_denote_gas_result_alias_at`: replacing a term by a fresh result slot.
- `ty_denote_gas_result_ext`: extending a world with all results of a term.
- `tlet_intro_denotation`: equivalence between a let body opened with a result
  slot and the corresponding `tlet`.
- `ty_denote_gas_drop_fresh_ext` and restrict/delete helpers: remove fresh
  worlds or variables after a denotation proof.

`TypeEquivArrow.v` and `TypeEquivWand.v` handle the result-first function
shape.  Their proofs open the outer function result first, then the argument
world, then the result body.  Helper statements should expose these normalized
worlds and not raw `formula_open` noise.

### Constants And Primitive Operations

Files:

- `Denotation/theories/ConstDenote*.v`
- `ContextTyping/theories/PrimOpContext.v`
- `ContextTyping/theories/PrimOpConcreteContext.v`

The constant-denotation lemmas show that closed constants inhabit their precise
refinement types.  Primitive operations are abstracted by `primop_ctx`; the
soundness theorem assumes `wf_primop_ctx Φ`.

`PrimOpConcreteContext.v` instantiates the abstract assumption with
`concrete_Φ` and proves:

```coq
Theorem concrete_Φ_wf : wf_primop_ctx concrete_Φ.
```

The current concrete context uses graph-precise result qualifiers for all
primitive operations:

- `eq0 : Nat -> Bool`, graph `ν = (x =? 0)`;
- `plus1 : Nat -> Nat`, graph `ν = S x`;
- `minus1 : Nat -> Nat`, graph `ν = pred x`;
- `boolGen : Unit -> Bool`, graph ranges over all boolean results;
- `natGen : Unit -> Nat`, graph ranges over all natural results.

The abstract soundness proof never unfolds these concrete graphs.  It only uses
the `wf_primop_ctx Φ` interface.  All primitive-specific reasoning is confined
to `PrimOpConcreteContext.v`.

### Context Denotation And Context Algebra

Files:

- `Denotation/theories/Context.v`
- `ContextTyping/theories/Typing.v`

`ctx_denote_under` combines the erased basic-world constraint with the
separation/choice structure of context types.

Important facts:

- `ctx_denote_under_minimal`
- `ctx_denote_bind_from_arg_denotation`
- `ctx_denote_under_star_elim`
- `ctx_denote_under_sum_elim`
- `ctx_denote_under_star_intro_product`
- `ctx_denote_under_star_self_of_persistent`

The persist-intro typing rule is value-only.  Its denotational support is in
`ContextTyping/theories/SoundnessPersist.v`.

### Fundamental Cases

Files:

- `ContextTyping/theories/SoundnessLam.v`
- `ContextTyping/theories/SoundnessApp.v`
- `ContextTyping/theories/SoundnessMatch.v`
- `ContextTyping/theories/SoundnessFix*.v`
- `ContextTyping/theories/SoundnessPersist.v`
- `ContextTyping/theories/Soundness.v`

`Soundness.v` dispatches on the typing derivation:

```coq
Theorem Fundamental ... :
  has_context_type Φ Σ Γ e τ ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
```

The case files prove the large semantic steps:

- Variables/constants/subsumption are discharged directly in `Soundness.v` and
  denotation/context helper files.
- Let/LetD use result extension and `tlet_intro_denotation`.
- Lam/App and LamD/AppD use result-first Arrow/Wand opening lemmas.
- Match splits branch worlds with `CTSum` and branch-refinement helpers.
- Fix is split across base, apply, self, and orchestration files.
- Persist intro uses `persistent_formula (ctx_denote_under Σ Γ)` to introduce
  `CTPersist` for values.

## Suggested Reading Order

1. `ContextLogic/theories/FormulaSemantics.v`
2. `ContextLogic/theories/FormulaConnectives*.v`
3. `ContextBasicDenotation/theories/TermOpen.v`
4. `Denotation/theories/TypeDenote.v`
5. `Denotation/theories/TypeEquiv.v`
6. `Denotation/theories/Context.v`
7. `ContextTyping/theories/Typing.v`
8. `ContextTyping/theories/Soundness.v`

For function cases, read `ResultFirstOpen.v` before `TypeEquivArrow.v`,
`TypeEquivWand.v`, `SoundnessLam.v`, and `SoundnessApp.v`.

For persistence, read `FormulaConnectivesHigher.v`, `TypePersist*.v`,
`Typing.v`, and `SoundnessPersist.v`.

## Proof Engineering Rules

- Normalize first.  Opened denotations should be simplified at proof
  boundaries, especially `formula_open`, `lty_env_open_one`, `cty_open`,
  `tm_open`, `erase_ty`, and `relevant_env`.
- Keep set/map/store facts low.  If a proof only manipulates stores,
  restrictions, domains, or fibers, it does not belong in a soundness case.
- Do not silently replace resource subset, projection order, and fiber
  equality.  They serve different semantic roles.
- Keep helper statements reviewer-readable.  If the statement is longer than
  the proof, consider inlining it or moving the real reusable fact lower.
- Prefer applying lemmas with explicit arguments over `apply ...; exact ...`
  chains that create avoidable subgoals.
- After editing `_CoqProject`, regenerate `Makefile`.

## Debugging Checklist

When a soundness case breaks:

1. Check whether the failing goal still contains raw opens or unnormalized
   inserted environments.  If so, normalize earlier.
2. Check whether the fact is actually syntax/basic-denotation/resource-level.
   Move or reuse a lower-level lemma if possible.
3. If the goal involves term results, identify whether it needs result alias,
   result extension, `tlet_intro_denotation`, or ordinary term equivalence.
4. If the goal involves Arrow/Wand, open the outer result slot before the
   argument slot.
5. If a solver is slow, clear irrelevant hypotheses or extract the set/store
   side condition into a deterministic lemma.
