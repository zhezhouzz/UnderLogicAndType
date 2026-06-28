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

- The checked core language is smaller than the language used in the paper
  examples.  It has `Unit`, `Bool`, and `Nat`; unary primitive operations;
  function application; `let`; and a boolean-specific match.  It does not
  currently include the paper's general datatype match, fixed tree/list
  syntax, binary operator syntax, or n-ary primitive operator judgment.
- Primitive operations are parameterized in the abstract proof.  The concrete
  checked instance is `concrete_Φ`, proved well formed by `concrete_Φ_wf`.
- The core semantics is nondeterministic-ready.  In particular, `boolGen` and
  `natGen` are concrete generator primitives with `Unit` arguments.
- Concrete primitive result types are graph precise.  Deterministic primitives
  use their exact input/output graph; generators use graph qualifiers whose
  graphs enumerate all boolean or natural results.  This is not the same
  presentation as the paper's persistent generator-function types, although
  the proof has separate `FPersist`/`CTPersist` infrastructure.
- Qualifiers are semantic predicates with explicit support sets, not the
  paper's first-order qualifier syntax.  This is why the implementation
  records qualifier support explicitly and why several paper-side logical
  connectives are represented as Rocq-level predicate structure instead of
  syntax.
- Qualifier top is not empty-support top.  `qual_top_on D` carries an explicit
  support domain, and the usual `qual_top` notation observes the result binder.
  This is necessary because an empty-support qualifier would impose no
  result-slot constraint.
- The context logic has set-indexed fiber quantification `FFibVars D P`.
  The paper presents this idea as a binding-reference/fiber connective.  The
  implementation form is more general but less syntactically close to the
  prose notation.
- The compiled formula syntax does not include `FExists`.  Earlier drafts and
  some paper discussion mention existential formulas, but the checked
  denotation path on `main` does not require them.
- The type denotation for `CTOver b φ` and `CTUnder b φ` interprets the result
  refinement in the typed carrier for `b`: the result body is
  `FOver`/`FUnder` of `FAnd (FAtom φ) result_basic_typing_formula`.
  Consequently `CTUnder b qual_top` covers all values of base type `b`, not all
  syntactic values.
- The checked type denotation follows the nondeterministic, result-first shape:
  `CTSum`, `CTArrow`, `CTWand`, and `CTPersist` first bind the result of the
  scrutinized term/function value and then state the branch/value obligation.
  This corresponds to the later nondeterministic design rather than the
  simpler deterministic presentation.
- The implementation has additional proof infrastructure compared with the
  paper core, including `FPersist`/`CTPersist`, a value-only persistence intro
  rule, fiberwise joinability lemmas, result-first Arrow/Wand support, and
  concrete graph-precise primitive contexts.
- Paper Section 5 case-study programs are not part of the current compiled
  source on `main`.  The proof currently establishes the generic soundness
  theorem for the checked core calculus and concrete primitive context, not the
  full collection of paper examples.

## Paper-To-Proof Correspondence

This section lists the main definitions and theorems that appear in the paper
and where they live in the checked Rocq development.  When the proof uses an
equivalent implementation form rather than the exact paper syntax, the
equivalence or bridge theorem is listed explicitly.

| Paper item | Checked Rocq counterpart | Status |
| --- | --- | --- |
| Core values/terms and operational semantics | `CoreLang/theories/SyntaxCore.v`, `SmallStep.v`, `OperationalResults.v` | Checked for the smaller core: unit, booleans, naturals, unary primops, application, `let`, and boolean match. |
| Base/basic typing | `CoreLang/theories/BasicTyping.v`, `BasicTypingProps.v` | Checked. |
| Qualifier syntax | `ContextQualifier/theories/Qualifier.v` | Implemented semantically as `tqual D (Store -> Prop)` with explicit support, not as a first-order syntax tree. |
| Qualifier top | `qual_top_on D` in `ContextQualifier/theories/Qualifier.v`; standard notation `qual_top` | Checked with explicit support.  This intentionally differs from an empty-support top. |
| Context type syntax | `ContextTypeLanguage/theories/SyntaxCore.v` | Checked, with paper types plus proof extensions such as `CTPersist`. |
| `O[b | φ]`, `U[b | φ]`, precise type | `over_ty`, `under_ty`, `precise_ty`; notations `{: b | φ }`, `[: b | φ ]` | Checked definitions. |
| Type contexts | `ctx` in `ContextTypeLanguage/theories/SyntaxCore.v`; notations `Emp`, `x ∷ τ`, `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` | Checked definitions. |
| Context logic formulas | `Formula` in `ContextLogic/theories/FormulaSyntaxCore.v` | Checked, but `FExists` is absent on `main`. |
| Formula satisfaction | `res_models` in `ContextLogic/theories/FormulaSemantics.v`; notation `m ⊨ P` | Checked. |
| Entailment and formula equivalence | `entails`, `formula_equiv`; notations `P ⊫ Q`, `P ⊣⊢ Q` | Checked. |
| Binding reference/fiber connective `∀M` | `FFibVars D P`; notation `fib D |> P` | Checked set-indexed implementation of the paper connective. |
| Ordinary universal formula | `FForall P`; notation `∀. P` | Checked. |
| Ordinary existential formula | Paper syntax only | Not present in compiled formula syntax. |
| Demonic/angelic formula modalities | `FOver P`, `FUnder P`; notations `over P`, `under P` | Checked. |
| Additive/multiplicative connectives | `FAnd`, `FOr`, `FImpl`, `FStar`, `FBWand`, `FPlus`; notations `∧`, `∨`, `→`, `∗`, `-∗[d]`, `⊕` | Checked. |
| Persistent modality `□P` | `FPersist P`; notation `□ P` | Checked.  The projection/singleton implementation is bridged by `res_models_persist_iff`, `persistent_formula_persist`, and related persistence laws. |
| Persistent formula laws | `persistent_formula`, `persistent_formula_equiv_persist`, `persistent_star_self`, `persistent_star_and` | Checked theorems. |
| Type denotation `[[τ]]Σ e` | `ty_denote_gas`, `ty_denote`; notations `⟦ty⟧[Σ, gas] τ e`, `⟦ty⟧[Δ] τ e` | Checked.  Uses the nondeterministic result-first shape. |
| Type context denotation `[[Γ]]Σ` | `ctx_denote_under`, `ctx_denote`; notations `⟦ctx⟧[Σ] Γ`, `⟦ctx⟧ Γ` | Checked. |
| Guard in type denotation | `ty_guard_formula`, `ty_static_guard_formula`; notations `guard[Σ] τ e`, `static_guard[Σ] τ e` | Checked. |
| Paper `mstep(e, x)` result graph | `expr_result_formula_at D e x`; compatibility wrapper `expr_result_formula e x` | Checked.  The proof tracks the observation domain explicitly. |
| Typed Over/Under result body | `over_result_body b φ`, `under_result_body b φ` | Checked implementation correction: refinement atom is paired with result-slot basic typing. |
| Nondeterministic result-first Arrow/Wand/Sum denotation | `arrow_value_denote_gas_with`, `wand_value_denote_gas_with`, branches of `ty_denote_gas` | Checked. |
| Persistent type `□τ` | `CTPersist τ`; notation `□ τ`; branch of `ty_denote_gas` | Checked. |
| Persistence intro typing rule | `CT_PersistIntro` in `ContextTyping/theories/Typing.v` | Checked soundness case in `SoundnessPersist.v`. |
| Context duplication for persistent bindings | `ctx_bind_persist_star_dup` | Checked theorem. |
| Primitive operator context | `primop_ctx`, `primop_sig`, `wf_primop_ctx` | Checked unary abstraction, not paper's n-ary presentation. |
| Concrete primitive context | `concrete_Φ`, `concrete_Φ_wf` | Checked.  Concrete result qualifiers are graph precise. |
| Fundamental theorem | `Fundamental` in `ContextTyping/theories/Soundness.v` | Checked theorem. |
| Closed-program denotational soundness | `denotational_soundness`; concrete wrapper `concrete_denotational_soundness` | Checked theorem. |

### Typing Rule Correspondence

The paper presents typing rules as inference rules.  In the proof, the main
rules are constructors of `has_context_type` in
`ContextTyping/theories/Typing.v`, printed in the file with the judgment
notation `Φ ⊢ᶜ [Σ; Γ] e ⋮ τ`; their soundness cases are proved in
`ContextTyping/theories/Soundness*.v`.

| Paper rule/form | Rocq rule/form | Notes |
| --- | --- | --- |
| `T-Var` | `CT_Var` | Checked for singleton context `x ∷ τ`. |
| `T-Const` | `CT_Const` | Constants have `const_precise_ty c`. |
| `T-Sub` | `CT_Sub` with premise `sub_type_under Σ Γ τ1 τ2` | Semantic subtyping is a definition, not a separate syntactic judgment. |
| `T-CtxSub` | `CT_CtxSub` with premise `ctx_sub_under Σ X Γ1 Γ2` | Context subtyping is semantic/projection-based. |
| `T-Let` | `CT_Let` | Checked. |
| Separating let | `CT_LetD` | Checked extension for separating contexts. |
| `T-Lam` | `CT_Lam` | Checked for ordinary function type `τx → τ`. |
| Separating lambda | `CT_LamD` | Checked for `τx -∗ τ`. |
| Function application | `CT_AppFun` | Checked, but the argument is a fresh atom variable `vfvar x`, not an arbitrary value expression. |
| Separating function application | `CT_AppFunD` | Checked with the same fresh-atom argument restriction. |
| Fixpoint rule | `CT_Fix` | Checked ordinary recursive function rule.  `FixD` is not compiled. |
| Primitive operation application | `CT_AppOp` | Checked unary primop rule; the paper's n-ary rule is represented by the unary `primop_sig` abstraction. |
| Pattern match | `CT_MatchBoth`, `CT_MatchTrueOnly`, `CT_MatchFalseOnly` | Checked boolean-only match split into reachable-branch variants, not the paper's general datatype match rule. |
| Persistent intro | `CT_PersistIntro` | Checked value-only rule corresponding to the paper's persistence-introduction idea. |

The semantic relations used by `CT_Sub` and `CT_CtxSub` are:

```coq
sub[Σ; Γ](τ1, τ2)
ctxsub[Σ; X](Γ1, Γ2)
```

These are intentionally semantic definitions: the proof does not introduce a
separate syntactic subtyping derivation and then prove it sound.

Important theorem-level bridges for equivalent definitions:

- `res_models_persist_iff` states the operational meaning of `□P` in terms of
  singleton projection and satisfaction of `P` on the singleton world.
- `persistent_formula_equiv_persist`, `persistent_star_self`, and
  `persistent_star_and` justify the persistent algebra laws used by the paper
  prose.
- `fiberwise_joinable_on_*` lemmas in
  `ContextLogic/theories/FormulaFiberwise.v` and
  `ContextBasicDenotation/theories/BasicFormulaFiberwise.v` formalize the
  fiberwise aggregation principles used by the nondeterministic proof.
- `ty_denote_gas_result_ext` and `ty_denote_gas_result_alias_at` are the
  checked bridges from result-extension/result-graph facts back into type
  denotation.
- `ty_denote_wand_over_param_persist_over_result_equiv` and
  `ty_denote_wand_over_param_persist_under_result_equiv` record the checked
  persistent-over parameter equivalences for Wand results where the return
  body is fiberwise joinable.  The analogous unrestricted Arrow reverse is not
  claimed.

## Notation Guide

The proof uses a compact object-language notation layer.  The most important
notations for reading theorem statements are:

| Paper notation | Rocq notation | Meaning |
| --- | --- | --- |
| `x`, bound `#k` | `$ₗ x`, `#ₗ k` | Logical variables in type/formula support. |
| `O[b | φ]` | `{: b | φ }` | Overapproximate context type. |
| `U[b | φ]` | `[: b | φ ]` | Underapproximate context type. |
| `τ1 ∧ τ2` / intersection | `τ1 ⊓ τ2` | Type intersection. |
| `τ1 ∨ τ2` / union | `τ1 ⊔ τ2` | Type union. |
| `τ1 ⊕ τ2` | `τ1 ⊕ τ2` | Additive/sum context type. |
| `τx -> τ` | `τx → τ` | Ordinary function context type. |
| `τx -* τ` | `τx -∗ τ` | Separating function context type. |
| `□τ` | `□ τ` | Persistent context type. |
| `∅`, `x : τ` | `Emp`, `x ∷ τ` | Empty and singleton contexts. |
| `Γ1, Γ2` | `Γ1 ,, Γ2` | Ordered/comma context composition. |
| `Γ1 * Γ2` | `Γ1 ∗ Γ2` | Separating context composition. |
| `Γ1 ⊕ Γ2` | `Γ1 ⊕ Γ2` | Additive context composition. |
| `r ⊨ P` | `m ⊨ P` | Formula satisfaction. |
| `P ⊢ Q` | `P ⊫ Q` | Semantic entailment. |
| `P ≡ Q` | `P ⊣⊢ Q` | Formula equivalence. |
| `P * Q` | `P ∗ Q` | Multiplicative conjunction. |
| `P -* Q` | `P -∗[d] Q` | Binder-aware magic wand; `d` is the binder depth shift. |
| `P ⊕ Q` | `P ⊕ Q` | Additive/sum formula. |
| `∀x. P` | `∀. P` plus locally nameless opening | Ordinary formula forall. |
| `∀M X. P` | `fib D |> P` | Fiber/binding-reference connective over support set `D`. |
| `□P` | `□ P` | Persistent formula. |
| `[[τ]]Σ e` | `⟦ty⟧[Σ, gas] τ e`, `⟦ty⟧[Δ] τ e`, `TyDenote[Δ; τ; e]` | Gas-indexed and saturated type denotation; `TyDenote[...]` is the stable definition-facing form used when bracket notation would be hard to parse. |
| `[[Γ]]Σ` | `⟦ctx⟧[Σ] Γ` | Context denotation. |
| Typing judgment | `Φ ⊢ᶜ [Σ; Γ] e ⋮ τ` | Main checked context typing judgment. |
| Typing side condition | `wf[Σ; Γ] e ⋮ τ` | Abbreviation for `context_typing_wf Σ Γ e τ`. |
| Semantic subtype premise | `sub[Σ; Γ](τ1, τ2)` | Abbreviation for `sub_type_under Σ Γ τ1 τ2`. |
| Semantic context-subtype premise | `ctxsub[Σ; X](Γ1, Γ2)` | Abbreviation for `ctx_sub_under Σ X Γ1 Γ2`. |
| Unreachable branch premise | `unreachable[Σ; Γ] v @ b` | Abbreviation for semantic branch unreachability. |

The canonical notation for persistence is the square `□`; the old word-style
formula notation `persist P` is intentionally not provided.  Word-style
`over P` and `under P` remain because they name formula modalities rather than
context types; context types use the closer paper-style `{: b | φ }` and
`[: b | φ ]`.

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
  Φ ⊢ᶜ [Σ; Γ] e ⋮ τ ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
```

The closed-program denotational soundness theorem is:

```coq
Theorem denotational_soundness e τ :
  Φ ⊢ᶜ [∅; CtxEmpty] e ⋮ τ ->
  forall x,
    exists mres : WfWorldT,
      closed_result_world_of e x mres /\
      mres ⊨ TyDenote[({[x := ⌊τ⌋]} : gmap atom ty);
                       τ;
                       (ret (vfvar x))%core].
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
guard[rel[Σ | τ] e; τ; e] ∧ ...
```

The guard proves well-formedness of the context type, a basic world, erased
basic typing of the term, and totality of the term.  The recursive body uses
the result-first shape for result-sensitive types:

- `CTOver` / `CTUnder`: quantify over a result slot with `∀.` and
  `FResult[⇑ₗ (dom Σg) ⊢ e ↑ ⇓ #ₗ 0]`, then check the opened typed
  over/under body.  In the defining equation this is expanded down to the
  formula level:
  `fib (qual_vars φ ∖ {[#ₗ0]}) |> over (@atom φ ∧ FHasType[∅ ▷ TBase b ⊢ ret #0 ⋮ TBase b])`
  and similarly for `under`.  Proof scripts may temporarily `change` this
  expanded body back to `over_result_body b φ` or `under_result_body b φ`.
- `CTSum`: quantify over a result slot and split the result resource with
  `FPlus`.
- `CTArrow` / `CTWand`: first quantify over the function result, then check
  `arrow_value_denote_gas_with` or `wand_value_denote_gas_with` for `ret f`.
- `CTPersist`: quantify over the value result and wrap the inner denotation in
  `□`.

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
  Φ ⊢ᶜ [Σ; Γ] e ⋮ τ ->
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
