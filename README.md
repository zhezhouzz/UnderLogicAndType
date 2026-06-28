# UnderLogicAndType Supplemental Material

This repository contains the Rocq formalization accompanying the POPL
submission on underapproximate context types.  The development proves a
parameterized Fundamental theorem and closed-program denotational soundness for
our checked core calculus, together with a concrete graph-precise primitive
operation context.

The current `main` branch is fully checked: compiled Rocq files contain no
`Admitted.`/`admit.`.

## Artifact Contents

The formalization is organized as a layered Rocq development:

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

- `ContextBase`: atoms, logical variables, finite-set support, and shared base
  utilities.
- `ContextStore`: stores and store restriction/update facts.
- `ContextAlgebra`: resources/worlds, Kripke restriction, fibers, resource
  product/sum, and result/fiber extensions.
- `ContextLogic`: formula syntax and semantics, BI-style connectives,
  fiber quantification, persistence, and fiberwise joinability.
- `CoreLang`: checked core language, basic typing, small-step semantics, and
  operational result facts.
- `ContextTypeLanguage`: context types, contexts, erasure, locally nameless
  operations, and well-formedness.
- `ContextBasicDenotation`: semantic atoms for basic worlds, typing, term
  totality/results, qualifiers, and relevant environments.
- `Denotation`: recursive type/context denotation, constants, result-first
  support, result extension, let transport, and primitive-operation denotation
  support.
- `ContextTyping`: primitive-operation contexts, context typing rules, the
  Fundamental theorem, and concrete soundness wrappers.

## Requirements And Build

The development was checked with:

| Package | Version |
| --- | --- |
| [Rocq](https://rocq-prover.org/) | 9.1.0 |
| [rocq-stdpp](https://gitlab.mpi-sws.org/iris/stdpp) | dev.2026-01-23 |
| [coq-hammer](https://github.com/lukaszcz/coqhammer) | 1.3.2+9.1 |

A typical opam setup is:

```bash
opam switch create with-rocq-1 ocaml-base-compiler
eval $(opam env --switch=with-rocq-1)

opam repo add rocq-released https://github.com/rocq-archive/opam-rocq-archive/releases/download/0.0.1/rocq-released-repo.tar.gz
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam/-/raw/master/index

opam install rocq-core.9.1.0 rocq-stdpp.dev.2026-01-23 coq-hammer.1.3.2+9.1
```

To build the artifact:

```bash
rocq makefile -f _CoqProject -o Makefile
make
```

## Main Checked Theorems

The main typing judgment is defined in
`ContextTyping/theories/Typing.v` and printed with the context as the subject:

```coq
Γ ⊢ᶜ [Φ; Σ] e ⋮ τ
```

This abbreviates `has_context_type Φ Σ Γ e τ`.  The well-formedness and
semantic subsumption premises use matching notation:

```coq
Γ ⊢wf[Σ] e ⋮ τ
Γ ⊢ᶜ τ1 ≤[Σ] τ2
Γ1 ≤ᶜ[Σ; X] Γ2
```

The direct Fundamental theorem is in
`ContextTyping/theories/Soundness.v`, inside `Section WithPrimopContext`:

```coq
Theorem Fundamental
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) :
  Γ ⊢ᶜ [Φ; Σ] e ⋮ τ ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
```

The closed-program denotational soundness theorem is:

```coq
Theorem denotational_soundness e τ :
  CtxEmpty ⊢ᶜ [Φ; ∅] e ⋮ τ ->
  forall x,
    exists mres : WfWorldT,
      closed_result_world_of e x mres /\
      mres ⊨ TyDenote[({[x := ⌊τ⌋]} : gmap atom ty);
                       τ;
                       (ret (vfvar x))%core].
```

Both theorems are parameterized by a primitive-operation context `Φ` and the
assumption `wf_primop_ctx Φ`.  The concrete primitive instance is
`concrete_Φ` in `ContextTyping/theories/PrimOpConcreteContext.v`, with checked
well-formedness theorem:

```coq
Theorem concrete_Φ_wf : wf_primop_ctx concrete_Φ.
```

The concrete wrappers are in `ContextTyping/theories/SoundnessConcrete.v`:

```coq
Theorem concrete_Fundamental Σ Γ e τ : ...
Theorem concrete_denotational_soundness e τ : ...
```

## Implementation/Paper Alignment

The Rocq development intentionally differs from the paper presentation in a few
places.  These are proof-engineering or artifact-scope choices, not unstated
assumptions.

- The checked core language is smaller than the language used in the paper's
  examples.  It has `Unit`, `Bool`, `Nat`, unary primitive operations,
  application, `let`, and boolean-specific match.  It does not include the
  paper's general datatype match, fixed tree/list syntax, binary-operator
  syntax, or n-ary primitive-operation judgment.
- Primitive operations are abstract in the main proof.  Generic soundness
  assumes `wf_primop_ctx Φ`; concrete primitive behavior is isolated in
  `concrete_Φ_wf`.
- The core semantics and type denotation are nondeterministic-ready.  Result
  graphs are explicit formulas, and result-sensitive types use a result-first
  denotation shape.
- Qualifiers are semantic predicates with explicit support sets:
  `tqual D (Store -> Prop)`.  This differs from a first-order qualifier syntax
  in the paper, but it makes the support tracked by the mechanization explicit.
- Qualifier top is domain-indexed.  `qual_top_on D` is the real definition, and
  the standard notation `qual_top` observes the result binder.  There is no
  empty-support top qualifier: an empty-support top would impose no result-slot
  constraint and would make underapproximate coverage vacuous.
- `CTOver b φ` and `CTUnder b φ` interpret refinement bodies in the typed
  carrier for base type `b`.  The formula checked under `FOver`/`FUnder` pairs
  the qualifier atom with the result slot's basic typing formula.  Therefore
  `CTUnder b qual_top` covers all values of base type `b`, not all syntactic
  values.
- The formula syntax includes the persistent modality `FPersist`; it does not
  include a compiled `FExists` constructor on `main`.
- The type language includes `CTPersist` and a value-only persistence-intro
  typing rule.  These support the paper's persistent-resource story, while the
  generic soundness theorem remains parameterized over the ordinary context
  typing judgment.
- Paper Section 5 case-study programs are not compiled as part of `main`.  The
  checked result is the generic soundness theorem for the current core calculus
  and concrete primitive context.

## Paper-To-Proof Correspondence

| Paper item | Checked Rocq counterpart | Status |
| --- | --- | --- |
| Core values/terms and small-step semantics | `CoreLang/theories/Syntax.v`, `SmallStep.v`, `OperationalResults.v` | Checked for the smaller core. |
| Base/basic typing | `CoreLang/theories/BasicTyping.v`, `BasicTypingProps.v` | Checked. |
| Qualifiers | `ContextQualifier/theories/Qualifier.v` | Semantic predicate plus explicit support set. |
| Qualifier top | `qual_top_on D`; notation `qual_top` | Checked, support-indexed. |
| Context type syntax | `ContextTypeLanguage/theories/Syntax.v` | Checked, including `CTPersist`. |
| Over/Under/precise types | `over_ty`, `under_ty`, `precise_ty`; notations `{: b | φ }`, `[: b | φ ]` | Checked. |
| Contexts | `ctx`; notations `Emp`, `x ∷ τ`, `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` | Checked. |
| Formula syntax | `Formula` in `ContextLogic/theories/FormulaSyntax.v` | Checked. |
| Formula satisfaction | `res_models`; notation `m ⊨ P` | Checked. |
| Entailment/equivalence | `entails`, `formula_equiv`; notations `P ⊫ Q`, `P ⊣⊢ Q` | Checked. |
| Fiber/binding-reference connective | `FFibVars D P`; notation `fib D |> P` | Checked set-indexed version. |
| Universal formula | `FForall P`; notation `∀. P` | Checked. |
| Demonic/angelic modalities | `FOver P`, `FUnder P`; notations `over P`, `under P` | Checked. |
| BI connectives | `FAnd`, `FOr`, `FImpl`, `FStar`, `FBWand`, `FPlus` | Checked. |
| Persistent formula | `FPersist P`; notation `□ P` | Checked. |
| Persistent laws | `persistent_formula_equiv_persist`, `persistent_star_self`, `persistent_star_and` | Checked theorems. |
| Type denotation | `ty_denote_gas`, `ty_denote`; notations `⟦ty τ⟧[Σ, gas] e`, `⟦ty τ⟧[Δ] e`, `TyDenote[Δ; τ; e]` | Checked. |
| Context denotation | `ctx_denote_under`, `ctx_denote`; notation `⟦ctx⟧[Σ] Γ` | Checked. |
| Type-denotation guard | `ty_guard_formula`, `ty_static_guard_formula`; notations `guard[Σ] τ e`, `static_guard[Σ] τ e` | Checked. |
| Result graph / `mstep(e,x)` | `expr_result_formula_at D e x`; notation `FResult[D ⊢ e ⇓ x]` | Checked with explicit observation domain. |
| Typed Over/Under body | Expanded in `ty_denote_gas`; helper names `over_result_body`, `under_result_body` remain for proofs | Checked. |
| Result-first Arrow/Wand/Sum | Branches of `ty_denote_gas`; helpers `arrow_value_denote_gas_with`, `wand_value_denote_gas_with` | Checked.  The branch definitions are expanded in `ty_denote_gas`. |
| Persistent type | `CTPersist τ`; notation `□ τ` | Checked. |
| Persistence intro rule | `CT_PersistIntro` | Checked soundness case. |
| Persistent binding duplication | `ctx_bind_persist_star_dup` | Checked theorem. |
| Primitive-operation context | `primop_ctx`, `primop_sig`, `wf_primop_ctx` | Checked unary abstraction. |
| Concrete primitive context | `concrete_Φ`, `concrete_Φ_wf` | Checked. |
| Fundamental theorem | `Fundamental` | Checked theorem. |
| Closed-program soundness | `denotational_soundness`, `concrete_denotational_soundness` | Checked theorem. |

### Typing Rule Correspondence

The paper's typing rules are represented as constructors of
`has_context_type` in `ContextTyping/theories/Typing.v`:

| Paper rule/form | Rocq constructor | Notes |
| --- | --- | --- |
| `T-Var` | `CT_Var` | Singleton context `x ∷ τ`. |
| `T-Const` | `CT_Const` | Constants have precise type `const_precise_ty c`. |
| `T-Sub` | `CT_Sub` | Uses semantic premise `Γ ⊢ᶜ τ1 ≤[Σ] τ2`. |
| `T-CtxSub` | `CT_CtxSub` | Uses semantic premise `Γ1 ≤ᶜ[Σ; X] Γ2`. |
| Persistence intro | `CT_PersistIntro` | Value-only rule for `ret v`. |
| Let / separating let | `CT_Let`, `CT_LetD` | Checked. |
| Lambda / separating lambda | `CT_Lam`, `CT_LamD` | Checked. |
| Application / separating application | `CT_AppFun`, `CT_AppFunD` | Arguments are fresh atom variables. |
| Fixpoint | `CT_Fix` | Ordinary recursive function rule.  `FixD` is not compiled. |
| Primitive operation | `CT_AppOp` | Unary primitive rule via `primop_ctx`. |
| Boolean match | `CT_MatchBoth`, `CT_MatchTrueOnly`, `CT_MatchFalseOnly` | Boolean-specific split into reachable-branch variants. |

Important theorem-level bridges for definitions presented differently in the
paper:

- `res_models_persist_iff` gives the singleton-projection characterization of
  `□ P`.
- `persistent_formula_equiv_persist`, `persistent_star_self`, and
  `persistent_star_and` prove the persistent algebra laws.
- `fiberwise_joinable_on_*` lemmas in
  `ContextLogic/theories/FormulaFiberwise.v` and
  `ContextBasicDenotation/theories/BasicFormulaFiberwise.v` formalize
  fiberwise aggregation principles used by nondeterministic result proofs.
- `ty_denote_gas_result_ext` and `ty_denote_gas_result_alias_at` bridge
  result-extension/result-graph facts back into type denotation.
- `ty_denote_wand_over_param_persist_over_result_equiv` and
  `ty_denote_wand_over_param_persist_under_result_equiv` are the checked
  persistent-over parameter equivalences for Wand results where the return body
  is fiberwise joinable.  The unrestricted Arrow reverse is not claimed.

## Notation Guide

The proof uses notation close to the paper where doing so improves readability.
The following table is the fastest way to map paper notation to Rocq source.

| Paper notation | Rocq notation | Meaning |
| --- | --- | --- |
| Logical variable `x`, bound variable `#k` | `$ₗ x`, `#ₗ k` | Logical variables in qualifiers/formulas. |
| `O[b | φ]` | `{: b | φ }` | Overapproximate type. |
| `U[b | φ]` | `[: b | φ ]` | Underapproximate type. |
| Precise base refinement | `{: b | φ } ⊓ [: b | φ ]` or `precise_ty b φ` | Intersection of over and under. |
| Type intersection/union | `τ1 ⊓ τ2`, `τ1 ⊔ τ2` | Context-type meet/join. |
| Type sum | `τ1 ⊕ τ2` | Additive result/context type. |
| Function / wand type | `τx → τ`, `τx -∗ τ` | Ordinary/separating functions. |
| Persistent type | `□ τ` | Type-level persistence. |
| Empty/singleton context | `Emp`, `x ∷ τ` | Context syntax. |
| Context comma/star/sum | `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` | Context composition. |
| Typing judgment | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ` | Main context typing judgment. |
| Well-formed typing side condition | `Γ ⊢wf[Σ] e ⋮ τ` | `context_typing_wf Σ Γ e τ`. |
| Semantic subtype | `Γ ⊢ᶜ τ1 ≤[Σ] τ2` | `sub_type_under Σ Γ τ1 τ2`. |
| Semantic context subtype | `Γ1 ≤ᶜ[Σ; X] Γ2` | `ctx_sub_under Σ X Γ1 Γ2`. |
| Formula satisfaction | `m ⊨ P` | Resource/world satisfaction. |
| Formula entailment/equivalence | `P ⊫ Q`, `P ⊣⊢ Q` | Semantic entailment/equivalence. |
| Multiplicative conjunction | `P ∗ Q` | Separating formula product. |
| Magic wand | `P -∗[d] Q` | Binder-aware wand; `d` records binder-depth shift. |
| Formula sum | `P ⊕ Q` | Additive formula sum. |
| Universal formula | `∀. P` | Locally nameless universal formula. |
| Fiber quantification | `fib D |> P` | `FFibVars D P`. |
| Persistent formula | `□ P` | Logic-level persistence. |
| Type denotation | `⟦ty τ⟧[Σ, gas] e`, `⟦ty τ⟧[Δ] e`, `TyDenote[Δ; τ; e]` | Gas-indexed and saturated denotation. |
| Context denotation | `⟦ctx⟧[Σ] Γ` | Context denotation. |
| Result graph | `FResult[D ⊢ e ⇓ x]` | `expr_result_formula_at D e x`. |
| Basic typing formula | `FHasType[Σ ⊢ e ⋮ T]` | Basic erased typing atom. |
| Kripke/resource order | `m ⊑ n` | World/resource restriction order. |
| Resource subset | `m ⊆ᵣ n` | `res_subset`; distinct from `⊑`. |
| Fiber relation | `fiber(mfib, m, X, σ)` | `mfib` is an `X`-fiber of `m`. |
| Result extension | `m #> F ~~> mx` | `res_extend_by m F mx`. |

`P -∗[d] Q` carries the number `d` because formulas are locally nameless: the
wand body may sit under binders, and the semantic clause must shift/open both
sides at the correct binder depth.  Ordinary value-level wands use `d = 1`.

## Type Denotation Shape

The central definition is in `Denotation/theories/TypeDenote.v`:

```coq
Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT := ...
```

Every nonzero branch starts with a guard:

```coq
guard[rel[Σ | τ] e; τ; e] ∧ ...
```

For result-sensitive types, the recursive body is result-first:

- `CTOver` / `CTUnder`: quantify over a fresh result slot, assume the term
  result graph `FResult[dom Σg ⊢ e ⇓ result]`, then check the typed
  over/under body.  The body is expanded at formula level as an over/under
  modality over the conjunction of the qualifier atom and the result-slot basic
  typing formula.
- `CTSum`: quantify over the result slot and split the result resource with
  `FPlus`.
- `CTArrow` / `CTWand`: first bind the function value result of `e`, then
  quantify over or wand over the argument value.  The helper definitions
  `arrow_value_denote_gas_with` and `wand_value_denote_gas_with` are retained
  for proof normalization, but the `ty_denote_gas` branches are written
  expanded so readers see the actual denotation.
- `CTPersist`: bind the value result and wrap the inner type denotation in
  `□`.

Important support lemmas include:

- `formula_open_env_ty_denote_gas`
- `ty_denote_gas_env_agree_on`
- `ty_denote_gas_lvars_subset`
- `ty_denote_gas_fv_subset`
- `ty_denote_gas_scope_of_guard`

## Constants And Primitive Operations

Constants inhabit precise refinement types, proved in
`Denotation/theories/ConstDenote*.v`.

Primitive operations are abstracted by `primop_ctx`; generic soundness assumes
only `wf_primop_ctx Φ`.  The concrete instance in
`ContextTyping/theories/PrimOpConcreteContext.v` is:

```coq
eq0    : {: Nat  | qual_top } -> precise Bool (ν = (x =? 0))
plus1  : {: Nat  | qual_top } -> precise Nat  (ν = S x)
minus1 : {: Nat  | qual_top } -> precise Nat  (ν = pred x)
boolGen: {: Unit | qual_top } -> precise Bool (ν ranges over bool results)
natGen : {: Unit | qual_top } -> precise Nat  (ν ranges over nat results)
```

In Rocq these precise result qualifiers are uniformly represented by
`primop_graph_qual op`; the graph relation is unfolded only inside
`concrete_Φ_wf` and its supporting lemmas.  The abstract soundness theorem does
not inspect concrete primitive graphs.

## Suggested Reading Order

For reviewers comparing the proof to the paper, a useful reading path is:

1. `ContextLogic/theories/FormulaSemantics.v`
2. `ContextLogic/theories/FormulaConnectives.v` and
   `FormulaConnectivesHigher.v`
3. `ContextBasicDenotation/theories/TermOpen.v`
4. `Denotation/theories/TypeDenote.v`
5. `Denotation/theories/TypeEquiv.v`
6. `Denotation/theories/Context.v`
7. `ContextTyping/theories/Typing.v`
8. `ContextTyping/theories/Soundness.v`

For function cases, read `Denotation/theories/ResultFirstOpen.v` before the
Arrow/Wand denotation and soundness files.  For persistence, read
`ContextLogic/theories/FormulaConnectivesHigher.v`, `Denotation/theories/TypePersist*.v`,
`ContextTyping/theories/Typing.v`, and
`ContextTyping/theories/SoundnessPersist.v`.
