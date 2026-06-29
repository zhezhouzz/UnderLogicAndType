# Supplemental Artifact for *Context Types: Bunched Modalities for Unifying Safety and Reachability*

This repository is the Rocq proof artifact for the paper *Context Types:
Bunched Modalities for Unifying Safety and Reachability*.  It mechanizes the
core context-type calculus, its resource semantics, the main Fundamental
Theorem, and the closed-program denotational soundness theorem.

The compiled development contains no `Admitted.`/`admit.` in Rocq source files.

## Compilation and Dependencies

The artifact was checked with:

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

Build from the repository root with:

```bash
rocq makefile -f _CoqProject -o Makefile
make
```

## Design Choices and Differences from the Paper

- The paper first introduces a restricted deterministic language and then
  presents its nondeterministic extension.  This artifact implements the full
  nondeterministic language and context type system used by the metatheory:
  nondeterministic operational semantics, nondeterministic generators
  `boolGen` and `natGen`, precise primitive-operation contracts, and
  type-level persistence.
- The checked core language is limited to `Unit`, `Bool`, and `Nat`; it does
  not include lists or trees.  These are straightforward datatype extensions
  of the core.  The primitive operators include the usual unary operations
  such as `plus1`, `minus1`, and `eq0`, together with random generators such
  as `boolGen` and `natGen`.
- For simplicity, pattern matching only matches on Boolean discriminees.
  Pattern matching on natural numbers can be implemented by first testing
  whether the scrutinee is zero:

  ```text
  let cond = op_eq0 n in
  match cond with
  | true -> e1
  | false ->
      let m = op_minus1 n in
      e2
  ```
- The type system contains union types in addition to the constructs used in
  the paper examples.
- The logic does not include an existential formula constructor, because the
  checked denotation and soundness proof do not use one.
- The formalization follows
  [The Locally Nameless Representation](https://chargueraud.org/research/2009/ln/main.pdf):
  bound variables are represented de Bruijn-style and free variables by atoms.
  Consequently, binder-heavy definitions look slightly different from the
  paper's surface notation.
- Refinement propositions are shallowly embedded Coq propositions.  A
  qualifier is a semantic predicate together with an explicit support set, not
  a first-order syntax tree.  See Proof Details for the artifact-level
  treatment of qualifier support.

## Proof File Structures

The artifact is organized as a layered Rocq development:

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

- `ContextBase`, `ContextStore`, and `ContextAlgebra` define atoms, logical
  variables, stores, and resources.  A store is the artifact name for the
  paper's environment: a finite map from variables to values.  Worlds,
  resources, and capabilities refer to the same semantic objects in this
  development.
- `ContextLogic` defines formulas, satisfaction, bunched connectives,
  fiber quantification, and persistence.
- `CoreLang` defines the core term language, basic typing, small-step
  semantics, and operational result facts.
- `ContextTypeLanguage` defines context types, contexts, erasure,
  locally nameless operations, and well-formedness.
- `ContextBasicDenotation` defines formula atoms for basic worlds, basic
  typing, term totality/results, qualifiers, and relevant environments.
- `Denotation` defines type/context denotation, constants, result-first
  Arrow/Wand support, let transport, and primitive-operation denotation
  support.
- `ContextTyping` defines primitive-operation contexts, typing rules, and the
  soundness proof.  The main soundness proof is split by typing-rule families,
  with separate files for lambdas, applications, match, recursion, and
  persistence.

## Paper-to-artifact Correspondence

| Definition/Theorems | Paper | Definition | Notation |
| --- | --- | --- | --- |
| Store/environment | Definition 4.1 | Stores (`Store`, `LStore`) in `ContextStore/StoreInterface.v` (lines 13 and 14); restriction and compatibility notations in the same file (lines 45-50) | `σ ↾ X`, `σ1 ##ₛ σ2`, map notation `<[x := v]> σ`, `σ !! x` |
| Capability/resource/world | Definition 4.1 | Worlds/resources (`World`, `WfWorld`) in `ContextAlgebra/theories/ResourceInterfaceCore.v` (lines 17 and 18); domain/stores/restriction/unit in the same file (lines 27-56) | `𝟙`, `Dom m`, `m ↾ X`, `m ⊑ᵣ n` |
| Resource algebra operations | Definition 4.2 + Sec 4.2 | Abstract algebra class (`ContextAlgebra`) in `ContextAlgebra/theories/ResourceAlgebra.v` (line 10); concrete compatibility/product/sum/subset in `ContextAlgebra/theories/ResourceInterfaceCore.v` (lines 438-446); fiber/projection operations in `ContextAlgebra/theories/ResourceInterfaceCore.v` (lines 597-600) | `m1 ##ᵣ m2`, `m1 ×[H] m2`, `m1 +[H] m2`, `m1 ⊆ᵣ m2`, `fiber(mfib, m, X, σ)`, `mfib ∈ᶠ Fiber(m, X)` |
| Formula syntax | Definition 4.3 | Formula syntax (`Formula`) in `ContextLogic/theories/FormulaSyntaxCore.v` (line 20) | `⊤`, `⊥`, `@atom q`, `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ∗ Q`, `P -∗[d] Q`, `P ⊕ Q`, `∀. P`, `over P`, `under P`, `□ P`, `fib D |> P` |
| Formula satisfaction | Definition 4.3 and persistence in Sec. 5 | Satisfaction (`res_models`) in `ContextLogic/theories/FormulaSemantics.v` (line 891) | `m ⊨ P` |
| Entailment and equivalence | Definition 4.3 | Entailment (`entails`) in `ContextLogic/theories/FormulaSemantics.v` (line 910); formula equivalence (`formula_equiv`) in `ContextLogic/theories/FormulaConnectivesHigher.v` (line 825) | `P ⊫ Q`, `P ⊣⊢ Q` |
| Kripke monotonicity | Theorem 4.4 | `res_models_kripke` in `ContextLogic/theories/FormulaSemantics.v` (line 913) | `m ⊑ n -> m ⊨ P -> n ⊨ P` |
| Core base types and primitive operations | Core language syntax figures (Fig. 2) | Basic types (`base_ty`) in `CoreLang/theories/Syntax.v` (line 14); primitive operations (`prim_op`) in `CoreLang/theories/Syntax.v` (line 45) | `Unit`, `Bool`, `Nat`, `T1 →ₜ T2`, `op_eq0`, `op_plus1`, `op_minus1`, `op_boolGen`, `op_natGen` |
| Term syntax | Core language syntax figures (Fig. 2) | Mutually recursive values (`value`) and expressions (`tm`) in `CoreLang/theories/Syntax.v` (lines 75 and 82) | `ret v`, `let: e1 in e2`, `v1 · v2`, `if v then et else ef` |
| Operational semantics | Standard, not shown separately in paper | Small-step relation (`step`) in `CoreLang/theories/SmallStep.v` (line 98) | `step e e'` |
| Basic typing | Standard, not shown separately in paper | Basic typing judgments (`value_has_type`, `tm_has_type`) in `CoreLang/theories/BasicTyping.v` (lines 34 and 49) | `Γ ⊢ᵥ v ⋮ T`, `Γ ⊢ₑ e ⋮ T` |
| Qualifiers | Type syntax (Fig. 3) | Semantic qualifiers (`tqual D P`) in `ContextQualifier/theories/Qualifier.v`; equality qualifier (`mk_q_eq`) in `ContextTypeLanguage/theories/Syntax.v` (line 390) | Shallow Coq propositions with explicit support |
| Context type syntax | Type syntax (Fig. 3) | Context types (`context_ty`) in `ContextTypeLanguage/theories/Syntax.v` (line 31) | `{: b | φ }`, `[: b | φ ]`, `τ1 ⊓ τ2`, `τ1 ⊔ τ2`, `τ1 ⊕ τ2`, `τx → τ`, `τx -∗ τ`, `□ τ` |
| Type context syntax | Type syntax (Fig. 3) | Contexts (`ctx`) in `ContextTypeLanguage/theories/Syntax.v` (line 41) | `Emp`, `x ∷ τ`, `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` |
| Term-denotation and guard formulas | Sec. 4.4, Type Denotation and Soundness, first paragraph: denotation of a term `e`, basic typing, and totality guards | Result formula (`expr_result_formula_at`) in `ContextBasicDenotation/theories/TermOpen.v` (line 1086); total formula (`expr_total_formula`) in `ContextBasicDenotation/theories/TermEval.v` (line 1140); basic typing formula (`expr_basic_typing_formula`) in `ContextBasicDenotation/theories/BasicTypingFormula.v` (line 1136); world/guard formulas (`basic_world_formula`, `ty_guard_formula`, `ty_static_guard_formula`) in `ContextBasicDenotation/theories/StoreTyping.v` (line 48) and `Denotation/theories/TypeDenote.v` (lines 7 and 13) | `FResult[D ⊢ e ⇓ x]`, `FTotal[e]`, `FHasType[Σ ⊢ e ⋮ T]`, `FWorld[Σ]`, `guard[Σ; τ; e]`, `static_guard[Σ; τ; e]` |
| Type denotation | Definition 4.7, Definition 5.2, and Sec. 5.2 | Gas-indexed type denotation (`ty_denote_gas`) in `Denotation/theories/TypeDenote.v` (line 122); saturated denotation (`ty_denote`) in `Denotation/theories/TypeDenote.v` (line 187) | `⟦ty τ⟧[Σ, gas] e`, `⟦ty τ⟧[Δ] e`, `TyDenote[Δ; τ; e]` |
| Type context denotation | Definition 4.8 | Context denotation (`ctx_denote_under`) in `Denotation/theories/Context.v` (line 17) | `⟦ctx⟧[Σ] Γ` |
| Typing judgment | Fig. 5 and Sec. 5.1 | Context typing judgment (`has_context_type`) in `ContextTyping/theories/Typing.v` (line 103) | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ` |
| Typing well-formedness | Fig. 4 | Well-formedness (`context_typing_wf`) in `ContextTyping/theories/Typing.v` (line 66) | `Γ ⊢wf[Σ] e ⋮ τ` |
| Semantic type subsumption | Fig. 6 | Semantic subtype (`sub_type_under`) in `ContextTyping/theories/Typing.v` (line 44) | `Γ ⊢ᶜ τ1 ≤[Σ] τ2` |
| Semantic context subsumption | Fig. 6 | Semantic context subtype (`ctx_sub_under`) in `ContextTyping/theories/Typing.v` (line 54) | `Γ1 ≤ᶜ[Σ; X] Γ2` |
| Primitive-operation context | Theorem 4.9 | Primitive signature (`primop_sig`) and context (`primop_ctx`) in `ContextTyping/theories/PrimOpContext.v` (lines 17 and 30); well-formedness (`wf_primop_ctx`) in `ContextTyping/theories/PrimOpContext.v` (line 56) | `wf_primop_ctx Φ` |
| Concrete primitive context | Concrete instance of Theorem 4.9 | Concrete context (`concrete_Φ`) in `ContextTyping/theories/PrimOpConcreteContext.v` (line 171); well-formedness theorem (`concrete_Φ_wf`) in `ContextTyping/theories/PrimOpConcreteContext.v` (line 1297) | `concrete_Φ` |
| Fundamental theorem | Theorem 4.10 | `Fundamental` in `ContextTyping/theories/Soundness.v` (line 977); concrete wrapper `concrete_Fundamental` in the same file (line 1152) | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ -> ⟦ctx⟧[Σ] Γ ⊫ ...` |
| Denotational soundness | Theorem 4.11 | `denotational_soundness` in `ContextTyping/theories/Soundness.v` (line 1079); concrete wrapper `concrete_denotational_soundness` in the same file (line 1159) | closed programs have a result world satisfying `TyDenote[...]`; concrete versions instantiate `Φ := concrete_Φ` |

The artifact defines universal quantification and persistence in forms that
are slightly different from the paper presentation because these definitions
are more convenient for the mechanized proof.  The bridge theorems are listed
in Proof Details below.

## Proof Details

### Logic formulas

`FFibVars D P`, written `fib D |> P`, is the artifact's multi-variable form
of the Binding Reference Operator from Definition 4.3.  It evaluates `P` on
the fibers induced by the variables in `D`.

The proof repeatedly uses the fact that formula satisfaction depends only on
the free variables of the formula:

```coq
Lemma res_models_minimal_on (S : aset) (m : WfWorldT) (φ : FormulaT) :
  formula_fv φ ⊆ S →
  res_models m φ ↔ res_models (res_restrict m S) φ.
```

`FForall P`, written `∀. P`, is implemented using explicit resource
extensions.  Intuitively, for every fresh name `y`, the artifact considers
every minimal extension of the current resource that provides exactly the
variables needed to interpret the opened body and outputs the fresh result
slot `y`; the opened body must hold on every such minimal extension.  The
locally nameless details
`exists L : aset, forall y : atom, y ∉ L ->` and
`formula_open 0 y φ` are the usual freshness/opening noise: semantically, this
matches the quantification described in the paper.  The main introduction
principle used in proofs is:

```coq
Lemma res_models_forall_rev_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ) ->
  m ⊨ FForall φ.
```

`FPersist P`, written `□ P`, is implemented similarly by using the smallest
singleton resource needed to model `P`.  The definition projects the current
resource to the support of `P` and requires this projection to be a singleton
resource satisfying `P`.  By `res_models_minimal_on`, this is equivalent to
the paper-style characterization: `r |= □P` iff there is a singleton resource
`{σ}` such that `{σ} ⊑ r` and `{σ} |= P`.

```coq
Lemma res_models_persist_order_iff (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FPersist φ <->
  exists σ : Store (V := V),
    let σw :=
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) in
    σw ⊑ m /\ σw ⊨ φ.
```

The algebraic behavior used in the paper is then recovered by:

```coq
Lemma persistent_formula_equiv_persist (φ : FormulaT) :
  persistent_formula φ ->
  φ ⊣⊢ FPersist φ.

Lemma persistent_star_self (φ : FormulaT) :
  persistent_formula φ ->
  FStar φ φ ⊣⊢ φ.

Lemma persistent_star_and (φ ψ : FormulaT) :
  persistent_formula φ ->
  FStar φ ψ ⊣⊢ FAnd φ ψ.
```

The magic wand also has a more explicit locally nameless shape.  In the paper
notation `P -* Q`, the consequent `Q` may mention variables introduced by the
antecedent `P`; this is direct with named variables.  In locally nameless
syntax, both `P` and `Q` may contain bound variables, so the artifact records
how many binders from `P` remain in scope when opening the wand body.  Thus the
constructor is `FBWand d P Q`, written `P -∗[d] Q`, where the binder-depth
parameter `d` is an offset.  In ordinary value-level uses, `d = 1`; nested
result-first definitions may require the depth to be stated explicitly.

### Concrete primitive context

The abstract soundness proof assumes only `wf_primop_ctx Φ`.  The concrete
instance `concrete_Φ` records precise input-output relations:

```coq
eq0    : {: Nat  | qual_top } -> precise Bool (ν = (x =? 0))
plus1  : {: Nat  | qual_top } -> precise Nat  (ν = S x)
minus1 : {: Nat  | qual_top } -> precise Nat  (ν = pred x)
boolGen: {: Unit | qual_top } -> precise Bool (ν ranges over bool results)
natGen : {: Unit | qual_top } -> precise Nat  (ν ranges over nat results)
```

In Rocq these input-output relations are represented uniformly by
`primop_graph_qual op`.  Primitive-specific semantic reasoning is confined to
`concrete_Φ_wf` and its supporting lemmas; the generic Fundamental theorem does
not inspect concrete primitive-operation relations.

### Typed top and typed result bodies

`qual_top_on D` is domain-indexed.  The standard `qual_top` notation observes
the result binder.  An empty-support top qualifier would impose no result-slot
constraint and would make underapproximate coverage vacuous.

The nonzero denotation for `CTOver b φ` and `CTUnder b φ` checks refinement
inside the typed carrier for `b`: the result body combines `FAtom φ` with the
result slot's basic typing formula.  Thus `CTUnder b qual_top` covers all
values of base type `b`, not all syntactic values.

### Result-first type denotation

Every nonzero type denotation begins with a guard:

```coq
guard[rel[Σ | τ] e; τ; e] ∧ ...
```

Result-sensitive types then bind the result of the scrutinized term first.
`CTSum`, `CTArrow`, `CTWand`, and `CTPersist` all follow this result-first
shape.  The helper definitions `arrow_value_denote_gas_with` and
`wand_value_denote_gas_with` are retained for proof normalization, but the
Arrow/Wand branches in `ty_denote_gas` are expanded so that the definition
shows the actual denotation.

### Core proof technical infrastructure

The notation

```coq
m #> F ~~> mx
```

means that `mx` extends `m` by the result/fiber extension `F`.  Result
extension is the bridge from operational result sets to type denotation.  The
main lemmas in this area are:

- `ty_denote_gas_result_ext`: transports denotation along a result extension;
- `ty_denote_gas_result_alias_at`: replaces a term by a fresh result slot when
  the result graph is available;
- `tlet_intro_denotation`: connects a let body opened with a result slot to the
  corresponding `let` term.

The proof also uses fiberwise aggregation facts, especially
`fiberwise_joinable_on_*`, to combine fiber-local obligations back into whole
resource worlds for the formula fragments that support such aggregation.
