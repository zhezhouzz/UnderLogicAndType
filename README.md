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
| Well-founded recursive-call relation | Fig. 5, T-Fix rule | Base-value order (`constant_lt_for_base`) in `ContextTypeLanguage/theories/Syntax.v` (line 414); recursive-call argument type (`fix_rec_call_ty`) in the same file (line 449); used by T-Fix in `ContextTyping/theories/Typing.v` (line 188) | `c1 ≺[b] c2`, `fix_rec_call_ty b y τx τ` |
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

The notation

```coq
m #> F ~~> mx
```

means that `F` is a resource extension function applicable to `m`, and `mx` is
the resource obtained by applying `F` to every store/environment in `m`.  A
typical example is the result extension for `[[e -->* x]]`: it maps each store
in the current capability to stores where the fresh variable `x` records a
value that `e` can reduce to in that store.  Thus the current capability `m`
is extended to `mx`, where `x` stores the possible results of `e` across the
stores in `m`.

`FForall P`, written `∀. P`, is implemented using explicit resource
extensions.  Intuitively, for every fresh name `y`, the artifact considers
every minimal extension of the current resource that provides exactly the
variables needed to interpret the opened body and outputs the fresh result
slot `y`; the opened body must hold on every such minimal extension.  The
locally nameless details
`exists L : aset, forall y : atom, y ∉ L ->` and
`formula_open 0 y φ` are the usual freshness/opening noise: semantically, this
matches the quantification described in the paper.  The full-world
characterization used by many later proofs is an iff:

```coq
Lemma res_models_forall_full_world_iff
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (m ⊨ FForall φ <->
    exists L : aset,
      forall y : atom, y ∉ L ->
        forall my : WfWorldT,
          world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
          res_restrict my (world_dom (m : WorldT)) = m ->
          my ⊨ formula_open 0 y φ).
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

### Qualifier embedding

Refinement qualifiers are shallowly embedded as Coq propositions.  This lets
the artifact use the full expressiveness of `Prop` for the rich predicates
needed by type denotation, including basic well-typedness and totality
properties, without being limited by a first-order qualifier syntax.
Concretely, a qualifier is a support set of logical variables together with a
Coq predicate over stores whose domain is exactly that support:

```coq
Record qualifier : Type := tqual {
  qual_lvars : lvset;
  qual_prop : LStoreOnT qual_lvars -> Prop;
}.
```

This definition appears in `ContextQualifier/theories/Qualifier.v` (line 26).

The explicit support also gives the artifact precise control over which
variables a qualifier can observe.  For example, `top[x]` and `top[x,y]` are
not interchangeable: the former ranges over all values of `x`, while the
latter ranges over joint assignments to both `x` and `y`.  This distinction is
usually invisible in logics that use only overapproximate semantics, but it is
important for the precise over/under semantics used here.

Because qualifiers themselves are untyped, a bare top qualifier would range
over all syntactic values.  Thus `[v : Bool | top]` would otherwise also try to
cover natural numbers.  The type denotation fixes this at the embedding point:
the Over/Under result body conjoins the qualifier atom with a basic typing atom
for the result slot.  The helper definitions are in
`Denotation/theories/TypeDenote.v` (lines 80-87), and the expanded
`CTOver`/`CTUnder` branches in `ty_denote_gas` show the same structure
(lines 131-142):

```coq
Definition result_basic_typing_formula (b : base_ty) : FormulaT :=
  FHasType[(∅ ▷ TBase b)%lvar ⊢ (ret # 0)%core ⋮ TBase b].

Definition over_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  (over (@atom φ ∧ result_basic_typing_formula b))%formula.

Definition under_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  (under (@atom φ ∧ result_basic_typing_formula b))%formula.
```

### Type denotation

The formula layer proves that satisfaction is determined by the projection of
the resource to the free variables of the formula:

```coq
Lemma res_models_minimal_on (S : aset) (m : WfWorldT) (φ : FormulaT) :
  formula_fv φ ⊆ S →
  res_models m φ ↔ res_models (res_restrict m S) φ.
```

This theorem appears in `ContextLogic/theories/FormulaSemantics.v` (line
937).  The type denotation is designed so that the same idea is available for
the logical relation.  At the beginning of the `ty_denote_gas` fixpoint, the
environment is clipped to the variables relevant to the term `e` and type
`τ`:

```coq
Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := relevant_env Σ τ e in
  (guard[Σg; τ; e] ∧ ...)%formula.
```

The clipping loses no semantic information.  It makes the type-denotation
support theorem precise: whether `m` satisfies `[[τ]] e` depends only on the
projection of `m` to the free variables of `τ` and `e`.

```coq
Lemma ty_denote_gas_minimal_on gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e <->
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊨ ty_denote_gas gas Σ τ e.
```

This theorem is in `Denotation/theories/TypeDenoteRegular.v` (line 1803).

As in the paper, type denotation always includes the ordinary well-formedness,
well-typedness, and totality obligations.  These are encoded in the guard, and
the guard is conjoined at the start of every `ty_denote_gas` unfolding:

```coq
Definition ty_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  (FWfTy[Σ; τ] ∧
    (FWorld[Σ] ∧
      (FHasType[Σ ⊢ e ⋮ (⌊τ⌋)%cty] ∧ FTotal[e])))%formula.
```

The guard definition is in `Denotation/theories/TypeDenote.v` (line 7), and
the fixpoint begins with `guard[Σg; τ; e] ∧ ...` in the same file (lines
122-127).

### Typing proof core lemmas

Two denotation-transport lemmas carry much of the typing proof.

The first one is the let-introduction transport lemma.  It states that, after
extending a resource with the result graph of `e1` at a fresh slot `x`, the
opened body `e2 ^^ x` and the actual `let` term satisfy the same type
denotation at every gas level:

```coq
Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) <->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2).
```

This theorem is in `Denotation/theories/TypeEquivTLet.v` (line 1469).  It is
the core proof bridge for the `let` typing rules: soundness first constructs
the result-extension world, proves the body there, and then uses this theorem
to return to the source `let` term.

The second one says that type denotation is invariant under term-result
equivalence:

```coq
Definition typed_total_equiv_on
    (Σ : lty_env) (τ : context_ty) (m : WfWorldT)
    (e1 e2 : tm) : Prop :=
  tm_equiv_on m e1 e2 /\
  tm_total_equiv_on m e1 e2 /\
  m ⊨ ty_denote_gas 0 Σ τ e1 /\
  m ⊨ ty_denote_gas 0 Σ τ e2.

Lemma ty_denote_gas_tm_equiv
    gas Σ τ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ e1 ->
  m ⊨ ty_denote_gas gas Σ τ e2.
```

The premise is defined in `Denotation/theories/TypeEquivTermBase.v` (line 68),
and the transport theorem is in `Denotation/theories/TypeEquiv.v` (line 622).
This lemma lets the fundamental proof change the shape of a term without
changing its denotation.  For example, the match proof first relates a reachable
branch to the whole boolean match term (`SoundnessMatch.v`, line 264), the
lambda proof relates a beta-reduced body to an application of a lambda
(`SoundnessLam.v`, line 781), and the fix proof relates an application of a fix
value to the unfolded recursive body (`SoundnessFixBase.v`, line 675).

In a deterministic language, this kind of term-equivalence transport can often
derive the let-introduction transport: the result slot inserted by the
extension is the unique result obtained by re-running the term.  In the
nondeterministic language, that invariant breaks.  Let `m` be the singleton
world containing the empty store, let `e1` be `boolGen unit`, and let
`e2 = ret (vbvar 0)`.  If `mx` is the result-extension world
`m #> [[e1 --* x]] ~~> mx`, then `e2 ^^ x` is `ret x`, so an output slot `y`
is correlated with the already stored value of `x`.  But
`let x = e1 in ret x` re-runs the nondeterministic generator in each store of
`mx`; its output `y` may be either boolean independently of the old stored
`x`.  Thus the two result graphs are not equivalent in general.  This is one
of the places where the nondeterministic proof diverges from the deterministic
invariants and requires a separate `tlet_intro_denotation` theorem.

### Core proof technical infrastructure

Result extension is the bridge from operational result sets to type
denotation.  The main lemmas in this area are:

- `ty_denote_gas_result_ext`: transports denotation along a result extension;
- `ty_denote_gas_result_alias_at`: replaces a term by a fresh result slot when
  the result graph is available.

The proof also uses fiberwise aggregation facts, especially
`fiberwise_joinable_on_*`, to combine fiber-local obligations back into whole
resource worlds for the formula fragments that support such aggregation.
