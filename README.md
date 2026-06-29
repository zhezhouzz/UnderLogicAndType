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
| Term syntax | Core language syntax figures | Mutually recursive values (`value`) and expressions (`tm`) in `CoreLang/theories/Syntax.v` (lines 75 and 82) | `ret v`, `let: e1 in e2`, `v1 · v2`, `if v then et else ef` |
| Base types and primitive operations | Core language syntax figures | Basic types (`base_ty`) in `CoreLang/theories/Syntax.v` (line 14); primitive operations (`prim_op`) in `CoreLang/theories/Syntax.v` (line 45) | `Unit`, `Bool`, `Nat`, `op_eq0`, `op_plus1`, `op_minus1`, `op_boolGen`, `op_natGen` |
| Operational semantics | Operational semantics figures | Small-step relation (`step`) in `CoreLang/theories/SmallStep.v` (line 98) | `step e e'` |
| Basic typing | Core typing premises | Basic typing judgments (`value_has_type`, `tm_has_type`) in `CoreLang/theories/BasicTyping.v` (lines 31 and 49) | `Γ ⊢ᵥ v ⋮ T`, `Γ ⊢ₑ e ⋮ T`; basic type notation includes `T1 →ₜ T2` |
| Qualifiers | Refinement propositions | Semantic qualifiers (`tqual D P`) in `ContextQualifier/theories/Qualifier.v`; equality qualifier (`mk_q_eq`) in `ContextTypeLanguage/theories/Syntax.v` (line 390) | Shallow Coq propositions with explicit support |
| Context type syntax | Type syntax figures | Context types (`context_ty`) in `ContextTypeLanguage/theories/Syntax.v` (line 31) | `{: b | φ }`, `[: b | φ ]`, `τ1 ⊓ τ2`, `τ1 ⊔ τ2`, `τ1 ⊕ τ2`, `τx → τ`, `τx -∗ τ`, `□ τ` |
| Context syntax | Context syntax figures | Contexts (`ctx`) in `ContextTypeLanguage/theories/Syntax.v` (line 41) | `Emp`, `x ∷ τ`, `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` |
| Formula syntax | Logic figures | Formula syntax (`Formula`) in `ContextLogic/theories/FormulaSyntaxCore.v` (line 20) | `P ∧ Q`, `P ∨ Q`, `P → Q`, `P ∗ Q`, `P -∗[d] Q`, `P ⊕ Q`, `∀. P`, `over P`, `under P`, `□ P`, `fib D |> P` |
| Formula satisfaction | Logic semantics | Satisfaction (`res_models`) in `ContextLogic/theories/FormulaSemantics.v` (line 891) | `m ⊨ P` |
| Entailment and equivalence | Logical entailment/equivalence | Entailment (`entails`) in `ContextLogic/theories/FormulaSemantics.v` (line 910); formula equivalence (`formula_equiv`) in `ContextLogic/theories/FormulaConnectivesHigher.v` (line 825) | `P ⊫ Q`, `P ⊣⊢ Q` |
| Fiber connective | Binding-reference/fiber connective | Fiber formula (`FFibVars`) in `ContextLogic/theories/FormulaSyntaxCore.v` (line 20) | `fib D |> P` |
| Binder-aware wand | Magic wand in the logic | Bounded wand constructor (`FBWand d P Q`) in `ContextLogic/theories/FormulaSyntaxCore.v` (line 20) | `P -∗[d] Q`; `d` records the locally nameless binder-depth shift |
| Persistent formula | Persistent modality | Persistent formula constructor (`FPersist`) in `ContextLogic/theories/FormulaSyntaxCore.v` (line 20); characterization theorem `res_models_persist_iff` in the logic/connectives files | `□ P` |
| Type denotation | Type interpretation | Gas-indexed type denotation (`ty_denote_gas`) in `Denotation/theories/TypeDenote.v` (line 122); saturated denotation (`ty_denote`) in `Denotation/theories/TypeDenote.v` (line 187) | `⟦ty τ⟧[Σ, gas] e`, `⟦ty τ⟧[Δ] e`, `TyDenote[Δ; τ; e]` |
| Context denotation | Context interpretation | Context denotation (`ctx_denote_under`) in `Denotation/theories/Context.v` (line 17) | `⟦ctx⟧[Σ] Γ` |
| Result graph formula | Step-to-result formula | Result formula (`expr_result_formula_at`) and notation in `ContextBasicDenotation/theories/TermOpen.v` (line 1086) | `FResult[D ⊢ e ⇓ x]` |
| Basic typing formula | Basic typing atom | Basic typing formula (`expr_basic_typing_formula`) and notation in `ContextBasicDenotation/theories/BasicTypingFormula.v` (line 1136) | `FHasType[Σ ⊢ e ⋮ T]` |
| Typing judgment | Typing rules | Context typing judgment (`has_context_type`) in `ContextTyping/theories/Typing.v` (line 103) | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ` |
| Typing well-formedness | Typing side conditions | Well-formedness (`context_typing_wf`) in `ContextTyping/theories/Typing.v` (line 66) | `Γ ⊢wf[Σ] e ⋮ τ` |
| Semantic type subsumption | Subtyping/subsumption rule | Semantic subtype (`sub_type_under`) in `ContextTyping/theories/Typing.v` (line 44) | `Γ ⊢ᶜ τ1 ≤[Σ] τ2` |
| Semantic context subsumption | Context subsumption rule | Semantic context subtype (`ctx_sub_under`) in `ContextTyping/theories/Typing.v` (line 54) | `Γ1 ≤ᶜ[Σ; X] Γ2` |
| Primitive-operation context | Primitive-operation typing interface | Primitive signature (`primop_sig`) and context (`primop_ctx`) in `ContextTyping/theories/PrimOpContext.v` (lines 17 and 30); well-formedness (`wf_primop_ctx`) in `ContextTyping/theories/PrimOpContext.v` (line 56) | `wf_primop_ctx Φ` |
| Concrete primitive context | Concrete primitive instance | Concrete context (`concrete_Φ`) in `ContextTyping/theories/PrimOpConcreteContext.v` (line 171); well-formedness theorem (`concrete_Φ_wf`) in `ContextTyping/theories/PrimOpConcreteContext.v` (line 1297) | `concrete_Φ` |
| Fundamental theorem | Main theorem | `Fundamental` in `ContextTyping/theories/Soundness.v` (line 977) | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ -> ⟦ctx⟧[Σ] Γ ⊫ ...` |
| Closed-program denotational soundness | Soundness theorem | `denotational_soundness` in `ContextTyping/theories/Soundness.v` (line 1079) | closed programs have a result world satisfying `TyDenote[...]` |
| Concrete soundness wrappers | Concrete theorem instances | `concrete_Fundamental` and `concrete_denotational_soundness` in `ContextTyping/theories/Soundness.v` (lines 1152 and 1159) | concrete versions instantiate `Φ := concrete_Φ` |

The artifact defines universal quantification and persistence in forms that
are slightly different from the paper presentation because these definitions
are more convenient for the mechanized proof.  For `∀. P`, the locally
nameless definition is related to the expected quantified behavior by
`res_models_forall_iff`, `res_models_forall_rev`, and
`res_models_forall_rev_intro`.  For `□ P`, the implementation uses singleton
projection over the formula support; `res_models_persist_iff` states this
characterization, and `persistent_formula_equiv_persist`,
`persistent_star_self`, and `persistent_star_and` prove the algebraic laws used
in the paper.

The artifact's magic wand also has a more explicit locally nameless shape:
`P -∗[d] Q` records how many bound variables in `P` and `Q` must be kept in
scope when the wand is opened.  This makes the definition look more detailed
than the paper rule, but it has the same semantic role.  Proof Details gives
the informal explanation of this binder-depth parameter.

## Proof Details

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

### Binder-aware wand

Because the artifact uses locally nameless binders, opening a formula under a
wand must account for the bound variables that remain in scope on both sides
of the wand.  The parameter `d` in `P -∗[d] Q` records this binder depth.  In
ordinary value-level uses, `d = 1`; nested result-first definitions may require
the depth to be stated explicitly.

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

### Reading guide

For the central definitions and theorems, start with:

1. `ContextLogic/theories/FormulaSemantics.v`
2. `ContextBasicDenotation/theories/TermOpen.v`
3. `Denotation/theories/TypeDenote.v`
4. `Denotation/theories/Context.v`
5. `ContextTyping/theories/Typing.v`
6. `ContextTyping/theories/Soundness.v`

For function cases, read `Denotation/theories/ResultFirstOpen.v` before the
Arrow/Wand proof files.  For persistence, read
`ContextLogic/theories/FormulaConnectivesHigher.v`, the `TypePersist*.v` files,
`ContextTyping/theories/Typing.v`, and
`ContextTyping/theories/SoundnessPersist.v`.
