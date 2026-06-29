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
- The checked core language contains the constructs needed by that core
  metatheory: `Unit`, `Bool`, `Nat`, unary primitive operations, function
  application, `let`, and boolean-specific match.  Paper-level surface
  extensions such as list/tree syntax, additional operators, and general n-ary
  primitive-operator syntax are not included in `main`.
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
  a first-order syntax tree.  This makes the support needed by fiber semantics
  explicit in the artifact.

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
  variables, stores, worlds/resources, restriction, products/sums, fibers, and
  result extensions.
- `ContextLogic` defines formulas, satisfaction, bunched connectives,
  fiber quantification, persistence, and fiberwise joinability facts.
- `CoreLang` defines the core term language, basic typing, small-step
  semantics, and operational result facts.
- `ContextTypeLanguage` defines context types, contexts, erasure,
  locally nameless operations, and well-formedness.
- `ContextBasicDenotation` defines formula atoms for basic worlds, basic
  typing, term totality/results, qualifiers, and relevant environments.
- `Denotation` defines type/context denotation, constants, result-first
  Arrow/Wand support, result extension, let transport, and primitive-operation
  denotation support.
- `ContextTyping` defines primitive-operation contexts, typing rules, and the
  soundness proof.  The main soundness proof is split by typing-rule families,
  with separate files for lambdas, applications, match, recursion, and
  persistence.

## Paper-to-artifact Correspondence

| Paper concept | Artifact counterpart | Location / note |
| --- | --- | --- |
| Core syntax and operational semantics | `tm`, `value`, `step`, result relations | `CoreLang/theories/Syntax.v`, `SmallStep.v`, `OperationalResults.v` |
| Basic typing | `has_basic_type` and regularity lemmas | `CoreLang/theories/BasicTyping.v`, `BasicTypingProps.v` |
| Qualifiers | `tqual D (Store -> Prop)` | `ContextQualifier/theories/Qualifier.v`; shallow Coq embedding with explicit support |
| Context types | `context_ty` | `ContextTypeLanguage/theories/Syntax.v` |
| Over / Under types | `{: b | φ }`, `[: b | φ ]` | Notations for `CTOver b φ`, `CTUnder b φ` |
| Precise refinement type | `precise_ty b φ` | Intersection of over and under refinements |
| Type intersection / union / sum | `τ1 ⊓ τ2`, `τ1 ⊔ τ2`, `τ1 ⊕ τ2` | Union is present in the artifact although not used in the paper examples |
| Function / separating function | `τx → τ`, `τx -∗ τ` | Context-type Arrow/Wand |
| Persistent type | `□ τ` | `CTPersist τ` |
| Contexts | `Emp`, `x ∷ τ`, `Γ1 ,, Γ2`, `Γ1 ∗ Γ2`, `Γ1 ⊕ Γ2` | `ContextTypeLanguage/theories/Syntax.v` |
| Main typing judgment | `Γ ⊢ᶜ [Φ; Σ] e ⋮ τ` | `has_context_type Φ Σ Γ e τ` in `ContextTyping/theories/Typing.v` |
| Typing well-formedness | `Γ ⊢wf[Σ] e ⋮ τ` | `context_typing_wf Σ Γ e τ` |
| Semantic type subsumption | `Γ ⊢ᶜ τ1 ≤[Σ] τ2` | `sub_type_under Σ Γ τ1 τ2` |
| Semantic context subsumption | `Γ1 ≤ᶜ[Σ; X] Γ2` | `ctx_sub_under Σ X Γ1 Γ2` |
| Formula syntax | `FormulaT` constructors | `ContextLogic/theories/FormulaSyntax.v` |
| Satisfaction | `m ⊨ P` | `res_models` in `ContextLogic/theories/FormulaSemantics.v` |
| Entailment / equivalence | `P ⊫ Q`, `P ⊣⊢ Q` | Semantic entailment and equivalence |
| Fiber / binding-reference connective | `fib D |> P` | `FFibVars D P`; set-indexed mechanized form of the paper connective |
| Universal formula | `∀. P` | `FForall P`; locally nameless binder |
| Persistent formula | `□ P` | `FPersist P` |
| Formula wand | `P -∗[d] Q` | `FBWand d P Q`; `d` is the locally nameless binder-depth parameter used by the mechanized definition |
| Type denotation | `⟦ty τ⟧[Σ, gas] e`, `⟦ty τ⟧[Δ] e`, `TyDenote[Δ; τ; e]` | `Denotation/theories/TypeDenote.v` |
| Context denotation | `⟦ctx⟧[Σ] Γ` | `ctx_denote_under Σ Γ` |
| Result graph / step-to-result formula | `FResult[D ⊢ e ⇓ x]` | `expr_result_formula_at D e x` |
| Basic typing formula | `FHasType[Σ ⊢ e ⋮ T]` | `expr_basic_typing_formula Σ e T` |
| Primitive operation context | `primop_ctx`, `wf_primop_ctx Φ` | `ContextTyping/theories/PrimOpContext.v` |
| Concrete primitive context | `concrete_Φ`, `concrete_Φ_wf` | `ContextTyping/theories/PrimOpConcreteContext.v` |
| Fundamental theorem | `Fundamental` | `ContextTyping/theories/Soundness.v` |
| Closed-program denotational soundness | `denotational_soundness` | `ContextTyping/theories/Soundness.v` |
| Concrete wrappers | `concrete_Fundamental`, `concrete_denotational_soundness` | `ContextTyping/theories/SoundnessConcrete.v` |

Two logic definitions are more precise in the artifact than in the prose
presentation.  The universal formula is implemented as a locally nameless
binder, with opening lemmas connecting it to the expected quantified behavior.
The persistent modality is implemented by singleton projection over the
formula's support; `res_models_persist_iff` states this characterization, and
`persistent_formula_equiv_persist`, `persistent_star_self`, and
`persistent_star_and` prove the algebraic laws used in the paper.

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
