# Skill: Formula atoms as logic qualifiers

## Current convention

`ChoiceLogic.Formula` is not parameterized by an arbitrary atom type.  Atomic
formulas store logic qualifiers:

```coq
FAtom : logic_qualifier -> Formula
```

Consequently, satisfaction has no separate atom interpretation parameter:

```coq
res_models : WorldT -> Formula -> Prop
```

The atom case delegates to `logic_qualifier_denote` with the current explicit
store environment.

## Qualifier embedding

ChoiceType still has a type-level shallow qualifier:

```coq
type_qualifier : Type
qual_interp    : StoreT -> type_qualifier -> Prop
```

Its embedding into logic is intentionally abstract for now:

```coq
type_qualifier_to_logic : type_qualifier -> logic_qualifier
```

Expression atoms are also abstract for now:

```coq
expr_logic_qual : tm -> atom -> logic_qualifier
```

Use `FAtom (type_qualifier_to_logic q)` or `FAtom (expr_logic_qual e ν)` when
translating into a Choice Logic formula.

## Logic qualifier denotation

Logic qualifiers store a domain and a predicate:

```coq
lqual : aset -> (StoreT -> WorldT -> Prop) -> logic_qualifier
```

Denotation takes the explicit store environment and world, restricts both to
the recorded domain, and then applies the predicate:

```coq
logic_qualifier_denote (lqual d p) σ w =
  p (store_restrict σ d) (res_restrict w d)
```

## Fiberwise modality

`FFib x p` changes the current well-formed world to each `x`-fiber and extends
the explicit store environment with the projected store.  The current store
environment must be disjoint from `{x}`.

```coq
| FFib x p =>
    dom rho ## {[x]} /\
    forall sigma (Hproj : res_restrict m {[x]} sigma),
      res_models_with_store (rho ∪ sigma)
        (res_fiber_from_projection m {[x]} sigma Hproj) p
```
