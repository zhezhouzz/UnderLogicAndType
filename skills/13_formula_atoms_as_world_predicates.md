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

The atom case delegates to `logic_qualifier_denote`.

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

Logic qualifiers store a domain, a concrete store, and a predicate:

```coq
lqual : aset -> StoreT -> (StoreT -> WorldT -> Prop) -> logic_qualifier
```

Denotation restricts both the stored store and the input world to the recorded
domain before applying the predicate:

```coq
logic_qualifier_denote (lqual d σ p) w =
  p (store_restrict σ d) (res_restrict w d)
```

## Fiberwise modality

`FFib X p` changes the current well-formed world to each `X`-fiber and checks
the same formula there:

```coq
| FFib X p =>
    forall sigma (Hproj : res_restrict m X sigma),
      res_models (res_fiber_from_projection m X sigma Hproj) p
```

There is no `subst_atom` threading in the logic core.  Any qualifier-specific
substitution belongs in the qualifier layer, not in `Formula.res_models`.
