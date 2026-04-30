# Skill: Formula atoms as world predicates

## Current convention

`ChoiceLogic.Formula` is not parameterized by an arbitrary atom type.  Atomic
formulas are already semantic predicates over well-formed worlds:

```coq
FAtom : (WorldT -> Prop) -> Formula
```

Consequently, satisfaction has no separate atom interpretation parameter:

```coq
res_models : WorldT -> Formula -> Prop
```

The atom case is just predicate application.

## Qualifier embedding

ChoiceType still has a syntactic `qualifier` type with a store-level
interpretation:

```coq
qual_interp_world : qualifier -> RawWorldT
qual_atom         : qualifier -> WorldT -> Prop
```

Use `FAtom (qual_atom q)` when translating a qualifier into a Choice Logic
formula.

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
