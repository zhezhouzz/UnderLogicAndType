# Instantiation / Multi-Substitution Migration

This repo now has a CoreLang instantiation layer modeled after UnderType/HATs:

- `CoreLang/theories/Instantiation.v`
  - `env := gmap atom value`
  - `closed_env`
  - generic `msubst`
  - notation `m{σ} e`
- `CoreLang/theories/InstantiationProps.v`
  - `closed_env_*` and `lc_env_*` facts,
  - `SubstCommuteClosed`,
  - `MsubstInsert`,
  - `MsubstFresh`,
  - `MsubstFv`,
  - `MsubstRestrict`,
  - `MsubstOpen`,
  - `MsubstOpenVar`,
  - `MsubstIntro`,
  - `MsubstLc`,
  - initial `msubst_simp`.

## How To Use

- Use `msubst_insert` when rewriting an environment extension:
  `m{<[x := v]> σ} e = {x := v} (m{σ} e)`.
- Use `msubst_fresh` when `dom σ` is disjoint from the free variables of the
  target.
- Use `msubst_restrict` when a denotation has restricted the explicit store
  to a domain containing the target's free variables:
  `m{map_restrict value σ X} e = m{σ} e`.
- Use `msubst_open_var` for the common LN case where opening uses a fresh
  variable:
  `m{σ} ({k ~> vfvar x} e) = {k ~> vfvar x} (m{σ} e)`.
- Use `msubst_intro` to turn "open with a fresh variable, then extend the
  environment" into "open with the concrete value".

## Preconditions

- `closed_env σ` means every value in `σ` has empty free-variable set.
- `lc_env σ` means every value in `σ` is locally closed.
- `MsubstOpen` and `MsubstIntro` need `lc_env`; closedness alone is not enough
  because the underlying `subst_open` lemma requires locally closed substituted
  values.

## Proof Pattern

When `msubst_fresh` is applied to `vfvar x`, spell out the set goal if
automation does not see through typeclass notations:

```coq
rewrite (msubst_fresh σ (vfvar x))
  by (change (dom σ ∩ {[x]} = ∅); set_solver).
```

For fold-insertion proofs, use `map_fold_insert_L` or
`fin_maps.map_fold_ind` directly.  The commutation side condition should be
discharged through `SubstCommuteClosed`; this keeps the fold-order argument
separate from syntax-specific substitution proofs.

## Closed Environment Lookup

Use these lemmas when a denotational proof needs to evaluate a returned
variable under a store substitution:

```coq
msubst_fvar_lookup_closed
msubst_ret_fvar_lookup_closed
```

They say that if `closed_env σ` and `σ !! x = Some v`, then multi-substitution
of `vfvar x` (or `tret (vfvar x)`) yields `v` (or `tret v`).

Their proof pattern is useful when adding similar lookup lemmas:

```coq
change (map_fold (fun y vy acc => {y := vy} acc) (vfvar x) σ')
  with (m{σ'} (vfvar x)).
rewrite lookup_insert_Some in Hlookup.
```

Then split the inserted-key and old-key cases.  In the inserted-key case, use
`msubst_fresh` on the remaining environment.  In the old-key case, rewrite with
the induction hypothesis, then use `subst_fresh`; `closed_env_lookup` supplies
the closedness of the looked-up value.

At the ChoiceType layer, `store_has_type_on_closed_env` is the intended bridge
from basic store typing to `closed_env`.

## Restriction Locality

Prefer `map_restrict value σ X` in CoreLang instantiation lemmas.  The more
semantic `store_restrict` wrapper is useful in ChoicePrelude/ChoiceAlgebra, but
inside generic `map_fold` proofs it can leave Rocq trying to infer finite-map
instances for the `Store` type alias instead of the concrete `gmap`.

The useful proof shape for restriction locality is:

```coq
refine (fin_maps.map_fold_ind (fun (σ : env) => ...) _ _ σ).
```

Keep the `(σ : env)` annotation; without it, `store_restrict`/`Store` aliases
can make instance search drift.  In the insert case, split on `x ∈ X`.

- If `x ∈ X`, rewrite the restricted insert with `map_filter_insert_True`,
  then use `msubst_insert` on the restricted environment.
- If `x ∉ X`, rewrite with `map_filter_insert_not`, use the induction
  hypothesis, and finish with `subst_fresh`; `msubst_fv` plus `stale a ⊆ X`
  gives the freshness side condition.

For the restricted environment's freshness side condition, proving lookup-none
directly is often simpler than rewriting domains:

```coq
unfold map_restrict.
apply map_lookup_filter_None_2. left. exact Hfresh.
```

## Design Boundary

This migration intentionally starts in CoreLang with `value` substitution.
ChoiceType qualifiers/types open binders with atoms, so their instantiation
lemmas should be added in a later layer with care rather than forced into the
CoreLang value-opening interface.
