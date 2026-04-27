# Skill: Open typeclass and ^^ notation — avoid category-specific notations

## Problem

When `value` and `tm` are mutual inductives, it's tempting to define separate
notations for "open a tm" vs "open a value":

```coq
Notation "v '^v^' x" := (open_value 0 (vfvar x) v) (at level 20).
Notation "e '^t^' x" := (open_tm    0 (vfvar x) e) (at level 20).
```

These are **redundant** once the `Open` typeclass instances are registered and
the `atom → value` coercion is in place.

## Solution: use generic `^^`

Register the instances:
```coq
#[global] Instance open_value_inst : Open value value := open_value.
#[global] Instance open_tm_inst    : Open value tm    := open_tm.
```

With the coercion `Coercion vfvar : atom >-> value`, the generic notation
```coq
Notation "e '^^' x" := (open_one 0 x e) (at level 20).
```
handles both categories:
- `e ^^ x` where `e : tm`, `x : atom`  →  `open_tm 0 (vfvar x) e`
- `v ^^ x` where `v : value`, `x : atom`  →  `open_value 0 (vfvar x) v`

No separate `^t^` or `^v^` needed.

## General rule

**Do not define category-specific notation for a typeclass operation.**
Register a typeclass instance, rely on coercions for auxiliary conversions
(`atom → value` here), and use the single generic notation.  The typeclass
dispatcher handles dispatch; notation level and coercions handle the type.

## Exception

If two categories have the *same* carrier type but the notation would be
ambiguous (e.g., `open_value : nat → value → value → value` vs
`open_tm : nat → value → tm → tm`, both instantiate `Open value _`), the
instance uniquely disambiguates via unification, so a single notation is still
sufficient.

## How to apply

For every LN operation (open, close, subst, lc, fv):
1. Define the mutual-recursive fixpoints separately.
2. Register a typeclass instance for each syntactic category.
3. Add `Arguments <inst> /.` so `simpl`/`unfold` sees through the instance.
4. Use ONE generic notation per operation, not one per category.
