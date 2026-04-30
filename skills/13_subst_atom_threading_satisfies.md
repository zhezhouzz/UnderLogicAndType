# Skill: subst_atom threading in satisfies

## Problem

The `satisfies` fixpoint for Choice Logic takes a `subst_atom : StoreT → A → A`
parameter that appears to be unused in most cases — only the `FFib` case
actively calls it.  Why thread it through every branch?

## The FFib semantics

```
m ⊨ ∀X. p  ↔  ∀ σ_X ∈ proj(m, X).  fiber(m, σ_X) ⊨ σ_X(p)
```

The "σ_X(p)" part means: substitute σ_X into every atom of p.  If `p` contains
a nested `FFib Y q`, then evaluating `σ_X(FFib Y q)` = `FFib Y (σ_X(q))`,
so the substitution must compose across levels.

## Why not formula substitution?

The direct approach would be:
```coq
| FFib X p =>
    ∀ σ, res_restrict m X σ →
      satisfies interp sa (fiber m σ) (formula_subst sa σ p)
```
where `formula_subst` recurses on the formula structure.  **Problem**: Rocq's
structural `Fixpoint` checker requires the recursive argument to be a syntactic
subterm of the input.  `formula_subst sa σ p` is NOT a subterm of `FFib X p`,
so Rocq rejects this definition.

## The threading trick

Instead, thread σ into the interpretation function:

```coq
| FFib X p =>
    ∀ σ,
      res_restrict m X σ →
      satisfies (λ a, interp (sa σ a)) sa (fiber m σ) p
```

The recursive call has `p` as argument (a strict subterm of `FFib X p`), so
Rocq accepts the `Fixpoint`.  Unfolding confirms this equals the formula-subst
approach when `sa` distributes correctly over `interp`.

## Consequence: parameter threading

`sa` must be passed to EVERY branch so it is available when a nested `FFib`
is reached.  In all other branches it is merely forwarded unchanged.  This is
a **structural necessity**, not dead code.

## Correct instantiation

If atoms are closed (contain no free variables that FFib could capture):
```coq
sa := λ σ a, a   (* identity: FFib's substitution is a no-op on atoms *)
```

For qualifier atoms in ChoiceType:
```coq
sa := qual_subst   (* applies σ to the values inside a qualifier *)
```

## How to apply

Whenever a Fixpoint needs to apply a parametric transformation to recursive
sub-cases but the transformed term is not a syntactic subterm, thread the
transformation as an extra function parameter.  The pattern:

```coq
Fixpoint F (transform : ...) (x : T) : Prop :=
  match x with
  | Leaf a => ... transform ...
  | Node p q =>
      F transform p ∧ F transform q
  | Binder y body =>
      ∀ σ, F (compose σ transform) body  (* compose, not apply-then-recur *)
  end.
```
