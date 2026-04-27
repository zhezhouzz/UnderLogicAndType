# Skill: Partial order in stdpp

## Problem

Rocq's standard library has `PartialOrder` but stdpp uses a different (more
composable) convention.  Using the wrong set of instances causes typeclass
resolution failures or duplicated instances.

## stdpp convention

A partial order on type `M` requires three separate instances:

```coq
(* Step 1: the relation itself *)
#[global] Instance my_sqsubseteq : SqSubsetEq M :=
  fun x y => (* your ≤ relation *).

(* Step 2: reflexivity + transitivity *)
#[global] Instance my_preorder : PreOrder (sqsubseteq (A := M)).
Proof.
  constructor.
  - (* reflexivity *) ...
  - (* transitivity *) ...
Qed.

(* Step 3: antisymmetry (gives the partial order) *)
#[global] Instance my_antisym : AntiSymm eq (sqsubseteq (A := M)).
Proof.
  intros x y Hle Hge. (* prove x = y from x ⊑ y and y ⊑ x *) ...
Qed.
```

The notation `x ⊑ y` resolves to `sqsubseteq x y`.

## Why three instances, not one?

stdpp separates `PreOrder` (refl + trans) from `AntiSymm` to allow registering
preorders (weak orderings) without committing to antisymmetry.  Search for
`SqSubsetEq`, `PreOrder`, `AntiSymm` in stdpp source for how they compose.

## Sigma-type equality in AntiSymm

When the carrier is a sigma type `{x : T | P x}`:

```coq
intros ⟨x1, H1⟩ ⟨x2, H2⟩ Hle Hge.
assert (Heq : x1 = x2) by (* use antisymmetry of the underlying ≤ *).
subst. f_equal. apply proof_irrelevance.
```

`proof_irrelevance` (from `Stdlib.Logic.ProofIrrelevance`) closes the goal
`H1 = H2 : P x1` for any `P`.

## Key import

```coq
From Stdlib Require Import Logic.ProofIrrelevance.
```

## How to apply

Whenever you define a carrier type for an algebra or lattice in stdpp style,
immediately register all three instances.  The ordering `SqSubsetEq → PreOrder
→ AntiSymm` is the canonical stdpp approach; deviating causes notation or
typeclass failures.
