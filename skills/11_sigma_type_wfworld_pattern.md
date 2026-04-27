# Skill: WfWorld — sigma type for well-formedness

## Problem

A type `T` has a predicate `P : T → Prop` that every "real" object must satisfy
(well-formedness, local closure, typing, …).  Operations on `T` may only preserve
`P` under extra side conditions.  Two tempting but problematic designs:

1. **Everything on raw `T`**: `P` must be re-proved everywhere; order/algebra laws
   must lug around wf hypotheses; there is no type-level guarantee.
2. **Duplicate every operation**: define `op : T → T` AND a separate
   `wf_op : WfT → ... → WfT`.  This creates redundant boilerplate and diverging
   definitions to keep in sync.

## Solution: sigma type + single layer

```coq
Definition WfT : Type := { x : T | P x }.

(* Coercion: treat a WfT as a T where needed *)
Coercion wft_raw (w : WfT) : T := proj1_sig w.
Definition wft_pf (w : WfT) : P (wft_raw w) := proj2_sig w.

(* Define operations ONLY on WfT *)
Definition wft_op (w1 w2 : WfT) (side : side_cond w1 w2) : WfT :=
  exist _ (raw_op w1 w2) (raw_op_wf (wft_pf w1) (wft_pf w2) side).
```

**Rules:**
- Raw `T` operations (`raw_op`) are internal helpers — mark them `Local` or place
  them inside the section without export.
- The sigma-type `WfT` is the public interface.
- Every `WfT` lemma gets the wf proof "for free" from `wft_pf`; no manual
  `wf_world` hypothesis required in theorem statements.

## Concrete instance: Resource.v

```
World      : raw record (domain + store predicate)
wf_world   : well-formedness predicate
WfWorld    := { m : World | wf_world m }

res_product, res_sum, res_restrict, fiber : World → … → World  (Local helpers)
wfw_product, wfw_sum, wfw_restrict, wfw_fiber : WfWorld → … → WfWorld  (public)
```

## Why

- Fixes `ca_le_refl` in `ChoiceAlgebra`: when the carrier is `WfWorld`,
  `res_le_refl w` is provable because `wft_pf w : wf_world w` is in scope.
- Partial orders (`⊑`, `PreOrder`, `AntiSymm`) are registered on `WfWorld`
  using stdpp conventions (see skill 12).
- `proof_irrelevance` is needed to prove sigma-type equality:
  `exist _ x p1 = exist _ x p2` when `p1 p2 : P x`.

## How to apply

Use this pattern whenever you have:
- A type `T` with a non-trivial wf predicate
- Operations that need wf proofs to stay closed
- A need to register typeclass instances (order, algebra) on the "good" objects
