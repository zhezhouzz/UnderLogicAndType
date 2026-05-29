From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceInterface ResourceCompat.

(** * ContextAlgebra.ResourceSurface

    Proof-facing notation for resource algebra operations.

    The definitions remain in the resource interface files.  This file only adds a compact
    surface syntax, with explicit-proof variants next to proof-inferred ones. *)


Notation "m1 '×[' Hc ']' m2" :=
  (res_product m1 m2 Hc)
  (at level 40, Hc at level 0, left associativity,
   format "m1  ×[ Hc ]  m2").

Notation "m1 × m2" :=
  (res_product m1 m2 _)
  (at level 40, left associativity,
   format "m1  ×  m2").

Notation "m1 '⊕ᵣ[' Hdef ']' m2" :=
  (res_sum m1 m2 Hdef)
  (at level 50, Hdef at level 0, left associativity,
   format "m1  ⊕ᵣ[ Hdef ]  m2").

Notation "m1 ⊕ᵣ m2" :=
  (res_sum m1 m2 _)
  (at level 50, left associativity,
   format "m1  ⊕ᵣ  m2").

Notation "m '|ᵣ' X" :=
  (res_restrict m X)
  (at level 35, X at level 35, right associativity,
   format "m  |ᵣ  X").

Notation "wfib '∈ᶠ' 'Fiber(' w ',' X ',' σ ')'" :=
  (res_fiber_from_projection w X σ wfib)
  (at level 70, w at level 0, X at level 0, σ at level 0,
   format "wfib  ∈ᶠ  Fiber( w ,  X ,  σ )").

Module ResourceSurfaceSmoke.
  Section Smoke.
    Context {V : Type} `{ValueSig V}.
    Variables m n : WfWorld (V := V).
    Variable wfib : WfWorld (V := V).
    Variable σ : gmap atom V.
    Variable Hc : world_compat m n.
    Variable Hdef : raw_sum_defined m n.

    Example product_notation :
      m ×[Hc] n = res_product m n Hc := eq_refl.

    Example sum_notation :
      m ⊕ᵣ[Hdef] n = res_sum m n Hdef := eq_refl.

    Example restrict_notation :
      m |ᵣ world_dom (m : World (V := V)) =
      res_restrict m (world_dom (m : World (V := V))) := eq_refl.

    Example fiber_projection_notation :
      wfib ∈ᶠ Fiber(m, world_dom (m : World (V := V)), σ) =
      res_fiber_from_projection m (world_dom (m : World (V := V))) σ wfib :=
      eq_refl.
  End Smoke.
End ResourceSurfaceSmoke.


(** * Resource proof automation

    This file keeps resource-specific Ltac outside [ContextStore].  The
    prelude may know about polymorphic stores, but it should not depend on
    worlds or the algebraic resource order. *)


Ltac resource_world_norm :=
  cbn [world_dom world_stores raw_unit raw_product raw_sum raw_restrict raw_fiber] in *.

Ltac resource_restrict_norm :=
  repeat match goal with
  | H : context[res_restrict (res_restrict ?w ?X) ?Y] |- _ =>
      rewrite (res_restrict_restrict_eq w X Y) in H
  | |- context[res_restrict (res_restrict ?w ?X) ?Y] =>
      rewrite (res_restrict_restrict_eq w X Y)
  | Hle : ?m ⊑ ?n, H : context[res_restrict ?n (world_dom ?m)] |- _ =>
      rewrite (res_restrict_eq_of_le m n Hle) in H
  | Hle : ?m ⊑ ?n |- context[res_restrict ?n (world_dom ?m)] =>
      rewrite (res_restrict_eq_of_le m n Hle)
  end.

Ltac resource_store_dom_solver :=
  try solve
  [ better_store_solver
  | better_set_solver
  | eapply wfworldA_store_dom_subset; [eassumption | better_set_solver]
  ].

Ltac resource_norm :=
  repeat progress (resource_world_norm; store_normalize; resource_restrict_norm).

Ltac resource_solver :=
  resource_norm;
  try solve
    [ better_store_solver
    | resource_store_dom_solver
    | better_set_solver
    | eauto 6
    | reflexivity
    | congruence ].
