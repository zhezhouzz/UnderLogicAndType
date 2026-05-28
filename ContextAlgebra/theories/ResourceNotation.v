(** * ContextAlgebra.ResourceNotation

    Proof-facing notation for resource algebra operations.

    The definitions remain in [Resource].  This file only adds a compact
    surface syntax, with explicit-proof variants next to proof-inferred ones. *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import Store.
From ContextAlgebra Require Import Resource.

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

Module ResourceNotationSmoke.
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
End ResourceNotationSmoke.
