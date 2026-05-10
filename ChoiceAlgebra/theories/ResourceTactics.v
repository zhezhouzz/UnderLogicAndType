(** * Resource proof automation

    This file keeps resource-specific Ltac outside [ChoicePrelude].  The
    prelude may know about polymorphic stores, but it should not depend on
    worlds or the algebraic resource order. *)

From ChoiceAlgebra Require Import Resource.
From ChoicePrelude Require Import Store.

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

Ltac resource_norm :=
  repeat progress (resource_world_norm; store_norm; resource_restrict_norm).

Ltac resource_solver :=
  resource_norm; try solve [store_solver | set_solver | eauto | reflexivity | congruence].
