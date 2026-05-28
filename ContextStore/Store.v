(** * Stores *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Export StoreCore.
From ContextStore Require Export StoreKeyAction.
From ContextStore Require Export StoreRestrictCore.
From ContextStore Require Export StoreRestrictUnion.
From ContextStore Require Export StoreBind.
From ContextStore Require Export StoreInterfaceCompat.

Notation "σ '|ₛ' X" := (store_restrict σ X)
  (at level 30, format "σ  |ₛ  X").

(** ** Store-side proof automation

    [store_norm] exposes the finite-map/set normal forms that recur around
    [store_restrict].  [store_solver] is intentionally opt-in and conservative:
    it performs store-specific rewrites, then leaves pure freshness/domain
    obligations to [better_set_solver]. *)

Ltac store_set_norm :=
  repeat progress (map_normalize; set_normalize).

Ltac store_restrict_norm :=
  repeat match goal with
  | H : context[dom (store_restrict ?σ ?X)] |- _ =>
      rewrite (store_restrict_dom σ X) in H
  | |- context[dom (store_restrict ?σ ?X)] =>
      rewrite (store_restrict_dom σ X)
  | H : context[store_restrict (store_restrict ?σ ?X) ?Y] |- _ =>
      rewrite (store_restrict_restrict σ X Y) in H
  | |- context[store_restrict (store_restrict ?σ ?X) ?Y] =>
      rewrite (store_restrict_restrict σ X Y)
  | H : context[store_restrict ∅ ?X] |- _ =>
      rewrite (store_restrict_empty X) in H
  | |- context[store_restrict ∅ ?X] =>
      rewrite (store_restrict_empty X)
  | H : context[store_restrict ?σ ∅] |- _ =>
      rewrite (store_restrict_empty_set σ) in H
  | |- context[store_restrict ?σ ∅] =>
      rewrite (store_restrict_empty_set σ)
  end.

Ltac store_insert_norm :=
  repeat match goal with
  | H : context[store_restrict (<[?x := ?v]> ?σ) ?X] |- _ =>
      rewrite (store_restrict_insert_in σ X x v) in H by better_set_solver
  | H : context[store_restrict (<[?x := ?v]> ?σ) ?X] |- _ =>
      rewrite (store_restrict_insert_notin σ X x v) in H by better_set_solver
  | |- context[store_restrict (<[?x := ?v]> ?σ) ?X] =>
      rewrite (store_restrict_insert_in σ X x v) by better_set_solver
  | |- context[store_restrict (<[?x := ?v]> ?σ) ?X] =>
      rewrite (store_restrict_insert_notin σ X x v) by better_set_solver
  end.

Ltac store_lookup_norm :=
  repeat match goal with
  | H : context[store_restrict ?σ ?X !! ?x] |- _ =>
      rewrite (store_restrict_lookup σ X x) in H
  | |- context[store_restrict ?σ ?X !! ?x] =>
      rewrite (store_restrict_lookup σ X x)
  | H : context[decide (?P)] |- _ =>
      rewrite (decide_True P) in H by better_set_solver
  | |- context[decide (?P)] =>
      rewrite (decide_True P) by better_set_solver
  | H : context[decide (?P)] |- _ =>
      rewrite (decide_False P) in H by better_set_solver
  | |- context[decide (?P)] =>
      rewrite (decide_False P) by better_set_solver
  end.

Ltac store_norm :=
  repeat progress (store_set_norm; store_restrict_norm; store_insert_norm; store_lookup_norm).

Ltac store_solver :=
  store_norm; try solve [better_map_solver | better_set_solver | eauto 6 | reflexivity | congruence].

#[global] Instance stale_store {A} : Stale (gmap atom A) := dom.
Arguments stale_store /.
