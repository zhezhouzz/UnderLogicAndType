(** * Stores *)

From ContextBase Require Import Prelude LogicVarInterface.
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
    obligations to [set_solver]. *)

Ltac store_set_norm :=
  repeat match goal with
  | H : context[dom ∅] |- _ => rewrite dom_empty_L in H
  | |- context[dom ∅] => rewrite dom_empty_L
  | H : context[dom ({[_:=_]})] |- _ => rewrite dom_singleton_L in H
  | |- context[dom ({[_:=_]})] => rewrite dom_singleton_L
  | H : context[dom (<[_:=_]> _)] |- _ => rewrite dom_insert_L in H
  | |- context[dom (<[_:=_]> _)] => rewrite dom_insert_L
  | H : context[dom (delete _ _)] |- _ => rewrite dom_delete_L in H
  | |- context[dom (delete _ _)] => rewrite dom_delete_L
  | H : context[dom (_ ∪ _)] |- _ => rewrite dom_union_L in H
  | |- context[dom (_ ∪ _)] => rewrite dom_union_L
  | H : context[∅ ∪ _] |- _ => rewrite map_empty_union in H
  | |- context[∅ ∪ _] => rewrite map_empty_union
  | H : context[_ ∪ ∅] |- _ => rewrite map_union_empty in H
  | |- context[_ ∪ ∅] => rewrite map_union_empty
  | H : context[?X ∩ ?X] |- _ =>
      replace (X ∩ X) with X in H by set_solver
  | |- context[?X ∩ ?X] =>
      replace (X ∩ X) with X by set_solver
  | Hsub : ?X ⊆ ?Y, H : context[?Y ∩ ?X] |- _ =>
      replace (Y ∩ X) with X in H by set_solver
  | Hsub : ?X ⊆ ?Y |- context[?Y ∩ ?X] =>
      replace (Y ∩ X) with X by set_solver
  | Hsub : ?X ⊆ ?Y, H : context[?X ∩ ?Y] |- _ =>
      replace (X ∩ Y) with X in H by set_solver
  | Hsub : ?X ⊆ ?Y |- context[?X ∩ ?Y] =>
      replace (X ∩ Y) with X by set_solver
  end.

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
      rewrite (store_restrict_insert_in σ X x v) in H by set_solver
  | H : context[store_restrict (<[?x := ?v]> ?σ) ?X] |- _ =>
      rewrite (store_restrict_insert_notin σ X x v) in H by set_solver
  | |- context[store_restrict (<[?x := ?v]> ?σ) ?X] =>
      rewrite (store_restrict_insert_in σ X x v) by set_solver
  | |- context[store_restrict (<[?x := ?v]> ?σ) ?X] =>
      rewrite (store_restrict_insert_notin σ X x v) by set_solver
  | H : context[<[?x := ?v]> ?σ !! ?x] |- _ =>
      rewrite lookup_insert in H
  | |- context[<[?x := ?v]> ?σ !! ?x] =>
      rewrite lookup_insert
  | H : context[<[?x := ?v]> ?σ !! ?y] |- _ =>
      rewrite lookup_insert_ne in H by set_solver
  | |- context[<[?x := ?v]> ?σ !! ?y] =>
      rewrite lookup_insert_ne by set_solver
  end.

Ltac store_lookup_norm :=
  repeat match goal with
  | H : context[store_restrict ?σ ?X !! ?x] |- _ =>
      rewrite (store_restrict_lookup σ X x) in H
  | |- context[store_restrict ?σ ?X !! ?x] =>
      rewrite (store_restrict_lookup σ X x)
  | H : context[decide (?P)] |- _ =>
      rewrite (decide_True P) in H by set_solver
  | |- context[decide (?P)] =>
      rewrite (decide_True P) by set_solver
  | H : context[decide (?P)] |- _ =>
      rewrite (decide_False P) in H by set_solver
  | |- context[decide (?P)] =>
      rewrite (decide_False P) by set_solver
  end.

Ltac store_norm :=
  repeat progress (store_set_norm; store_restrict_norm; store_insert_norm; store_lookup_norm).

Ltac store_solver :=
  store_norm; try solve [set_solver | eauto 6 | reflexivity | congruence].

#[global] Instance stale_store {A} : Stale (gmap atom A) := dom.
Arguments stale_store /.
