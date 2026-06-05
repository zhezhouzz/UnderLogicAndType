(** * Stores *)

From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Export StoreCore.
From ContextStore Require Export StoreFilterMapKey.
From ContextStore Require Export StoreRestrict.
From ContextStore Require Export LVarStore.
From ContextStore Require Export StoreInterface.

Notation store_restrict := storeA_restrict (only parsing).

(** ** Store-side proof automation

    [store_normalize] exposes the finite-map/set normal forms that recur around
    [storeA_restrict], [storeA_swap], and the other generic store operations.
    [better_store_solver] follows the same shape as [better_set_solver] and
    [better_base_solver]: first normalize store expressions, then discharge the
    remaining map/set/base obligations with the shared automation. *)

Set Warnings "-cast-in-pattern".

Ltac store_set_normalize :=
  repeat progress (try map_normalize; try set_normalize).

Ltac store_restrict_normalize :=
  repeat match goal with
  | H : context[dom (storeA_restrict ?σ ?X : gmap _ _)] |- _ =>
      rewrite (storeA_restrict_dom σ X) in H
  | |- context[dom (storeA_restrict ?σ ?X : gmap _ _)] =>
      rewrite (storeA_restrict_dom σ X)
  | H : context[storeA_restrict (storeA_restrict ?σ ?X) ?Y] |- _ =>
      rewrite (storeA_restrict_restrict σ X Y) in H
  | |- context[storeA_restrict (storeA_restrict ?σ ?X) ?Y] =>
      rewrite (storeA_restrict_restrict σ X Y)
  | H : context[storeA_restrict ∅ ?X] |- _ =>
      rewrite (storeA_restrict_empty X) in H
  | |- context[storeA_restrict ∅ ?X] =>
      rewrite (storeA_restrict_empty X)
  | H : context[storeA_restrict ?σ ∅] |- _ =>
      rewrite (storeA_restrict_empty_set σ) in H
  | |- context[storeA_restrict ?σ ∅] =>
      rewrite (storeA_restrict_empty_set σ)
  | Hsub : dom (?σ : gmap _ _) ⊆ ?X,
    H : context[storeA_restrict ?σ ?X] |- _ =>
      rewrite (storeA_restrict_idemp σ X Hsub) in H
  | Hsub : dom (?σ : gmap _ _) ⊆ ?X
    |- context[storeA_restrict ?σ ?X] =>
      rewrite (storeA_restrict_idemp σ X Hsub)
  | Hdom : dom (?σ : gmap _ _) = ?X,
    H : context[storeA_restrict ?σ ?X] |- _ =>
      rewrite (storeA_restrict_idemp_eq σ X Hdom) in H
  | Hdom : dom (?σ : gmap _ _) = ?X
    |- context[storeA_restrict ?σ ?X] =>
      rewrite (storeA_restrict_idemp_eq σ X Hdom)
  end.

Ltac store_insert_normalize :=
  repeat match goal with
  | H : context[storeA_restrict (<[?x := ?v]> ?σ) ?X] |- _ =>
      rewrite (storeA_restrict_insert_in σ X x v) in H by better_set_solver
  | H : context[storeA_restrict (<[?x := ?v]> ?σ) ?X] |- _ =>
      rewrite (storeA_restrict_insert_notin σ X x v) in H by better_set_solver
  | |- context[storeA_restrict (<[?x := ?v]> ?σ) ?X] =>
      rewrite (storeA_restrict_insert_in σ X x v) by better_set_solver
  | |- context[storeA_restrict (<[?x := ?v]> ?σ) ?X] =>
      rewrite (storeA_restrict_insert_notin σ X x v) by better_set_solver
  end.

Ltac store_lookup_normalize :=
  repeat match goal with
  | H : context[storeA_restrict ?σ ?X !! ?x] |- _ =>
      rewrite (storeA_restrict_lookup σ X x) in H
  | |- context[storeA_restrict ?σ ?X !! ?x] =>
      rewrite (storeA_restrict_lookup σ X x)
  | H : context[@gmap_lookup ?K ?EqK ?CountK ?A ?x (storeA_restrict ?σ ?X)] |- _ =>
      rewrite (@storeA_restrict_lookup A K CountK σ X x) in H
  | |- context[@gmap_lookup ?K ?EqK ?CountK ?A ?x (storeA_restrict ?σ ?X)] =>
      rewrite (@storeA_restrict_lookup A K CountK σ X x)
  | H : context[decide (?P)] |- _ =>
      rewrite (decide_True P) in H by better_set_solver
  | |- context[decide (?P)] =>
      rewrite (decide_True P) by better_set_solver
  | H : context[decide (?P)] |- _ =>
      rewrite (decide_False P) in H by better_set_solver
  | |- context[decide (?P)] =>
      rewrite (decide_False P) by better_set_solver
  end.

Ltac store_key_normalize :=
  repeat match goal with
  | H : context[dom (storeA_swap ?x ?y ?σ : gmap _ _)] |- _ =>
      rewrite (storeA_swap_dom x y σ) in H
  | |- context[dom (storeA_swap ?x ?y ?σ : gmap _ _)] =>
      rewrite (storeA_swap_dom x y σ)
  | H : context[storeA_swap ?x ?y (storeA_swap ?x ?y ?σ)] |- _ =>
      rewrite (storeA_swap_involutive x y σ) in H
  | |- context[storeA_swap ?x ?y (storeA_swap ?x ?y ?σ)] =>
      rewrite (storeA_swap_involutive x y σ)
  | H : context[storeA_swap ?x ?y ∅] |- _ =>
      rewrite (storeA_rekey_empty (swap x y)) in H
  | |- context[storeA_swap ?x ?y ∅] =>
      rewrite (storeA_rekey_empty (swap x y))
  | H : context[storeA_shift ?k ∅] |- _ =>
      rewrite (storeA_shift_empty k) in H
  | |- context[storeA_shift ?k ∅] =>
      rewrite (storeA_shift_empty k)
  | H : context[dom (storeA_shift ?k ?σ : gmap _ _)] |- _ =>
      rewrite (storeA_shift_dom k σ) in H
  | |- context[dom (storeA_shift ?k ?σ : gmap _ _)] =>
      rewrite (storeA_shift_dom k σ)
  end.

Ltac store_normalize :=
  try repeat progress
    (try store_set_normalize;
     try store_restrict_normalize;
     try store_insert_normalize;
     try store_lookup_normalize;
     try store_key_normalize).

Ltac store_finish :=
  first
    [ solve [reflexivity]
    | solve [congruence]
    | solve [better_base_solver]
    | solve [better_map_solver]
    | solve [better_set_solver]
    | solve [eauto 8] ].

Ltac store_restrict_lookup_split :=
  repeat match goal with
  | H : (storeA_restrict ?σ ?X : gmap _ _) !! ?x = Some ?v |- _ =>
      apply storeA_restrict_lookup_some in H as [? ?]
  | Hlook : (?σ : gmap _ _) !! ?x = Some ?v,
    Hx : ?x ∈ ?X
    |- (storeA_restrict ?σ ?X : gmap _ _) !! ?x = Some ?v =>
      exact (storeA_restrict_lookup_some_2 σ X x v Hlook Hx)
  | Hlook : (?σ : gmap _ _) !! ?x = None
    |- (storeA_restrict ?σ ?X : gmap _ _) !! ?x = None =>
      exact (storeA_restrict_lookup_none_l σ X x Hlook)
  | Hx : ?x ∉ ?X
    |- (storeA_restrict ?σ ?X : gmap _ _) !! ?x = None =>
      exact (storeA_restrict_lookup_none_r σ X x Hx)
  end.

Ltac better_store_solver :=
  store_restrict_lookup_split;
  store_normalize;
  store_restrict_lookup_split;
  repeat match goal with
  | H : (storeA_restrict ?σ ?X : gmap _ _) !! ?x = Some ?v |- _ =>
      apply storeA_restrict_lookup_some in H as [? ?]
  | Hlook : (?σ : gmap _ _) !! ?x = Some ?v,
    Hx : ?x ∈ ?X
    |- (storeA_restrict ?σ ?X : gmap _ _) !! ?x = Some ?v =>
      exact (storeA_restrict_lookup_some_2 σ X x v Hlook Hx)
  | Hlook : (?σ : gmap _ _) !! ?x = None
    |- (storeA_restrict ?σ ?X : gmap _ _) !! ?x = None =>
      exact (storeA_restrict_lookup_none_l σ X x Hlook)
  | Hx : ?x ∉ ?X
    |- (storeA_restrict ?σ ?X : gmap _ _) !! ?x = None =>
      exact (storeA_restrict_lookup_none_r σ X x Hx)
  | |- dom (storeA_restrict ?σ ?X : gmap _ _) ⊆ ?X =>
      exact (storeA_restrict_dom_subset σ X)
  | Hdom : dom (?σ : gmap _ _) = ?X
    |- storeA_restrict ?σ ?X = ?σ =>
      exact (storeA_restrict_idemp_eq σ X Hdom)
  | Hsub : dom (?σ : gmap _ _) ⊆ ?X
    |- storeA_restrict ?σ ?X = ?σ =>
      exact (storeA_restrict_idemp σ X Hsub)
  | Hdisj : dom (?σ1 : gmap _ _) ## dom (?σ2 : gmap _ _)
    |- storeA_compat ?σ1 ?σ2 =>
      exact (storeA_disj_dom_compat σ1 σ2 Hdisj)
  | Hc : storeA_compat ?σ1 ?σ2,
    H1 : (?σ1 : gmap _ _) !! ?x = Some ?v1,
    H2 : (?σ2 : gmap _ _) !! ?x = Some ?v2
    |- ?v1 = ?v2 =>
      eapply Hc; [exact H1 | exact H2]
  end;
  store_normalize;
  store_finish.

Ltac store_norm := store_normalize.
Ltac store_solver := better_store_solver.

Set Warnings "+cast-in-pattern".

#[global] Instance stale_store {A} : Stale (gmap atom A) := dom.
Arguments stale_store /.
