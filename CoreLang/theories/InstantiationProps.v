(** * CoreLang multi-substitution properties

    This file migrates the reusable part of UnderType/HATs instantiation
    infrastructure.  The definitions are phrased through small typeclasses so
    later syntactic categories can reuse the same multi-substitution facts once
    they provide the corresponding single-substitution lemmas. *)

From CoreLang Require Import Instantiation LocallyNamelessExtra.
From LocallyNameless Require Import Classes Tactics.

Lemma closed_env_insert σ x v :
  σ !! x = None ->
  closed_env (<[x := v]> σ) ->
  stale v = ∅ /\ closed_env σ.
Proof.
  intros Hfresh Hclosed.
  unfold closed_env in *.
  apply map_Forall_insert in Hclosed; [exact Hclosed | exact Hfresh].
Qed.

Lemma closed_env_lookup σ x v :
  closed_env σ ->
  σ !! x = Some v ->
  stale v = ∅.
Proof.
  unfold closed_env. intros Hclosed Hlookup.
  exact (map_Forall_lookup_1 _ _ _ _ Hclosed Hlookup).
Qed.

Ltac gen_closed_env :=
  repeat
    match goal with
    | H : closed_env (<[?x := _]> ?σ), Hfresh : ?σ !! ?x = None |- _ =>
        let Hv := fresh "Hclosed_value" in
        let Hσ := fresh "Hclosed_env" in
        destruct (closed_env_insert σ x _ Hfresh H) as [Hv Hσ];
        clear H
    | H : closed_env ?σ, Hlookup : ?σ !! ?x = Some ?v |- _ =>
        let Hv := fresh "Hclosed_value" in
        pose proof (closed_env_lookup σ x v H Hlookup) as Hv
    end.

(** Single-substitutions commute when the two substituted values are closed.
    This is the exact hypothesis needed by [map_fold_insert_L]. *)
Class SubstCommuteClosed A `{Stale A} `{SubstV value A} :=
  subst_commute_closed :
    forall (x y : atom) (vx vy : value) (a : A),
      x <> y ->
      stale vx = ∅ ->
      stale vy = ∅ ->
      {x := vx} ({y := vy} a) = {y := vy} ({x := vx} a).

#[global] Instance SubstCommuteClosed_value : SubstCommuteClosed value.
Proof.
  intros x y vx vy v Hxy Hvx Hvy.
  apply subst_commute_value; auto; my_set_solver.
Qed.

#[global] Instance SubstCommuteClosed_tm : SubstCommuteClosed tm.
Proof.
  intros x y vx vy e Hxy Hvx Hvy.
  apply subst_commute_tm; auto; my_set_solver.
Qed.

Class MsubstInsert A `{SubstV value A} := msubst_insert :
  forall (σ : env) (x : atom) (vx : value) (a : A),
    closed_env σ ->
    stale vx = ∅ ->
    σ !! x = None ->
    m{<[x := vx]> σ} a = {x := vx} (m{σ} a).

Lemma MsubstInsert_all
    (A : Type)
    (staleA : Stale A)
    (substA : SubstV value A)
    (subst_commuteA : @SubstCommuteClosed A staleA substA) :
  @MsubstInsert A substA.
Proof.
  unfold MsubstInsert, msubst. intros σ x vx a Hclosed Hvx Hfresh.
  assert (Hclosed' : closed_env (<[x := vx]> σ)).
  { unfold closed_env in *. apply map_Forall_insert_2; [exact Hvx | exact Hclosed]. }
  apply map_fold_insert_L; [| exact Hfresh].
  intros y z vy vz acc Hyz Hy Hz.
  apply subst_commute_closed; auto.
  - exact (closed_env_lookup (<[x := vx]> σ) y vy Hclosed' Hy).
  - exact (closed_env_lookup (<[x := vx]> σ) z vz Hclosed' Hz).
Qed.

#[global] Instance MsubstInsert_value : MsubstInsert value.
Proof. eapply MsubstInsert_all; typeclasses eauto. Qed.

#[global] Instance MsubstInsert_tm : MsubstInsert tm.
Proof. eapply MsubstInsert_all; typeclasses eauto. Qed.

Ltac fold_msubst :=
  change (map_fold (fun x vx acc => {x := vx} acc) ?a ?σ) with (m{σ} a) in *.

Ltac rewrite_msubst_insert :=
  cbn; fold_msubst; rewrite !msubst_insert; eauto.

Ltac msubst_simp :=
  repeat match goal with
  | |- context [m{∅} _] => rewrite msubst_empty
  | H : context [m{∅} _] |- _ => rewrite msubst_empty in H
  | |- context [m{<[?x := ?vx]> ?σ} _] =>
      rewrite (msubst_insert σ x vx); eauto
  | H : context [m{<[?x := ?vx]> ?σ} _] |- _ =>
      rewrite (msubst_insert σ x vx) in H; eauto
  end.
