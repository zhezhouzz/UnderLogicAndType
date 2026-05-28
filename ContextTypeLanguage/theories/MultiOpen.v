(** * ContextTypeLanguage.MultiOpen

    Generic finite-map multi-opening infrastructure.

    This file is intentionally syntax-only: it knows about the opening
    operations on type-language syntax, but not about type environments or
    denotation. *)

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms.
From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export SyntaxEquiv.

Class MOpen Env A B := mopen : Env -> A -> B.
Arguments mopen {_ _ _ _} _ _.

Notation "η ⊙ x" := (mopen η x)
  (at level 30, right associativity, format "η  ⊙  x").

Class OpenCommute (A : Type) (openA : nat -> atom -> A -> A)
    (R : relation A) := {
  open_commute :
    forall i j x y (a : A),
      i <> j ->
      x <> y ->
      R (openA i x (openA j y a)) (openA j y (openA i x a));
}.

Class OpenProper (A : Type) (openA : nat -> atom -> A -> A)
    (R : relation A) := {
  open_proper :
    forall i x, Proper (R ==> R) (openA i x);
}.

#[global] Instance open_proper_cty_vars_equiv :
  OpenProper context_ty cty_open cty_vars_equiv.
Proof.
  constructor. intros i x τ1 τ2 Hτ.
  apply cty_vars_equiv_open. exact Hτ.
Qed.

#[global] Instance open_commute_cty_vars_equiv :
  OpenCommute context_ty cty_open cty_vars_equiv.
Proof.
  constructor. intros i j x y τ Hij Hxy.
  rewrite cty_open_commute_fvar by assumption. reflexivity.
Qed.

#[global] Instance open_commute_cty_eq :
  OpenCommute context_ty cty_open eq.
Proof.
  constructor. intros i j x y τ Hij Hxy.
  apply cty_open_commute_fvar; assumption.
Qed.

#[global] Instance open_commute_lvars :
  OpenCommute lvset lvars_open eq.
Proof.
  constructor. intros i j x y D Hij Hxy.
  rewrite !lvars_open_unfold.
  rewrite set_swap_conjugate.
  replace (swap (LVBound i) (LVFree x) (LVBound j)) with (LVBound j).
  2:{ unfold swap. repeat destruct decide; congruence. }
  replace (swap (LVBound i) (LVFree x) (LVFree y)) with (LVFree y).
  2:{ unfold swap. repeat destruct decide; congruence. }
  reflexivity.
Qed.

#[global] Instance open_commute_qual_eq :
  OpenCommute type_qualifier qual_open_atom eq.
Proof.
  constructor. intros i j x y q Hij Hxy.
  apply qual_open_commute_fvar; assumption.
Qed.

Class MOpenInsertLaws A B `{Open atom A}
    `{MOpen (gmap nat atom) A B} := {
  mopen_insert_norm :
    forall k x η (a : A),
      η !! k = None ->
      open_env_avoids_atom x η ->
      mopen η ({k ~> x} a) = mopen (<[k := x]> η) a;
}.

Definition open_env_values_inj (η : gmap nat atom) : Prop :=
  forall i j x,
    η !! i = Some x ->
    η !! j = Some x ->
    i = j.

Lemma open_env_values_inj_empty :
  open_env_values_inj ∅.
Proof.
  intros i j x Hi _.
  rewrite lookup_empty in Hi. discriminate.
Qed.

Lemma open_env_values_inj_insert k x η :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_env_values_inj (<[k := x]> η).
Proof.
  intros Hfresh Havoid Hinj i j z Hi Hj.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_insert in Hi.
    destruct (decide (k = k)) as [_|Hbad]; [|congruence].
    assert (z = x) by congruence. subst z.
    destruct (decide (j = k)) as [->|Hjk]; [reflexivity|].
    rewrite lookup_insert_ne in Hj by congruence.
    exfalso. exact (Havoid j Hj).
  - rewrite lookup_insert_ne in Hi by congruence.
    destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert in Hj.
      destruct (decide (k = k)) as [_|Hbad]; [|congruence].
      assert (z = x) by congruence. subst z.
      exfalso. exact (Havoid i Hi).
    + rewrite lookup_insert_ne in Hj by congruence.
      apply (Hinj i j z); assumption.
Qed.

Lemma open_env_values_inj_lift η :
  open_env_values_inj η ->
  open_env_values_inj ((kmap S η)).
Proof.
  intros Hinj i j x Hi Hj.
  destruct i as [|i].
  - rewrite open_env_lift_lookup_zero_none in Hi. discriminate.
  - destruct j as [|j].
    + rewrite open_env_lift_lookup_zero_none in Hj. discriminate.
    + assert (η !! i = Some x) as Hiη.
      {
        rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
          S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η i) in Hi.
        exact Hi.
      }
      assert (η !! j = Some x) as Hjη.
      {
        rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
          S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η j) in Hj.
        exact Hj.
      }
      f_equal. eapply Hinj; eassumption.
Qed.

Lemma open_env_values_inj_insert_inv η k x :
  η !! k = None ->
  open_env_values_inj (<[k := x]> η) ->
  open_env_values_inj η /\ open_env_avoids_atom x η.
Proof.
  intros Hfresh Hinj.
  split.
  - intros i j y Hi Hj.
    eapply Hinj.
    + rewrite lookup_insert_ne by congruence. exact Hi.
    + rewrite lookup_insert_ne by congruence. exact Hj.
  - intros j Hj.
    pose proof (Hinj k j x) as Hsame.
    rewrite lookup_insert_eq in Hsame.
    rewrite lookup_insert_ne in Hsame by congruence.
    specialize (Hsame eq_refl Hj). congruence.
Qed.

Lemma open_map_fold_insert_fresh_eq
    {A : Type} (openA : nat -> atom -> A -> A)
    `{!OpenCommute A openA eq}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  map_fold openA a (<[k := x]> η) =
  openA k x (map_fold openA a η).
Proof.
  intros Hfresh Havoid Hinj.
  apply (map_fold_insert_L (M:=gmap nat) (A:=atom) (B:=A)
    openA a k x η).
  - intros i j xi xj acc Hij Hi Hj.
    apply open_commute; [exact Hij|].
    intros Heq. subst xj.
    pose proof (open_env_values_inj_insert k x η Hfresh Havoid Hinj)
      as Hinj'.
    apply Hij. eapply Hinj'; eassumption.
  - exact Hfresh.
Qed.

Lemma open_map_fold_insert_fresh_rel
    {A : Type} (R : relation A) `{!PreOrder R}
    (openA : nat -> atom -> A -> A)
    `{HproperInst : !OpenProper A openA R}
    `{HcommuteInst : !OpenCommute A openA R}
    (η : gmap nat atom) k x (a : A) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  R (map_fold openA a (<[k := x]> η))
    (openA k x (map_fold openA a η)).
Proof.
  intros Hfresh Havoid Hinj.
  destruct HproperInst as [Hproper].
  destruct HcommuteInst as [Hcommute].
  eapply (map_fold_insert (M := gmap nat) (A := atom) (B := A)
    R openA a k x η).
  - intros i y. apply Hproper.
  - intros i j xi xj acc Hij Hi Hj.
    apply Hcommute; [exact Hij|].
    intros Heq. subst xj.
    pose proof (open_env_values_inj_insert k x η Hfresh Havoid Hinj)
      as Hinj'.
    apply Hij. eapply Hinj'; eassumption.
  - exact Hfresh.
Qed.
