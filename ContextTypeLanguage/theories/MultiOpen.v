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
