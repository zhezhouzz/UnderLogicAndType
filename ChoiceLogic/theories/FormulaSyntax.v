From ChoiceLogic Require Export LogicQualifier.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Choice Logic syntax

    Formulas track lvar support first; atom free variables are the projection
    [lvars_fv].  Exists is intentionally absent in this phase because the type
    denotation path does not need it yet. *)

Section Formula.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).

Inductive Formula : Type :=
  | FTrue
  | FFalse
  | FAtom    (a : LogicQualifierT)
  | FAnd     (p q : Formula)
  | FOr      (p q : Formula)
  | FImpl    (p q : Formula)
  | FStar    (p q : Formula)
  | FWand    (p q : Formula)
  | FPlus    (p q : Formula)
  | FForall  (p : Formula)
  | FOver    (p : Formula)
  | FUnder   (p : Formula)
  | FFibVars (D : lvset) (p : Formula).

Fixpoint formula_lvars (φ : Formula) : lvset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => lqual_lvars q
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FWand p q | FPlus p q =>
      formula_lvars p ∪ formula_lvars q
  | FForall p => formula_lvars p
  | FOver p | FUnder p => formula_lvars p
  | FFibVars D p => D ∪ formula_lvars p
  end.

Definition formula_fv (φ : Formula) : aset :=
  lvars_fv (formula_lvars φ).

Definition formula_stale : Formula → aset := formula_fv.

#[global] Instance stale_formula : Stale Formula := formula_fv.
Arguments stale_formula /.

Fixpoint formula_measure (φ : Formula) : nat :=
  match φ with
  | FTrue | FFalse | FAtom _ => 1
  | FAnd p q | FOr p q | FImpl p q | FStar p q | FWand p q | FPlus p q =>
      1 + formula_measure p + formula_measure q
  | FForall p | FOver p | FUnder p | FFibVars _ p =>
      1 + formula_measure p
  end.

Fixpoint formula_open (k : nat) (x : atom) (φ : Formula) : Formula :=
  match φ with
  | FTrue => FTrue
  | FFalse => FFalse
  | FAtom q => FAtom (lqual_open k x q)
  | FAnd p q => FAnd (formula_open k x p) (formula_open k x q)
  | FOr p q => FOr (formula_open k x p) (formula_open k x q)
  | FImpl p q => FImpl (formula_open k x p) (formula_open k x q)
  | FStar p q => FStar (formula_open k x p) (formula_open k x q)
  | FWand p q => FWand (formula_open k x p) (formula_open k x q)
  | FPlus p q => FPlus (formula_open k x p) (formula_open k x q)
  | FForall p => FForall (formula_open (S k) x p)
  | FOver p => FOver (formula_open k x p)
  | FUnder p => FUnder (formula_open k x p)
  | FFibVars D p => FFibVars (lvars_open k x D) (formula_open k x p)
  end.

Lemma formula_open_true k x :
  formula_open k x FTrue = FTrue.
Proof. reflexivity. Qed.

Lemma formula_open_false k x :
  formula_open k x FFalse = FFalse.
Proof. reflexivity. Qed.

Lemma formula_open_atom k x q :
  formula_open k x (FAtom q) = FAtom (lqual_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_and k x p q :
  formula_open k x (FAnd p q) =
  FAnd (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_or k x p q :
  formula_open k x (FOr p q) =
  FOr (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_impl k x p q :
  formula_open k x (FImpl p q) =
  FImpl (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_star k x p q :
  formula_open k x (FStar p q) =
  FStar (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_wand k x p q :
  formula_open k x (FWand p q) =
  FWand (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_plus k x p q :
  formula_open k x (FPlus p q) =
  FPlus (formula_open k x p) (formula_open k x q).
Proof. reflexivity. Qed.

Lemma formula_open_forall k x p :
  formula_open k x (FForall p) =
  FForall (formula_open (S k) x p).
Proof. reflexivity. Qed.

Lemma formula_open_over k x p :
  formula_open k x (FOver p) =
  FOver (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_under k x p :
  formula_open k x (FUnder p) =
  FUnder (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_fibvars k x D p :
  formula_open k x (FFibVars D p) =
  FFibVars (lvars_open k x D) (formula_open k x p).
Proof. reflexivity. Qed.

Lemma formula_open_preserves_measure k x φ :
  formula_measure (formula_open k x φ) = formula_measure φ.
Proof.
  revert k. induction φ; intros k; simpl; eauto; lia.
Qed.

Lemma formula_open_fv_subset k x φ :
  formula_fv (formula_open k x φ) ⊆ formula_fv φ ∪ {[x]}.
Proof.
  revert k. induction φ; intros k;
    unfold formula_fv in *;
    cbn [formula_lvars formula_open].
  - set_solver.
  - set_solver.
  - destruct a as [D P]. cbn [lqual_fv lqual_dom lqual_open].
    apply lvars_fv_open_subset.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - rewrite !lvars_fv_union. specialize (IHφ1 k). specialize (IHφ2 k).
    set_solver.
  - apply IHφ.
  - apply IHφ.
  - apply IHφ.
  - rewrite !lvars_fv_union.
    pose proof (lvars_fv_open_subset k x D) as HD.
    specialize (IHφ k). set_solver.
Qed.

Lemma formula_open_fv_subset_env k x φ X :
  formula_fv φ ⊆ X →
  formula_fv (formula_open k x φ) ⊆ X ∪ {[x]}.
Proof.
  intros Hfv.
  pose proof (formula_open_fv_subset k x φ) as Hopen.
  set_solver.
Qed.

Lemma formula_measure_pos (φ : Formula) :
  0 < formula_measure φ.
Proof. induction φ; simpl; lia. Qed.

Definition FPure (P : Prop) : Formula :=
  FAtom (lqual ∅ (λ _, P)).

Definition FResourceAtom {A : Type} `{IntoLVars A}
    (D : A) (P : LWorldOn (V := V) (into_lvars D) → Prop) : Formula :=
  FAtom (lqual (into_lvars D) P).

Lemma formula_fv_FResourceAtom_lvars D P :
  formula_fv (FResourceAtom D P) = lvars_fv D.
Proof. reflexivity. Qed.

Lemma formula_open_FResourceAtom_lvars k x (D : lvset) P :
  formula_open k x (FResourceAtom D P) =
  FResourceAtom (lvars_open k x D)
    (λ w, P (lworld_on_open_back k x D w)).
Proof. reflexivity. Qed.

Lemma FResourceAtom_ext (D : lvset) P1 P2 :
  (∀ m, P1 m ↔ P2 m) →
  FResourceAtom D P1 = FResourceAtom D P2.
Proof.
  intros HP. unfold FResourceAtom. simpl.
  f_equal. f_equal.
  apply functional_extensionality. intros m.
  apply propositional_extensionality. apply HP.
Qed.

End Formula.
