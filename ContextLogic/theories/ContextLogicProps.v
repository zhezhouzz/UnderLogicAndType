(** * ContextLogic.ContextLogicProps

    High-level algebraic properties of the store-free formula semantics. *)

From ContextLogic Require Import FormulaSemantics FormulaTactics FormulaConnectivesCore FormulaImpl FormulaWand FormulaForall.

Section ContextLogicProps.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Notation sat m φ := (res_models m φ).
Notation "φ ⊫ ψ" := (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** Over and under remain monotone.  Ordinary forall monotonicity is no longer
    exported as a separate lemma: the extension-form map lemmas are the useful
    interface under the new semantics. *)
Lemma over_mono (p q : FormulaT) :
  (p ⊫ q) → (FOver p ⊫ FOver q).
Proof.
  unfold entails, res_models. intros Hpq m Hover.
  simpl in Hover |- *.
  destruct Hover as [_ [m' [Hsub Hp]]].
  assert (Hq : res_models_fuel (formula_measure q) m' q).
  {
    unfold res_models in Hpq.
    apply Hpq. exact Hp.
  }
  split.
  - destruct Hsub as [Hdom _].
    change (formula_scoped_in_world m q).
    eapply formula_scoped_world_dom_eq; [symmetry; exact Hdom |].
    eapply res_models_fuel_scoped; exact Hq.
  - exists m'. split; [exact Hsub | exact Hq].
Qed.

Lemma under_mono (p q : FormulaT) :
  (p ⊫ q) → (FUnder p ⊫ FUnder q).
Proof.
  unfold entails, res_models. intros Hpq m Hunder.
  simpl in Hunder |- *.
  destruct Hunder as [_ [m' [Hsub Hp]]].
  assert (Hq : res_models_fuel (formula_measure q) m' q).
  {
    unfold res_models in Hpq.
    apply Hpq. exact Hp.
  }
  split.
  - destruct Hsub as [Hdom _].
    change (formula_scoped_in_world m q).
    eapply formula_scoped_world_dom_eq; [exact Hdom |].
    eapply res_models_fuel_scoped; exact Hq.
  - exists m'. split; [exact Hsub | exact Hq].
Qed.

Definition ext (φ : FormulaT) : WfWorldT → Prop :=
  λ m, sat m φ.

Definition over_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m m'.

Definition under_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m' m.

Lemma over_ext_eq (p : FormulaT) :
  ∀ m, ext (FOver p) m ↔ under_closure (ext p) m.
Proof.
  intros m. unfold ext, sat, under_closure, res_models.
  split.
  - simpl. intros [_ [m' [Hsub Hp]]].
    exists m'. split; [| exact Hsub].
    unfold res_models. models_fuel_irrel Hp.
  - intros [m' [Hp Hsub]]. simpl. split.
    + destruct Hsub as [Hdom _].
      change (formula_scoped_in_world m p).
      eapply formula_scoped_world_dom_eq; [symmetry; exact Hdom |].
      eapply res_models_fuel_scoped; exact Hp.
    + exists m'. split; [exact Hsub |].
      unfold res_models in Hp. models_fuel_irrel Hp.
Qed.

Lemma under_ext_eq (p : FormulaT) :
  ∀ m, ext (FUnder p) m ↔ over_closure (ext p) m.
Proof.
  intros m. unfold ext, sat, over_closure, res_models.
  split.
  - simpl. intros [_ [m' [Hsub Hp]]].
    exists m'. split; [| exact Hsub].
    unfold res_models. models_fuel_irrel Hp.
  - intros [m' [Hp Hsub]]. simpl. split.
    + destruct Hsub as [Hdom _].
      change (formula_scoped_in_world m p).
      eapply formula_scoped_world_dom_eq; [exact Hdom |].
      eapply res_models_fuel_scoped; exact Hp.
    + exists m'. split; [exact Hsub |].
      unfold res_models in Hp. models_fuel_irrel Hp.
Qed.

Lemma over_closure_mono (R S : WfWorldT → Prop) :
  (∀ m, R m → S m) →
  ∀ m, over_closure R m → over_closure S m.
Proof.
  intros HRS m [m' [HR Hsub]].
  exists m'. split; [apply HRS; exact HR | exact Hsub].
Qed.

Lemma under_closure_mono (R S : WfWorldT → Prop) :
  (∀ m, R m → S m) →
  ∀ m, under_closure R m → under_closure S m.
Proof.
  intros HRS m [m' [HR Hsub]].
  exists m'. split; [apply HRS; exact HR | exact Hsub].
Qed.

Lemma over_closure_idempotent (R : WfWorldT → Prop) :
  ∀ m, over_closure (over_closure R) m ↔ over_closure R m.
Proof.
  intros m. split.
  - intros [m1 [[m0 [HR Hsub01]] Hsub1m]].
    exists m0. split; [exact HR |].
    eapply res_subset_trans; eauto.
  - intros HR.
    exists m. split; [exact HR | apply res_subset_refl].
Qed.

Lemma under_closure_idempotent (R : WfWorldT → Prop) :
  ∀ m, under_closure (under_closure R) m ↔ under_closure R m.
Proof.
  intros m. split.
  - intros [m1 [[m0 [HR Hsub10]] Hsubm1]].
    exists m0. split; [exact HR |].
    eapply res_subset_trans; eauto.
  - intros HR.
    exists m. split; [exact HR | apply res_subset_refl].
Qed.

End ContextLogicProps.
