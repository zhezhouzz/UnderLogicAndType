(** * ContextLogic.FormulaWand

    Derived proof principles for wand formulas. *)

From ContextLogic Require Import LogicQualifier Formula FormulaTactics FormulaConnectivesCore FormulaImpl.

Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_wand_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FWand φ ψ) →
  (∀ m' Hc,
     m' ⊨ φ →
     res_product m' m Hc ⊨ ψ) →
  m ⊨ FWand φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hwand. split; [exact Hscope |].
  intros m' Hc Hφ.
  assert (Hφ_model : m' ⊨ φ).
  { unfold res_models. models_fuel_irrel Hφ. }
  pose proof (Hwand m' Hc Hφ_model) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_wand_elim
    (m1 m2 : WfWorldT) (Hc : world_compat m1 m2) (φ ψ : FormulaT) :
  m2 ⊨ FWand φ ψ →
  m1 ⊨ φ →
  res_product m1 m2 Hc ⊨ ψ.
Proof.
  unfold res_models.
  simpl. intros [_ Hwand] Hφ.
  assert (Hφ_fuel :
      res_models_fuel (formula_measure φ + formula_measure ψ) m1 φ).
  { models_fuel_irrel Hφ. }
  pose proof (Hwand m1 Hc Hφ_fuel) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_wand_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FWand φ ψ) →
  (m ⊨ FWand φ ψ ↔
    ∀ m' Hc,
      m' ⊨ φ →
      res_product m' m Hc ⊨ ψ).
Proof.
  intros Hscope. split.
  - intros Hwand m' Hc Hφ. eapply res_models_wand_elim; eauto.
  - intros Hwand. eapply res_models_wand_intro; eauto.
Qed.

Lemma res_models_wand_antecedent_strengthen
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world m (FWand φ2 ψ) →
  (∀ (m' : WfWorldT) (Hc : world_compat m' m),
    m' ⊨ φ2 →
    m' ⊨ φ1) →
  m ⊨ FWand φ1 ψ →
  m ⊨ FWand φ2 ψ.
Proof.
  intros Hscope Hφ Hwand.
  eapply res_models_wand_intro; [exact Hscope |].
  intros m' Hc Hφ2.
  eapply res_models_wand_elim; [exact Hwand |].
  eapply Hφ; eauto.
Qed.

Lemma res_models_wand_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FWand φ2 ψ2) →
  (∀ (m' : WfWorldT) (Hc : world_compat m' m),
    m' ⊨ φ2 →
    m' ⊨ φ1) →
  (∀ (m' : WfWorldT) (Hc : world_compat m' m),
    res_product m' m Hc ⊨ ψ1 →
    res_product m' m Hc ⊨ ψ2) →
  m ⊨ FWand φ1 ψ1 →
  m ⊨ FWand φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Hwand.
  eapply res_models_wand_intro; [exact Hscope |].
  intros m' Hc Hφ2.
  eapply Hψ.
  eapply res_models_wand_elim; [exact Hwand |].
  eapply Hφ; eauto.
Qed.

Lemma res_models_wand_antecedent_strengthen_simple
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world m (FWand φ2 ψ) →
  (∀ m', m' ⊨ φ2 → m' ⊨ φ1) →
  m ⊨ FWand φ1 ψ →
  m ⊨ FWand φ2 ψ.
Proof.
  intros Hscope Hφ.
  eapply res_models_wand_antecedent_strengthen; [exact Hscope |].
  intros m' _ Hφ2. apply Hφ. exact Hφ2.
Qed.

Lemma res_models_wand_map_simple
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FWand φ2 ψ2) →
  (∀ m', m' ⊨ φ2 → m' ⊨ φ1) →
  (∀ m', m' ⊨ ψ1 → m' ⊨ ψ2) →
  m ⊨ FWand φ1 ψ1 →
  m ⊨ FWand φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ.
  eapply res_models_wand_map; [exact Hscope | |].
  - intros m' _ Hφ2. apply Hφ. exact Hφ2.
  - intros m' Hc Hψ1. apply Hψ. exact Hψ1.
Qed.

End FormulaConnectives.
