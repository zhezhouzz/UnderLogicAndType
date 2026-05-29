(** * ContextLogic.FormulaImpl

    Derived proof principles for implication formulas. *)

From ContextLogic Require Import LogicQualifier FormulaSemantics FormulaTactics FormulaConnectivesCore.

Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_impl_future_iff_local (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  ((∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hφscope Hψscope. split.
  - intros Hfuture Hφ. eapply Hfuture; [reflexivity | exact Hφ].
  - intros Hlocal m' Hle Hφ.
    assert (Hφ_base : m ⊨ φ).
    {
      pose proof (res_models_minimal_on (world_dom (m : WorldT)) m' φ)
        as Hminimal.
      assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
      { exact Hφscope. }
      specialize (Hminimal Hfv).
      rewrite (res_restrict_eq_of_le m m' Hle) in Hminimal.
      apply (proj1 Hminimal). exact Hφ.
    }
    eapply res_models_kripke; [exact Hle |].
    eauto.
Qed.

Lemma res_models_impl_future_iff_local_from_impl_scope
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  ((∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hscope.
  eapply res_models_impl_future_iff_local;
    apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope;
    tauto.
Qed.

Lemma res_models_impl_intro_future (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
     m' ⊨ φ →
     m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hfuture. split; [exact Hscope |].
  intros m' Hle Hφ.
  assert (Hφ_model : m' ⊨ φ).
  { unfold res_models. models_fuel_irrel Hφ. }
  pose proof (Hfuture m' Hle Hφ_model) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_impl_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hscope Hlocal.
  eapply res_models_impl_intro_future; [exact Hscope |].
  apply (proj2 (res_models_impl_future_iff_local_from_impl_scope
    m φ ψ Hscope)).
  exact Hlocal.
Qed.

Lemma res_models_impl_intro_scoped (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hφscope Hψscope Hlocal.
  eapply res_models_impl_intro.
  - apply (proj2 (formula_scoped_impl_iff m φ ψ)).
    split; assumption.
  - exact Hlocal.
Qed.

Lemma res_models_impl_iff_future (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (m ⊨ FImpl φ ψ ↔
    ∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ Himpl] m' Hle Hφ.
    assert (Hφ_fuel :
        res_models_fuel (formula_measure φ + formula_measure ψ) m' φ).
    { models_fuel_irrel Hφ. }
    pose proof (Himpl m' Hle Hφ_fuel) as Hψ.
    unfold res_models. models_fuel_irrel Hψ.
  - intros Hfuture. eapply res_models_impl_intro_future; eauto.
Qed.

Lemma res_models_impl_elim_future (m n : WfWorldT) (φ ψ : FormulaT) :
  m ⊑ n →
  m ⊨ FImpl φ ψ →
  n ⊨ φ →
  n ⊨ ψ.
Proof.
  intros Hle Himpl Hφ.
  unfold res_models in Himpl.
  simpl in Himpl. destruct Himpl as [_ Himpl].
  assert (Hφ_fuel :
      res_models_fuel (formula_measure φ + formula_measure ψ) n φ).
  { models_fuel_irrel Hφ. }
  pose proof (Himpl n Hle Hφ_fuel) as Hψ.
  unfold res_models. models_fuel_irrel Hψ.
Qed.

Lemma res_models_impl_elim (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  intros Himpl Hφ.
  eapply res_models_impl_elim_future; [reflexivity | exact Himpl | exact Hφ].
Qed.

Lemma res_models_impl2_intro
    (m : WfWorldT) (φ ψ χ : FormulaT) :
  formula_scoped_in_world m (FImpl φ (FImpl ψ χ)) →
  (m ⊨ φ → m ⊨ ψ → m ⊨ χ) →
  m ⊨ FImpl φ (FImpl ψ χ).
Proof.
  intros Hscope Hlocal.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ.
  eapply res_models_impl_intro.
  - eapply formula_scoped_impl_r. exact Hscope.
  - intros Hψ. exact (Hlocal Hφ Hψ).
Qed.

Lemma res_models_impl2_elim
    (m : WfWorldT) (φ ψ χ : FormulaT) :
  m ⊨ FImpl φ (FImpl ψ χ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ χ.
Proof.
  intros Himpl Hφ Hψ.
  eapply res_models_impl_elim; [| exact Hψ].
  eapply res_models_impl_elim; eauto.
Qed.

Lemma res_models_impl2_map
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 χ1 χ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 (FImpl ψ2 χ2)) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ2 → m ⊨ ψ1) →
  (m ⊨ χ1 → m ⊨ χ2) →
  m ⊨ FImpl φ1 (FImpl ψ1 χ1) →
  m ⊨ FImpl φ2 (FImpl ψ2 χ2).
Proof.
  intros Hscope Hφ Hψ Hχ Himpl.
  eapply res_models_impl2_intro; [exact Hscope |].
  intros Hφ2 Hψ2.
  apply Hχ.
  eapply res_models_impl2_elim; [exact Himpl | |].
  - apply Hφ. exact Hφ2.
  - apply Hψ. exact Hψ2.
Qed.

Lemma res_models_impl_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (m ⊨ FImpl φ ψ ↔
    (m ⊨ φ →
      m ⊨ ψ)).
Proof.
  intros Hscope. split.
  - intros Himpl Hφ. eapply res_models_impl_elim; eauto.
  - intros Himpl. eapply res_models_impl_intro; eauto.
Qed.

Lemma res_models_impl_iff_scoped (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  (m ⊨ FImpl φ ψ ↔
    (m ⊨ φ →
      m ⊨ ψ)).
Proof.
  intros Hφscope Hψscope.
  eapply res_models_impl_iff.
  apply (proj2 (formula_scoped_impl_iff m φ ψ)).
  split; assumption.
Qed.

Lemma res_models_impl_antecedent_strengthen_future
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 ψ) →
  (∀ m', m ⊑ m' →
     m' ⊨ φ2 →
     m' ⊨ φ1) →
  m ⊨ FImpl φ1 ψ →
  m ⊨ FImpl φ2 ψ.
Proof.
  intros Hscope Hφ Himpl.
  eapply res_models_impl_intro_future; [exact Hscope |].
  intros m' Hle Hφ2.
  eapply res_models_impl_elim_future; [exact Hle | exact Himpl |].
  eapply Hφ; eauto.
Qed.

Lemma res_models_impl_antecedent_strengthen
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 ψ) →
  (m ⊨ φ2 → m ⊨ φ1) →
  m ⊨ FImpl φ1 ψ →
  m ⊨ FImpl φ2 ψ.
Proof.
  intros Hscope Hφ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  eapply res_models_impl_elim; [exact Himpl |].
  apply Hφ. exact Hφ2.
Qed.

Lemma res_models_impl_map_future
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 ψ2) →
  (∀ m', m ⊑ m' → m' ⊨ φ2 → m' ⊨ φ1) →
  (∀ m', m ⊑ m' → m' ⊨ ψ1 → m' ⊨ ψ2) →
  m ⊨ FImpl φ1 ψ1 →
  m ⊨ FImpl φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Himpl.
  eapply res_models_impl_intro_future; [exact Hscope |].
  intros m' Hle Hφ2.
  eapply Hψ; [exact Hle |].
  eapply res_models_impl_elim_future; [exact Hle | exact Himpl |].
  eapply Hφ; eauto.
Qed.

Lemma res_models_impl_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 ψ2) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ1 → m ⊨ ψ2) →
  m ⊨ FImpl φ1 ψ1 →
  m ⊨ FImpl φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  apply Hψ.
  eapply res_models_impl_elim; [exact Himpl |].
  apply Hφ. exact Hφ2.
Qed.

End FormulaConnectives.
