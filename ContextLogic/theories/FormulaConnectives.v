(** * ContextLogic.FormulaConnectives

    Derived proof principles for Context Logic connectives. *)

From ContextLogic Require Import LogicQualifier FormulaSemantics.
From ContextAlgebra Require Import ResourceInterface ResourceCompat.
From Stdlib Require Import Lia.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for the store-free formula semantics.  This file
    keeps only statements that still describe useful structure under the new
    dependent-lqual and extension-based forall definitions. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma formula_scoped_in_world_from_formula_fv
    (m : WfWorldT) (φ : FormulaT) :
  formula_fv φ ⊆ world_dom (m : WorldT) →
  formula_scoped_in_world m φ.
Proof.
  intros Hfv.
  eapply (formula_scoped_from_fv_subset m φ (world_dom (m : WorldT)));
    [set_solver | exact Hfv].
Qed.

Lemma res_models_and_intro_from_models (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  intros Hφ Hψ.
  eapply res_models_and_intro; [| exact Hφ | exact Hψ].
  apply (proj2 (formula_scoped_and_iff m φ ψ)).
  split; eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_and_iff (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FAnd φ ψ ↔ m ⊨ φ ∧ m ⊨ ψ.
Proof.
  split.
  - intros Hand. split.
    + eapply res_models_and_elim_l; exact Hand.
    + eapply res_models_and_elim_r; exact Hand.
  - intros [Hφ Hψ]. eapply res_models_and_intro_from_models; eauto.
Qed.

Lemma res_models_or_intro_l_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  formula_fv ψ ⊆ world_dom (m : WorldT) →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφ Hψscope.
  eapply res_models_or_intro_l; [| exact Hφ].
  apply (proj2 (formula_scoped_or_iff m φ ψ)).
  split; [eapply res_models_fuel_scoped; eauto | exact Hψscope].
Qed.

Lemma res_models_or_intro_r_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ ⊆ world_dom (m : WorldT) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφscope Hψ.
  eapply res_models_or_intro_r; [| exact Hψ].
  apply (proj2 (formula_scoped_or_iff m φ ψ)).
  split; [exact Hφscope | eapply res_models_fuel_scoped; eauto].
Qed.

Lemma res_models_or_transport_between_worlds
    (m n : WfWorldT) (φa φb ψa ψb : FormulaT) :
  formula_fv ψa ⊆ world_dom (n : WorldT) →
  formula_fv ψb ⊆ world_dom (n : WorldT) →
  (m ⊨ φa → n ⊨ ψa) →
  (m ⊨ φb → n ⊨ ψb) →
  m ⊨ FOr φa φb →
  n ⊨ FOr ψa ψb.
Proof.
  intros Hψa Hψb Ha Hb Hor.
  unfold res_models in Hor.
  simpl in Hor.
  destruct Hor as [_ [Hleft | Hright]].
  - eapply res_models_or_intro_l_from_model.
    + apply Ha. unfold res_models. models_fuel_irrel Hleft.
    + exact Hψb.
  - eapply res_models_or_intro_r_from_model.
    + exact Hψa.
    + apply Hb. unfold res_models. models_fuel_irrel Hright.
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  formula_scoped_in_world m (FStar φ ψ) →
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hle Hφ Hψ.
  split; [exact Hscope |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_star_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FStar φ ψ) →
  (m ⊨ FStar φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
      res_product m1 m2 Hc ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hc [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hc. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hc [Hle [Hφ Hψ]]]]].
    eapply res_models_star_intro; eauto.
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  formula_scoped_in_world m (FPlus φ ψ) →
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hle Hφ Hψ.
  split; [exact Hscope |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_plus_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FPlus φ ψ) →
  (m ⊨ FPlus φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
      res_sum m1 m2 Hdef ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hdef. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]].
    eapply res_models_plus_intro; eauto.
Qed.

Lemma res_models_plus_intro_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  intros Hle Hφ Hψ.
  eapply res_models_plus_intro; [| exact Hle | exact Hφ | exact Hψ].
  unfold formula_scoped_in_world, formula_fv.
  cbn [formula_lvars].
  rewrite lvars_fv_union.
  pose proof (raw_le_dom _ _ Hle) as Hdom_sum.
  pose proof (res_models_fuel_scoped _ _ _ Hφ) as Hscopeφ.
  pose proof (res_models_fuel_scoped _ _ _ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in Hscopeφ, Hscopeψ.
  assert (Hscopeψ_m1 : lvars_fv (formula_lvars ψ) ⊆ world_dom (m1 : WorldT)).
  {
    change (world_dom (m1 : WorldT) = world_dom (m2 : WorldT)) in Hdef.
    rewrite Hdef. exact Hscopeψ.
  }
  intros z Hz.
  apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom_sum. simpl. apply Hscopeφ. exact Hz.
  - apply Hdom_sum. simpl. apply Hscopeψ_m1. exact Hz.
Qed.

Lemma res_models_plus_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FPlus φ2 ψ2) →
  (∀ m', m' ⊨ φ1 → m' ⊨ φ2) →
  (∀ m', m' ⊨ ψ1 → m' ⊨ ψ2) →
  m ⊨ FPlus φ1 ψ1 →
  m ⊨ FPlus φ2 ψ2.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ Hψ [_ Hplus]. split; [exact Hscope |].
  destruct Hplus as [m1 [m2 [Hdef [Hle [Hm1 Hm2]]]]].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - assert (Hm1_model : m1 ⊨ φ1).
    { unfold res_models. models_fuel_irrel Hm1. }
    pose proof (Hφ m1 Hm1_model) as Hm1'.
    models_fuel_irrel Hm1'.
  - assert (Hm2_model : m2 ⊨ ψ1).
    { unfold res_models. models_fuel_irrel Hm2. }
    pose proof (Hψ m2 Hm2_model) as Hm2'.
    models_fuel_irrel Hm2'.
Qed.

Lemma res_models_atom_intro (m : WfWorldT) (q : LogicQualifierT) :
  formula_scoped_in_world m (FAtom q) →
  logic_qualifier_denote q m →
  m ⊨ FAtom q.
Proof.
  unfold res_models.
  simpl. intros Hscope Hq. split; [exact Hscope | exact Hq].
Qed.

Lemma res_models_over_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FOver φ) →
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_over_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  intros Hφ.
  eapply res_models_over_intro_same; [| exact Hφ].
  apply (proj2 (formula_scoped_over_iff m φ)).
  eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_under_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FUnder φ) →
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_under_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  intros Hφ.
  eapply res_models_under_intro_same; [| exact Hφ].
  apply (proj2 (formula_scoped_under_iff m φ)).
  eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_resource_atom_intro
    (m : WfWorldT) (D : lvset)
    (P : LWorldOn (V := V) D → Prop) :
  formula_scoped_in_world m (FResourceAtom D P) →
  logic_qualifier_denote (lqual D P) m →
  m ⊨ FResourceAtom D P.
Proof.
  intros Hscope Hden.
  eapply res_models_atom_intro; [exact Hscope | exact Hden].
Qed.

Lemma res_models_resource_atom_witness_intro
    (m m0 : WfWorldT) (D : lvset)
    (P : LWorldOn (V := V) D → Prop) :
  formula_scoped_in_world m (FResourceAtom D P) →
  formula_scoped_in_world m0 (FResourceAtom D P) →
  logic_qualifier_denote (lqual D P) m0 →
  m0 ⊑ m →
  m ⊨ FResourceAtom D P.
Proof.
  intros Hscope Hscope0 Hden Hle.
  eapply res_models_resource_atom_intro; [exact Hscope |].
  eapply logic_qualifier_denote_mono.
  - exact Hden.
  - exact Hscope0.
  - exact Hle.
Qed.

Lemma res_models_FFibVars_intro (m : WfWorldT) (D : lvset) (φ : FormulaT) :
	  formula_scoped_in_world m (FFibVars D φ) →
	  lc_lvars D →
	  (∀ (σ : Store (V := V)) (mfib : WfWorldT),
	    res_fiber_from_projection m (lvars_fv D) σ mfib →
	    mfib ⊨ formula_msubst_store σ φ) →
	  m ⊨ FFibVars D φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hlc Hfib. split; [exact Hscope |].
  split; [exact Hlc |].
	  intros σ mfib Hproj.
	  specialize (Hfib σ mfib Hproj).
	  models_fuel_irrel Hfib.
Qed.

Lemma res_models_FFibVars_projection_intro
    (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world m (FFibVars D φ) →
  lc_lvars D →
	  (∀ σ mfib,
	    res_fiber_from_projection m (lvars_fv D) σ mfib →
	    mfib ⊨ formula_msubst_store σ φ) →
	  m ⊨ FFibVars D φ.
Proof.
  intros Hscope Hlc Hfib.
  eapply res_models_FFibVars_intro; [exact Hscope | exact Hlc |].
	  exact Hfib.
Qed.

Lemma res_models_FFibVars_iff (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world m (FFibVars D φ) →
	(m ⊨ FFibVars D φ ↔
	  lc_lvars D ∧
	  ∀ (σ : Store (V := V)) (mfib : WfWorldT),
	    res_fiber_from_projection m (lvars_fv D) σ mfib →
	    mfib ⊨ formula_msubst_store σ φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [Hlc Hfib]]. split; [exact Hlc |].
	    intros σ mfib Hproj.
	    specialize (Hfib σ mfib Hproj).
	    models_fuel_irrel Hfib.
  - intros [Hlc Hfib].
    eapply res_models_FFibVars_intro; eauto.
Qed.

Lemma res_models_FFibVars_projection_iff
    (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world m (FFibVars D φ) →
	(m ⊨ FFibVars D φ ↔
	  lc_lvars D ∧
	  ∀ σ mfib,
	    res_fiber_from_projection m (lvars_fv D) σ mfib →
	    mfib ⊨ formula_msubst_store σ φ).
Proof.
  intros Hscope. split.
  - intros Hmodel.
    pose proof (proj1 (res_models_FFibVars_iff m D φ Hscope) Hmodel)
      as [Hlc Hfib].
    split; [exact Hlc |].
	    exact Hfib.
  - intros [Hlc Hfib].
    eapply res_models_FFibVars_projection_intro; eauto.
Qed.

End FormulaConnectives.

Ltac normalize_models_ands_in H :=
  repeat rewrite res_models_and_iff in H.

Ltac normalize_models_ands_goal :=
  repeat rewrite res_models_and_iff.

Ltac destruct_models_formula_hyps :=
  repeat match goal with
  | H : res_models _ (FAnd _ _) |- _ =>
      rewrite res_models_and_iff in H; destruct H
  | H : res_models _ _ /\ _ |- _ =>
      destruct H
  | H : _ /\ res_models _ _ |- _ =>
      destruct H
  end.

Ltac split_models_formula_goal :=
  repeat match goal with
  | |- res_models _ (FAnd _ _) =>
      rewrite res_models_and_iff; split
  | |- res_models _ _ /\ _ =>
      split
  | |- _ /\ res_models _ _ =>
      split
  end.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for implication formulas. *)


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

Ltac use_models_impl H Hout :=
  lazymatch type of H with
  | res_models ?m (FImpl ?p ?q) =>
      let Harg := fresh "Harg" in
      assert (Harg : res_models m p);
      [ | pose proof (res_models_impl_elim m p q H Harg) as Hout;
          clear Harg ]
  | res_models ?m (formula_open ?k ?x (FImpl ?p ?q)) =>
      rewrite formula_open_impl in H;
      use_models_impl H Hout
  end.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for wand formulas. *)


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

Lemma res_models_impl_wand_map
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 χ1 χ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 (FWand ψ2 χ2)) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (∀ (n : WfWorldT) (Hc : world_compat n m),
    n ⊨ ψ2 → n ⊨ ψ1) →
  (∀ (n : WfWorldT) (Hc : world_compat n m),
    res_product n m Hc ⊨ χ1 →
    res_product n m Hc ⊨ χ2) →
  m ⊨ FImpl φ1 (FWand ψ1 χ1) →
  m ⊨ FImpl φ2 (FWand ψ2 χ2).
Proof.
  intros Hscope Hφ Hψ Hχ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  eapply res_models_wand_map.
  - eapply formula_scoped_impl_r. exact Hscope.
  - exact Hψ.
  - exact Hχ.
  - eapply res_models_impl_elim; [exact Himpl |].
    apply Hφ. exact Hφ2.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for forall under the extension-based formula
    semantics. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition res_extend_by_input_widened_to
    (m : WfWorldT) (F : fiber_extension) (X : aset) (my : WfWorldT) : Prop :=
  ∃ Fwide : fiber_extension,
    F ~>i Fwide ∧
    ext_in Fwide = X ∧
    res_extend_by m Fwide my.

Lemma res_models_forall_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F : fiber_extension,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      ∀ my : WfWorldT,
        res_extend_by m F my →
        my ⊨ formula_open 0 y φ) →
  m ⊨ FForall φ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hforall]. split; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  pose proof (Hforall y Hy F HFin HFout my Hext) as Hbody.
  models_fuel_irrel Hbody.
Qed.

Lemma res_models_forall_iff (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (m ⊨ FForall φ ↔
    ∃ L : aset,
      ∀ y : atom, y ∉ L →
      ∀ F : fiber_extension,
        ext_in F = formula_fv φ →
        ext_out F = {[y]} →
        ∀ my : WfWorldT,
          res_extend_by m F my →
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [L Hforall]]. exists L.
    intros y Hy F HFin HFout my Hext.
    specialize (Hforall y Hy F HFin HFout my Hext).
    unfold res_models. models_fuel_irrel Hforall.
  - intros Hforall.
    eapply res_models_forall_intro; eauto.
Qed.

Lemma res_models_forall_map_subset_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv ψ ⊆ formula_fv φ →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F my,
      ext_in F = formula_fv ψ →
      ext_out F = {[y]} →
      res_extend_by_input_widened_to m F (formula_fv φ) my →
      my ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hsub Hscope Hmap Hforall.
  eapply res_models_forall_intro; [exact Hscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall) as [L Hbody].
  destruct Hmap as [Lmap Hmap].
  exists (L ∪ Lmap ∪ world_dom (m : WorldT)).
  intros y Hy F HFin HFout my Hext.
  assert (HyBody : y ∉ L) by set_solver.
  assert (HyMap : y ∉ Lmap) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hin : ext_in F ⊆ formula_fv φ) by (rewrite HFin; exact Hsub).
  assert (Hdisj : formula_fv φ ## ext_out F).
  {
    rewrite HFout.
    unfold formula_scoped_in_world in Hφscope. set_solver.
  }
  pose (Fφ := fiber_extension_input_widen F (formula_fv φ) Hin Hdisj).
  assert (Hwid : F ~>i Fφ)
    by apply fiber_extension_input_widen_to_construct.
  assert (HFinφ : ext_in Fφ = formula_fv φ) by reflexivity.
  assert (HFoutφ : ext_out Fφ = {[y]}).
  {
    rewrite (input_widen_out _ _ Hwid). exact HFout.
  }
  assert (Hextφ : res_extend_by m Fφ my).
  {
    apply (proj1 (res_extend_by_input_widen_to_iff m F Fφ my Hwid
      ltac:(rewrite HFinφ; exact Hφscope))).
    exact Hext.
  }
  eapply (Hmap y HyMap F my);
    [exact HFin | exact HFout | |].
  - exists Fφ. split; [exact Hwid | split; [exact HFinφ | exact Hextφ]].
  - eapply (Hbody y HyBody Fφ); eauto.
Qed.

Lemma res_models_forall_map_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F my,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      res_extend_by m F my →
      my ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hfv Hscope [L Hmap] Hforall.
  eapply res_models_forall_map_subset_fv; [| exact Hscope | | exact Hforall].
  - rewrite <- Hfv. reflexivity.
  - exists L. intros y Hy F my _ HFout [Fφ [Hwid [HFinφ Hext]]] Hφ.
    eapply Hmap; [exact Hy | exact HFinφ | | exact Hext | exact Hφ].
    rewrite (input_widen_out _ _ Hwid). exact HFout.
Qed.

Lemma res_models_forall_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ (F : fiber_extension (V := V)) (my : WfWorldT),
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      res_extend_by m F my →
      my ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  apply res_models_forall_map_same_fv.
Qed.

Lemma res_models_forall_congr_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall φ) →
  formula_scoped_in_world m (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ (F : fiber_extension (V := V)) (my : WfWorldT),
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      res_extend_by m F my →
      (my ⊨ formula_open 0 y φ ↔
	     my ⊨ formula_open 0 y ψ)) →
  (m ⊨ FForall φ ↔ m ⊨ FForall ψ).
Proof.
  intros Hfv Hφscope Hψscope [Liff Hiff]. split.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [exact Hfv | exact Hψscope | | exact Hforall].
    exists Liff. intros y Hy F my HFin HFout Hext Hφ.
    apply (proj1 (Hiff y Hy F my HFin HFout Hext)). exact Hφ.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [symmetry; exact Hfv | exact Hφscope | | exact Hforall].
    exists Liff. intros y Hy F my HFin HFout Hext Hψ.
    apply (proj2 (Hiff y Hy F my ltac:(rewrite Hfv; exact HFin) HFout Hext)).
    exact Hψ.
Qed.

Lemma res_models_forall_transport
    (m n : WfWorldT) (φ ψ : FormulaT) :
  formula_fv ψ ⊆ formula_fv φ →
  formula_scoped_in_world n (FForall ψ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F my ny,
      ext_in F = formula_fv ψ →
      ext_out F = {[y]} →
      res_extend_by_input_widened_to m F (formula_fv φ) my →
      res_extend_by n F ny →
	      my ⊨ formula_open 0 y φ →
	      ny ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  n ⊨ FForall ψ.
Proof.
  intros Hsub Hψscope Htransport Hforall.
  eapply res_models_forall_intro; [exact Hψscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall)
    as [L Hbody].
  destruct Htransport as [Ltransport Htransport].
  exists (L ∪ Ltransport ∪ world_dom (m : WorldT)).
  intros y Hy F HFin HFout ny Hny.
  assert (HyL : y ∉ L) by set_solver.
  assert (HyTransport : y ∉ Ltransport) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hin : ext_in F ⊆ formula_fv φ) by (rewrite HFin; exact Hsub).
  assert (Hdisj : formula_fv φ ## ext_out F).
  {
    rewrite HFout.
    unfold formula_scoped_in_world in Hφscope. set_solver.
  }
  pose (Fφ := fiber_extension_input_widen F (formula_fv φ) Hin Hdisj).
  assert (Hwid : F ~>i Fφ)
    by apply fiber_extension_input_widen_to_construct.
  assert (HFinφ : ext_in Fφ = formula_fv φ) by reflexivity.
  assert (HFoutφ : ext_out Fφ = {[y]}).
  {
    rewrite (input_widen_out _ _ Hwid). exact HFout.
  }
  assert (Happ : extension_applicable Fφ m).
  {
    constructor.
    - change (ext_in Fφ ⊆ world_dom (m : WorldT)).
      rewrite HFinφ. exact Hφscope.
    - change (ext_out Fφ ## world_dom (m : WorldT)).
      rewrite HFoutφ. set_solver.
  }
  destruct (res_extend_by_exists m Fφ Happ) as [my Hmy].
  eapply (Htransport y HyTransport F my ny);
    [exact HFin | exact HFout | | exact Hny |].
  - exists Fφ. split; [exact Hwid | split; [exact HFinφ | exact Hmy]].
  - eapply (Hbody y HyL Fφ); eauto.
Qed.

Lemma res_models_forall_rev
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FForall φ ->
  exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ.
Proof.
  intros Hforall.
  pose proof (res_models_scoped m (FForall φ) Hforall) as Hscope.
  pose proof (proj1 (res_models_forall_iff m φ Hscope) Hforall)
    as [L Hbody].
  exists (L ∪ world_dom (m : WorldT)).
  intros y Hy my Hdom Hrestrict.
  assert (HyL : y ∉ L) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
  { exact Hscope. }
  destruct (forall_extension_from_world_dom_projection
    m my (formula_fv φ) y Hfv Hym Hdom Hrestrict)
    as [F [n [HFin [HFout [Hext Hproj]]]]].
  pose proof (Hbody y HyL F HFin HFout n Hext) as Hn.
  assert (Hopen_fv :
      formula_fv (formula_open 0 y φ) ⊆ formula_fv φ ∪ {[y]}).
  { apply formula_open_fv_subset. }
  apply (proj2 (res_models_minimal_on (formula_fv φ ∪ {[y]}) my
    (formula_open 0 y φ) Hopen_fv)).
  rewrite <- Hproj.
  apply (proj1 (res_models_minimal_on (formula_fv φ ∪ {[y]}) n
    (formula_open 0 y φ) Hopen_fv)).
  exact Hn.
Qed.

Lemma res_models_forall_rev_intro
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ) ->
  m ⊨ FForall φ.
Proof.
  intros Hscope [L Hfull].
  eapply res_models_forall_intro; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  eapply Hfull; [exact Hy | |].
  - pose proof (res_extend_by_dom m F my Hext) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
  - eapply res_extend_by_restrict_base; exact Hext.
Qed.

Lemma res_models_forall_full_world_iff
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (m ⊨ FForall φ <->
    exists L : aset,
      forall y : atom, y ∉ L ->
        forall my : WfWorldT,
          world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
          res_restrict my (world_dom (m : WorldT)) = m ->
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - apply res_models_forall_rev.
  - apply res_models_forall_rev_intro. exact Hscope.
Qed.

Lemma res_models_forall_full_world_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  (** This is the "full-world" view of [FForall].  The primitive semantics
      only asks extensions to read [formula_fv φ], but nested denotation
      transports often open a formula under several binders and then need to
      compare witnesses whose input domain is the whole current world.  The
      proof converts [FForall φ] to that full-world form with
      [res_models_forall_rev], maps the opened body there, and packages the
      result back with [res_models_forall_rev_intro].  This is intentionally
      independent of any [formula_fv φ = formula_fv ψ] side condition; the
      world-domain restriction/restrict-back hypotheses carry the alignment. *)
  formula_scoped_in_world m (FForall ψ) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ ->
        my ⊨ formula_open 0 y ψ) ->
  m ⊨ FForall φ ->
  m ⊨ FForall ψ.
Proof.
  intros Hψscope [Lmap Hmap] Hφ.
  pose proof (res_models_forall_rev m φ Hφ) as [Lφ Hφfull].
  eapply res_models_forall_rev_intro; [exact Hψscope |].
  exists (Lmap ∪ Lφ). intros y Hy my Hdom Hrestrict.
  eapply Hmap; [set_solver | exact Hdom | exact Hrestrict |].
  eapply Hφfull; [set_solver | exact Hdom | exact Hrestrict].
Qed.

Lemma res_models_forall_ext_transport_by_extension
    (m mx : WfWorldT) (F : fiber_extension (V := V)) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FForall ψ) →
  res_extend_by m F mx →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ Fy my myx,
      ext_in Fy = formula_fv ψ →
      ext_out Fy = {[y]} →
      res_extend_by m Fy my →
      res_extend_by my F myx →
      myx ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  mx ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hψscope HmF [Ltransport Htransport] Hmx_forall.
  eapply res_models_forall_intro; [exact Hψscope |].
  pose proof (res_models_forall_rev mx φ Hmx_forall) as [Lφ Hφrev].
  exists (Ltransport ∪ Lφ ∪ world_dom (mx : WorldT)).
  intros y Hy Fy HFin HFout my HmFy.
  assert (HyTransport : y ∉ Ltransport) by set_solver.
  assert (Hyφ : y ∉ Lφ) by set_solver.
  assert (Hymx : y ∉ world_dom (mx : WorldT)) by set_solver.
  assert (HFinFy_mx : ext_in Fy ⊆ world_dom (mx : WorldT)).
  {
    pose proof (res_extend_by_dom m F mx HmF) as Hdom_mx.
    unfold formula_scoped_in_world in Hψscope.
    rewrite HFin. set_solver.
  }
  destruct (res_extend_by_commute_exists_right m mx my F Fy HmF HmFy
    HFinFy_mx ltac:(rewrite HFout; set_solver)) as [myx [HmyF HmxFy]].
  assert (Hdom_myx : world_dom (myx : WorldT) =
      world_dom (mx : WorldT) ∪ {[y]}).
  {
    pose proof (res_extend_by_dom mx Fy myx HmxFy) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
  }
  assert (Hrestrict_myx : res_restrict myx (world_dom (mx : WorldT)) = mx).
  { eapply res_extend_by_restrict_base; exact HmxFy. }
  pose proof (Hφrev y Hyφ myx Hdom_myx Hrestrict_myx) as Hmyxφ.
  eapply Htransport; eauto.
Qed.

Lemma res_models_forall_ext_transport
    (m mx : WfWorldT) (F : fiber_extension (V := V)) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FForall ψ) →
  res_extend_by m F mx →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ my myx,
      m ⊑ my ->
      world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
      res_extend_by my F myx →
      myx ⊨ formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) →
  mx ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hψscope HmF [L Htransport] Hmx.
  eapply res_models_forall_ext_transport_by_extension; eauto.
  exists L. intros y Hy Fy my myx HFin HFout HmFy HmyF Hmyxφ.
  eapply Htransport; eauto.
  - eapply res_extend_by_le; exact HmFy.
  - pose proof (res_extend_by_dom m Fy my HmFy) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectives

    High-level algebraic properties of the store-free formula semantics. *)


Section FormulaConnectives.

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

End FormulaConnectives.

