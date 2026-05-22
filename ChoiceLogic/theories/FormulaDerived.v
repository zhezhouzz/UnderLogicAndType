(** * ChoiceLogic.FormulaDerived

    Derived proof principles for the store-free formula semantics.  This file
    keeps only statements that still describe useful structure under the new
    dependent-lqual and extension-based forall definitions. *)

From ChoiceLogic Require Import LogicQualifier Formula FormulaTactics.

Section FormulaDerived.

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
  (∀ mfib : WfWorldT,
    res_fiber_member m (lvars_fv D) mfib →
    mfib ⊨ φ) →
  m ⊨ FFibVars D φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hlc Hfib. split; [exact Hscope |].
  split; [exact Hlc |].
  intros mfib Hmember.
  specialize (Hfib mfib Hmember).
  models_fuel_irrel Hfib.
Qed.

Lemma res_models_FFibVars_projection_intro
    (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world m (FFibVars D φ) →
  lc_lvars D →
  (∀ σ mfib,
    res_fiber_from_projection m (lvars_fv D) σ mfib →
    mfib ⊨ φ) →
  m ⊨ FFibVars D φ.
Proof.
  intros Hscope Hlc Hfib.
  eapply res_models_FFibVars_intro; [exact Hscope | exact Hlc |].
  intros mfib Hmember.
  destruct Hmember as [σ Hproj].
  eapply Hfib. exact Hproj.
Qed.

Lemma res_models_FFibVars_iff (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world m (FFibVars D φ) →
  (m ⊨ FFibVars D φ ↔
    lc_lvars D ∧
    ∀ mfib : WfWorldT,
      res_fiber_member m (lvars_fv D) mfib →
      mfib ⊨ φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [Hlc Hfib]]. split; [exact Hlc |].
    intros mfib Hmember.
    specialize (Hfib mfib Hmember).
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
      mfib ⊨ φ).
Proof.
  intros Hscope. split.
  - intros Hmodel.
    pose proof (proj1 (res_models_FFibVars_iff m D φ Hscope) Hmodel)
      as [Hlc Hfib].
    split; [exact Hlc |].
    intros σ mfib Hproj.
    apply Hfib. exists σ. exact Hproj.
  - intros [Hlc Hfib].
    eapply res_models_FFibVars_projection_intro; eauto.
Qed.

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

Lemma res_models_forall_map_same_fv
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∀ y F my,
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    my ⊨ formula_open 0 y φ →
    my ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hfv Hscope Hmap Hforall.
  eapply res_models_forall_intro; [exact Hscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall) as [L Hbody].
  exists L. intros y Hy F HFin HFout my Hext.
  eapply (Hmap y F my); [| exact HFout | exact Hext |].
  - rewrite Hfv. exact HFin.
  - apply (Hbody y Hy F); [| exact HFout | exact Hext].
    rewrite Hfv. exact HFin.
Qed.

Lemma res_models_forall_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world m (FForall ψ) →
  (∀ (y : atom) (F : fiber_extension (V := V)) (my : WfWorldT),
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
  (∀ (y : atom) (F : fiber_extension (V := V)) (my : WfWorldT),
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    (my ⊨ formula_open 0 y φ ↔
	     my ⊨ formula_open 0 y ψ)) →
  (m ⊨ FForall φ ↔ m ⊨ FForall ψ).
Proof.
  intros Hfv Hφscope Hψscope Hiff. split.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [exact Hfv | exact Hψscope | | exact Hforall].
    intros y F my HFin HFout Hext Hφ.
    apply (proj1 (Hiff y F my HFin HFout Hext)). exact Hφ.
  - intros Hforall.
    eapply res_models_forall_map_same_fv; [symmetry; exact Hfv | exact Hφscope | | exact Hforall].
    intros y F my HFin HFout Hext Hψ.
    apply (proj2 (Hiff y F my ltac:(rewrite Hfv; exact HFin) HFout Hext)).
    exact Hψ.
Qed.

Lemma res_models_forall_transport
    (m n : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ = formula_fv ψ →
  formula_scoped_in_world n (FForall ψ) →
  (∀ y F my ny,
    ext_in F = formula_fv φ →
    ext_out F = {[y]} →
    res_extend_by m F my →
    res_extend_by n F ny →
	    my ⊨ formula_open 0 y φ →
	    ny ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  n ⊨ FForall ψ.
Proof.
  intros Hfv Hψscope Htransport Hforall.
  eapply res_models_forall_intro; [exact Hψscope |].
  pose proof (res_models_fuel_scoped _ _ _ Hforall) as Hφscope.
  pose proof (proj1 (res_models_forall_iff m φ Hφscope) Hforall)
    as [L Hbody].
  exists (L ∪ world_dom (m : WorldT)).
  intros y Hy F HFin HFout ny Hny.
  assert (HyL : y ∉ L) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Happ : extension_applicable F m).
  {
    constructor.
    - unfold ext_in in HFin. rewrite HFin. rewrite <- Hfv. exact Hφscope.
    - unfold ext_out in HFout. rewrite HFout. set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [my Hmy].
  eapply Htransport; [| exact HFout | exact Hmy | exact Hny |].
  - rewrite Hfv. exact HFin.
  - eapply (Hbody y HyL F); [| exact HFout | exact Hmy].
    rewrite Hfv. exact HFin.
Qed.

End FormulaDerived.
