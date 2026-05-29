(** * ContextLogic.FormulaConnectives

    Derived proof principles for the store-free formula semantics.  This file
    keeps only statements that still describe useful structure under the new
    dependent-lqual and extension-based forall definitions. *)

From ContextLogic Require Import LogicQualifier FormulaSemantics FormulaTactics.

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
