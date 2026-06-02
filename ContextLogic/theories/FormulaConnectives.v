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
Local Notation StoreT := (Store (V := V)) (only parsing).
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

Lemma res_models_of_restrict_eq
    (m n : WfWorldT) (S : aset) (φ : FormulaT) :
  formula_fv φ ⊆ S ->
  res_restrict m S = n ->
  n ⊨ φ ->
  m ⊨ φ.
Proof.
  intros Hfv <- Hmodel.
  apply (proj2 (res_models_minimal_on S m φ Hfv)).
  exact Hmodel.
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

Lemma res_models_and_map_iff
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  (m ⊨ φ1 ↔ m ⊨ φ2) ->
  (m ⊨ ψ1 ↔ m ⊨ ψ2) ->
  (m ⊨ FAnd φ1 ψ1 ↔ m ⊨ FAnd φ2 ψ2).
Proof.
  intros Hφ Hψ.
  rewrite !res_models_and_iff.
  tauto.
Qed.

Lemma res_models_or_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FOr φ ψ) ->
  m ⊨ FOr φ ψ ↔ m ⊨ φ ∨ m ⊨ ψ.
Proof.
  intros Hscope.
  split.
  - unfold res_models. simpl.
    intros [_ [Hφ|Hψ]].
    + left. eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
    + right. eapply res_models_fuel_irrel; [| | exact Hψ]; lia.
  - intros [Hφ|Hψ].
    + eapply res_models_or_intro_l; [exact Hscope | exact Hφ].
    + eapply res_models_or_intro_r; [exact Hscope | exact Hψ].
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

Lemma formula_scoped_star_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  formula_scoped_in_world m (FStar φ ψ).
Proof.
  intros Hle Hφ Hψ.
  pose proof (res_models_scoped m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_scoped m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in *.
  formula_fv_syntax_norm.
  pose proof (raw_le_dom (res_product m1 m2 Hc : WorldT) (m : WorldT) Hle)
    as Hdom.
  change (world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT) ⊆
          world_dom (m : WorldT)) in Hdom.
  set_solver.
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  intros Hle Hφ Hψ. unfold res_models. simpl.
  split; [eapply formula_scoped_star_from_models; eauto |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_star_iff (m : WfWorldT) (φ ψ : FormulaT) :
  (m ⊨ FStar φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
      res_product m1 m2 Hc ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hc [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hc. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hc [Hle [Hφ Hψ]]]]].
    eapply res_models_star_intro; eauto.
Qed.

Lemma formula_scoped_plus_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  formula_scoped_in_world m (FPlus φ ψ).
Proof.
  intros Hle Hφ Hψ.
  pose proof (res_models_scoped m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_scoped m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in *.
  formula_fv_syntax_norm.
  pose proof (raw_le_dom (res_sum m1 m2 Hdef : WorldT) (m : WorldT) Hle)
    as Hdom.
  change (world_dom (m1 : WorldT) = world_dom (m2 : WorldT)) in Hdef.
  change (world_dom (m1 : WorldT) ⊆ world_dom (m : WorldT)) in Hdom.
  intros z Hz. apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom. exact (Hscopeφ z Hz).
  - apply Hdom. rewrite Hdef. exact (Hscopeψ z Hz).
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  intros Hle Hφ Hψ. unfold res_models. simpl.
  split; [eapply formula_scoped_plus_from_models; eauto |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_plus_iff (m : WfWorldT) (φ ψ : FormulaT) :
  (m ⊨ FPlus φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
      res_sum m1 m2 Hdef ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hdef. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]].
    eapply res_models_plus_intro; eauto.
Qed.

Lemma res_models_plus_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  (∀ m', m' ⊨ φ1 → m' ⊨ φ2) →
  (∀ m', m' ⊨ ψ1 → m' ⊨ ψ2) →
  m ⊨ FPlus φ1 ψ1 →
  m ⊨ FPlus φ2 ψ2.
Proof.
  intros Hφ Hψ Hplus.
  apply res_models_plus_iff in Hplus as [m1 [m2 [Hdef [Hle [Hm1 Hm2]]]]].
  eapply res_models_plus_intro; eauto.
Qed.

Lemma res_models_atom_intro (m : WfWorldT) (q : LogicQualifierT) :
  logic_qualifier_denote q m →
  m ⊨ FAtom q.
Proof.
  unfold res_models. simpl. intros Hq. split; [| exact Hq].
  destruct q as [D P]. simpl in Hq |- *.
  destruct Hq as [Hlc [Hsub HP]]. exact Hsub.
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

Lemma res_models_over_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FOver ψ) →
  (∀ n : WfWorldT, res_subset m n → n ⊨ φ → n ⊨ ψ) →
  m ⊨ FOver φ →
  m ⊨ FOver ψ.
Proof.
  unfold res_models. cbn [formula_measure res_models_fuel].
  intros Hscope Hmap [_ [n [Hle Hφ]]].
  split; [exact Hscope|].
  exists n. split; [exact Hle|].
  apply Hmap; [exact Hle|].
  unfold res_models. models_fuel_irrel Hφ.
Qed.

Lemma res_models_under_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FUnder ψ) →
  (∀ n : WfWorldT, res_subset n m → n ⊨ φ → n ⊨ ψ) →
  m ⊨ FUnder φ →
  m ⊨ FUnder ψ.
Proof.
  unfold res_models. cbn [formula_measure res_models_fuel].
  intros Hscope Hmap [_ [n [Hle Hφ]]].
  split; [exact Hscope|].
  exists n. split; [exact Hle|].
  apply Hmap; [exact Hle|].
  unfold res_models. models_fuel_irrel Hφ.
Qed.

Lemma res_models_resource_atom_intro
    (m : WfWorldT) (D : lvset)
    (P : LWorldOn (V := V) D → Prop) :
  logic_qualifier_denote (lqual D P) m →
  m ⊨ FResourceAtom D P.
Proof.
  intros Hden.
  eapply res_models_atom_intro. exact Hden.
Qed.

Lemma res_models_resource_atom_witness_intro
    (m m0 : WfWorldT) (D : lvset)
    (P : LWorldOn (V := V) D → Prop) :
  logic_qualifier_denote (lqual D P) m0 →
  m0 ⊑ m →
  m ⊨ FResourceAtom D P.
Proof.
  intros Hden Hle.
  eapply res_models_resource_atom_intro.
  eapply logic_qualifier_denote_mono.
  - exact Hden.
  - destruct Hden as [_ [Hsub _]]. exact Hsub.
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

Lemma res_models_FFibVars_map
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FFibVars D ψ) →
  (∀ σ mfib,
    res_fiber_from_projection m (lvars_fv D) σ mfib →
    mfib ⊨ formula_msubst_store σ φ →
    mfib ⊨ formula_msubst_store σ ψ) →
  m ⊨ FFibVars D φ →
  m ⊨ FFibVars D ψ.
Proof.
  intros Hscopeψ Hmap Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscopeφ.
  pose proof (proj1 (res_models_FFibVars_iff m D φ Hscopeφ) Hmodel)
    as [Hlc Hfib].
  eapply res_models_FFibVars_intro; [exact Hscopeψ | exact Hlc |].
  intros σ mfib Hproj.
  apply Hmap; [exact Hproj|].
  apply Hfib. exact Hproj.
Qed.

Lemma res_models_FFibVars_singleton_elim
    (m : WfWorldT) (D : lvset) (φ : FormulaT) (σD : StoreT) :
  dom σD = lvars_fv D ->
  (res_restrict m (lvars_fv D) : WorldT) = singleton_world σD ->
  m ⊨ FFibVars D φ ->
  m ⊨ formula_msubst_store σD φ.
Proof.
  intros HdomσD Hsingleton Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff m D φ Hscope) Hmodel)
    as [_ Hfib].
  destruct (res_fiber_from_projection_exists m (lvars_fv D)) as
    [σ [mfib Hproj]].
  { apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope.
    exact (proj1 Hscope). }
  pose proof (res_fiber_singleton_projection_inv
    m mfib (lvars_fv D) σ σD HdomσD Hsingleton Hproj) as [-> ->].
  exact (Hfib σD m Hproj).
Qed.

Lemma res_models_FFibVars_singleton_intro
    (m : WfWorldT) (D : lvset) (φ : FormulaT) (σD : StoreT) :
  formula_scoped_in_world m (FFibVars D φ) ->
  lc_lvars D ->
  dom σD = lvars_fv D ->
  (res_restrict m (lvars_fv D) : WorldT) = singleton_world σD ->
  m ⊨ formula_msubst_store σD φ ->
  m ⊨ FFibVars D φ.
Proof.
  intros Hscope Hlc HdomσD Hsingleton Hmodel.
  eapply res_models_FFibVars_projection_intro; [exact Hscope | exact Hlc |].
  intros σ mfib Hproj.
  pose proof (res_fiber_singleton_projection_inv
    m mfib (lvars_fv D) σ σD HdomσD Hsingleton Hproj) as [-> ->].
  exact Hmodel.
Qed.

Lemma formula_scoped_FFibVars_from_singleton_msubst
    (m : WfWorldT) (D : lvset) (φ : FormulaT) (σD : StoreT) :
  dom σD = lvars_fv D ->
  (res_restrict m (lvars_fv D) : WorldT) = singleton_world σD ->
  formula_scoped_in_world m (formula_msubst_store σD φ) ->
  formula_scoped_in_world m (FFibVars D φ).
Proof.
  intros HdomσD Hsingleton Hscope_msubst.
  assert (HDsub : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    pose proof (f_equal world_dom Hsingleton) as Hdom.
    simpl in Hdom.
    change (world_dom (m : WorldT) ∩ lvars_fv D = dom (σD : StoreT)) in Hdom.
    rewrite HdomσD in Hdom. set_solver.
  }
  apply (proj2 (formula_scoped_fibvars_iff m D φ)). split.
  - exact HDsub.
  - eapply formula_scoped_in_world_from_formula_fv.
    pose proof (formula_msubst_store_fv_restore σD φ) as Hrestore.
    unfold formula_scoped_in_world in Hscope_msubst.
    intros x Hx.
    apply Hrestore in Hx. apply elem_of_union in Hx as [Hx | Hx].
    + exact (Hscope_msubst x Hx).
    + apply HDsub. rewrite <- HdomσD. exact Hx.
Qed.

Lemma res_models_FFibVars_empty_iff (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FFibVars ∅ φ ↔ m ⊨ φ.
Proof.
  split.
  - intros Hmodel.
    pose proof (res_models_scoped m (FFibVars ∅ φ) Hmodel) as Hscope.
    pose proof (proj1 (res_models_FFibVars_iff m ∅ φ Hscope) Hmodel)
      as [_ Hfib].
    specialize (Hfib (∅ : StoreT) m
      (res_fiber_from_projection_empty_self m)).
    rewrite formula_msubst_store_empty in Hfib; [exact Hfib | reflexivity].
  - intros Hmodel.
    pose proof (res_models_scoped m φ Hmodel) as Hscope.
    eapply res_models_FFibVars_intro.
    + apply (proj2 (formula_scoped_fibvars_iff m ∅ φ)).
      split; [rewrite lvars_fv_empty; set_solver | exact Hscope].
    + unfold lc_lvars. set_solver.
    + intros σ mfib Hproj.
      rewrite formula_msubst_store_empty.
      * pose proof (res_fiber_from_projection_empty_eq m mfib σ Hproj) as ->.
        exact Hmodel.
      * eapply res_fiber_from_projection_empty_store_dom; exact Hproj.
Qed.

Lemma res_models_msubst_store_fibvars_singleton_exact_iff
    (m : WfWorldT) (D : lvset) (φ : FormulaT) (σD : StoreT) :
  lc_lvars D ->
  dom (σD : StoreT) = lvars_fv D ->
  (res_restrict m (lvars_fv D) : WorldT) = singleton_world σD ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ formula_msubst_store σD (FFibVars D φ) <->
  m ⊨ FFibVars D φ.
Proof.
  intros Hlc HdomσD Hsingleton Hscope.
  rewrite formula_msubst_store_fibvars.
  assert (HDempty : D ∖ lvars_of_atoms (dom (σD : StoreT)) = ∅).
  {
    apply set_eq. intros v.
    rewrite elem_of_empty, elem_of_difference.
    split; [|tauto].
    intros [HvD Hvnot].
    exfalso. apply Hvnot.
    rewrite HdomσD.
    apply lvars_bv_empty_subset_of_atoms_fv.
    - apply lc_lvars_no_bv. exact Hlc.
    - exact HvD.
  }
  rewrite HDempty.
  rewrite res_models_FFibVars_empty_iff.
  split.
  - intros Hmodel.
    eapply res_models_FFibVars_singleton_intro; eauto.
  - intros Hmodel.
    eapply res_models_FFibVars_singleton_elim; eauto.
Qed.

Lemma formula_msubst_store_fibvars_restrict_to_domain
    (σ : StoreT) (D : lvset) (φ : FormulaT) :
  dom (σ : StoreT) ∩ formula_fv φ ⊆ lvars_fv D ->
  formula_msubst_store σ (FFibVars D φ) =
  formula_msubst_store (store_restrict σ (lvars_fv D)) (FFibVars D φ).
Proof.
  intros HσD.
  apply formula_msubst_store_agree_fv.
  apply storeA_map_eq. intros x.
  rewrite !storeA_restrict_lookup.
  destruct (decide (x ∈ formula_fv (FFibVars D φ))) as [Hxfv|Hxfv];
    [|reflexivity].
  destruct (decide (x ∈ lvars_fv D)) as [HxD|HxD]; [reflexivity|].
  rewrite formula_fv_fibvars in Hxfv.
  assert (Hxφ : x ∈ formula_fv φ) by set_solver.
  assert (Hnone : (σ : StoreT) !! x = None).
  {
    assert (Hxnotdom : x ∉ dom (σ : StoreT)).
    {
      intros Hxdom.
      pose proof (HσD x ltac:(set_solver)) as Hbad.
      exact (HxD Hbad).
    }
    change ((σ : gmap atom V) !! x = None).
    change (x ∉ dom (σ : gmap atom V)) in Hxnotdom.
    apply not_elem_of_dom_1. exact Hxnotdom.
  }
  exact Hnone.
Qed.

Lemma res_models_msubst_store_fibvars_singleton_iff
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  lc_lvars D ->
  (res_restrict m (lvars_fv D) : WorldT) =
    singleton_world (store_restrict σ (lvars_fv D)) ->
  dom (σ : StoreT) ∩ formula_fv φ ⊆ lvars_fv D ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ formula_msubst_store σ (FFibVars D φ) <->
  m ⊨ FFibVars D φ.
Proof.
  intros Hlc Hsingleton HσD Hscope.
  rewrite (formula_msubst_store_fibvars_restrict_to_domain σ D φ HσD).
  eapply res_models_msubst_store_fibvars_singleton_exact_iff.
  - exact Hlc.
  - pose proof (f_equal world_dom Hsingleton) as Hdom.
    apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope.
    destruct Hscope as [HD _].
    change (world_dom (m : WorldT) ∩ lvars_fv D =
      dom (store_restrict σ (lvars_fv D) : StoreT)) in Hdom.
    change (world_dom (m : WorldT) ∩ lvars_fv D =
      dom (store_restrict σ (lvars_fv D) : gmap atom V)) in Hdom.
    rewrite storeA_restrict_dom in Hdom.
    change (dom (store_restrict σ (lvars_fv D) : gmap atom V) = lvars_fv D).
    rewrite storeA_restrict_dom.
    set_solver.
  - exact Hsingleton.
  - exact Hscope.
Qed.

Lemma res_models_msubst_store_fibvars_from_projection_iff
    (m mfib : WfWorldT) (X : aset) (σ : StoreT)
    (D : lvset) (φ : FormulaT) :
  res_fiber_from_projection m X σ mfib ->
  lc_lvars D ->
  lvars_fv D ⊆ X ->
  dom (σ : StoreT) ∩ formula_fv φ ⊆ lvars_fv D ->
  formula_scoped_in_world mfib (FFibVars D φ) ->
  mfib ⊨ formula_msubst_store σ (FFibVars D φ) <->
  mfib ⊨ FFibVars D φ.
Proof.
  intros Hproj Hlc HDX HσD Hscope.
  eapply res_models_msubst_store_fibvars_singleton_iff; eauto.
  eapply (res_restrict_singleton_subset mfib (dom (σ : StoreT))
    (lvars_fv D) σ).
  - pose proof (wfworld_store_dom (res_restrict m X) σ (proj1 Hproj))
      as Hdomσ.
    change (dom (σ : StoreT) = world_dom (res_restrict m X : WorldT))
      in Hdomσ.
    simpl in Hdomσ.
    pose proof (res_fiber_from_projection_world_dom m mfib X σ Hproj)
      as Hdom_mfib.
    apply (proj1 (formula_scoped_fibvars_iff mfib D φ)) in Hscope.
    destruct Hscope as [HscopeD _].
    set_solver.
  - eapply res_restrict_fiber_from_projection_dom_singleton. exact Hproj.
Qed.

Lemma fiber_projection_agree_with_singleton_on_overlap
    (m mfib : WfWorldT) (σ σD : StoreT) (D : lvset) (X : aset) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  res_fiber_from_projection m (lvars_fv D) σD mfib ->
  X ⊆ dom (σ : StoreT) ->
  X ⊆ lvars_fv D ->
  store_restrict σD X = store_restrict σ X.
Proof.
  intros Hsingle [Hproj _] HXσ HXD.
  destruct Hproj as [τ [Hτ HτD]].
  assert (Hτsingleton :
    (res_restrict m (dom (σ : StoreT)) : WorldT)
      (store_restrict τ (dom (σ : StoreT)))).
  {
    exists τ. split; [exact Hτ | reflexivity].
  }
  rewrite Hsingle in Hτsingleton.
  simpl in Hτsingleton.
  rewrite <- HτD, <- Hτsingleton.
  rewrite !storeA_restrict_twice_subset by assumption.
  reflexivity.
Qed.

Lemma res_models_FFibVars_and_l
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) :
  m ⊨ FFibVars D (FAnd φ ψ) ->
  m ⊨ FFibVars D φ.
Proof.
  intros Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope_and.
  pose proof (proj1 (res_models_FFibVars_iff m D (FAnd φ ψ) Hscope_and)
    Hmodel) as [Hlc Hfib].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D φ)).
    apply (proj1 (formula_scoped_fibvars_iff m D (FAnd φ ψ))) in Hscope_and.
    destruct Hscope_and as [HD Hinner].
    apply (proj1 (formula_scoped_and_iff m φ ψ)) in Hinner.
    split; [exact HD | tauto].
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store formula_mlsubst] in Hfib.
    rewrite res_models_and_iff in Hfib. tauto.
Qed.

Lemma res_models_FFibVars_and_r
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) :
  m ⊨ FFibVars D (FAnd φ ψ) ->
  m ⊨ FFibVars D ψ.
Proof.
  intros Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope_and.
  pose proof (proj1 (res_models_FFibVars_iff m D (FAnd φ ψ) Hscope_and)
    Hmodel) as [Hlc Hfib].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D ψ)).
    apply (proj1 (formula_scoped_fibvars_iff m D (FAnd φ ψ))) in Hscope_and.
    destruct Hscope_and as [HD Hinner].
    apply (proj1 (formula_scoped_and_iff m φ ψ)) in Hinner.
    split; [exact HD | tauto].
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    cbn [formula_msubst_store formula_mlsubst] in Hfib.
    rewrite res_models_and_iff in Hfib. tauto.
Qed.

Lemma res_models_FFibVars_and_intro
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) :
  m ⊨ FFibVars D φ ->
  m ⊨ FFibVars D ψ ->
  m ⊨ FFibVars D (FAnd φ ψ).
Proof.
  intros Hφ Hψ.
  pose proof (res_models_scoped _ _ Hφ) as Hscopeφ.
  pose proof (res_models_scoped _ _ Hψ) as Hscopeψ.
  pose proof (proj1 (res_models_FFibVars_iff m D φ Hscopeφ) Hφ)
    as [Hlc Hfibφ].
  pose proof (proj1 (res_models_FFibVars_iff m D ψ Hscopeψ) Hψ)
    as [_ Hfibψ].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D (FAnd φ ψ))).
    apply (proj1 (formula_scoped_fibvars_iff m D φ))
      in Hscopeφ as [HD Hscopeφ'].
    apply (proj1 (formula_scoped_fibvars_iff m D ψ))
      in Hscopeψ as [_ Hscopeψ'].
    split; [exact HD |].
    apply (proj2 (formula_scoped_and_iff m φ ψ)).
    split; assumption.
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfibφ σ mfib Hproj).
    specialize (Hfibψ σ mfib Hproj).
    cbn [formula_msubst_store formula_mlsubst].
    rewrite res_models_and_iff. tauto.
Qed.

Lemma res_models_FFibVars_same_fv
    (m : WfWorldT) (D1 D2 : lvset) (φ : FormulaT) :
  lc_lvars D2 ->
  lvars_fv D1 = lvars_fv D2 ->
  m ⊨ FFibVars D1 φ ->
  m ⊨ FFibVars D2 φ.
Proof.
  intros Hlc2 Hfv Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope1.
  pose proof (proj1 (res_models_FFibVars_iff m D1 φ Hscope1) Hmodel)
    as [_ Hfib1].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D2 φ)).
    apply (proj1 (formula_scoped_fibvars_iff m D1 φ)) in Hscope1.
    destruct Hscope1 as [HD1 Hφ].
    split; [rewrite <- Hfv; exact HD1 | exact Hφ].
  - exact Hlc2.
  - intros σ mfib Hproj2.
    apply Hfib1.
    rewrite Hfv. exact Hproj2.
Qed.

Lemma res_models_msubst_store_full_FFibVars_elim
    (m : WfWorldT) (D : lvset) (φ : FormulaT) (σD : StoreT) :
  dom σD = lvars_fv D ->
  m ⊨ formula_msubst_store σD (FFibVars D φ) ->
  m ⊨ formula_msubst_store σD φ.
Proof.
  intros HdomσD Hmodel.
  rewrite formula_msubst_store_fibvars in Hmodel.
  eapply res_models_FFibVars_empty_iff.
  eapply res_models_FFibVars_same_fv; [| | exact Hmodel].
  - unfold lc_lvars. set_solver.
  - rewrite lvars_fv_empty, lvars_fv_difference_of_atoms.
    rewrite HdomσD. set_solver.
Qed.

Lemma res_models_FFibVars_nested_union_l
    (m : WfWorldT) (D1 D2 : lvset) (φ : FormulaT) :
  m ⊨ FFibVars D1 (FFibVars D2 φ) ->
  m ⊨ FFibVars (D1 ∪ D2) φ.
Proof.
  intros Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope_nested.
  pose proof (proj1 (res_models_FFibVars_iff m D1 (FFibVars D2 φ)
    Hscope_nested) Hmodel) as [Hlc1 Hfib1].
  assert (Hscope_union : formula_scoped_in_world m (FFibVars (D1 ∪ D2) φ)).
  {
    apply (proj2 (formula_scoped_fibvars_iff m (D1 ∪ D2) φ)).
    apply (proj1 (formula_scoped_fibvars_iff m D1 (FFibVars D2 φ)))
      in Hscope_nested as [HD1 Hscope_inner].
    apply (proj1 (formula_scoped_fibvars_iff m D2 φ))
      in Hscope_inner as [HD2 Hφ].
    split; [rewrite lvars_fv_union; set_solver | exact Hφ].
  }
  assert (HlcU : lc_lvars (D1 ∪ D2)).
  {
    apply (proj1 (formula_scoped_fibvars_iff m D1 (FFibVars D2 φ)))
      in Hscope_nested as [HD1 _].
    destruct (res_fiber_from_projection_exists m (lvars_fv D1) HD1)
      as [σ1 [mfib1 Hproj1]].
    specialize (Hfib1 σ1 mfib1 Hproj1).
    rewrite formula_msubst_store_fibvars in Hfib1.
    pose proof (res_models_scoped _ _ Hfib1) as Hscope_inner.
    pose proof (proj1 (res_models_FFibVars_iff mfib1
      (D2 ∖ lvars_of_atoms (dom (σ1 : StoreT)))
      (formula_msubst_store σ1 φ) Hscope_inner) Hfib1) as [Hlc2res _].
    intros v Hv.
    apply elem_of_union in Hv as [Hv1 | Hv2].
    - exact (Hlc1 v Hv1).
    - destruct v as [k | x]; cbn [lc_logic_var_key]; [|exact I].
      apply (Hlc2res (LVBound k)).
      apply elem_of_difference. split; [exact Hv2 |].
      unfold lvars_of_atoms.
      intros Hatom. apply elem_of_map in Hatom as [x [Heq _]].
      discriminate.
  }
  eapply res_models_FFibVars_intro.
  - exact Hscope_union.
  - exact HlcU.
  - intros σXY mfibXY HprojXY.
    rewrite lvars_fv_union in HprojXY.
    destruct (res_fiber_from_projection_nested_union_residual_r
      m mfibXY (lvars_fv D1) (lvars_fv D2) σXY HprojXY)
      as [σ1 [mfib1 [σ2 [Hσ1 [Hσ2 [Hσunion [Hproj1 Hproj2]]]]]]].
    subst σ1 σ2.
    specialize (Hfib1 (storeA_restrict σXY (lvars_fv D1)) mfib1 Hproj1).
    rewrite formula_msubst_store_fibvars in Hfib1.
    pose proof (res_models_scoped _ _ Hfib1) as Hscope_inner.
    pose proof (proj1 (res_models_FFibVars_iff mfib1
      (D2 ∖ lvars_of_atoms
        (dom (storeA_restrict σXY (lvars_fv D1) : StoreT)))
      (formula_msubst_store (storeA_restrict σXY (lvars_fv D1)) φ)
      Hscope_inner) Hfib1) as [_ Hfib2].
    assert (Hdomσ1 : dom (storeA_restrict σXY (lvars_fv D1) : StoreT) =
        lvars_fv D1).
    {
      destruct Hproj1 as [Hproj1 _].
      pose proof (wfworld_store_dom (res_restrict m (lvars_fv D1))
        (storeA_restrict σXY (lvars_fv D1)) Hproj1) as Hdom.
      simpl in Hdom.
      change (dom (storeA_restrict σXY (lvars_fv D1) : StoreT) =
        world_dom (m : WorldT) ∩ lvars_fv D1) in Hdom.
      apply (proj1 (formula_scoped_fibvars_iff m D1 (FFibVars D2 φ)))
        in Hscope_nested as [HD1 _].
      rewrite Hdom. set_solver.
    }
    rewrite Hdomσ1 in Hfib2.
    rewrite lvars_fv_difference_of_atoms in Hfib2.
    specialize (Hfib2 (storeA_restrict σXY (lvars_fv D2 ∖ lvars_fv D1))
      mfibXY).
    specialize (Hfib2 Hproj2).
    rewrite formula_msubst_store_union in Hfib2.
    + change (mfibXY ⊨ formula_msubst_store
        ((storeA_restrict σXY (lvars_fv D1) : StoreT) ∪
         storeA_restrict σXY (lvars_fv D2 ∖ lvars_fv D1)) φ) in Hfib2.
      replace ((storeA_restrict σXY (lvars_fv D1) : StoreT) ∪
          storeA_restrict σXY (lvars_fv D2 ∖ lvars_fv D1))
        with σXY in Hfib2 by (symmetry; exact Hσunion).
      exact Hfib2.
    + eapply res_fiber_from_projection_store_compat; eauto.
Qed.

Lemma res_models_FFibVars_nested_union_r
    (m : WfWorldT) (D1 D2 : lvset) (φ : FormulaT) :
  m ⊨ FFibVars (D1 ∪ D2) φ ->
  m ⊨ FFibVars D1 (FFibVars D2 φ).
Proof.
  intros Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope_union.
  pose proof (proj1 (res_models_FFibVars_iff m (D1 ∪ D2) φ
    Hscope_union) Hmodel) as [HlcU HfibU].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D1 (FFibVars D2 φ))).
    apply (proj1 (formula_scoped_fibvars_iff m (D1 ∪ D2) φ))
      in Hscope_union as [HDU Hφ].
    split.
    + rewrite lvars_fv_union in HDU. set_solver.
    + apply (proj2 (formula_scoped_fibvars_iff m D2 φ)).
      split; [rewrite lvars_fv_union in HDU; set_solver | exact Hφ].
  - intros v Hv. apply HlcU. set_solver.
  - intros σ1 mfib1 Hproj1.
    rewrite formula_msubst_store_fibvars.
    eapply res_models_FFibVars_intro.
    + pose proof (res_models_scoped _ _ Hmodel) as HscopeU.
      pose proof (formula_scoped_fibvars_r _ _ _ HscopeU) as Hscopeφ.
      apply (proj2 (formula_scoped_fibvars_iff mfib1
        (D2 ∖ lvars_of_atoms (dom (σ1 : StoreT)))
        (formula_msubst_store σ1 φ))).
      split.
      * pose proof (res_fiber_from_projection_world_dom m mfib1
          (lvars_fv D1) σ1 Hproj1) as Hdom_mfib1.
        rewrite Hdom_mfib1.
        apply (proj1 (formula_scoped_fibvars_iff m (D1 ∪ D2) φ))
          in HscopeU as [HDU _].
        rewrite lvars_fv_difference_of_atoms, lvars_fv_union in *.
        set_solver.
      * unfold formula_scoped_in_world in *.
        pose proof (res_fiber_from_projection_world_dom m mfib1
          (lvars_fv D1) σ1 Hproj1) as Hdom_mfib1.
        rewrite Hdom_mfib1.
        pose proof (formula_msubst_store_fv_subset σ1 φ) as Hfvsub.
        set_solver.
    + intros v Hv.
      apply HlcU.
      apply elem_of_union_r.
      apply elem_of_difference in Hv as [Hv _].
      exact Hv.
    + intros σ2 mfibXY Hproj2.
      assert (Hdomσ1 : dom (σ1 : StoreT) = lvars_fv D1).
      {
        destruct Hproj1 as [Hproj1' _].
        pose proof (wfworld_store_dom (res_restrict m (lvars_fv D1))
          σ1 Hproj1') as Hdom.
        simpl in Hdom.
        change (dom (σ1 : StoreT) =
          world_dom (m : WorldT) ∩ lvars_fv D1) in Hdom.
        apply (proj1 (formula_scoped_fibvars_iff m (D1 ∪ D2) φ))
          in Hscope_union as [HDU _].
        rewrite lvars_fv_union in HDU.
        rewrite Hdom. set_solver.
      }
      rewrite Hdomσ1 in Hproj2.
      rewrite lvars_fv_difference_of_atoms in Hproj2.
      pose proof (res_fiber_from_projection_store_compat
        m mfib1 mfibXY (lvars_fv D1) (lvars_fv D2 ∖ lvars_fv D1)
        σ1 σ2 Hproj1 Hproj2) as Hcompat12.
      pose proof (res_fiber_from_projection_nested_union_l
        m mfib1 mfibXY (lvars_fv D1) (lvars_fv D2 ∖ lvars_fv D1)
        σ1 σ2 Hproj1 Hproj2 Hcompat12) as HprojU.
      replace (lvars_fv D1 ∪ (lvars_fv D2 ∖ lvars_fv D1))
        with (lvars_fv D1 ∪ lvars_fv D2) in HprojU.
      2:{ apply set_eq. intros z.
          rewrite !elem_of_union, elem_of_difference. tauto. }
      rewrite lvars_fv_union in HfibU.
      specialize (HfibU (σ1 ∪ σ2) mfibXY HprojU).
      rewrite formula_msubst_store_union by exact Hcompat12.
      exact HfibU.
Qed.

Lemma res_models_FFibVars_nested_union_iff
    (m : WfWorldT) (D1 D2 : lvset) (φ : FormulaT) :
  m ⊨ FFibVars D1 (FFibVars D2 φ) <->
  m ⊨ FFibVars (D1 ∪ D2) φ.
Proof.
  split.
  - apply res_models_FFibVars_nested_union_l.
  - apply res_models_FFibVars_nested_union_r.
Qed.

Lemma res_models_FFibVars_split_fixed_residual
    (m : WfWorldT) (D : lvset) (φ : FormulaT) (σ : StoreT) :
  lc_lvars D ->
  dom (σ : StoreT) ∩ formula_fv φ ⊆ lvars_fv D ->
  m ⊨ FFibVars D φ <->
  m ⊨ FFibVars
    (D ∩ lvars_of_atoms (dom (σ : StoreT)))
    (FFibVars (D ∖ lvars_of_atoms (dom (σ : StoreT))) φ).
Proof.
  intros Hlc _.
  set (A := lvars_of_atoms (dom (σ : StoreT))).
  set (Df := D ∩ A).
  set (Dr := D ∖ A).
  assert (HlcU : lc_lvars (Df ∪ Dr)).
  { subst Df Dr A. unfold lc_lvars in *. set_solver. }
  assert (HfvU : lvars_fv (Df ∪ Dr) = lvars_fv D).
  {
    subst Df Dr A.
    rewrite lvars_fv_union, lvars_fv_intersection_of_atoms,
      lvars_fv_difference_of_atoms.
    apply set_eq. intros x.
    rewrite elem_of_union, elem_of_intersection, elem_of_difference.
    tauto.
  }
  split.
  - intros Hmodel.
    apply (proj2 (res_models_FFibVars_nested_union_iff m Df Dr φ)).
    eapply res_models_FFibVars_same_fv; [exact HlcU | | exact Hmodel].
    symmetry. exact HfvU.
  - intros Hmodel.
    apply (proj1 (res_models_FFibVars_nested_union_iff m Df Dr φ))
      in Hmodel.
    eapply res_models_FFibVars_same_fv; [exact Hlc | | exact Hmodel].
    exact HfvU.
Qed.

Lemma res_models_msubst_store_fibvars_local_singleton_iff
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  lc_lvars D ->
  dom (σ : StoreT) ∩ formula_fv φ ⊆ lvars_fv D ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ formula_msubst_store σ (FFibVars D φ) <->
  m ⊨ FFibVars D φ.
Proof.
  intros Hsingle Hlc Hcover Hscope.
  set (A := lvars_of_atoms (dom (σ : StoreT))).
  set (Df := D ∩ A).
  set (Dr := D ∖ A).
  assert (HlcDf : lc_lvars Df)
    by (subst Df A; unfold lc_lvars in *; set_solver).
  assert (Hscope_parts :
      lvars_fv D ⊆ world_dom (m : WorldT) /\
      formula_scoped_in_world m φ).
  {
    apply (proj1 (formula_scoped_fibvars_iff m D φ)).
    exact Hscope.
  }
  destruct Hscope_parts as [HscopeD Hscopeφ].
  assert (Hscope_nested :
      formula_scoped_in_world m (FFibVars Df (FFibVars Dr φ))).
  {
    apply (proj2 (formula_scoped_fibvars_iff m Df (FFibVars Dr φ))).
    split.
    - subst Df A.
      rewrite lvars_fv_intersection_of_atoms.
      set_solver.
    - apply (proj2 (formula_scoped_fibvars_iff m Dr φ)).
      split.
      + subst Dr A.
        rewrite lvars_fv_difference_of_atoms.
        set_solver.
      + exact Hscopeφ.
  }
  assert (HsingleDf :
      (res_restrict m (lvars_fv Df) : WorldT) =
        singleton_world (store_restrict σ (lvars_fv Df))).
  {
    eapply res_restrict_singleton_subset; [| exact Hsingle].
    subst Df A.
    rewrite lvars_fv_intersection_of_atoms.
    set_solver.
  }
  assert (HcoverDf :
      dom (σ : StoreT) ∩ formula_fv (FFibVars Dr φ) ⊆ lvars_fv Df).
  {
    subst Df Dr A.
    rewrite formula_fv_fibvars, lvars_fv_difference_of_atoms,
      lvars_fv_intersection_of_atoms.
    set_solver.
  }
  pose proof (res_models_msubst_store_fibvars_singleton_iff
    m σ Df (FFibVars Dr φ) HlcDf HsingleDf HcoverDf Hscope_nested)
    as Hfixed.
  assert (Hnested_msubst :
      formula_msubst_store σ (FFibVars Df (FFibVars Dr φ)) =
      FFibVars ∅ (FFibVars Dr (formula_msubst_store σ φ))).
  {
    subst Df Dr A.
    rewrite !formula_msubst_store_fibvars.
    replace ((D ∩ lvars_of_atoms (dom (σ : StoreT))) ∖
        lvars_of_atoms (dom (σ : StoreT))) with (∅ : lvset).
    2:{ apply set_eq. intros v.
        rewrite elem_of_empty, elem_of_difference, elem_of_intersection.
        tauto. }
    replace ((D ∖ lvars_of_atoms (dom (σ : StoreT))) ∖
        lvars_of_atoms (dom (σ : StoreT)))
      with (D ∖ lvars_of_atoms (dom (σ : StoreT))).
    2:{ apply set_eq. intros v.
        rewrite !elem_of_difference. tauto. }
    reflexivity.
  }
  assert (Hsource_msubst :
      formula_msubst_store σ (FFibVars D φ) =
      FFibVars Dr (formula_msubst_store σ φ)).
  {
    subst Dr A.
    apply formula_msubst_store_fibvars.
  }
  rewrite Hsource_msubst.
  rewrite (res_models_FFibVars_split_fixed_residual m D φ σ
    Hlc Hcover).
  fold A Df Dr.
  rewrite <- Hfixed.
  rewrite Hnested_msubst.
  rewrite res_models_FFibVars_empty_iff.
  reflexivity.
Qed.

Lemma res_models_msubst_store_fibvars_keep_domain_iff
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  lc_lvars D ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ formula_msubst_store σ (FFibVars D φ) <->
  m ⊨ FFibVars D (formula_msubst_store (store_without_lvars σ D) φ).
Proof.
  intros Hsingle Hlc Hscope.
  set (σD := store_restrict σ (lvars_fv D) : StoreT).
  assert (HsingleD :
      (res_restrict m (dom (σD : StoreT)) : WorldT) =
        singleton_world σD).
  {
    assert (Htmp :
      (res_restrict m (dom (σD : StoreT)) : WorldT) =
        singleton_world (store_restrict σ (dom (σD : StoreT)))).
    {
      eapply res_restrict_singleton_subset; [| exact Hsingle].
      unfold σD.
      change (dom (storeA_restrict σ (lvars_fv D) : gmap atom V) ⊆
        dom (σ : StoreT)).
      rewrite storeA_restrict_dom. set_solver.
    }
    rewrite Htmp. f_equal.
    unfold σD.
    apply storeA_restrict_projection_dom with (X := lvars_fv D).
    reflexivity.
  }
  assert (Hscope_keep :
      formula_scoped_in_world m
        (FFibVars D (formula_msubst_store (store_without_lvars σ D) φ))).
  {
    apply (proj2 (formula_scoped_fibvars_iff m D
      (formula_msubst_store (store_without_lvars σ D) φ))).
    apply (proj1 (formula_scoped_fibvars_iff m D φ)) in Hscope
      as [HD Hφ].
    split; [exact HD|].
    eapply formula_scoped_in_world_from_formula_fv.
    transitivity (formula_fv φ).
    - apply formula_msubst_store_fv_subset.
    - exact Hφ.
  }
  rewrite formula_msubst_store_fibvars_keep_domain_syntax.
  fold σD.
  eapply res_models_msubst_store_fibvars_local_singleton_iff.
  - exact HsingleD.
  - exact Hlc.
  - change (dom (storeA_restrict σ (lvars_fv D) : gmap atom V) ∩
      formula_fv (formula_msubst_store (store_without_lvars σ D) φ)
      ⊆ lvars_fv D).
    rewrite storeA_restrict_dom.
    set_solver.
  - exact Hscope_keep.
Qed.

Lemma res_models_msubst_store_fibvars_keep_domain_elim
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  lc_lvars D ->
  dom (store_without_lvars σ D : StoreT) ## formula_fv φ ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ formula_msubst_store σ (FFibVars D φ) ->
  m ⊨ FFibVars D φ.
Proof.
  intros Hsingle Hlc Hfresh Hscope Hmodel.
  pose proof (proj1 (res_models_msubst_store_fibvars_keep_domain_iff
    m σ D φ Hsingle Hlc Hscope) Hmodel) as Hkeep.
  rewrite formula_msubst_store_fresh in Hkeep by exact Hfresh.
  exact Hkeep.
Qed.

Lemma res_models_msubst_store_fibvars_keep_domain_intro
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  lc_lvars D ->
  dom (store_without_lvars σ D : StoreT) ## formula_fv φ ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ FFibVars D φ ->
  m ⊨ formula_msubst_store σ (FFibVars D φ).
Proof.
  intros Hsingle Hlc Hfresh Hscope Hmodel.
  apply (proj2 (res_models_msubst_store_fibvars_keep_domain_iff
    m σ D φ Hsingle Hlc Hscope)).
  change (m ⊨ FFibVars D
    (formula_msubst_store (store_without_lvars σ D) φ)).
  rewrite formula_msubst_store_fresh by exact Hfresh.
  exact Hmodel.
Qed.

Lemma lc_lvars_of_msubst_fibvars_model
    (m : WfWorldT) σ D φ :
  m ⊨ formula_msubst_store σ (FFibVars D φ) ->
  lc_lvars D.
Proof.
  intros Hmodel v Hv.
  destruct v as [k|a]; [|exact I].
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  formula_msubst_syntax_norm_in Hmodel.
  formula_msubst_syntax_norm_in Hscope.
  pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hmodel)
    as [Hlc _].
  unfold lc_lvars in Hlc.
	  eapply (Hlc (LVBound k)).
	  apply elem_of_difference. split; [exact Hv |].
	  unfold lvars_of_atoms.
	  rewrite elem_of_map.
	  intros [x [Hbad _]].
	  discriminate Hbad.
Qed.

Lemma lc_lvars_of_fibvars_model
    (m : WfWorldT) D φ :
  m ⊨ FFibVars D φ ->
  lc_lvars D.
Proof.
  intros Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff _ _ _ Hscope) Hmodel)
    as [Hlc _].
  exact Hlc.
Qed.

Lemma res_models_msubst_store_fibvars_keep_domain_elim_from_model
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  dom (store_without_lvars σ D : StoreT) ## formula_fv φ ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ formula_msubst_store σ (FFibVars D φ) ->
  m ⊨ FFibVars D φ.
Proof.
  intros Hsingle Hfresh Hscope Hmodel.
  eapply res_models_msubst_store_fibvars_keep_domain_elim; eauto.
  eapply lc_lvars_of_msubst_fibvars_model. exact Hmodel.
Qed.

Lemma res_models_msubst_store_fibvars_keep_domain_intro_from_model
    (m : WfWorldT) (σ : StoreT) (D : lvset) (φ : FormulaT) :
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ ->
  dom (store_without_lvars σ D : StoreT) ## formula_fv φ ->
  formula_scoped_in_world m (FFibVars D φ) ->
  m ⊨ FFibVars D φ ->
  m ⊨ formula_msubst_store σ (FFibVars D φ).
Proof.
  intros Hsingle Hfresh Hscope Hmodel.
  eapply res_models_msubst_store_fibvars_keep_domain_intro; eauto.
  eapply lc_lvars_of_fibvars_model. exact Hmodel.
Qed.

Lemma res_models_FFibVars_nested_elim
    (m : WfWorldT) (D1 D2 : lvset) (φ : FormulaT) :
  lvars_fv D1 ⊆ lvars_fv D2 ->
  m ⊨ FFibVars D1 (FFibVars D2 φ) ->
  m ⊨ FFibVars D2 φ.
Proof.
  intros Hsub Hmodel.
  apply res_models_FFibVars_nested_union_iff in Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff m (D1 ∪ D2) φ Hscope) Hmodel)
    as [HlcU _].
  eapply res_models_FFibVars_same_fv; [| | exact Hmodel].
  - intros v Hv. apply HlcU. set_solver.
  - rewrite lvars_fv_union. set_solver.
Qed.

Lemma res_models_FFibVars_outer_intro_subset
    (m : WfWorldT) (Dsmall Dbig : lvset) (φ : FormulaT) :
  lc_lvars Dsmall ->
  lvars_fv Dsmall ⊆ lvars_fv Dbig ->
  m ⊨ FFibVars Dbig φ ->
  m ⊨ FFibVars Dsmall (FFibVars Dbig φ).
Proof.
  intros Hlc_small Hsub Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff m Dbig φ Hscope) Hmodel)
    as [Hlc_big _].
  apply (proj2 (res_models_FFibVars_nested_union_iff m Dsmall Dbig φ)).
  eapply res_models_FFibVars_same_fv; [| | exact Hmodel].
  - intros v Hv.
    rewrite elem_of_union in Hv.
    destruct Hv as [Hv|Hv]; [apply Hlc_small | apply Hlc_big]; exact Hv.
  - rewrite lvars_fv_union. set_solver.
Qed.

Lemma res_models_FFibVars_idemp_elim
    (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  m ⊨ FFibVars D (FFibVars D φ) ->
  m ⊨ FFibVars D φ.
Proof.
  intros Hmodel.
  apply res_models_FFibVars_nested_union_iff in Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff m (D ∪ D) φ Hscope) Hmodel)
    as [HlcU _].
  eapply res_models_FFibVars_same_fv; [| | exact Hmodel].
  - intros v Hv. apply HlcU. set_solver.
  - rewrite lvars_fv_union. set_solver.
Qed.

Lemma res_models_FFibVars_star_elim_shared_singleton
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) (σD : StoreT) :
  dom σD = lvars_fv D ->
  (res_restrict m (lvars_fv D) : WorldT) = singleton_world σD ->
  m ⊨ FFibVars D (FStar (FFibVars D φ) (FFibVars D ψ)) ->
  exists (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m /\
    m1 ⊨ FFibVars D φ /\
    m2 ⊨ FFibVars D ψ.
Proof.
  intros HdomσD Hsingleton Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff m D
    (FStar (FFibVars D φ) (FFibVars D ψ)) Hscope) Hmodel)
    as [HlcD _].
  pose proof (res_models_FFibVars_singleton_elim
    m D (FStar (FFibVars D φ) (FFibVars D ψ)) σD
    HdomσD Hsingleton Hmodel) as Hstar.
  cbn [formula_msubst_store formula_mlsubst] in Hstar.
  apply res_models_star_iff in Hstar as
    [n1 [n2 [Hc [Hle [Hn1 Hn2]]]]].
  destruct (res_product_le_singleton_pullback
    m n1 n2 Hc (lvars_fv D) σD Hle HdomσD Hsingleton)
    as [m1 [m2 [Hc' [Hle' [Hsing1 [Hsing2 [Hrest1 Hrest2]]]]]]].
  exists m1, m2, Hc'. split; [exact Hle' |].
  split.
  - pose proof (res_models_msubst_store_full_FFibVars_elim
      n1 D φ σD HdomσD Hn1) as Hn1φ.
    assert (Hm1φ : m1 ⊨ formula_msubst_store σD φ).
    {
      eapply (res_models_of_restrict_eq m1 n1 (world_dom (n1 : WorldT))
        (formula_msubst_store σD φ)).
      - eapply res_models_scoped; exact Hn1φ.
      - exact Hrest1.
      - exact Hn1φ.
    }
    eapply res_models_FFibVars_singleton_intro.
    + eapply formula_scoped_FFibVars_from_singleton_msubst; eauto.
      eapply res_models_scoped; exact Hm1φ.
    + exact HlcD.
    + exact HdomσD.
    + exact Hsing1.
    + exact Hm1φ.
  - pose proof (res_models_msubst_store_full_FFibVars_elim
      n2 D ψ σD HdomσD Hn2) as Hn2ψ.
    assert (Hm2ψ : m2 ⊨ formula_msubst_store σD ψ).
    {
      eapply (res_models_of_restrict_eq m2 n2 (world_dom (n2 : WorldT))
        (formula_msubst_store σD ψ)).
      - eapply res_models_scoped; exact Hn2ψ.
      - exact Hrest2.
      - exact Hn2ψ.
    }
    eapply res_models_FFibVars_singleton_intro.
    + eapply formula_scoped_FFibVars_from_singleton_msubst; eauto.
      eapply res_models_scoped; exact Hm2ψ.
    + exact HlcD.
    + exact HdomσD.
    + exact Hsing2.
    + exact Hm2ψ.
Qed.

Lemma res_models_FFibVars_plus_elim_shared_singleton
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) (σD : StoreT) :
  dom σD = lvars_fv D ->
  (res_restrict m (lvars_fv D) : WorldT) = singleton_world σD ->
  m ⊨ FFibVars D (FPlus (FFibVars D φ) (FFibVars D ψ)) ->
  exists (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m /\
    m1 ⊨ FFibVars D φ /\
    m2 ⊨ FFibVars D ψ.
Proof.
  intros HdomσD Hsingleton Hmodel.
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (proj1 (res_models_FFibVars_iff m D
    (FPlus (FFibVars D φ) (FFibVars D ψ)) Hscope) Hmodel)
    as [HlcD _].
  pose proof (res_models_FFibVars_singleton_elim
    m D (FPlus (FFibVars D φ) (FFibVars D ψ)) σD
    HdomσD Hsingleton Hmodel) as Hplus.
  cbn [formula_msubst_store formula_mlsubst] in Hplus.
  apply res_models_plus_iff in Hplus as
    [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]].
  destruct (res_sum_le_singleton_pullback
    m n1 n2 Hdef (lvars_fv D) σD Hle HdomσD Hsingleton)
    as [m1 [m2 [Hdef' [Hle' [Hsing1 [Hsing2 [Hrest1 Hrest2]]]]]]].
  exists m1, m2, Hdef'. split; [exact Hle' |].
  split.
  - pose proof (res_models_msubst_store_full_FFibVars_elim
      n1 D φ σD HdomσD Hn1) as Hn1φ.
    assert (Hm1φ : m1 ⊨ formula_msubst_store σD φ).
    {
      eapply (res_models_of_restrict_eq m1 n1 (world_dom (n1 : WorldT))
        (formula_msubst_store σD φ)).
      - eapply res_models_scoped; exact Hn1φ.
      - exact Hrest1.
      - exact Hn1φ.
    }
    eapply res_models_FFibVars_singleton_intro.
    + eapply formula_scoped_FFibVars_from_singleton_msubst; eauto.
      eapply res_models_scoped; exact Hm1φ.
    + exact HlcD.
    + exact HdomσD.
    + exact Hsing1.
    + exact Hm1φ.
  - pose proof (res_models_msubst_store_full_FFibVars_elim
      n2 D ψ σD HdomσD Hn2) as Hn2ψ.
    assert (Hm2ψ : m2 ⊨ formula_msubst_store σD ψ).
    {
      eapply (res_models_of_restrict_eq m2 n2 (world_dom (n2 : WorldT))
        (formula_msubst_store σD ψ)).
      - eapply res_models_scoped; exact Hn2ψ.
      - exact Hrest2.
      - exact Hn2ψ.
    }
    eapply res_models_FFibVars_singleton_intro.
    + eapply formula_scoped_FFibVars_from_singleton_msubst; eauto.
      eapply res_models_scoped; exact Hm2ψ.
    + exact HlcD.
    + exact HdomσD.
    + exact Hsing2.
    + exact Hm2ψ.
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

Lemma res_models_FFibVars_impl_elim
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) :
  m ⊨ FFibVars D (FImpl φ ψ) ->
  m ⊨ FFibVars D φ ->
  m ⊨ FFibVars D ψ.
Proof.
  intros Himpl Hφ.
  pose proof (res_models_scoped _ _ Himpl) as Hscope_impl.
  pose proof (proj1 (res_models_FFibVars_iff m D (FImpl φ ψ) Hscope_impl)
    Himpl) as [Hlc Hfib_impl].
  pose proof (res_models_scoped _ _ Hφ) as Hscope_φ.
  pose proof (proj1 (res_models_FFibVars_iff m D φ Hscope_φ) Hφ)
    as [_ Hfib_φ].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D ψ)).
    apply (proj1 (formula_scoped_fibvars_iff m D (FImpl φ ψ)))
      in Hscope_impl.
    destruct Hscope_impl as [HD Hscope_inner].
    apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope_inner.
    split; [exact HD | tauto].
  - exact Hlc.
  - intros σ mfib Hproj.
    specialize (Hfib_impl σ mfib Hproj).
    specialize (Hfib_φ σ mfib Hproj).
    cbn [formula_msubst_store formula_mlsubst] in Hfib_impl.
    eapply res_models_impl_elim; [exact Hfib_impl | exact Hfib_φ].
Qed.

Lemma res_models_FFibVars_impl_intro
    (m : WfWorldT) (D : lvset) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FFibVars D (FImpl φ ψ)) ->
  lc_lvars D ->
  (forall σ mfib,
    res_fiber_from_projection m (lvars_fv D) σ mfib ->
    mfib ⊨ formula_msubst_store σ φ ->
    mfib ⊨ formula_msubst_store σ ψ) ->
  m ⊨ FFibVars D (FImpl φ ψ).
Proof.
  intros Hscope Hlc Hlocal.
  eapply res_models_FFibVars_intro; [exact Hscope | exact Hlc |].
  intros σ mfib Hproj.
  formula_msubst_syntax_norm.
  eapply res_models_impl_intro.
  - apply (proj2 (formula_scoped_impl_iff mfib
      (formula_msubst_store σ φ) (formula_msubst_store σ ψ))).
    pose proof (proj1 (formula_scoped_fibvars_iff m D (FImpl φ ψ))
      Hscope) as [_ Hscope_impl].
    apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope_impl
      as [Hscopeφ Hscopeψ].
    pose proof (res_fiber_from_projection_world_dom m mfib
      (lvars_fv D) σ Hproj) as Hdom.
    split; eapply formula_scoped_in_world_from_formula_fv;
      intros a Ha; rewrite Hdom.
    + apply Hscopeφ. eapply formula_msubst_store_fv_subset. exact Ha.
    + apply Hscopeψ. eapply formula_msubst_store_fv_subset. exact Ha.
  - apply Hlocal. exact Hproj.
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

Lemma res_models_forall_full_world_impl2_map
    (m : WfWorldT)
    (A1 A2 B1 B2 C1 C2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 (FImpl B2 C2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B2 -> my ⊨ formula_open 0 y B1) /\
        (my ⊨ formula_open 0 y C1 -> my ⊨ formula_open 0 y C2)) ->
  m ⊨ FForall (FImpl A1 (FImpl B1 C1)) ->
  m ⊨ FForall (FImpl A2 (FImpl B2 C2)).
Proof.
  intros Hscope [L Hmap] Hsrc.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hsrc].
  exists L. intros y Hy my Hdom Hrestrict Hopen.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA [HB HC]].
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 (FImpl B2 C2)))).
  {
    eapply formula_scoped_open_from_fv.
    unfold formula_scoped_in_world in Hscope |- *.
    rewrite Hdom.
    pose proof (formula_open_fv_subset 0 y (FImpl A2 (FImpl B2 C2))).
    rewrite formula_fv_forall in Hscope.
    set_solver.
  }
  formula_open_syntax_norm_in Hopen.
  formula_open_syntax_norm_in Hopened_scope.
  formula_open_syntax_norm.
  eapply res_models_impl2_map; eauto.
Qed.

Lemma res_models_forall_full_world_impl_wand_map
    (m : WfWorldT)
    (A1 A2 B1 B2 C1 C2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 (FWand B2 C2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (forall (n : WfWorldT) (Hc : world_compat n my),
          n ⊨ formula_open 0 y B2 ->
          n ⊨ formula_open 0 y B1) /\
        (forall (n : WfWorldT) (Hc : world_compat n my),
          res_product n my Hc ⊨ formula_open 0 y C1 ->
          res_product n my Hc ⊨ formula_open 0 y C2)) ->
  m ⊨ FForall (FImpl A1 (FWand B1 C1)) ->
  m ⊨ FForall (FImpl A2 (FWand B2 C2)).
Proof.
  intros Hscope [L Hmap] Hsrc.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hsrc].
  exists L. intros y Hy my Hdom Hrestrict Hopen.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA [HB HC]].
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 (FWand B2 C2)))).
  {
    eapply formula_scoped_open_from_fv.
    unfold formula_scoped_in_world in Hscope |- *.
    rewrite Hdom.
    pose proof (formula_open_fv_subset 0 y (FImpl A2 (FWand B2 C2))).
    rewrite formula_fv_forall in Hscope.
    set_solver.
  }
  formula_open_syntax_norm_in Hopen.
  formula_open_syntax_norm_in Hopened_scope.
  formula_open_syntax_norm.
  eapply res_models_impl_wand_map; eauto.
Qed.

Lemma formula_scoped_forall_impl_wand_opened
    (m my : WfWorldT) y (A B C : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A (FWand B C))) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  formula_scoped_in_world my (formula_open 0 y A) /\
  formula_scoped_in_world my (formula_open 0 y B) /\
  forall (n : WfWorldT) (Hc : world_compat n my),
    formula_scoped_in_world (res_product n my Hc) (formula_open 0 y C).
Proof.
  intros Hscope Hdom.
  pose proof (formula_scoped_open_from_forall_world_dom
    m my (FImpl A (FWand B C)) y Hscope Hdom) as Hopen.
  formula_open_syntax_norm_in Hopen.
  split.
  - eapply formula_scoped_impl_l. exact Hopen.
  - split.
    + eapply formula_scoped_wand_l.
      eapply formula_scoped_impl_r. exact Hopen.
    + intros n Hc.
      eapply formula_scoped_in_world_from_formula_fv.
      pose proof (formula_scoped_wand_r my (formula_open 0 y B)
        (formula_open 0 y C)
        (formula_scoped_impl_r my (formula_open 0 y A)
          (FWand (formula_open 0 y B) (formula_open 0 y C)) Hopen))
        as HCscope.
      unfold formula_scoped_in_world in HCscope |- *.
      cbn [res_product raw_world world_dom].
      set_solver.
Qed.

Lemma formula_scoped_forall_impl2_opened
    (m my : WfWorldT) y (A B C : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A (FImpl B C))) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  formula_scoped_in_world my (formula_open 0 y A) /\
  formula_scoped_in_world my (formula_open 0 y B) /\
  formula_scoped_in_world my (formula_open 0 y C).
Proof.
  intros Hscope Hdom.
  pose proof (formula_scoped_open_from_forall_world_dom
    m my (FImpl A (FImpl B C)) y Hscope Hdom) as Hopen.
  formula_open_syntax_norm_in Hopen.
  split.
  - eapply formula_scoped_impl_l. exact Hopen.
  - split.
    + eapply formula_scoped_impl_l.
      eapply formula_scoped_impl_r. exact Hopen.
    + eapply formula_scoped_impl_r.
      eapply formula_scoped_impl_r. exact Hopen.
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
