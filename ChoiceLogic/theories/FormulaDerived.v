(** * ChoiceLogic.FormulaDerived

    Convenience lemmas for the empty-store satisfaction judgment.

    The core semantics in [Formula] is stated for [res_models_with_store].
    Many downstream proofs use the closed-resource shorthand [res_models];
    this file provides the corresponding intro/elim and transport lemmas at
    the logic layer, so typing proofs do not need to carry local copies. *)

From ChoiceLogic Require Import LogicQualifier Formula FormulaTactics.

Section FormulaDerived.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_and_elim_l (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FAnd φ ψ →
  m ⊨ φ.
Proof.
  unfold res_models.
  apply res_models_with_store_and_elim_l.
Qed.

Lemma res_models_and_elim_r (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FAnd φ ψ →
  m ⊨ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_and_elim_r.
Qed.

Lemma res_models_and_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FAnd φ ψ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_and_intro.
Qed.

Lemma res_models_and_intro_from_models (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  intros Hφ Hψ.
  eapply res_models_and_intro; eauto 6.
  - unfold formula_scoped_in_world.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscopeφ.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure ψ) ∅ m ψ Hψ) as Hscopeψ.
    unfold formula_scoped_in_world in *.
    set_solver.
Qed.

Lemma res_models_and_iff (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FAnd φ ψ ↔ m ⊨ φ ∧ m ⊨ ψ.
Proof.
  split.
  - intros Hand. split.
    + eapply res_models_and_elim_l; eauto 6.
    + eapply res_models_and_elim_r; eauto 6.
  - intros [Hφ Hψ]. eapply res_models_and_intro_from_models; eauto 6.
Qed.

Lemma res_models_or_intro_l (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ φ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_or_intro_l.
Qed.

Lemma res_models_or_intro_r (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_or_intro_r.
Qed.

Lemma res_models_or_intro_l_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  formula_fv ψ ⊆ world_dom (m : World) →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφ Hψscope.
  eapply res_models_or_intro_l; eauto 6.
  - unfold formula_scoped_in_world. simpl.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscopeφ.
    unfold formula_scoped_in_world in Hscopeφ.
    set_solver.
Qed.

Lemma res_models_or_intro_r_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ ⊆ world_dom (m : World) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφscope Hψ.
  eapply res_models_or_intro_r; eauto 6.
  - unfold formula_scoped_in_world. simpl.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure ψ) ∅ m ψ Hψ) as Hscopeψ.
    unfold formula_scoped_in_world in Hscopeψ.
    set_solver.
Qed.

Lemma res_models_or_transport_between_worlds
    (m n : WfWorldT) (φa φb ψa ψb : FormulaT) :
  formula_fv ψa ⊆ world_dom (n : World) →
  formula_fv ψb ⊆ world_dom (n : World) →
  (m ⊨ φa → n ⊨ ψa) →
  (m ⊨ φb → n ⊨ ψb) →
  m ⊨ FOr φa φb →
  n ⊨ FOr ψa ψb.
Proof.
  intros Hψa Hψb Ha Hb Hor.
  unfold res_models, res_models_with_store in Hor.
  simpl in Hor. destruct Hor as [_ [Hleft | Hright]].
  - eapply res_models_or_intro_l_from_model.
    + apply Ha. unfold res_models, res_models_with_store.
      lazymatch type of Hleft with
      | res_models_with_store_fuel ?g ?ρ ?w ?φ =>
          eapply (res_models_with_store_fuel_irrel g (formula_measure φ) ρ w φ);
          [simpl; lia | lia | exact Hleft]
      end.
    + exact Hψb.
  - eapply res_models_or_intro_r_from_model.
    + exact Hψa.
    + apply Hb. unfold res_models, res_models_with_store.
      lazymatch type of Hright with
      | res_models_with_store_fuel ?g ?ρ ?w ?φ =>
          eapply (res_models_with_store_fuel_irrel g (formula_measure φ) ρ w φ);
          [simpl; lia | lia | exact Hright]
      end.
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT) (Hc : world_compat m1 m2) :
  formula_scoped_in_world ∅ m (FStar φ ψ) →
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hle Hφ Hψ. split; [exact Hscope |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_star_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FStar φ ψ) →
  (m ⊨ FStar φ ψ ↔
   ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
     res_product m1 m2 Hc ⊑ m ∧ m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  intros Hscope. split.
  - unfold res_models, res_models_with_store.
    simpl. intros [_ [m1 [m2 [Hc [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hc. repeat split; eauto.
    + unfold res_models, res_models_with_store. models_fuel_irrel Hφ.
    + unfold res_models, res_models_with_store. models_fuel_irrel Hψ.
  - intros [m1 [m2 [Hc [Hle [Hφ Hψ]]]]].
    eapply res_models_star_intro; eauto 6.
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT) (Hdef : raw_sum_defined m1 m2) :
  formula_scoped_in_world ∅ m (FPlus φ ψ) →
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hle Hφ Hψ. split; [exact Hscope |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_plus_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FPlus φ ψ) →
  (m ⊨ FPlus φ ψ ↔
   ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
     res_sum m1 m2 Hdef ⊑ m ∧ m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  intros Hscope. split.
  - unfold res_models, res_models_with_store.
    simpl. intros [_ [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hdef. repeat split; eauto.
    + unfold res_models, res_models_with_store. models_fuel_irrel Hφ.
    + unfold res_models, res_models_with_store. models_fuel_irrel Hψ.
  - intros [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]].
    eapply res_models_plus_intro; eauto 6.
Qed.

Lemma res_models_plus_intro_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT) (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  intros Hle Hφ Hψ.
  eapply res_models_plus_intro; [| exact Hle | exact Hφ | exact Hψ].
  unfold formula_scoped_in_world.
  cbn [formula_fv].
  pose proof (raw_le_dom _ _ Hle) as Hdom_sum.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in Hscopeφ, Hscopeψ.
  intros z Hz.
  apply elem_of_union in Hz as [Hz | Hz]; [set_solver |].
  apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom_sum. simpl. apply Hscopeφ. set_solver.
  - apply Hdom_sum. simpl. rewrite Hdef. apply Hscopeψ. set_solver.
Qed.

Lemma res_models_plus_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world ∅ m (FPlus φ2 ψ2) →
  (∀ m', m' ⊨ φ1 → m' ⊨ φ2) →
  (∀ m', m' ⊨ ψ1 → m' ⊨ ψ2) →
  m ⊨ FPlus φ1 ψ1 →
  m ⊨ FPlus φ2 ψ2.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ Hψ [_ Hplus]. split; [exact Hscope |].
  destruct Hplus as [m1 [m2 [Hdef [Hle [Hm1 Hm2]]]]].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - assert (Hm1_model : m1 ⊨ φ1).
    {
      unfold res_models, res_models_with_store.
      models_fuel_irrel Hm1.
    }
    pose proof (Hφ m1 Hm1_model) as Hm1'.
    models_fuel_irrel Hm1'.
  - assert (Hm2_model : m2 ⊨ ψ1).
    {
      unfold res_models, res_models_with_store.
      models_fuel_irrel Hm2.
    }
    pose proof (Hψ m2 Hm2_model) as Hm2'.
    models_fuel_irrel Hm2'.
Qed.

Lemma res_models_atom_intro (m : WfWorldT) (q : LogicQualifierT) :
  formula_scoped_in_world ∅ m (FAtom q) →
  logic_qualifier_denote q ∅ m →
  m ⊨ FAtom q.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hscope |]. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_with_store_atom_intro
    (ρ : StoreT) (m : WfWorldT) (q : LogicQualifierT) :
  formula_scoped_in_world ρ m (FAtom q) →
  logic_qualifier_denote q ρ m →
  res_models_with_store ρ m (FAtom q).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hscope |]. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_over_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FOver φ) →
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_with_store_over_intro_same
    (ρ : StoreT) (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ρ m (FOver φ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FOver φ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_over_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  intros Hφ.
  eapply res_models_over_intro_same; eauto 6.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscope.
    unfold formula_scoped_in_world in *. simpl. exact Hscope.
Qed.

Lemma res_models_under_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FUnder φ) →
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_with_store_under_intro_same
    (ρ : StoreT) (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ρ m (FUnder φ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FUnder φ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_under_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  intros Hφ.
  eapply res_models_under_intro_same; eauto 6.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscope.
    unfold formula_scoped_in_world in *. simpl. exact Hscope.
Qed.

Lemma res_models_with_store_resource_atom_vars_witness_intro
    (ρ : StoreT) (m m0 : WfWorldT) D (P : WfWorldT → Prop) :
  formula_scoped_in_world ρ m (FResourceAtom D P) →
  formula_scoped_in_world ρ m0 (FResourceAtom D P) →
  P (res_restrict m0 (lvars_fv D)) →
  m0 ⊑ m →
  res_models_with_store ρ m (FResourceAtom D P).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hscope0 HP Hle.
  split; [exact Hscope |].
  exists m0. repeat split; eauto.
Qed.

Lemma res_models_with_store_store_resource_atom_vars_witness_intro
    (ρ : StoreT) (m m0 : WfWorldT) D
    (P : gmap nat atom → StoreT → WfWorldT → Prop) :
  formula_scoped_in_world ρ m (FStoreResourceAtom D P) →
  formula_scoped_in_world ρ m0 (FStoreResourceAtom D P) →
  P ∅ (store_restrict ρ (lvars_fv D)) (res_restrict m0 (lvars_fv D)) →
  m0 ⊑ m →
  res_models_with_store ρ m (FStoreResourceAtom D P).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hscope0 HP Hle.
  split; [exact Hscope |].
  exists m0. repeat split; eauto.
Qed.

Lemma res_models_FFibVars_intro (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FFibVars D φ) →
  (∀ σ,
     ∀ Hproj : res_restrict m (lvars_fv D) σ,
     res_models_with_store σ
       (res_fiber_from_projection m (lvars_fv D) σ Hproj)
       φ) →
  m ⊨ FFibVars D φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hfib. split; [exact Hscope |].
  split.
  - set_solver.
  - intros σ Hproj.
    rewrite map_empty_union.
    models_fuel_irrel (Hfib σ Hproj).
Qed.

Lemma res_models_FFibVars_iff (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FFibVars D φ) →
  (m ⊨ FFibVars D φ ↔
   ∀ σ,
     ∀ Hproj : res_restrict m (lvars_fv D) σ,
     res_models_with_store σ
       (res_fiber_from_projection m (lvars_fv D) σ Hproj)
       φ).
Proof.
  intros Hscope. split.
  - unfold res_models, res_models_with_store.
    simpl. intros [_ [_ Hfib]] σ Hproj.
    specialize (Hfib σ Hproj).
    rewrite map_empty_union in Hfib.
    models_fuel_irrel Hfib.
  - intros Hfib. eapply res_models_FFibVars_intro; eauto 6.
Qed.

Lemma res_models_impl_future_iff_local (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m φ →
  formula_scoped_in_world ∅ m ψ →
  ((∀ m', m ⊑ m' → m' ⊨ φ → m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hφscope Hψscope. split.
  - intros Hfuture Hφ. eapply Hfuture; [reflexivity | exact Hφ].
  - intros Hlocal m' Hle Hφ.
    assert (Hφ_base : m ⊨ φ).
    {
      pose proof (res_models_minimal_on (world_dom (m : World)) m' φ
        ltac:(unfold formula_scoped_in_world in Hφscope; simpl in Hφscope; set_solver))
        as Hminimal.
      rewrite <- (res_restrict_eq_of_le m m' Hle) at 1.
      apply (proj1 Hminimal). exact Hφ.
    }
    eapply res_models_kripke; [exact Hle |].
    eauto 6.
Qed.

Lemma res_models_impl_future_iff_local_from_impl_scope
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  ((∀ m', m ⊑ m' → m' ⊨ φ → m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hscope.
  eapply res_models_impl_future_iff_local;
    unfold formula_scoped_in_world in *; simpl in *; set_solver.
Qed.

Lemma res_models_impl_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hscope Hlocal.
  pose proof (proj2 (res_models_impl_future_iff_local_from_impl_scope
    m φ ψ Hscope) Hlocal) as Hfuture.
  unfold res_models.
  eapply res_models_with_store_impl_intro; [exact Hscope |].
  intros m' Hle Hφ.
  change (m' ⊨ φ) in Hφ.
  change (m' ⊨ ψ).
  eauto 6.
Qed.

Lemma res_models_impl_elim (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_elim.
Qed.

Lemma res_models_impl_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  (m ⊨ FImpl φ ψ ↔ (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hscope. split.
  - intros Himpl Hφ. eapply res_models_impl_elim; eauto 6.
  - intros Himpl. eapply res_models_impl_intro; eauto 6.
Qed.

Lemma res_models_impl_antecedent_strengthen
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ2 ψ) →
  (m ⊨ φ2 → m ⊨ φ1) →
  m ⊨ FImpl φ1 ψ →
  m ⊨ FImpl φ2 ψ.
Proof.
  intros Hscope Hφ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  eapply res_models_impl_elim; eauto 6.
Qed.

Lemma res_models_impl_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ2 ψ2) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ1 → m ⊨ ψ2) →
  m ⊨ FImpl φ1 ψ1 →
  m ⊨ FImpl φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  apply Hψ.
  eapply res_models_impl_elim.
  - exact Himpl.
  - apply Hφ. exact Hφ2.
Qed.

Lemma res_models_wand_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FWand φ ψ) →
  (∀ m' : WfWorldT, ∀ Hc : world_compat m' m,
     m' ⊨ φ →
     res_product m' m Hc ⊨ ψ) →
  m ⊨ FWand φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hwand. split; [exact Hscope |].
  intros m' Hc Hφ.
  pose proof (Hwand m' Hc ltac:(models_fuel_irrel Hφ)) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_wand_elim
    (m m' : WfWorldT) (φ ψ : FormulaT) (Hc : world_compat m' m) :
  m ⊨ FWand φ ψ →
  m' ⊨ φ →
  res_product m' m Hc ⊨ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ Hwand] Hφ.
  pose proof (Hwand m' Hc ltac:(models_fuel_irrel Hφ)) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_wand_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FWand φ ψ) →
  (m ⊨ FWand φ ψ ↔
   ∀ (m' : WfWorldT) (Hc : world_compat m' m),
     m' ⊨ φ →
     res_product m' m Hc ⊨ ψ).
Proof.
  intros Hscope. split.
  - intros Hwand m' Hc Hφ. eapply res_models_wand_elim; eauto 6.
  - intros Hwand. eapply res_models_wand_intro; eauto 6.
Qed.

Lemma res_models_wand_antecedent_strengthen
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FWand φ2 ψ) →
  (∀ m' : WfWorldT, ∀ Hc : world_compat m' m, m' ⊨ φ2 → m' ⊨ φ1) →
  m ⊨ FWand φ1 ψ →
  m ⊨ FWand φ2 ψ.
Proof.
  intros Hscope Hφ Hwand.
  eapply res_models_wand_intro; [exact Hscope |].
  intros m' Hc Hφ2.
  eapply res_models_wand_elim; eauto 6.
Qed.

Lemma res_models_wand_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world ∅ m (FWand φ2 ψ2) →
  (∀ m' : WfWorldT, ∀ Hc : world_compat m' m, m' ⊨ φ2 → m' ⊨ φ1) →
  (∀ m' : WfWorldT, ∀ Hc : world_compat m' m,
      res_product m' m Hc ⊨ ψ1 →
      res_product m' m Hc ⊨ ψ2) →
  m ⊨ FWand φ1 ψ1 →
  m ⊨ FWand φ2 ψ2.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ Hψ [_ Hwand]. split; [exact Hscope |].
  intros m' Hc Hφ2.
  assert (Hφ2_fuel :
      res_models_with_store_fuel (formula_measure φ2) ∅ m' φ2).
  {
    models_fuel_irrel Hφ2.
  }
  pose proof (Hφ m' Hc Hφ2_fuel) as Hφ1_fuel.
  assert (Hφ1_sum :
      res_models_with_store_fuel
        (formula_measure φ1 + formula_measure ψ1) ∅ m' φ1).
  {
    models_fuel_irrel Hφ1_fuel.
  }
  pose proof (Hwand m' Hc Hφ1_sum) as Hψ1.
  assert (Hψ1_fuel :
      res_models_with_store_fuel (formula_measure ψ1) ∅
        (res_product m' m Hc) ψ1).
  {
    models_fuel_irrel Hψ1.
  }
  pose proof (Hψ m' Hc Hψ1_fuel) as Hψ2.
  models_fuel_irrel Hψ2.
Qed.

Lemma res_models_forall_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FForall φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∀ m' : WfWorldT,
        world_dom m' = world_dom m ∪ {[y]} →
        res_restrict m' (world_dom m) = m →
        m' ⊨ formula_open 0 y φ) →
  m ⊨ FForall φ.
Proof.
  intros Hscope [L [HLdom Hopen]].
  unfold res_models, res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv].
  split; [exact Hscope |].
  exists L. split; [exact HLdom |].
  intros y Hy m' Hdom Hrestrict.
  specialize (Hopen y Hy m' Hdom Hrestrict).
  models_fuel_irrel Hopen.
Qed.

Lemma res_models_forall_iff (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FForall φ) →
  (m ⊨ FForall φ ↔
   ∃ L : aset,
     world_dom m ⊆ L ∧
     ∀ y : atom,
       y ∉ L →
       ∀ m' : WfWorldT,
         world_dom m' = world_dom m ∪ {[y]} →
         res_restrict m' (world_dom m) = m →
         m' ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - unfold res_models, res_models_with_store.
    cbn [formula_measure res_models_with_store_fuel
      formula_scoped_in_world formula_fv].
    intros [_ [L [HLdom Hopen]]].
    exists L. split; [exact HLdom |].
    intros y Hy m' Hdom Hrestrict.
    specialize (Hopen y Hy m' Hdom Hrestrict).
    models_fuel_irrel Hopen.
  - intros Hforall.
    eapply res_models_forall_intro; eauto.
Qed.

Lemma res_models_forall_map (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FForall ψ) →
  (∀ y : atom,
    y ∉ world_dom m →
    ∀ m' : WfWorldT,
      world_dom m' = world_dom m ∪ {[y]} →
      res_restrict m' (world_dom m) = m →
      m' ⊨ formula_open 0 y φ →
      m' ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  m ⊨ FForall ψ.
Proof.
  intros Hscope Hmap Hforall.
  eapply res_models_forall_intro; [exact Hscope |].
  unfold res_models, res_models_with_store in Hforall.
  cbn [formula_measure res_models_with_store_fuel
    formula_scoped_in_world formula_fv] in Hforall.
  destruct Hforall as [_ [L [HLdom Hopen]]].
  exists (L ∪ world_dom m).
  split; [set_solver |].
  intros y Hy m' Hdom Hrestrict.
  rewrite not_elem_of_union in Hy.
  destruct Hy as [HyL Hym].
  eapply Hmap; eauto.
  specialize (Hopen y HyL m' Hdom Hrestrict).
  models_fuel_irrel Hopen.
Qed.

Lemma res_models_forall_transport
    (m n : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ n (FForall ψ) →
  (∃ L : aset,
    world_dom (m : World) ∪ world_dom (n : World) ⊆ L ∧
    ∀ y (ny : WfWorldT),
      y ∉ L →
      world_dom (ny : World) = world_dom (n : World) ∪ {[y]} →
      res_restrict ny (world_dom (n : World)) = n →
      (∀ my : WfWorldT,
        world_dom (my : World) = world_dom (m : World) ∪ {[y]} →
        res_restrict my (world_dom (m : World)) = m →
        my ⊨ formula_open 0 y φ) →
      ny ⊨ formula_open 0 y ψ) →
  m ⊨ FForall φ →
  n ⊨ FForall ψ.
Proof.
  intros Hscope [Lmap [HLmap Hmap]] Hforall.
  eapply res_models_forall_intro; [exact Hscope |].
  unfold res_models, res_models_with_store in Hforall.
  cbn [formula_measure res_models_with_store_fuel
    formula_scoped_in_world formula_fv] in Hforall.
  destruct Hforall as [_ [L [HLdom Hopen]]].
  exists (L ∪ Lmap).
  split; [set_solver |].
  intros y Hy ny Hdom_ny Hrestrict_ny.
  rewrite not_elem_of_union in Hy.
  destruct Hy as [HyL HyMap].
  specialize (Hopen y HyL).
  eapply Hmap; eauto.
  intros my Hdom_my Hrestrict_my.
  specialize (Hopen my Hdom_my Hrestrict_my).
  models_fuel_irrel Hopen.
Qed.

Lemma res_models_exists_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world ∅ m (FExists φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorldT,
        world_dom m' = world_dom m ∪ {[y]} ∧
        res_restrict m' (world_dom m) = m ∧
        m' ⊨ formula_open 0 y φ) →
  m ⊨ FExists φ.
Proof.
  intros Hscope [L [HLdom Hopen]].
  unfold res_models, res_models_with_store.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv].
  split; [exact Hscope |].
  exists L. split; [exact HLdom |].
  intros y Hy.
  destruct (Hopen y Hy) as [m' [Hdom [Hrestrict Hmodel]]].
  exists m'. repeat split; eauto.
  models_fuel_irrel Hmodel.
Qed.

End FormulaDerived.
