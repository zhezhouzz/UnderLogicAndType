(** * ChoiceLogic.FormulaDerived

    Convenience lemmas for the empty-store satisfaction judgment.

    The core semantics in [Formula] is stated for [res_models_with_store].
    Many downstream proofs use the closed-resource shorthand [res_models];
    this file provides the corresponding intro/elim and transport lemmas at
    the logic layer, so typing proofs do not need to carry local copies. *)

From ChoiceLogic Require Import Prelude LogicQualifier Formula FormulaTactics.

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
  eapply res_models_and_intro.
  - unfold formula_scoped_in_world.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscopeφ.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure ψ) ∅ m ψ Hψ) as Hscopeψ.
    unfold formula_scoped_in_world in *.
    set_solver.
  - exact Hφ.
  - exact Hψ.
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
  eapply res_models_or_intro_l.
  - unfold formula_scoped_in_world. simpl.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscopeφ.
    unfold formula_scoped_in_world in Hscopeφ.
    set_solver.
  - exact Hφ.
Qed.

Lemma res_models_or_intro_r_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ ⊆ world_dom (m : World) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφscope Hψ.
  eapply res_models_or_intro_r.
  - unfold formula_scoped_in_world. simpl.
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure ψ) ∅ m ψ Hψ) as Hscopeψ.
    unfold formula_scoped_in_world in Hscopeψ.
    set_solver.
  - exact Hψ.
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
  eapply res_models_over_intro_same.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscope.
    unfold formula_scoped_in_world in *. simpl. exact Hscope.
  - exact Hφ.
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
  eapply res_models_under_intro_same.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure φ) ∅ m φ Hφ) as Hscope.
    unfold formula_scoped_in_world in *. simpl. exact Hscope.
  - exact Hφ.
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

Lemma res_models_impl_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_intro.
Qed.

Lemma res_models_impl_elim (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_elim.
Qed.

Lemma res_models_impl_antecedent_strengthen
    (m : WfWorldT) (φ1 φ2 ψ : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ2 ψ) →
  (∀ m', m ⊑ m' → m' ⊨ φ2 → m' ⊨ φ1) →
  m ⊨ FImpl φ1 ψ →
  m ⊨ FImpl φ2 ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_antecedent_strengthen.
Qed.

Lemma res_models_impl_map
    (m : WfWorldT) (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world ∅ m (FImpl φ2 ψ2) →
  (∀ m', m ⊑ m' → m' ⊨ φ2 → m' ⊨ φ1) →
  (∀ m', m ⊑ m' → m' ⊨ ψ1 → m' ⊨ ψ2) →
  m ⊨ FImpl φ1 ψ1 →
  m ⊨ FImpl φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros m' Hle Hφ2.
  apply Hψ; [exact Hle |].
  eapply res_models_impl_elim.
  - eapply res_models_kripke; [exact Hle | exact Himpl].
  - apply Hφ; [exact Hle | exact Hφ2].
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
  eapply res_models_wand_elim.
  - exact Hwand.
  - apply Hφ; [exact Hc | exact Hφ2].
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
