(** * ChoiceTyping.SoundnessHelpers

    Stable formula/context helper lemmas used by the soundness proof.  Keeping
    them outside [Soundness.v] leaves the fundamental-theorem file focused on
    the proof cases themselves. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export Typing.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma res_models_impl_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FImpl φ ψ →
  m ⊑ m' →
  m' ⊨ FImpl φ ψ.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.

Lemma res_models_and_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FAnd φ ψ →
  m ⊑ m' →
  m' ⊨ FAnd φ ψ.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.

Lemma res_models_and_elim_l (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FAnd φ ψ →
  m ⊨ φ.
Proof.
  unfold res_models.
  apply res_models_with_store_and_elim_l.
Qed.

Lemma res_models_and_elim_r (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FAnd φ ψ →
  m ⊨ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_and_elim_r.
Qed.

Lemma res_models_and_intro (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FAnd φ ψ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_and_intro.
Qed.

Lemma res_models_and_intro_from_models (m : WfWorld) (φ ψ : FormulaQ) :
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

Lemma res_models_or_intro_l (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ φ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_or_intro_l.
Qed.

Lemma res_models_or_intro_r (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_or_intro_r.
Qed.

Lemma res_models_or_intro_l_from_model (m : WfWorld) (φ ψ : FormulaQ) :
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

Lemma res_models_or_intro_r_from_model (m : WfWorld) (φ ψ : FormulaQ) :
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

Lemma basic_world_formula_dom_subset Σ X (m : WfWorld) :
  m ⊨ basic_world_formula Σ X →
  X ⊆ world_dom (m : World).
Proof.
  intros Hm.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (basic_world_formula Σ X)) ∅ m
    (basic_world_formula Σ X) Hm) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite basic_world_formula_fv in Hscope.
  intros z Hz. apply Hscope. set_solver.
Qed.

Lemma basic_steps_result_regular e v T :
  ∅ ⊢ₑ e ⋮ T →
  e →* tret v →
  stale v = ∅ ∧ is_lc v.
Proof.
  intros Hty Hsteps.
  pose proof (basic_steps_preservation ∅ e (tret v) T Hty Hsteps) as Hret.
  inversion Hret; subst.
  match goal with
  | H : _ ⊢ᵥ _ ⋮ _ |- _ =>
      split;
      [eapply basic_typing_closed_value; exact H
      | eapply basic_typing_regular_value; exact H]
  end.
Qed.

Lemma env_has_type_lc_env_dom Γ σ :
  dom σ ⊆ dom Γ →
  env_has_type Γ σ →
  lc_env σ.
Proof.
  intros Hdom Htyped.
  unfold lc_env. apply map_Forall_lookup_2.
  intros x v Hlookup.
  assert (HxΓ : x ∈ dom Γ).
  { apply Hdom. apply elem_of_dom. eexists. exact Hlookup. }
  apply elem_of_dom in HxΓ as [T HΓ].
  exact (basic_typing_regular_value ∅ v T (Htyped x T v HΓ Hlookup)).
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorld) (φ ψ : FormulaQ) (Hc : world_compat m1 m2) :
  formula_scoped_in_world ∅ m (FStar φ ψ) →
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hle Hφ Hψ. split; [exact Hscope |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorld) (φ ψ : FormulaQ) (Hdef : raw_sum_defined m1 m2) :
  formula_scoped_in_world ∅ m (FPlus φ ψ) →
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hle Hφ Hψ. split; [exact Hscope |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_atom_intro (m : WfWorld) (q : logic_qualifier) :
  formula_scoped_in_world ∅ m (FAtom q) →
  logic_qualifier_denote q ∅ m →
  m ⊨ FAtom q.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hscope |]. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_with_store_atom_intro
    (ρ : Store) (m : WfWorld) (q : logic_qualifier) :
  formula_scoped_in_world ρ m (FAtom q) →
  logic_qualifier_denote q ρ m →
  res_models_with_store ρ m (FAtom q).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hscope |]. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_over_intro_same (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOver φ) →
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_with_store_over_intro_same
    (ρ : Store) (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ρ m (FOver φ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FOver φ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_over_intro_same_from_model (m : WfWorld) (φ : FormulaQ) :
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

Lemma res_models_under_intro_same (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FUnder φ) →
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_with_store_under_intro_same
    (ρ : Store) (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ρ m (FUnder φ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FUnder φ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_under_intro_same_from_model (m : WfWorld) (φ : FormulaQ) :
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

Lemma res_models_fib_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FFib x φ) →
  (∀ σ,
     ∀ Hproj : res_restrict m {[x]} σ,
     res_models_with_store σ
       (res_fiber_from_projection m {[x]} σ Hproj)
       φ) →
  m ⊨ FFib x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hfib. split; [exact Hscope |].
  split.
  - set_solver.
  - intros σ Hproj.
    rewrite map_empty_union.
    eapply res_models_with_store_fuel_irrel; [| | exact (Hfib σ Hproj)];
      simpl; lia.
Qed.

Lemma res_models_impl_intro (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_intro.
Qed.

(** Kripke implication elimination at the current world. *)
Lemma res_models_impl_elim (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_elim.
Qed.

Lemma res_models_impl_antecedent_strengthen
    (m : WfWorld) (φ1 φ2 ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FImpl φ2 ψ) →
  (∀ m', m ⊑ m' → m' ⊨ φ2 → m' ⊨ φ1) →
  m ⊨ FImpl φ1 ψ →
  m ⊨ FImpl φ2 ψ.
Proof.
  unfold res_models.
  apply res_models_with_store_impl_antecedent_strengthen.
Qed.

Lemma res_models_impl_map
    (m : WfWorld) (φ1 φ2 ψ1 ψ2 : FormulaQ) :
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

Lemma res_models_forall_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FForall x φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∀ m' : WfWorld,
        world_dom m' = world_dom m ∪ {[y]} →
        res_restrict m' (world_dom m) = m →
        m' ⊨ formula_rename_atom x y φ) →
  m ⊨ FForall x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hforall]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy m' Hdom Hrestr.
  eapply res_models_with_store_fuel_irrel; [| | exact (Hforall y Hy m' Hdom Hrestr)];
    rewrite ?formula_rename_preserves_measure; simpl; lia.
Qed.

Lemma res_models_fresh_forall_transport
    (m : WfWorld) (D : aset) (body1 body2 : atom → FormulaQ) :
  formula_scoped_in_world ∅ m (fresh_forall D body2) →
  (∀ y m',
    m' ⊨ formula_rename_atom (fresh_for D) y (body1 (fresh_for D)) →
    m' ⊨ formula_rename_atom (fresh_for D) y (body2 (fresh_for D))) →
  m ⊨ fresh_forall D body1 →
  m ⊨ fresh_forall D body2.
Proof.
  intros Hscope Hbody Hm.
  unfold res_models in *.
  eapply res_models_with_store_fresh_forall_transport; eauto.
Qed.

Lemma res_models_fresh_forall_transport2
    (m : WfWorld) (D1 D2 : aset) (body1 body2 : atom → FormulaQ) :
  formula_scoped_in_world ∅ m (fresh_forall D2 body2) →
  (∀ y m',
    m' ⊨ formula_rename_atom (fresh_for D1) y (body1 (fresh_for D1)) →
    m' ⊨ formula_rename_atom (fresh_for D2) y (body2 (fresh_for D2))) →
  m ⊨ fresh_forall D1 body1 →
  m ⊨ fresh_forall D2 body2.
Proof.
  intros Hscope Hbody Hm.
  unfold res_models in *.
  eapply res_models_with_store_fresh_forall_transport; eauto.
Qed.

Lemma res_models_exists_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FExists x φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom m' = world_dom m ∪ {[y]} ∧
        res_restrict m' (world_dom m) = m ∧
        m' ⊨ formula_rename_atom x y φ) →
  m ⊨ FExists x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hexists]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hφ]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ];
    rewrite ?formula_rename_preserves_measure; simpl; lia.
Qed.

(** ** Environment-indexed context helpers *)

Lemma denot_ctx_in_env_basic Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ basic_world_formula Σ (dom Σ).
Proof.
  unfold denot_ctx_in_env.
  apply res_models_and_elim_l.
Qed.

Lemma denot_ctx_in_env_ctx Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ctx_under Σ Γ.
Proof.
  unfold denot_ctx_in_env.
  intros HΓ.
  apply res_models_and_elim_r in HΓ.
  apply res_models_and_elim_r in HΓ.
  exact HΓ.
Qed.

Lemma denot_ctx_in_env_erased_basic Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ basic_world_formula
        (erase_ctx_under Σ Γ) (dom (erase_ctx_under Σ Γ)).
Proof.
  unfold denot_ctx_in_env.
  intros HΓ.
  apply res_models_and_elim_r in HΓ.
  apply res_models_and_elim_l in HΓ.
  exact HΓ.
Qed.

Lemma denot_ctx_in_env_world_has_type Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  world_has_type_on Σ (dom Σ) (res_restrict m (dom Σ)).
Proof.
  intros HΓ.
  apply basic_world_formula_current.
  apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
Qed.

Lemma denot_ctx_in_env_world_has_type_on Σ Γ X m :
  X ⊆ dom Σ →
  m ⊨ denot_ctx_in_env Σ Γ →
  world_has_type_on Σ X (res_restrict m X).
Proof.
  intros HXΣ HΓ.
  eapply basic_world_formula_subset_current; [exact HXΣ |].
  apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
Qed.

Lemma denot_ctx_in_env_world_closed_on Σ Γ X m :
  X ⊆ dom Σ →
  m ⊨ denot_ctx_in_env Σ Γ →
  world_closed_on X m.
Proof.
  intros HXΣ HΓ σ Hσ.
  pose proof (denot_ctx_in_env_world_has_type_on Σ Γ X m HXΣ HΓ)
    as [_ Htyped].
  eapply (store_has_type_on_closed_env Σ X (store_restrict σ X)).
  - rewrite store_restrict_dom. set_solver.
  - exact HXΣ.
  - apply Htyped. simpl. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma denot_ctx_in_env_store_typed Σ Γ m σ :
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  store_has_type_on Σ (dom Σ) (store_restrict σ (dom Σ)).
Proof.
  intros HΓ Hσ.
  eapply basic_world_formula_store_restrict_typed.
  - apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
  - exact Hσ.
Qed.

Lemma denot_ctx_in_env_store_restrict_closed Σ Γ m σ :
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  closed_env (store_restrict σ (dom Σ)).
Proof.
  intros HΓ Hσ.
  eapply basic_world_formula_store_restrict_closed_env.
  - apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
  - set_solver.
  - exact Hσ.
Qed.

Lemma denot_ctx_in_env_store_restrict_closed_on Σ Γ X m σ :
  X ⊆ dom Σ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  closed_env (store_restrict σ X).
Proof.
  intros HXΣ HΓ Hσ.
  pose proof (denot_ctx_in_env_world_has_type_on Σ Γ X m HXΣ HΓ)
    as [Hdom Htyped].
  eapply (store_has_type_on_closed_env Σ X).
  - pose proof (wfworld_store_dom (res_restrict m X)
      (store_restrict σ X) ltac:(simpl; exists σ; split; [exact Hσ | reflexivity]))
      as Hdomσ.
    rewrite Hdomσ. simpl. set_solver.
  - exact HXΣ.
  - apply Htyped. simpl. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma denot_ctx_in_env_store_restrict_lc Σ Γ m σ :
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  lc_env (store_restrict σ (dom Σ)).
Proof.
  intros HΓ Hσ.
  eapply basic_world_formula_store_restrict_lc_env.
  - apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
  - set_solver.
  - exact Hσ.
Qed.

Lemma denot_ctx_in_env_store_restrict_lc_on Σ Γ X m σ :
  X ⊆ dom Σ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  lc_env (store_restrict σ X).
Proof.
  intros HXΣ HΓ Hσ.
  pose proof (denot_ctx_in_env_world_has_type_on Σ Γ X m HXΣ HΓ)
    as [Hdom Htyped].
  eapply (store_has_type_on_lc_env Σ X).
  - pose proof (wfworld_store_dom (res_restrict m X)
      (store_restrict σ X) ltac:(simpl; exists σ; split; [exact Hσ | reflexivity]))
      as Hdomσ.
    rewrite Hdomσ. simpl. set_solver.
  - exact HXΣ.
  - apply Htyped. simpl. exists σ. split; [exact Hσ | reflexivity].
Qed.

(** Regularity obligation for context denotations: a world satisfying
    [denot_ctx_in_env Σ Γ] provides basic typed values for every coordinate
    used by the erased environment [erase_ctx_under Σ Γ].  This is independent
    of any particular typing rule; the full proof should proceed by induction
    over [Γ], using the basic-world conjuncts produced by type denotations for
    binders. *)
Lemma denot_ctx_in_env_store_erased_typed Σ Γ m σ :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  let X := dom Σ ∪ ctx_dom Γ in
  closed_env (store_restrict σ X) ∧
  env_has_type (erase_ctx_under Σ Γ) (store_restrict σ X).
Proof.
  intros Hbasic HΓ Hσ X.
  assert (HdomX : X = dom (erase_ctx_under Σ Γ)).
  {
    unfold X, erase_ctx_under.
    rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hbasic).
    reflexivity.
  }
  rewrite HdomX.
  split.
  - eapply basic_world_formula_store_restrict_closed_env.
    + apply denot_ctx_in_env_erased_basic. exact HΓ.
    + set_solver.
    + exact Hσ.
  - intros x T v HΣx Hσx.
    pose proof (basic_world_formula_store_restrict_typed
      (erase_ctx_under Σ Γ) (dom (erase_ctx_under Σ Γ)) m σ
      (denot_ctx_in_env_erased_basic Σ Γ m HΓ) Hσ) as Htyped.
    eapply Htyped; [| exact HΣx | exact Hσx].
    apply elem_of_dom. eexists. exact HΣx.
Qed.

Lemma denot_ctx_in_env_store_erased_lc Σ Γ m σ :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  let X := dom Σ ∪ ctx_dom Γ in
  lc_env (store_restrict σ X).
Proof.
  intros Hbasic HΓ Hσ X.
  destruct (denot_ctx_in_env_store_erased_typed Σ Γ m σ Hbasic HΓ Hσ)
    as [_ Htyped].
  eapply env_has_type_lc_env_dom; [| exact Htyped].
  intros z Hz.
  assert (Hdom_erase : dom (erase_ctx_under Σ Γ) = X).
  {
    unfold erase_ctx_under, X.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
    rewrite dom_union_L, HdomΓ. reflexivity.
  }
  rewrite Hdom_erase.
  change (z ∈ dom (store_restrict σ X)) in Hz.
  rewrite store_restrict_dom in Hz. set_solver.
Qed.

Lemma choice_typing_wf_result_closed_in_ctx Σ Γ e τ m σ vx :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  subst_map σ e →* tret vx →
  stale vx = ∅.
Proof.
  intros Hwf HΓ Hσ Hsteps.
  pose proof (choice_typing_wf_fv_tm_subset Σ Γ e τ Hwf) as Hfv.
  destruct Hwf as [Hty Herase].
  set (X := dom Σ ∪ ctx_dom Γ).
  destruct (denot_ctx_in_env_store_erased_typed Σ Γ m σ
    (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty)) HΓ Hσ) as
    [Hclosed Henv].
  assert (Hdom_erase : dom (erase_ctx_under Σ Γ) = X).
  {
    unfold erase_ctx_under, X.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ
      (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty))) as HdomΓ.
    rewrite dom_union_L, HdomΓ. reflexivity.
  }
  assert (HXworld : X ⊆ world_dom (m : World)).
  {
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
      (denot_ctx_in_env Σ Γ) HΓ) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    intros z Hz. apply Hscope.
    pose proof (denot_ctx_in_env_dom_subset_formula_fv Σ Γ z) as Hdomfv.
    apply elem_of_union. right. apply Hdomfv. unfold X in Hz. exact Hz.
  }
  assert (Hdom_del : env_delete (store_restrict σ X) (erase_ctx_under Σ Γ) = ∅).
  {
    apply env_delete_empty_of_dom_subset.
    rewrite Hdom_erase.
    intros z Hz.
    pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
    apply elem_of_dom.
    assert (Hzdom : z ∈ dom σ) by (rewrite Hdomσ; set_solver).
    apply elem_of_dom in Hzdom as [v Hlookup].
    exists v. apply store_restrict_lookup_some_2; [exact Hlookup | set_solver].
  }
  assert (Htyped :
    ∅ ⊢ₑ m{store_restrict σ X} e ⋮ erase_ty τ).
  {
    rewrite <- Hdom_del.
    eapply msubst_basic_typing_tm; eauto.
  }
  assert (Hsubst : m{store_restrict σ X} e = subst_map σ e).
  {
    change (subst_map σ e) with (m{σ} e).
    eapply (@msubst_restrict_closed_on tm stale_tm_inst subst_tm_inst _ _ _).
    - exact Hclosed.
    - unfold X in *. set_solver.
  }
  rewrite Hsubst in Htyped.
  eapply basic_steps_result_closed; eauto.
Qed.

Lemma choice_typing_wf_result_regular_restrict_in_ctx Σ Γ e τ m σ vx :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e →* tret vx →
  stale vx = ∅ ∧ is_lc vx.
Proof.
  intros Hwf HΓ Hσ Hsteps.
  destruct Hwf as [Hty Herase].
  pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty))
    as Hbasic.
  set (X := dom Σ ∪ ctx_dom Γ).
  destruct (denot_ctx_in_env_store_erased_typed Σ Γ m σ Hbasic HΓ Hσ)
    as [Hclosed Henv].
  assert (Hdom_erase : dom (erase_ctx_under Σ Γ) = X).
  {
    unfold erase_ctx_under, X.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
    rewrite dom_union_L, HdomΓ. reflexivity.
  }
  assert (Hdom_del : env_delete (store_restrict σ X) (erase_ctx_under Σ Γ) = ∅).
  {
    apply env_delete_empty_of_dom_subset.
    rewrite Hdom_erase.
    assert (HXworld : X ⊆ world_dom (m : World)).
    {
      pose proof (res_models_with_store_fuel_scoped
        (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
        (denot_ctx_in_env Σ Γ) HΓ) as Hscope.
      unfold formula_scoped_in_world in Hscope.
      intros z Hz. apply Hscope.
      pose proof (denot_ctx_in_env_dom_subset_formula_fv Σ Γ z) as Hdomfv.
      apply elem_of_union. right. apply Hdomfv. unfold X in Hz. exact Hz.
    }
    pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
    intros z Hz.
    apply elem_of_dom.
    assert (Hzdom : z ∈ dom σ) by (rewrite Hdomσ; set_solver).
    apply elem_of_dom in Hzdom as [v Hlookup].
    exists v. apply store_restrict_lookup_some_2; [exact Hlookup | set_solver].
  }
  assert (Htyped :
    ∅ ⊢ₑ m{store_restrict σ X} e ⋮ erase_ty τ).
  {
    rewrite <- Hdom_del.
    eapply msubst_basic_typing_tm; eauto.
  }
  rewrite Hdom_erase in Hsteps.
  eapply basic_steps_result_regular; eauto.
Qed.

Lemma choice_typing_wf_result_typed_restrict_in_ctx Σ Γ e τ m σ vx :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e →* tret vx →
  ∅ ⊢ᵥ vx ⋮ erase_ty τ.
Proof.
  intros Hwf HΓ Hσ Hsteps.
  destruct Hwf as [Hty Herase].
  pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty))
    as Hbasic.
  set (X := dom Σ ∪ ctx_dom Γ).
  destruct (denot_ctx_in_env_store_erased_typed Σ Γ m σ Hbasic HΓ Hσ)
    as [Hclosed Henv].
  assert (Hdom_erase : dom (erase_ctx_under Σ Γ) = X).
  {
    unfold erase_ctx_under, X.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
    rewrite dom_union_L, HdomΓ. reflexivity.
  }
  assert (Hdom_del : env_delete (store_restrict σ X) (erase_ctx_under Σ Γ) = ∅).
  {
    apply env_delete_empty_of_dom_subset.
    rewrite Hdom_erase.
    assert (HXworld : X ⊆ world_dom (m : World)).
    {
      pose proof (res_models_with_store_fuel_scoped
        (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
        (denot_ctx_in_env Σ Γ) HΓ) as Hscope.
      unfold formula_scoped_in_world in Hscope.
      intros z Hz. apply Hscope.
      pose proof (denot_ctx_in_env_dom_subset_formula_fv Σ Γ z) as Hdomfv.
      apply elem_of_union. right. apply Hdomfv. unfold X in Hz. exact Hz.
    }
    pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
    intros z Hz.
    apply elem_of_dom.
    assert (Hzdom : z ∈ dom σ) by (rewrite Hdomσ; set_solver).
    apply elem_of_dom in Hzdom as [v Hlookup].
    exists v. apply store_restrict_lookup_some_2; [exact Hlookup | set_solver].
  }
  assert (Htyped :
    ∅ ⊢ₑ m{store_restrict σ X} e ⋮ erase_ty τ).
  {
    rewrite <- Hdom_del.
    eapply msubst_basic_typing_tm; eauto.
  }
  rewrite Hdom_erase in Hsteps.
  pose proof (basic_steps_preservation ∅ _ _ _ Htyped Hsteps) as Hret.
  inversion Hret; subst.
  assumption.
Qed.

Lemma choice_typing_wf_let_body_helper Σ Γ e1 e2 τ :
  choice_typing_wf Σ Γ (tlete e1 e2) τ →
  body_tm e2.
Proof.
  intros [_ Hbasic].
  apply basic_typing_regular_tm in Hbasic.
  apply lc_lete_iff_body in Hbasic as [_ Hbody].
  exact Hbody.
Qed.

Lemma erase_ctx_under_comma_bind_dom Σ Γ x τ :
  dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ))) =
  dom (erase_ctx_under Σ Γ) ∪ {[x]}.
Proof.
  unfold erase_ctx_under. simpl.
  rewrite !dom_union_L, dom_singleton_L. set_solver.
Qed.

Lemma choice_typing_wf_ctx_stale_subset_erase_dom Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  ctx_stale Γ ⊆ dom (erase_ctx_under Σ Γ).
Proof.
  intros [Hwfτ _].
  pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
    as Hbasic.
  pose proof (basic_ctx_fv_subset (dom Σ) Γ Hbasic) as Hfv.
  rewrite ctx_stale_eq_fv_dom.
  unfold erase_ctx_under.
  rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hbasic).
  set_solver.
Qed.

(** ** Let-result worlds *)

Definition let_result_raw_world
    (ρ : Store) (e : tm) (x : atom) (w : WfWorld) : World := {|
  world_dom := world_dom (w : World) ∪ {[x]};
  world_stores := fun σx =>
    ∃ σ vx,
      (w : World) σ ∧
      subst_map σ (subst_map ρ e) →* tret vx ∧
      σx = <[x := vx]> σ;
|}.

Lemma let_result_raw_world_wf ρ e x (w : WfWorld) :
  x ∉ world_dom (w : World) →
  (∀ σ, (w : World) σ → ∃ vx, subst_map σ (subst_map ρ e) →* tret vx) →
  wf_world (let_result_raw_world ρ e x w).
Proof.
  intros Hfresh Hresult. constructor.
  - destruct (world_wf w) as [[σ Hσ] _].
    destruct (Hresult σ Hσ) as [vx Hsteps].
    exists (<[x := vx]> σ). exists σ, vx. repeat split; eauto.
  - intros σx [σ [vx [Hσ [Hsteps ->]]]].
    rewrite dom_insert_L.
    rewrite (wfworld_store_dom w σ Hσ).
    set_solver.
Qed.

Definition let_result_world
    (ρ : Store) (e : tm) (x : atom) (w : WfWorld)
    (Hfresh : x ∉ world_dom (w : World))
    (Hresult : ∀ σ, (w : World) σ → ∃ vx, subst_map σ (subst_map ρ e) →* tret vx)
    : WfWorld :=
  exist _ (let_result_raw_world ρ e x w)
    (let_result_raw_world_wf ρ e x w Hfresh Hresult).

Lemma let_result_world_member ρ e x (w : WfWorld) Hfresh Hresult σ vx :
  (w : World) σ →
  subst_map σ (subst_map ρ e) →* tret vx →
  (let_result_world ρ e x w Hfresh Hresult : World) (<[x := vx]> σ).
Proof.
  intros Hσ Hsteps. exists σ, vx. repeat split; eauto.
Qed.

Lemma let_result_world_elim ρ e x (w : WfWorld) Hfresh Hresult σx :
  (let_result_world ρ e x w Hfresh Hresult : World) σx →
  ∃ σ vx,
    (w : World) σ ∧
    subst_map σ (subst_map ρ e) →* tret vx ∧
    σx = <[x := vx]> σ.
Proof. intros Hσx. exact Hσx. Qed.

Lemma let_result_world_restrict ρ e x (w : WfWorld) Hfresh Hresult :
  res_restrict (let_result_world ρ e x w Hfresh Hresult)
    (world_dom (w : World)) = w.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
      rewrite store_restrict_insert_notin in Hrestrict by exact Hfresh.
      assert (Hid : store_restrict σ0 (world_dom (w : World)) = σ0).
      { apply store_restrict_idemp.
        pose proof (wfworld_store_dom w σ0 Hσ0). set_solver. }
      rewrite Hid in Hrestrict.
      subst. exact Hσ0.
    + intros Hσ.
      destruct (Hresult σ Hσ) as [vx Hsteps].
      exists (<[x := vx]> σ). split.
      * exists σ, vx. repeat split; eauto.
      * rewrite store_restrict_insert_notin by exact Hfresh.
        apply store_restrict_idemp.
        pose proof (wfworld_store_dom w σ Hσ). set_solver.
Qed.

Lemma let_result_world_le ρ e x (w : WfWorld) Hfresh Hresult :
  w ⊑ let_result_world ρ e x w Hfresh Hresult.
Proof.
  pose proof (res_restrict_le
    (let_result_world ρ e x w Hfresh Hresult)
    (world_dom (w : World))) as Hle.
  rewrite (let_result_world_restrict ρ e x w Hfresh Hresult) in Hle.
  exact Hle.
Qed.

Lemma let_result_world_preserves_context Σ Γ ρ e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world ρ e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
Proof.
  intros Hctx.
  eapply res_models_kripke.
  - apply let_result_world_le.
  - exact Hctx.
Qed.

Definition let_result_raw_world_on
    (X : aset) (e : tm) (x : atom) (w : WfWorld) : World := {|
  world_dom := world_dom (w : World) ∪ {[x]};
  world_stores := fun σx =>
    ∃ σ vx,
      (w : World) σ ∧
      subst_map (store_restrict σ X) e →* tret vx ∧
      σx = <[x := vx]> σ;
|}.

Lemma let_result_raw_world_on_wf X e x (w : WfWorld) :
  x ∉ world_dom (w : World) →
  (∀ σ, (w : World) σ → ∃ vx, subst_map (store_restrict σ X) e →* tret vx) →
  wf_world (let_result_raw_world_on X e x w).
Proof.
  intros Hfresh Hresult. constructor.
  - destruct (world_wf w) as [[σ Hσ] _].
    destruct (Hresult σ Hσ) as [vx Hsteps].
    exists (<[x := vx]> σ). exists σ, vx. repeat split; eauto.
  - intros σx [σ [vx [Hσ [Hsteps ->]]]].
    rewrite dom_insert_L.
    rewrite (wfworld_store_dom w σ Hσ).
    set_solver.
Qed.

Definition let_result_world_on
    (X : aset) (e : tm) (x : atom) (w : WfWorld)
    (Hfresh : x ∉ world_dom (w : World))
    (Hresult : ∀ σ, (w : World) σ → ∃ vx, subst_map (store_restrict σ X) e →* tret vx)
    : WfWorld :=
  exist _ (let_result_raw_world_on X e x w)
    (let_result_raw_world_on_wf X e x w Hfresh Hresult).

Lemma let_result_world_on_member X e x (w : WfWorld) Hfresh Hresult σ vx :
  (w : World) σ →
  subst_map (store_restrict σ X) e →* tret vx →
  (let_result_world_on X e x w Hfresh Hresult : World) (<[x := vx]> σ).
Proof.
  intros Hσ Hsteps. exists σ, vx. repeat split; eauto.
Qed.

Lemma let_result_world_on_elim X e x (w : WfWorld) Hfresh Hresult σx :
  (let_result_world_on X e x w Hfresh Hresult : World) σx →
  ∃ σ vx,
    (w : World) σ ∧
    subst_map (store_restrict σ X) e →* tret vx ∧
    σx = <[x := vx]> σ.
Proof. intros Hσx. exact Hσx. Qed.

Lemma let_result_world_on_restrict X e x (w : WfWorld) Hfresh Hresult :
  res_restrict (let_result_world_on X e x w Hfresh Hresult)
    (world_dom (w : World)) = w.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
      rewrite store_restrict_insert_notin in Hrestrict by exact Hfresh.
      assert (Hid : store_restrict σ0 (world_dom (w : World)) = σ0).
      { apply store_restrict_idemp.
        pose proof (wfworld_store_dom w σ0 Hσ0). set_solver. }
      rewrite Hid in Hrestrict.
      subst. exact Hσ0.
    + intros Hσ.
      destruct (Hresult σ Hσ) as [vx Hsteps].
      exists (<[x := vx]> σ). split.
      * exists σ, vx. repeat split; eauto.
      * rewrite store_restrict_insert_notin by exact Hfresh.
        apply store_restrict_idemp.
        pose proof (wfworld_store_dom w σ Hσ). set_solver.
Qed.

Lemma let_result_world_on_restrict_old
    X e x (w : WfWorld) Hfresh Hresult S :
  S ⊆ world_dom (w : World) →
  x ∉ S →
  res_restrict (let_result_world_on X e x w Hfresh Hresult) S =
  res_restrict w S.
Proof.
  intros HSw HxS.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
      rewrite store_restrict_insert_notin in Hrestrict by exact HxS.
      exists σ0. split; [exact Hσ0 | exact Hrestrict].
    + intros [σ0 [Hσ0 Hrestrict]].
      destruct (Hresult σ0 Hσ0) as [vx Hsteps].
      exists (<[x := vx]> σ0). split.
      * exists σ0, vx. repeat split; eauto.
      * rewrite store_restrict_insert_notin by exact HxS.
        exact Hrestrict.
Qed.

Lemma let_result_world_on_le X e x (w : WfWorld) Hfresh Hresult :
  w ⊑ let_result_world_on X e x w Hfresh Hresult.
Proof.
  pose proof (res_restrict_le
    (let_result_world_on X e x w Hfresh Hresult)
    (world_dom (w : World))) as Hle.
  rewrite (let_result_world_on_restrict X e x w Hfresh Hresult) in Hle.
  exact Hle.
Qed.

(** Proof-only exact graph for [tlet] results.

    This definition is deliberately not part of the paper syntax or semantic
    presentation.  The paper reasons informally with the result set of
    [let x = e1 in e2]; the Rocq proof sometimes needs a concrete witness
    world that remembers which intermediate result produced which final result.

    The important design point is that this is a *relation graph*, not a
    function graph.  If [e1] is nondeterministic, the same input projection
    [σ|X] may produce many intermediate values [vx].  If [e2] is
    nondeterministic, the same pair [(σ|X, vx)] may produce many final values
    [v].  Membership below therefore ranges over all triples [(σ, vx, v)]
    satisfying the two operational reductions:

      [subst_map (store_restrict σ X) e1 →* tret vx]
      [open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v]

    The graph must be exact: it should contain no store unless it comes from
    such a triple, and every such triple is represented by the store
    [<[ν := v]> (<[x := vx]> σ)].  This exactness is what preserves the
    [X -> x -> ν] pairing that [CTOver] needs and also gives the forward
    composition used by [CTUnder].

    Freshness of [x] and [ν] is essential.  They are proof coordinates, so
    inserting them must not overwrite fields already present in the base
    world.  The final result coordinate [ν] is also kept distinct from [x].

    Whenever this definition appears in a proof, remember: it is an auxiliary
    Rocq witness world for tlet soundness, not a new paper-level modality.

    Relation to the expression-result/fiber view:

    - The paper-level intuition is still [∀M FV(e). Atom(mstep e ν)].  The
      surrounding fiber fixes the input store; the atom at the leaf should only
      talk about the result coordinate.  The graph below is the proof-side
      expansion of that idea for [tlet], where the input projection [X], the
      intermediate coordinate [x], and the final result coordinate [ν] all have
      to stay paired.
    - Do not read [world_stores] as allowing arbitrary extensions such as
      [{x ↦ vx, ν ↦ v}] disconnected from the same base input [σ].  Every member
      must come from one base store [σ] in [w], one result [vx] of [e1] over
      [σ|X], and one result [v] of [e2] opened with exactly that [vx].
    - Conversely, every such operational triple must be present.  This is the
      "no extra and no missing stores" invariant we need before proving either
      the over-approximate direction or the under-approximate direction.

    High-risk proof obligation to check first: after projecting/fibering this
    graph at [X ∪ {[x]}], the remaining [ν]-fiber must be exactly the result
    world for [(e2 ^^ x)] under that paired projection.  If that lemma fails,
    this graph shape is wrong and the later fundamental [tlet] case should not
    be trusted. *)
Definition tlet_result_graph_raw_world_on
    (X : aset) (e1 e2 : tm) (x ν : atom) (w : WfWorld) : World := {|
  world_dom := world_dom (w : World) ∪ {[x]} ∪ {[ν]};
  world_stores := fun σxν =>
    ∃ σ vx v,
      (w : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v ∧
      σxν = <[ν := v]> (<[x := vx]> σ);
|}.

Lemma tlet_result_graph_raw_world_on_wf X e1 e2 x ν (w : WfWorld) :
  x ∉ world_dom (w : World) →
  ν ∉ world_dom (w : World) ∪ {[x]} →
  (∃ σ vx v,
    (w : World) σ ∧
    subst_map (store_restrict σ X) e1 →* tret vx ∧
    open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
    stale vx = ∅ ∧
    is_lc vx ∧
    stale v = ∅ ∧
    is_lc v) →
  wf_world (tlet_result_graph_raw_world_on X e1 e2 x ν w).
Proof.
  intros Hfreshx Hfreshν Hinh.
  destruct Hinh as [σ [vx [v Hinh]]].
  destruct Hinh as [Hσ [Hsteps1 [Hsteps2 [Hvx_stale [Hvx_lc [Hv_stale Hv_lc]]]]]].
  constructor.
  - exists (<[ν := v]> (<[x := vx]> σ)).
    exists σ, vx, v. repeat split; eauto.
  - intros σxν Hσxν.
    destruct Hσxν as [σ' [vx' [v' Hgraph]]].
    destruct Hgraph as [Hσ' [_ [_ [_ [_ [_ [_ ->]]]]]]].
    rewrite !dom_insert_L.
    rewrite (wfworld_store_dom w σ' Hσ').
    set_solver.
Qed.

Definition tlet_result_graph_world_on
    (X : aset) (e1 e2 : tm) (x ν : atom) (w : WfWorld)
    (Hfreshx : x ∉ world_dom (w : World))
    (Hfreshν : ν ∉ world_dom (w : World) ∪ {[x]})
    (Hinh : ∃ σ vx v,
      (w : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
      stale vx = ∅ ∧
      is_lc vx ∧
      stale v = ∅ ∧
      is_lc v)
    : WfWorld :=
  exist _ (tlet_result_graph_raw_world_on X e1 e2 x ν w)
    (tlet_result_graph_raw_world_on_wf X e1 e2 x ν w Hfreshx Hfreshν Hinh).

Lemma tlet_result_graph_world_on_member
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh σ vx v :
  (w : World) σ →
  subst_map (store_restrict σ X) e1 →* tret vx →
  open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v →
  stale vx = ∅ →
  is_lc vx →
  stale v = ∅ →
  is_lc v →
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh : World)
    (<[ν := v]> (<[x := vx]> σ)).
Proof.
  intros Hσ Hsteps1 Hsteps2 Hvx_stale Hvx_lc Hv_stale Hv_lc.
  exists σ, vx, v. repeat split; eauto.
Qed.

Lemma tlet_result_graph_world_on_elim
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh σxν :
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh : World) σxν →
  ∃ σ vx v,
    (w : World) σ ∧
    subst_map (store_restrict σ X) e1 →* tret vx ∧
    open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v ∧
    stale vx = ∅ ∧
    is_lc vx ∧
    stale v = ∅ ∧
    is_lc v ∧
    σxν = <[ν := v]> (<[x := vx]> σ).
Proof. intros Hσxν. exact Hσxν. Qed.

Lemma store_restrict_insert_singleton (σ : Store) (x : atom) (v : value) :
  store_restrict (<[x := v]> σ) {[x]} = {[x := v]}.
Proof.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z ∈ {[x]})) as [Hz|Hz].
  - apply elem_of_singleton in Hz. subst z.
    transitivity (Some v).
    + change ((<[x := v]> σ : gmap atom value) !! x = Some v).
      apply lookup_insert_eq.
    + symmetry. rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
  - rewrite lookup_singleton.
    rewrite decide_False by set_solver.
    reflexivity.
Qed.

Lemma store_restrict_insert_fresh_union (σ : Store) (X : aset) (x : atom) (v : value) :
  σ !! x = None →
  x ∉ X →
  store_restrict (<[x := v]> σ) (X ∪ {[x]}) =
  <[x := v]> (store_restrict σ X).
Proof.
  intros Hx_none HxX.
  rewrite store_restrict_insert_in by set_solver.
  f_equal.
  apply (map_eq (M := gmap atom)). intros z.
  change ((store_restrict σ (X ∪ {[x]}) : Store) !! z =
    (store_restrict σ X : Store) !! z).
  rewrite (@store_restrict_lookup value σ (X ∪ {[x]}) z) at 1.
  rewrite (@store_restrict_lookup value σ X z) at 1.
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite decide_True by set_solver.
    rewrite decide_False by exact HxX.
    exact Hx_none.
  - destruct (decide (z ∈ X)) as [HzX|HzX].
    + rewrite !decide_True by set_solver. reflexivity.
    + rewrite !decide_False by set_solver. reflexivity.
Qed.

Lemma tlet_result_graph_member_to_tlet_result_store
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh σxν :
  x ∉ X →
  ν ∉ X →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh : World) σxν →
  expr_result_in_store
    (store_restrict σxν X) (tlete e1 e2) ν
    (store_restrict σxν {[ν]}).
Proof.
  intros HxX HνX Hbody Hgraph.
  destruct (tlet_result_graph_world_on_elim
    X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν Hgraph)
    as [σ [vx [v [Hσ [Hsteps1 [Hsteps2 [Hvx_stale [Hvx_lc [Hv_stale [Hv_lc ->]]]]]]]]]].
  assert (Hρ :
    store_restrict (<[ν := v]> (<[x := vx]> σ)) X =
    store_restrict σ X).
  {
    rewrite store_restrict_insert_notin by exact HνX.
    rewrite store_restrict_insert_notin by exact HxX.
    reflexivity.
  }
  assert (Hν :
    store_restrict (<[ν := v]> (<[x := vx]> σ)) {[ν]} =
    ({[ν := v]} : Store)).
  {
    apply store_restrict_insert_singleton.
  }
  rewrite Hρ, Hν.
  eapply expr_result_in_store_let_intro; eauto.
Qed.

Lemma tlet_result_graph_member_to_body_result_store
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh σxν :
  x ∉ X →
  x ∉ fv_tm e2 →
  ν ∉ X ∪ {[x]} →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh : World) σxν →
  expr_result_in_store
    (store_restrict σxν (X ∪ {[x]})) (e2 ^^ x) ν
    (store_restrict σxν {[ν]}).
Proof.
  intros HxX Hxe2 HνXx Hclosed Hlc Hgraph.
  destruct (tlet_result_graph_world_on_elim
    X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν Hgraph)
    as [σ [vx [v [Hσ [Hsteps1 [Hsteps2 [Hvx_stale [Hvx_lc [Hv_stale [Hv_lc ->]]]]]]]]]].
  assert (Hσx :
    store_restrict (<[ν := v]> (<[x := vx]> σ)) (X ∪ {[x]}) =
    <[x := vx]> (store_restrict σ X)).
  {
    rewrite store_restrict_insert_notin by exact HνXx.
    apply store_restrict_insert_fresh_union.
    - apply not_elem_of_dom.
      pose proof (wfworld_store_dom w σ Hσ) as Hdomσ.
      rewrite Hdomσ. exact Hfreshx.
    - exact HxX.
  }
  assert (Hν :
    store_restrict (<[ν := v]> (<[x := vx]> σ)) {[ν]} =
    ({[ν := v]} : Store)).
  { apply store_restrict_insert_singleton. }
  rewrite Hσx, Hν.
  apply expr_result_store_intro; [exact Hv_stale | exact Hv_lc |].
  change (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x)) with
    (m{<[x := vx]> (store_restrict σ X)} (e2 ^^ x)).
  replace (m{<[x := vx]> (store_restrict σ X)} (e2 ^^ x))
    with (open_tm 0 vx (m{store_restrict σ X} e2)).
  - exact Hsteps2.
  - change (e2 ^^ x) with (open_tm 0 (vfvar x) e2).
    symmetry. apply msubst_intro_open_tm.
    + apply Hclosed. exact Hσ.
    + exact Hvx_stale.
    + exact Hvx_lc.
    + apply Hlc. exact Hσ.
    + change (x ∉ dom (store_restrict σ X) ∪ fv_tm e2).
      rewrite store_restrict_dom. set_solver.
Qed.

Lemma tlet_result_store_to_graph_member
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh σ σν :
  x ∉ X →
  ν ∉ X →
  (w : World) σ →
  store_restrict σν {[ν]} = σν →
  expr_result_in_store (store_restrict σ X) (tlete e1 e2) ν σν →
  (∀ vx,
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  ∃ σxν,
    (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh : World) σxν ∧
    store_restrict σxν X = store_restrict σ X ∧
    store_restrict σxν {[ν]} = σν.
Proof.
  intros HxX HνX Hσ Hσν_dom Hstore Hvx_reg.
  destruct (expr_result_in_store_let_elim
    (store_restrict σ X) e1 e2 ν σν Hstore)
    as [v [vx [Hσν_eq [Hsteps1 Hsteps2]]]].
  destruct (expr_result_store_elim ν
    (subst_map (store_restrict σ X) (tlete e1 e2)) σν Hstore)
    as [v' [Hσν_eq' [Hv_stale [Hv_lc _]]]].
  assert (Hv' : v' = v).
  {
    assert (Hlookv : σν !! ν = Some v).
    { change ((σν : gmap atom value) !! ν = Some v).
      rewrite Hσν_eq, lookup_singleton, decide_True by reflexivity. reflexivity. }
    assert (Hlookv' : σν !! ν = Some v').
    { change ((σν : gmap atom value) !! ν = Some v').
      rewrite Hσν_eq', lookup_singleton, decide_True by reflexivity. reflexivity. }
    rewrite Hlookv in Hlookv'. inversion Hlookv'. reflexivity.
  }
  subst v'.
  pose proof (Hvx_reg vx Hsteps1) as [Hvx_stale Hvx_lc].
  exists (<[ν := v]> (<[x := vx]> σ)).
  split.
  - apply tlet_result_graph_world_on_member; assumption.
  - split.
    + rewrite store_restrict_insert_notin by exact HνX.
      rewrite store_restrict_insert_notin by exact HxX.
      reflexivity.
    + rewrite store_restrict_insert_singleton.
      subst σν. reflexivity.
Qed.

Lemma tlet_result_graph_body_fiber_exact
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh ρx Hproj :
  X ⊆ world_dom (w : World) →
  x ∉ X →
  x ∉ fv_tm e2 →
  ν ∉ X ∪ {[x]} →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  expr_result_in_world
    (store_restrict ρx (X ∪ {[x]})) (e2 ^^ x) ν
    (res_fiber_from_projection
      (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh)
      (X ∪ {[x]}) ρx Hproj).
Proof.
  intros HXdom HxX Hxe2 HνXx Hclosed Hlc σν. split.
  - intros Hσν.
    assert (Hdomρx : dom ρx = X ∪ {[x]}).
    {
      pose proof (wfworld_store_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh)
          (X ∪ {[x]})) ρx Hproj) as Hdom.
      transitivity (world_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh)
          (X ∪ {[x]}) : World)).
      - exact Hdom.
      - simpl. unfold tlet_result_graph_raw_world_on. simpl. set_solver.
    }
    destruct Hσν as [σxν [Hσxν Hσν_eq]].
    destruct Hσxν as [Hgraph Hρx].
    assert (Hρx_full : store_restrict σxν (X ∪ {[x]}) = ρx).
    { rewrite <- Hdomρx. exact Hρx. }
    pose proof (tlet_result_graph_member_to_body_result_store
      X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν
      HxX Hxe2 HνXx Hclosed Hlc Hgraph) as Hstore.
    rewrite Hρx_full in Hstore.
    rewrite Hσν_eq in Hstore.
    replace (store_restrict ρx (X ∪ {[x]})) with ρx.
    2:{ symmetry. apply store_restrict_idemp. rewrite Hdomρx. set_solver. }
    exact Hstore.
  - intros Hstore.
    assert (Hdomρx : dom ρx = X ∪ {[x]}).
    {
      pose proof (wfworld_store_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh)
          (X ∪ {[x]})) ρx Hproj) as Hdom.
      transitivity (world_dom
        (res_restrict
          (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh)
          (X ∪ {[x]}) : World)).
      - exact Hdom.
      - simpl. unfold tlet_result_graph_raw_world_on. simpl. set_solver.
    }
    destruct Hproj as [σxν0 [Hgraph0 Hρx0]].
    destruct (tlet_result_graph_world_on_elim
      X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν0 Hgraph0)
      as [σ [vx [v0 [Hσ [Hsteps1 [_ [Hvx_stale [Hvx_lc [_ [_ ->]]]]]]]]]].
    assert (Hρx_shape :
      ρx = <[x := vx]> (store_restrict σ X)).
    {
      assert (Hρx0_full :
        store_restrict (<[ν := v0]> (<[x := vx]> σ)) (X ∪ {[x]}) = ρx).
      { exact Hρx0. }
      rewrite <- Hρx0_full.
      rewrite store_restrict_insert_notin by exact HνXx.
      apply store_restrict_insert_fresh_union.
      - apply not_elem_of_dom.
        pose proof (wfworld_store_dom w σ Hσ) as Hdomσ.
        rewrite Hdomσ. exact Hfreshx.
      - exact HxX.
    }
    assert (Hρx_id : store_restrict ρx (X ∪ {[x]}) = ρx).
    { apply store_restrict_idemp. rewrite Hdomρx. set_solver. }
    rewrite Hρx_id in Hstore.
    rewrite Hρx_shape in Hstore.
    destruct (expr_result_store_elim ν
      (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x)) σν Hstore)
      as [v [Hσν_eq [Hv_stale [Hv_lc Hsteps_body]]]].
    assert (Hsteps2 :
      open_tm 0 vx (subst_map (store_restrict σ X) e2) →* tret v).
    {
      change (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x)) with
        (m{<[x := vx]> (store_restrict σ X)} (e2 ^^ x)) in Hsteps_body.
      change (e2 ^^ x) with (open_tm 0 (vfvar x) e2) in Hsteps_body.
      pose proof (msubst_intro_open_tm e2 0 vx x (store_restrict σ X)
        ltac:(apply Hclosed; exact Hσ)
        Hvx_stale
        Hvx_lc
        ltac:(apply Hlc; exact Hσ)
        ltac:(change (x ∉ dom (store_restrict σ X) ∪ fv_tm e2);
              rewrite store_restrict_dom; set_solver)) as Heq.
      replace (m{<[x := vx]> (store_restrict σ X)} open_tm 0 x e2)
        with (open_tm 0 vx (m{store_restrict σ X} e2)) in Hsteps_body
        by (symmetry; exact Heq).
      exact Hsteps_body.
    }
    exists (<[ν := v]> (<[x := vx]> σ)). split.
    + split.
      * apply tlet_result_graph_world_on_member; eauto.
      * assert (Hνdomρx : ν ∉ dom ρx).
        { rewrite Hdomρx. exact HνXx. }
        rewrite store_restrict_insert_notin by exact Hνdomρx.
        replace (dom ρx) with (X ∪ {[x]}) by (symmetry; exact Hdomρx).
        rewrite store_restrict_insert_fresh_union.
        -- symmetry. exact Hρx_shape.
        -- apply not_elem_of_dom.
           pose proof (wfworld_store_dom w σ Hσ) as Hdomσ.
           rewrite Hdomσ. exact Hfreshx.
        -- exact HxX.
    + rewrite Hσν_eq.
      apply store_restrict_insert_singleton.
Qed.

(** Input-fiber exactness of the tlet graph.

    This is the companion check to [tlet_result_graph_body_fiber_exact].  If
    we project the graph only at the original input domain [X], then the
    remaining [ν]-fiber is exactly the result world of the whole
    [tlete e1 e2].  In other words, the graph has neither extra final results
    nor missing final results when viewed from the outside.

    This is the high-risk invariant needed by the [CTOver] side of the tlet
    proof: an arbitrary final result of the let expression can be represented
    in the same graph that also remembers the intermediate [x] result used by
    the body proof. *)
Lemma tlet_result_graph_tlet_fiber_exact
    X e1 e2 x ν (w : WfWorld) Hfreshx Hfreshν Hinh ρ Hproj :
  X ⊆ world_dom (w : World) →
  x ∉ X →
  ν ∉ X →
  (∀ σ, (w : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (w : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (w : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (w : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  expr_result_in_world
    (store_restrict ρ X) (tlete e1 e2) ν
    (res_fiber_from_projection
      (tlet_result_graph_world_on X e1 e2 x ν w Hfreshx Hfreshν Hinh)
      X ρ Hproj).
Proof.
  intros HXdom HxX HνX Hclosed Hlc Hresult_closed Hbody σν. split.
  - intros Hσν.
    assert (Hdomρ : dom ρ = X).
    {
      destruct Hproj as [σxν0 [Hgraph0 Hρ0]].
      assert (Hρeq : ρ = store_restrict σxν0 X) by (symmetry; exact Hρ0).
      destruct (tlet_result_graph_world_on_elim
        X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν0 Hgraph0)
        as [σ0 [vx0 [v0 [Hσ0 [_ [_ [_ [_ [_ [_ ->]]]]]]]]]].
      rewrite Hρeq, store_restrict_dom.
      change ((dom (<[ν := v0]> (<[x := vx0]> σ0) : Store) ∩ X) = X).
      rewrite !dom_insert_L.
      pose proof (wfworld_store_dom w σ0 Hσ0) as Hdomσ0.
      rewrite Hdomσ0. set_solver.
    }
    destruct Hσν as [σxν [Hσxν Hσν_eq]].
    destruct Hσxν as [Hgraph Hρ].
    pose proof (tlet_result_graph_member_to_tlet_result_store
      X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν
      HxX HνX Hbody Hgraph) as Hstore.
    rewrite Hσν_eq in Hstore.
    assert (HρX : store_restrict σxν X = store_restrict ρ X).
    {
      transitivity ρ.
      - rewrite <- Hdomρ. exact Hρ.
      - symmetry. apply store_restrict_idemp. set_solver.
    }
    rewrite HρX in Hstore. exact Hstore.
  - intros Hstore.
    destruct Hproj as [σxν0 [Hgraph0 Hρ0]].
    destruct (tlet_result_graph_world_on_elim
      X e1 e2 x ν w Hfreshx Hfreshν Hinh σxν0 Hgraph0)
      as [σ [vx0 [v0 [Hσ [Hsteps10 [_ [_ [_ [_ [_ ->]]]]]]]]]].
    assert (Hρ_shape : ρ = store_restrict σ X).
    {
      rewrite <- Hρ0.
      rewrite store_restrict_insert_notin by exact HνX.
      rewrite store_restrict_insert_notin by exact HxX.
      reflexivity.
    }
    rewrite Hρ_shape in Hstore.
    replace (store_restrict (store_restrict σ X) X) with (store_restrict σ X) in Hstore.
    2:{ rewrite store_restrict_restrict.
        replace (X ∩ X) with X by set_solver.
        reflexivity. }
    assert (Hσν_dom : store_restrict σν {[ν]} = σν).
    {
      destruct (expr_result_store_elim ν
        (subst_map (store_restrict σ X) (tlete e1 e2)) σν Hstore)
        as [v [-> _]].
      apply store_restrict_insert_singleton.
    }
    destruct (tlet_result_store_to_graph_member
      X e1 e2 x ν w Hfreshx Hfreshν Hinh σ σν
      HxX HνX Hσ Hσν_dom Hstore
      (fun vx Hsteps => Hresult_closed σ vx Hσ Hsteps))
      as [σxν [Hgraph [HX Hν]]].
    exists σxν. split.
    + split; [exact Hgraph |].
      rewrite Hρ_shape.
      replace (dom (store_restrict σ X)) with X.
      * exact HX.
      * rewrite store_restrict_dom.
        pose proof (wfworld_store_dom w σ Hσ) as Hdomσ.
        set_solver.
    + exact Hν.
Qed.

Lemma expr_total_results_on_le
    X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  (∀ σ, (m : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v) →
  ∀ σ, (n : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v.
Proof.
  intros HXm Hle Hresult σn Hσn.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  specialize (Hresult (store_restrict σn (world_dom (m : World)))).
  assert (Hσm :
    (m : World) (store_restrict σn (world_dom (m : World)))).
  {
    rewrite Hle. simpl.
    exists σn. split; [exact Hσn |].
    pose proof (raw_le_dom (m : World) (n : World)
      ltac:(unfold raw_le; exact Hle)) as Hdom_mn.
    replace (world_dom (n : World) ∩ world_dom (m : World))
      with (world_dom (m : World)) by set_solver.
    reflexivity.
  }
  destruct (Hresult Hσm) as [v Hsteps].
  exists v.
  rewrite !store_restrict_restrict in Hsteps.
  replace (world_dom (m : World) ∩ X) with X in Hsteps by set_solver.
  exact Hsteps.
Qed.

Lemma expr_total_results_on_restrict
    X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  (∀ σ, (n : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v) →
  ∀ σ, (m : World) σ →
    ∃ v, subst_map (store_restrict σ X) e →* tret v.
Proof.
  intros HXm Hle Hresult σm Hσm.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  rewrite Hle in Hσm. simpl in Hσm.
  destruct Hσm as [σn [Hσn Hrestrict]].
  destruct (Hresult σn Hσn) as [v Hsteps].
  exists v.
  rewrite <- Hrestrict.
  rewrite !store_restrict_restrict.
  replace (world_dom (m : World) ∩ X) with X by set_solver.
  exact Hsteps.
Qed.

Lemma let_result_world_on_base_mono
    X e x (m n : WfWorld)
    (Hfresh_m : x ∉ world_dom (m : World))
    (Hfresh_n : x ∉ world_dom (n : World))
    Hresult_m Hresult_n :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  let_result_world_on X e x m Hfresh_m Hresult_m ⊑
    let_result_world_on X e x n Hfresh_n Hresult_n.
Proof.
  intros HXm Hle.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl.
    pose proof (raw_le_dom (m : World) (n : World) Hle) as Hdom.
    set_solver.
  - intros σx. simpl. split.
    + intros Hσx.
      destruct Hσx as [σm [vx [Hσm [Hsteps ->]]]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hσm.
      destruct Hσm as [σn [Hσn Hrestrict_m]].
      exists (<[x := vx]> σn). split.
      * exists σn, vx. repeat split; eauto.
        assert (HstoreX : store_restrict σn X = store_restrict σm X).
        {
          rewrite <- Hrestrict_m.
          rewrite !store_restrict_restrict.
          replace (world_dom (m : World) ∩ X) with X by set_solver.
          reflexivity.
        }
        rewrite HstoreX. exact Hsteps.
      * rewrite <- Hrestrict_m.
        apply (map_eq (M := gmap atom)). intros z.
        rewrite !store_restrict_lookup.
        destruct (decide (z ∈ world_dom (m : World) ∪ {[x]})) as [Hz|Hz].
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ change ((<[x:=vx]> σn : Store) !! x =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! x).
              rewrite !lookup_insert.
              rewrite !decide_True by reflexivity.
              reflexivity.
           ++ change ((<[x:=vx]> σn : Store) !! z =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite !lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_True by set_solver.
              reflexivity.
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ exfalso. apply Hz. set_solver.
           ++ change (None =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_False by set_solver.
              reflexivity.
    + intros Hσx.
      destruct Hσx as [σxn [Hσxn Hrestrict]].
      destruct Hσxn as [σn [vx [Hσn [Hsteps ->]]]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      assert (Hσm : (m : World) (store_restrict σn (world_dom (m : World)))).
      {
        pose proof (raw_le_dom (m : World) (n : World)
          ltac:(unfold sqsubseteq, wf_world_sqsubseteq, raw_le; exact Hle)) as Hdom_mn.
        rewrite Hle.
        exists σn. split; [exact Hσn |].
        simpl.
        replace (world_dom (n : World) ∩ world_dom (m : World))
          with (world_dom (m : World)) by set_solver.
        reflexivity.
      }
      exists (store_restrict σn (world_dom (m : World))), vx.
      split; [exact Hσm |].
      split.
      * assert (HstoreX :
          store_restrict (store_restrict σn (world_dom (m : World))) X =
          store_restrict σn X).
        {
          rewrite !store_restrict_restrict.
          replace (world_dom (m : World) ∩ X) with X by set_solver.
          reflexivity.
        }
        rewrite HstoreX. exact Hsteps.
      * rewrite <- Hrestrict.
        apply (map_eq (M := gmap atom)). intros z.
        rewrite !store_restrict_lookup.
        destruct (decide (z ∈ world_dom (m : World) ∪ {[x]})) as [Hz|Hz].
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ change ((<[x:=vx]> σn : Store) !! x =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! x).
              rewrite !lookup_insert.
              rewrite !decide_True by reflexivity.
              reflexivity.
           ++ change ((<[x:=vx]> σn : Store) !! z =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite !lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_True by set_solver.
              reflexivity.
        -- destruct (decide (z = x)) as [->|Hzx].
           ++ exfalso. apply Hz. set_solver.
           ++ change (None =
                (<[x:=vx]> (store_restrict σn (world_dom (m : World))) : Store) !! z).
              rewrite lookup_insert_ne by congruence.
              rewrite store_restrict_lookup.
              rewrite decide_False by set_solver.
              reflexivity.
Qed.

Lemma let_result_world_on_base_mono_from_total
    X e x (m n : WfWorld)
    (Hfresh_m : x ∉ world_dom (m : World))
    (Hfresh_n : x ∉ world_dom (n : World))
    Hresult_m :
  ∀ (HXm : X ⊆ world_dom (m : World)) (Hle : m ⊑ n),
  let Hresult_n :=
    expr_total_results_on_le X e m n HXm Hle Hresult_m in
  let_result_world_on X e x m Hfresh_m Hresult_m ⊑
    let_result_world_on X e x n Hfresh_n Hresult_n.
Proof.
  intros HXm Hle.
  apply let_result_world_on_base_mono; assumption.
Qed.

Lemma let_result_world_on_preserves_context Σ Γ X e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world_on X e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
Proof.
  intros Hctx.
  eapply res_models_kripke.
  - apply let_result_world_on_le.
  - exact Hctx.
Qed.

Lemma let_result_world_on_erased_basic
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  x ∉ dom (erase_ctx_under Σ Γ) →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult ⊨
    basic_world_formula
      (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))
      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))).
Proof.
  intros Hwf Hm Hx.
  eapply res_models_atom_intro.
  - unfold formula_scoped_in_world, basic_world_formula, basic_world_lqual.
    simpl.
    rewrite erase_ctx_under_comma_bind_dom.
    intros z Hz. simpl.
    apply elem_of_union in Hz as [Hz|Hz].
    + rewrite dom_empty_L in Hz. set_solver.
    + change (z ∈ dom (erase_ctx_under Σ Γ) ∪ {[x]}) in Hz.
      apply elem_of_union in Hz as [Hzold|Hzx].
      * apply elem_of_union. left.
        pose proof (res_models_with_store_fuel_scoped
          (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
          (denot_ctx_in_env Σ Γ) Hm) as Hscope.
        unfold formula_scoped_in_world in Hscope.
        apply Hscope.
        apply elem_of_union. right.
        apply denot_ctx_in_env_dom_subset_formula_fv.
        destruct Hwf as [Hwfτ _].
        rewrite <- (basic_ctx_erase_dom (dom Σ) Γ
          (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))).
        unfold erase_ctx_under in Hzold.
        rewrite dom_union_L in Hzold.
        exact Hzold.
      * apply elem_of_union. right. exact Hzx.
  - unfold logic_qualifier_denote, basic_world_lqual. simpl.
    rewrite erase_ctx_under_comma_bind_dom.
    split.
    + intros z Hz. simpl.
      apply elem_of_intersection. split; [| exact Hz].
      apply elem_of_union in Hz as [Hz|Hz].
      * apply elem_of_union. left.
        pose proof (res_models_with_store_fuel_scoped
          (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
          (denot_ctx_in_env Σ Γ) Hm) as Hscope.
        unfold formula_scoped_in_world in Hscope.
        apply Hscope.
        apply elem_of_union. right.
        apply denot_ctx_in_env_dom_subset_formula_fv.
        destruct Hwf as [Hwfτ _].
        rewrite <- (basic_ctx_erase_dom (dom Σ) Γ
          (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))).
        unfold erase_ctx_under in Hz.
        rewrite dom_union_L in Hz.
        exact Hz.
      * apply elem_of_union. right. exact Hz.
    + intros σx Hσx.
      simpl in Hσx.
      destruct Hσx as [σfull [Hσfull Hrestrict_full]].
      destruct (let_result_world_on_elim
        (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult σfull Hσfull)
        as [σ [vx [Hσ [Hsteps ->]]]].
      intros z T v Hz HΣext Hlookup.
      rewrite <- Hrestrict_full in Hlookup.
      apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
      destruct (decide (z = x)) as [->|Hzx].
      * change ((<[x := vx]> σ : Store) !! x = Some v) in Hlookup.
        assert (Hins : (<[x := vx]> σ : Store) !! x = Some vx)
          by apply lookup_insert_eq.
        rewrite Hins in Hlookup.
        inversion Hlookup. subst v.
        assert (HT : T = erase_ty τ).
        {
          assert (HΣx :
            erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) !! x = Some (erase_ty τ)).
          {
            unfold erase_ctx_under. simpl.
            rewrite lookup_union_r.
            - rewrite lookup_union_r.
              + rewrite lookup_singleton. rewrite decide_True by reflexivity. reflexivity.
              + apply not_elem_of_dom. set_solver.
            - apply not_elem_of_dom.
              intros HxΣ. apply Hx.
              unfold erase_ctx_under. rewrite dom_union_L.
              apply elem_of_union. left. exact HxΣ.
          }
          rewrite HΣx in HΣext. inversion HΣext. reflexivity.
        }
        subst T.
        eapply choice_typing_wf_result_typed_restrict_in_ctx; eauto.
      * change ((<[x := vx]> σ : Store) !! z = Some v) in Hlookup.
        rewrite lookup_insert_ne in Hlookup by congruence.
        assert (Hzold : z ∈ dom (erase_ctx_under Σ Γ)) by set_solver.
        pose proof (basic_world_formula_store_restrict_typed
          (erase_ctx_under Σ Γ) (dom (erase_ctx_under Σ Γ)) m σ
          (denot_ctx_in_env_erased_basic Σ Γ m Hm) Hσ) as Htyped_old.
        assert (HΣold : erase_ctx_under Σ Γ !! z = Some T).
        {
          unfold erase_ctx_under in *. simpl in HΣext.
          rewrite lookup_union_Some_raw in HΣext.
          apply lookup_union_Some_raw.
          destruct HΣext as [HΣz | [HΣnone Hz_right]].
          - left. exact HΣz.
          - right. split; [exact HΣnone |].
            rewrite lookup_union_Some_raw in Hz_right.
            destruct Hz_right as [HΓz | [HΓnone Hsingle]].
            + exact HΓz.
            + rewrite lookup_singleton in Hsingle.
              destruct (decide (z = x)) as [->|Hne].
              * contradiction.
              * rewrite decide_False in Hsingle by congruence.
                discriminate.
        }
        eapply Htyped_old.
        -- exact Hzold.
        -- exact HΣold.
        -- apply store_restrict_lookup_some_2; [exact Hlookup | exact Hzold].
Qed.

(** Result-binding compatibility for the let-result world.

    If [m] satisfies [τ] for the expression [e], then the world obtained by
    adding a fresh coordinate [x] containing exactly the possible results of
    [e] satisfies [τ] for [return x]. *)
Lemma denot_ty_on_let_result_representative
    X Σ τ e x (m : WfWorld) Hfresh Hresult :
  basic_choice_ty (dom Σ) τ →
  fv_tm e ⊆ X →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e →
  m ⊨ basic_world_formula Σ (dom Σ) →
  m ⊨ denot_ty_on X Σ τ e →
  let_result_world_on X e x m Hfresh Hresult ⊨
    denot_ty_on (X ∪ {[x]}) (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
Admitted.

Lemma let_result_world_on_bound_type
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult ⊨
    denot_ty_on
      (dom (erase_ctx_under Σ Γ) ∪ {[x]})
      (<[x := erase_ty τ]> (erase_ctx_under Σ Γ))
      τ (tret (vfvar x)).
Proof.
  intros Hwf Hm Hτ Hx.
  eapply (denot_ty_on_let_result_representative
    (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e x m Hfresh Hresult).
  - destruct Hwf as [Hwfτ _].
    pose proof (wf_choice_ty_under_basic Σ Γ τ Hwfτ) as Hbasicτ.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hbasicτ.
    + pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - pose proof (choice_typing_wf_fv_tm_subset Σ Γ e τ Hwf) as Hfv.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hfv.
    + destruct Hwf as [Hwfτ _].
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - exact Hx.
  - apply denot_ctx_in_env_erased_basic. exact Hm.
  - exact Hτ.
Qed.

Lemma let_result_world_on_denot_ctx_in_env
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e x m Hfresh Hresult ⊨
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ)).
Proof.
  intros Hwf Hm Hτ Hx.
  unfold denot_ctx_in_env.
  apply res_models_and_intro_from_models.
  - eapply res_models_kripke.
    + apply let_result_world_on_le.
    + eapply denot_ctx_in_env_basic; eauto.
  - apply res_models_and_intro_from_models.
    + eapply let_result_world_on_erased_basic; eauto. set_solver.
    + apply denot_ctx_under_comma. split.
      * apply denot_ctx_in_env_ctx.
        eapply let_result_world_on_preserves_context; exact Hm.
      * simpl.
        unfold erase_ctx_under.
        eapply let_result_world_on_bound_type; eauto.
Qed.

Lemma let_result_world_on_bound_fresh
    Σ Γ τ e x (m : WfWorld) :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m →
  x ∉ world_dom (m : World) →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e.
Proof.
  intros Hwf Hm Htotal Hfresh.
  destruct Htotal as [Hfv_e _].
  assert (Hfv_τ : fv_cty τ ⊆ dom (erase_ctx_under Σ Γ)).
  {
    destruct Hwf as [Hwfτ _].
    pose proof (wf_choice_ty_under_basic Σ Γ τ Hwfτ) as Hbasic.
    pose proof (basic_choice_ty_fv_subset (dom Σ ∪ ctx_dom Γ) τ Hbasic) as Hfv.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    - exact Hfv.
    - pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  }
  assert (Hdom_world : dom (erase_ctx_under Σ Γ) ⊆ world_dom (m : World)).
  {
    pose proof (res_models_with_store_fuel_scoped
      (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
      (denot_ctx_in_env Σ Γ) Hm) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    intros z Hz. apply Hscope.
    apply elem_of_union. right.
    apply denot_ctx_in_env_dom_subset_formula_fv.
    destruct Hwf as [Hwfτ _].
    replace (dom Σ ∪ ctx_dom Γ) with (dom (erase_ctx_under Σ Γ)).
    - exact Hz.
    - symmetry.
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  }
  apply not_elem_of_union. split.
  - apply not_elem_of_union. split.
    + intros Hbad. apply Hfresh. apply Hdom_world. exact Hbad.
    + intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_τ. exact Hbad.
  - intros Hbad. apply Hfresh. apply Hdom_world. apply Hfv_e. exact Hbad.
Qed.

Lemma let_result_world_on_le_store_elim
    X e x (n w : WfWorld) Hfresh Hresult σw :
  w ⊑ let_result_world_on X e x n Hfresh Hresult →
  X ∪ {[x]} ⊆ world_dom (w : World) →
  x ∉ X →
  (w : World) σw →
  ∃ σ vx,
    (n : World) σ ∧
    σw !! x = Some vx ∧
    store_restrict σw X = store_restrict σ X ∧
    subst_map (store_restrict σw X) e →* tret vx.
Proof.
  intros Hle Hscope HxX Hw.
  assert (Hw_raw := Hw).
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  rewrite Hle in Hw_raw. simpl in Hw_raw.
  destruct Hw_raw as [σwx [Hwx_store Hrestrict_w]].
  destruct (let_result_world_on_elim X e x n Hfresh Hresult
    _ Hwx_store) as [σ [vx [Hσ [Hsteps Hσwx_dom]]]].
  assert (Hstore_eq : store_restrict σw X = store_restrict σ X).
  {
    rewrite <- Hrestrict_w.
    rewrite !store_restrict_restrict.
    replace (world_dom (w : World) ∩ X) with X by set_solver.
    rewrite Hσwx_dom.
    change (store_restrict (<[x:=vx]> σ) X = store_restrict σ X).
    exact (store_restrict_insert_notin σ X x vx HxX).
  }
  exists σ, vx. repeat split; try exact Hσ.
  - assert (Hx_lookup_dom :
      σwx !! x =
      Some vx).
    {
      rewrite Hσwx_dom.
      rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
    }
    rewrite <- Hrestrict_w.
    apply store_restrict_lookup_some_2; [exact Hx_lookup_dom | set_solver].
  - exact Hstore_eq.
  - rewrite Hstore_eq. exact Hsteps.
Qed.

Lemma lc_env_restrict σ X :
  lc_env σ →
  lc_env (store_restrict σ X).
Proof.
  unfold lc_env. intros Hlc.
  apply map_Forall_lookup_2. intros y v Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact (map_Forall_lookup_1 _ _ _ _ Hlc Hlookup).
Qed.

Lemma store_restrict_insert_fresh_union_lookup_none
    (σ : Store) (X : aset) (x : atom) (v : value) :
  σ !! x = None →
  x ∉ X →
  (<[x := v]> (store_restrict σ X) : Store) !! x = Some v.
Proof.
  intros _ _. rewrite lookup_insert. rewrite decide_True by reflexivity.
  reflexivity.
Qed.

Lemma store_restrict_union_singleton_insert (σ : Store) (X : aset) (x : atom) (v : value) :
  dom σ ⊆ X →
  x ∉ X →
  store_restrict (σ ∪ {[x := v]}) (X ∪ {[x]}) = <[x := v]> σ.
Proof.
  intros Hdomσ HxX.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite decide_True by set_solver.
    transitivity (Some v).
    + rewrite (lookup_union_r σ ({[x := v]} : Store) x).
      * rewrite lookup_singleton. rewrite decide_True by reflexivity. reflexivity.
      * apply not_elem_of_dom. set_solver.
    + symmetry. change ((<[x := v]> σ : gmap atom value) !! x = Some v).
      apply lookup_insert_eq.
  - rewrite lookup_insert_ne by congruence.
    destruct (decide (z ∈ X)) as [HzX|HzX].
    + rewrite decide_True by set_solver.
      destruct (σ !! z) eqn:Hσz.
      * rewrite (lookup_union_l' σ ({[x := v]} : Store) z) by eauto.
        rewrite Hσz.
        reflexivity.
      * rewrite (lookup_union_r σ ({[x := v]} : Store) z) by exact Hσz.
        rewrite lookup_singleton. rewrite decide_False by congruence.
        reflexivity.
    + rewrite decide_False by set_solver.
      assert (Hzdom : z ∉ dom σ) by set_solver.
      apply not_elem_of_dom in Hzdom.
      rewrite Hzdom.
      reflexivity.
Qed.

Lemma store_restrict_union_from_parts
    (σ ρ σx : Store) (S : aset) (x : atom) :
  x ∉ S →
  store_restrict σ S = ρ →
  store_restrict σ {[x]} = σx →
  store_restrict σ (S ∪ {[x]}) = ρ ∪ σx.
Proof.
  intros HxS Hρ Hσx.
  apply (map_eq (M := gmap atom)). intros z.
  rewrite store_restrict_lookup.
  destruct (decide (z ∈ S)) as [HzS|HzS].
  - rewrite decide_True by set_solver.
    assert (Hρz : ρ !! z = σ !! z).
    {
      rewrite <- Hρ.
      rewrite store_restrict_lookup.
      rewrite decide_True by exact HzS.
      reflexivity.
    }
    assert (Hσx_none : σx !! z = None).
    {
      rewrite <- Hσx.
      rewrite store_restrict_lookup.
      rewrite decide_False by set_solver.
      reflexivity.
    }
    destruct (σ !! z) eqn:Hσz.
    + rewrite lookup_union_l'.
      * transitivity (Some v); [exact Hσz | symmetry; exact Hρz].
      * rewrite Hρz. eauto.
    + rewrite lookup_union_r.
      * transitivity (@None value); [exact Hσz | symmetry; exact Hσx_none].
      * exact Hρz.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite decide_True by set_solver.
      assert (Hρ_none : ρ !! x = None).
      {
        rewrite <- Hρ.
        rewrite store_restrict_lookup.
        rewrite decide_False by exact HxS.
        reflexivity.
      }
      rewrite lookup_union_r by exact Hρ_none.
      rewrite <- Hσx.
      rewrite store_restrict_lookup.
      rewrite decide_True by set_solver.
      reflexivity.
    + rewrite decide_False by set_solver.
      assert (Hρ_none : ρ !! z = None).
      {
        rewrite <- Hρ.
        rewrite store_restrict_lookup.
        rewrite decide_False by exact HzS.
        reflexivity.
      }
      assert (Hσx_none : σx !! z = None).
      {
        rewrite <- Hσx.
        rewrite store_restrict_lookup.
        rewrite decide_False by set_solver.
        reflexivity.
      }
      rewrite lookup_union_r by exact Hρ_none.
      symmetry. exact Hσx_none.
Qed.

Lemma difference_cons_decompose (X S : aset) (y : atom) :
  y ∈ X →
  y ∉ S →
  X ∖ S = (X ∖ ({[y]} ∪ S)) ∪ {[y]}.
Proof.
  intros HyX HyS.
  apply set_eq. intros z. split.
  - intros Hz.
    destruct (decide (z = y)) as [->|Hzy].
    + set_solver.
    + set_solver.
  - intros Hz. set_solver.
Qed.

Lemma fiber_projection_member_elim (w : WfWorld) X σ Hproj σw :
  (res_fiber_from_projection w X σ Hproj : World) σw →
  (w : World) σw ∧ store_restrict σw (dom σ) = σ.
Proof.
  unfold res_fiber_from_projection, res_fiber, raw_fiber.
  simpl. intros H. exact H.
Qed.

Lemma let_result_world_on_fiber_elim
    X e x (n : WfWorld) Hfresh Hresult ρ Hprojn Hprojlet σx :
  X ⊆ world_dom (n : World) →
  x ∉ X →
  (res_fiber_from_projection
    (let_result_world_on X e x n Hfresh Hresult) X ρ Hprojlet : World) σx →
  ∃ σ vx,
    (res_fiber_from_projection n X ρ Hprojn : World) σ ∧
    subst_map (store_restrict σ X) e →* tret vx ∧
    σx = <[x := vx]> σ.
Proof.
  intros _ HxX [Hσx Hσxρ].
  destruct (let_result_world_on_elim X e x n Hfresh Hresult σx Hσx)
    as [σ [vx [Hσ [Hsteps ->]]]].
  exists σ, vx. split.
  - simpl. split; [exact Hσ |].
    assert (Hdomρ : dom ρ ⊆ X).
    { destruct Hprojlet as [τ [_ Hτrestrict]].
      rewrite <- Hτrestrict. rewrite store_restrict_dom. set_solver. }
    assert (Hxdomρ : x ∉ dom ρ) by set_solver.
    assert (Hσρ : store_restrict σ (dom ρ) = ρ).
    {
      transitivity (store_restrict (<[x := vx]> σ) (dom ρ)).
      - symmetry. apply store_restrict_insert_notin. exact Hxdomρ.
      - exact Hσxρ.
    }
    exact Hσρ.
  - split; [exact Hsteps | reflexivity].
Qed.

Lemma let_result_world_on_fiber_intro
    X e x (n : WfWorld) Hfresh Hresult ρ Hprojn Hprojlet σ vx :
  X ⊆ world_dom (n : World) →
  x ∉ X →
  (res_fiber_from_projection n X ρ Hprojn : World) σ →
  subst_map (store_restrict σ X) e →* tret vx →
  (res_fiber_from_projection
    (let_result_world_on X e x n Hfresh Hresult) X ρ Hprojlet : World)
    (<[x := vx]> σ).
Proof.
  intros HXdom HxX Hσ Hsteps.
  destruct Hσ as [Hσn Hσρ].
  assert (Hdomρ : dom ρ = X).
  {
    destruct Hprojn as [σ0 [Hσ0 Hσ0ρ]].
    assert (Hρeq : ρ = store_restrict σ0 X) by (symmetry; exact Hσ0ρ).
    pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
    rewrite Hρeq.
    rewrite store_restrict_dom.
    set_solver.
  }
  apply res_fiber_from_projection_member.
  - apply let_result_world_on_member; [exact Hσn | exact Hsteps].
  - rewrite store_restrict_insert_notin by exact HxX.
    rewrite <- Hdomρ. exact Hσρ.
Qed.

Lemma expr_total_on_tlete_from_open
    (X : aset) e1 e2 x (m : WfWorld) Hfresh Hresult :
  x ∉ X →
  x ∉ fv_tm e2 →
  (∀ σ, (m : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (m : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (m : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on X e1 x m Hfresh Hresult) →
  fv_tm (tlete e1 e2) ⊆ X →
  expr_total_on X (tlete e1 e2) m.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hresult_closed Hbody Hbody_total Hfv.
  split; [exact Hfv |].
  intros σ Hσ.
  destruct (Hresult σ Hσ) as [vx Hsteps1].
  pose proof (let_result_world_on_member X e1 x m Hfresh Hresult
    σ vx Hσ Hsteps1) as Hσx.
  destruct Hbody_total as [_ Hbody_total].
  specialize (Hbody_total (<[x := vx]> σ) Hσx) as [v Hsteps2].
  exists v.
  change (subst_map (store_restrict σ X) (tlete e1 e2))
    with (m{store_restrict σ X} (tlete e1 e2)).
  rewrite (msubst_lete (store_restrict σ X) e1 e2).
  eapply reduction_lete_intro.
  - apply Hbody. exact Hσ.
  - exact Hsteps1.
  - rewrite store_restrict_insert_fresh_union in Hsteps2.
    2:{
      pose proof (wfworld_store_dom m σ Hσ) as Hdom.
      apply not_elem_of_dom. rewrite Hdom. exact Hfresh.
    }
    2:{ exact HxX. }
    change (m{<[x := vx]> (store_restrict σ X)} (open_tm 0 (vfvar x) e2)
      →* tret v) in Hsteps2.
    rewrite <- (msubst_intro_open_tm e2 0 vx x (store_restrict σ X)).
    + exact Hsteps2.
    + apply Hclosed. exact Hσ.
    + apply (proj1 (Hresult_closed σ vx Hσ Hsteps1)).
    + apply (proj2 (Hresult_closed σ vx Hσ Hsteps1)).
    + apply Hlc. exact Hσ.
    + change (x ∉ dom (store_restrict σ X) ∪ fv_tm e2).
      rewrite store_restrict_dom. set_solver.
Qed.

Lemma expr_result_value_tlete_from_body_projection
    X e1 e2 x σ vx v :
  x ∉ X →
  x ∉ fv_tm e2 →
  closed_env (store_restrict σ X) →
  lc_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  body_tm (subst_map (store_restrict σ X) e2) →
  subst_map (store_restrict σ X) e1 →* tret vx →
  subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x) →* tret v →
  subst_map (store_restrict σ X) (tlete e1 e2) →* tret v.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hvx_closed Hvx_lc Hbody He1 Hbody_steps.
  change (subst_map (store_restrict σ X) (tlete e1 e2))
    with (m{store_restrict σ X} (tlete e1 e2)).
  rewrite (msubst_lete (store_restrict σ X) e1 e2).
  eapply reduction_lete_intro; [exact Hbody | exact He1 |].
  rewrite <- (msubst_intro_open_tm e2 0 vx x (store_restrict σ X)).
  - exact Hbody_steps.
  - exact Hclosed.
  - exact Hvx_closed.
  - exact Hvx_lc.
  - exact Hlc.
  - change (x ∉ dom (store_restrict σ X) ∪ fv_tm e2).
    rewrite store_restrict_dom. set_solver.
Qed.

Lemma expr_result_value_tlete_from_body_store
    X e1 e2 x ν σ vx v :
  x ∉ X →
  x ∉ fv_tm e2 →
  closed_env (store_restrict σ X) →
  lc_env (store_restrict σ X) →
  stale vx = ∅ →
  is_lc vx →
  body_tm (subst_map (store_restrict σ X) e2) →
  subst_map (store_restrict σ X) e1 →* tret vx →
  expr_result_store ν (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x)) {[ν := v]} →
  expr_result_store ν (subst_map (store_restrict σ X) (tlete e1 e2)) {[ν := v]}.
Proof.
  intros HxX Hxe2 Hclosed Hlc Hvx_closed Hvx_lc Hbody He1 Hstore.
  destruct Hstore as [v' [Hσ [Hv_closed [Hv_lc Hbody_steps]]]].
  assert (Hv_eq : v' = v).
  {
    assert (Hlookup : ({[ν := v']} : Store) !! ν = Some v).
    {
      rewrite <- Hσ.
      rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
    }
    rewrite lookup_singleton in Hlookup.
    rewrite decide_True in Hlookup by reflexivity.
    inversion Hlookup. reflexivity.
  }
  subst v'.
  exists v. repeat split; try reflexivity; try exact Hv_closed; try exact Hv_lc.
  unfold expr_result_value.
  eapply (expr_result_value_tlete_from_body_projection X e1 e2 x σ vx v); eauto.
Qed.

Lemma expr_result_in_store_ret_fvar_to_source
    ρ e x ν σ vx σν :
  stale vx = ∅ →
  ν ≠ x →
  σ !! x = None →
  subst_map σ (subst_map ρ e) →* tret vx →
  expr_result_in_store ∅ (tret (vfvar x)) ν σν →
  store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) = σν →
  expr_result_in_store ρ e ν σ.
Proof.
  intros _ _ _ _ Hret _.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_in_store_ret_fvar_to_source_restrict
    e x ν σ vx σν :
  let S := stale e ∪ {[ν]} in
  stale vx = ∅ →
  ν ≠ x →
  x ∉ S →
  closed_env (store_restrict σ S) →
  σ !! x = None →
  subst_map σ e →* tret vx →
  expr_result_in_store ∅ (tret (vfvar x)) ν σν →
  store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) = σν →
  expr_result_in_store ∅ e ν (store_restrict σ S).
Proof.
  intros S Hvx Hνx HxS Hclosed Hxnone Hsteps_e Hret Hrestrict.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma closed_env_restrict_insert_result σ S ν vx :
  closed_env (store_restrict σ (S ∖ {[ν]})) →
  σ !! ν = Some vx →
  stale vx = ∅ →
  closed_env (store_restrict σ S).
Proof.
  intros Hclosed Hν Hvx.
  unfold closed_env in *.
  apply map_Forall_lookup_2. intros z v Hz.
  apply store_restrict_lookup_some in Hz as [HzS Hzσ].
  destruct (decide (z = ν)) as [->|Hzν].
  - rewrite Hν in Hzσ. inversion Hzσ. subst. exact Hvx.
  - apply (map_Forall_lookup_1 _ _ z v Hclosed).
    apply store_restrict_lookup_some_2; [exact Hzσ | set_solver].
Qed.

Lemma expr_result_in_world_ret_fvar_to_source_pullback
    e x ν (n p : WfWorld) Hle :
  ν ≠ x →
  x ∉ stale e ∪ {[ν]} →
  {[x]} ∪ {[ν]} ⊆ world_dom (p : World) →
  (∀ σx,
    (n : World) σx →
    ∃ σ vx,
      σx = <[x := vx]> σ ∧
      σ !! x = None ∧
      subst_map σ e →* tret vx) →
  (∀ σ vx,
    (n : World) (<[x := vx]> σ) →
    subst_map σ e →* tret vx →
    closed_env (store_restrict σ ((stale e ∪ {[ν]}) ∖ {[ν]}))) →
  (∀ σ vx,
    (n : World) (<[x := vx]> σ) →
    subst_map σ e →* tret vx →
    stale vx = ∅) →
  expr_result_in_world ∅ (tret (vfvar x)) ν
    (res_restrict p ({[x]} ∪ {[ν]})) →
  expr_result_in_world ∅ e ν
    (res_restrict (res_pullback_projection n p Hle) (stale e ∪ {[ν]})).
Proof.
  intros _ _ Hscope _ _ _ Hret_world.
  exfalso.
  destruct (world_wf p) as [[σp Hσp] _].
  set (σxν := store_restrict σp ({[x]} ∪ {[ν]})).
  assert (Hproj_xν : (res_restrict p ({[x]} ∪ {[ν]}) : World) σxν).
  { exists σp. split; [exact Hσp | reflexivity]. }
  set (σν := store_restrict σp {[ν]}).
  assert (Hproj_ν :
    (res_restrict (res_restrict p ({[x]} ∪ {[ν]})) {[ν]} : World) σν).
  {
    exists σxν. split; [exact Hproj_xν |].
    subst σxν σν.
    rewrite store_restrict_restrict.
    replace (({[x]} ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
    reflexivity.
  }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν
    (res_restrict p ({[x]} ∪ {[ν]})) σν Hret_world Hproj_ν) as Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

(** Semantic compatibility of bunched let.

    This is the remaining tlet-specific denotation theorem.  Its proof should
    combine:
    - [expr_result_in_world_let_intro]/[_elim] for operational composition;
    - [choice_typing_wf_result_closed_in_ctx] for closed intermediate values;
    - the body entailment under [CtxComma Γ (CtxBind x τ1)].

    Keeping this theorem separate prevents the fundamental theorem case from
    doing any recursion on [τ2]. *)
Lemma denot_tlet_semantic_at_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
Admitted.

(** The fold order chosen by [stdpp.set_fold] is intentionally abstract.  For
    the tlet proof we need to expose the semantic order [X] first and the bound
    result coordinate [x] second.  This is pure fiber bookkeeping: it follows
    from commutation of independent [FFib] modalities and [res_fiber_commute]. *)
Lemma fib_vars_obligation_insert_fresh_to_fib
    X x p ρ m :
  x ∉ X →
  fib_vars_obligation (X ∪ {[x]}) p ρ m →
  fib_vars_obligation X (FFib x p) ρ m.
Proof.
Admitted.

Lemma expr_result_store_from_body_xfiber
    X e2 x ν ρ (mlet : WfWorld) σ vx v :
  x ∉ X →
  store_restrict σ X = ρ →
  (mlet : World) (<[x := vx]> σ) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_store ν
    (subst_map (<[x := vx]> (store_restrict σ X)) (e2 ^^ x))
    {[ν := v]} →
  expr_result_store ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x))
    {[ν := v]}.
Proof.
  intros _ Hρ _ _ Hstore. rewrite <- Hρ. exact Hstore.
Qed.

Lemma expr_result_in_world_tlete_xfiber_sound
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) σν :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  (res_restrict m {[ν]} : World) σν →
  expr_result_in_store ρ (tlete e1 e2) ν σν.
Proof.
  intros Hx Hclosed Hlc Hresult_closed Hbody Hm Hmlet_elim Hmlet_intro Hbody_model Hν.
  destruct Hν as [σ [Hσm Hσν]].
  destruct (Hm σ Hσm) as [Hσn HσX].
  destruct (Hresult σ Hσn) as [vx He1].
  pose proof (Hmlet_intro σ vx Hσm He1) as Hσx_mlet.
  assert (Hprojx : res_restrict mlet {[x]} {[x := vx]}).
  {
    exists (<[x := vx]> σ). split; [exact Hσx_mlet |].
    apply store_restrict_insert_singleton.
  }
  unfold res_models_with_store in Hbody_model. simpl in Hbody_model.
  destruct Hbody_model as [_ [Hdisj Hfib]].
  specialize (Hfib {[x := vx]} Hprojx).
  assert (Hatom :
    res_models_with_store (ρ ∪ {[x := vx]})
      (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
      (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))).
  { unfold res_models_with_store. exact Hfib. }
  pose proof (FAtom_expr_logic_qual_on_exact
    (X ∪ {[x]}) (e2 ^^ x) ν (ρ ∪ {[x := vx]})
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    Hatom) as Hbody_exact.
  assert (Hσν_body :
    (res_restrict
      (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx) {[ν]} : World) σν).
  {
    exists (<[x := vx]> σ). split.
    - apply res_fiber_from_projection_member.
      + exact Hσx_mlet.
      + apply store_restrict_insert_singleton.
    - rewrite store_restrict_insert_notin by set_solver.
      exact Hσν.
  }
  pose proof (expr_result_in_world_sound
    (store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}))
    (e2 ^^ x) ν
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    σν Hbody_exact Hσν_body) as Hbody_store.
  assert (Hρx :
    store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}) =
    <[x := vx]> ρ).
  {
    apply store_restrict_union_singleton_insert.
    - rewrite <- HσX. rewrite store_restrict_dom. set_solver.
    - set_solver.
  }
  rewrite Hρx in Hbody_store.
  destruct (expr_result_store_elim ν
    (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν Hbody_store)
    as [v [Hσν_eq [Hv_stale [Hv_lc Hbody_steps]]]].
  subst σν.
  rewrite Hσν_eq.
  apply expr_result_store_intro; [exact Hv_stale | exact Hv_lc |].
  assert (HxX : x ∉ X) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  rewrite <- HσX.
  eapply expr_result_value_tlete_from_body_projection.
  - exact HxX.
  - exact Hxe2.
  - apply Hclosed. exact Hσn.
  - apply Hlc. exact Hσn.
  - apply (proj1 (Hresult_closed σ vx Hσn He1)).
  - apply (proj2 (Hresult_closed σ vx Hσn He1)).
  - apply Hbody. exact Hσn.
  - exact He1.
  - rewrite HσX. exact Hbody_steps.
Qed.

Lemma expr_result_in_world_tlete_xfiber_complete
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) σν :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_store ρ (tlete e1 e2) ν σν →
  (res_restrict m {[ν]} : World) σν.
Proof.
  intros Hx Hclosed Hlc Hresult_closed Hbody Hm Hmlet_elim Hmlet_intro Hbody_model Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
    as [v [Hσν_eq [Hv_stale [Hv_lc Hsteps]]]].
  subst σν.
  destruct (world_wf m) as [[σ Hσm] _].
  destruct (Hm σ Hσm) as [Hσn HσX].
  rewrite <- HσX in Hsteps.
  change (subst_map (store_restrict σ X) (tlete e1 e2)) with
    (m{store_restrict σ X} (tlete e1 e2)) in Hsteps.
  rewrite msubst_lete in Hsteps.
  destruct (reduction_lete (m{store_restrict σ X} e1)
    (m{store_restrict σ X} e2) v Hsteps) as [vx [He1 Hbody_steps_open]].
  pose proof (Hmlet_intro σ vx Hσm He1) as Hσx_mlet.
  assert (Hprojx : res_restrict mlet {[x]} {[x := vx]}).
  {
    exists (<[x := vx]> σ). split; [exact Hσx_mlet |].
    apply store_restrict_insert_singleton.
  }
  unfold res_models_with_store in Hbody_model. simpl in Hbody_model.
  destruct Hbody_model as [_ [Hdisj Hfib]].
  specialize (Hfib {[x := vx]} Hprojx).
  assert (Hatom :
    res_models_with_store (ρ ∪ {[x := vx]})
      (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
      (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))).
  { unfold res_models_with_store. exact Hfib. }
  pose proof (FAtom_expr_logic_qual_on_exact
    (X ∪ {[x]}) (e2 ^^ x) ν (ρ ∪ {[x := vx]})
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    Hatom) as Hbody_exact.
  assert (HxX : x ∉ X) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  assert (Hρx :
    store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}) =
    <[x := vx]> ρ).
  {
    apply store_restrict_union_singleton_insert.
    - rewrite <- HσX. rewrite store_restrict_dom. set_solver.
    - exact HxX.
  }
  assert (Hbody_steps :
    subst_map (<[x := vx]> ρ) (e2 ^^ x) →* tret v).
  {
    pose proof Hbody_steps_open as Htmp.
    rewrite <- (msubst_intro_open_tm e2 0 vx x (store_restrict σ X)) in Htmp.
    - rewrite HσX in Htmp. exact Htmp.
    - apply Hclosed. exact Hσn.
    - apply (proj1 (Hresult_closed σ vx Hσn He1)).
    - apply (proj2 (Hresult_closed σ vx Hσn He1)).
    - apply Hlc. exact Hσn.
    - change (x ∉ dom (store_restrict σ X) ∪ fv_tm e2).
      rewrite store_restrict_dom. set_solver.
  }
  assert (Hbody_store :
    expr_result_in_store
      (store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}))
      (e2 ^^ x) ν {[ν := v]}).
  {
    rewrite Hρx.
    apply expr_result_store_intro; [exact Hv_stale | exact Hv_lc | exact Hbody_steps].
  }
  pose proof (expr_result_in_world_complete
    (store_restrict (ρ ∪ {[x := vx]}) (X ∪ {[x]}))
    (e2 ^^ x) ν
    (res_fiber_from_projection mlet {[x]} {[x := vx]} Hprojx)
    {[ν := v]} Hbody_exact Hbody_store) as Hν_body.
  destruct Hν_body as [σx [[Hσx_mlet' Hσx_proj] Hσxν]].
  destruct (Hmlet_elim σx Hσx_mlet') as [σ' [vx' [Hσ'm [He1' Hσx_eq]]]].
  subst σx.
  exists σ'. split; [exact Hσ'm |].
  rewrite <- Hσxν.
  rewrite store_restrict_insert_notin by set_solver.
  reflexivity.
Qed.

(** One-projection semantic core of tlet.

    After the outer [X]-fibers have fixed the input store [ρ], the body-side
    obligation still contains one more fiber for [x].  That [x]-fiber ranges
    over exactly the stores produced by [let_result_world_on]: each admissible
    input store is paired with an actual result [vx] of [e1].  Exactness of the
    inner result projection for [e2 ^^ x], together with the operational let
    bridge [expr_result_value_tlete_from_body_store], yields exactness of the
    [ν]-projection for [tlete e1 e2].

    The remaining proof work here is algebraic alignment of the fibered
    [let_result_world_on] with the fibered base world. *)
Lemma expr_result_in_world_tlete_from_body_xfiber
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    (ρ : Store) (m mlet : WfWorld) :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (* [m] is the current [X]-fiber of [n], and [ρ] is its fixed projection. *)
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (* [mlet] is the matching [X]-fiber of [let_result_world_on X e1 x n]. *)
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_world ρ (tlete e1 e2) ν m.
Proof.
  intros Hx _ Hclosed Hlc Hresult_closed Hbody Hm Hmlet_elim Hmlet_intro Hbody_model.
  intros σν. split.
  - eapply expr_result_in_world_tlete_xfiber_sound; eauto.
  - eapply expr_result_in_world_tlete_xfiber_complete; eauto.
Qed.

Lemma expr_result_in_world_tlete_from_body_projection_fiber
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    ρ Hprojn Hprojlet :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  res_models_with_store ρ
    (res_fiber_from_projection
      (let_result_world_on X e1 x n Hfresh Hresult) X ρ Hprojlet)
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  expr_result_in_world ρ (tlete e1 e2) ν
    (res_fiber_from_projection n X ρ Hprojn).
Proof.
  intros HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_model.
  eapply expr_result_in_world_tlete_from_body_xfiber; eauto.
  - intros σ Hσ.
    destruct Hσ as [Hσn Hσρ]. split; [exact Hσn |].
    assert (Hdomρ : dom ρ = X).
    {
      destruct Hprojn as [σ0 [Hσ0 Hσ0ρ]].
      assert (Hρeq : ρ = store_restrict σ0 X) by (symmetry; exact Hσ0ρ).
      pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
      rewrite Hρeq, store_restrict_dom. set_solver.
    }
    rewrite <- Hdomρ. exact Hσρ.
  - intros σx Hσx.
    eapply let_result_world_on_fiber_elim; eauto; set_solver.
  - intros σ vx Hσ Hsteps.
    eapply let_result_world_on_fiber_intro; eauto; set_solver.
Qed.

Lemma fib_vars_obligation_tlete_from_body_foldr_base
    X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx)
    ρ (m mlet : WfWorld) :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  world_dom (m : World) = world_dom (n : World) →
  world_dom (mlet : World) = world_dom (n : World) ∪ {[x]} →
  (∀ σ, (m : World) σ → (n : World) σ ∧ store_restrict σ X = ρ) →
  (∀ σx, (mlet : World) σx →
    ∃ σ vx,
      (m : World) σ ∧
      subst_map (store_restrict σ X) e1 →* tret vx ∧
      σx = <[x := vx]> σ) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    (mlet : World) (<[x := vx]> σ)) →
  res_models_with_store ρ mlet
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) →
  res_models_with_store ρ m
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)).
Proof.
  intros Hx Hfv Hclosed Hlc Hres_closed Hbody Hdomm Hdommlet
    Hm Hmlet_elim Hmlet_intro Hbody_model.
  assert (Hexact : expr_result_in_world ρ (tlete e1 e2) ν m).
  {
    eapply (expr_result_in_world_tlete_from_body_xfiber
      X e1 e2 x ν n Hfresh Hresult ρ m mlet).
    - exact Hx.
    - exact Hfv.
    - exact Hclosed.
    - exact Hlc.
    - exact Hres_closed.
    - exact Hbody.
    - exact Hm.
    - exact Hmlet_elim.
    - exact Hmlet_intro.
    - exact Hbody_model.
  }
  assert (Hscope_body :
    formula_scoped_in_world ρ mlet
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))).
  { apply (res_models_with_store_fuel_scoped _ _ _ _ Hbody_model). }
  assert (Hscope :
    formula_scoped_in_world ρ m
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))).
  {
    assert (HdomρX : dom ρ ⊆ X).
    {
      destruct (world_wf m) as [[σ Hσm] _].
      destruct (Hm σ Hσm) as [_ Hσρ].
      rewrite <- Hσρ, store_restrict_dom. set_solver.
    }
    unfold formula_scoped_in_world in *.
    simpl in *. unfold stale, stale_logic_qualifier in *. simpl in *.
    intros z Hz.
    rewrite Hdomm.
    assert (Hz_body :
      z ∈ dom ρ ∪ ({[x]} ∪ (X ∪ {[x]} ∪ {[ν]}))).
    { set_solver. }
    pose proof (Hscope_body z Hz_body) as Hz_mlet.
    rewrite Hdommlet in Hz_mlet.
    assert (z ≠ x) by set_solver.
    set_solver.
  }
  eapply FAtom_expr_logic_qual_on_intro.
  - exact Hscope.
  - replace (store_restrict ρ X) with ρ.
    + exact Hexact.
    + symmetry. apply store_restrict_idemp.
      destruct (world_wf m) as [[σ Hσm] _].
      destruct (Hm σ Hσm) as [_ Hσρ].
      rewrite <- Hσρ, store_restrict_dom. set_solver.
Qed.

Lemma fib_vars_obligation_tlete_from_body_foldr
    xs X e1 e2 x ν (n : WfWorld)
    (Hfresh : x ∉ world_dom (n : World))
    (Hresult : ∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) :
  NoDup xs →
  (list_to_set xs : aset) ⊆ X →
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  ∀ ρ (m mlet : WfWorld),
    world_dom (m : World) = world_dom (n : World) →
    world_dom (mlet : World) = world_dom (n : World) ∪ {[x]} →
    (∀ σ, (m : World) σ →
      (n : World) σ ∧
      store_restrict σ (X ∖ (list_to_set xs : aset)) = ρ) →
    (∀ σx, (mlet : World) σx →
      ∃ σ vx,
        (m : World) σ ∧
        subst_map (store_restrict σ X) e1 →* tret vx ∧
        σx = <[x := vx]> σ) →
    (∀ σ vx,
      (m : World) σ →
      subst_map (store_restrict σ X) e1 →* tret vx →
      (mlet : World) (<[x := vx]> σ)) →
    snd (foldr fib_vars_acc_step
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)),
       fun ρ m => res_models_with_store ρ m
         (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))) xs)
      ρ mlet →
    snd (foldr fib_vars_acc_step
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν),
       fun ρ m => res_models_with_store ρ m
         (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))) xs)
      ρ m.
Proof.
  induction xs as [|y xs IH]; simpl; intros Hnodup Hsub HXdom Hx Hfv Hclosed Hlc Hres_closed Hbody
    ρ m mlet Hdomm Hdommlet Hm Hmlet_elim Hmlet_intro Hbody_obl.
  - eapply (fib_vars_obligation_tlete_from_body_foldr_base
      X e1 e2 x ν n Hfresh Hresult ρ m mlet).
    + exact Hx.
    + exact Hfv.
    + exact Hclosed.
    + exact Hlc.
    + exact Hres_closed.
    + exact Hbody.
    + exact Hdomm.
    + exact Hdommlet.
    + intros σ Hσ. destruct (Hm σ Hσ) as [Hσn Hσρ].
      split; [exact Hσn |]. rewrite difference_empty_L in Hσρ. exact Hσρ.
    + exact Hmlet_elim.
    + exact Hmlet_intro.
    + exact Hbody_obl.
  - inversion Hnodup as [|? ? Hy_notin Hnodup']; subst.
    destruct (foldr fib_vars_acc_step
      (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)),
       fun ρ m => res_models_with_store ρ m
         (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))) xs)
      as [p_body R_body] eqn:Hbody_tail.
    destruct (foldr fib_vars_acc_step
      (FAtom (expr_logic_qual_on X (tlete e1 e2) ν),
       fun ρ m => res_models_with_store ρ m
         (FAtom (expr_logic_qual_on X (tlete e1 e2) ν))) xs)
      as [p_let R_let] eqn:Hlet_tail.
    simpl in Hbody_obl |- *.
    unfold fib_vars_obligation_step in Hbody_obl.
    destruct Hbody_obl as [Hdisj Hfib]. split; [exact Hdisj |].
    intros σy Hprojy_m.
    assert (HyX : y ∈ X).
    { apply Hsub. set_solver. }
    assert (Hyx : y ≠ x) by set_solver.
    assert (Hdomσy : dom σy = {[y]}).
    {
      destruct Hprojy_m as [σ0 [Hσ0 Hσ0y]].
      assert (Hσyeq : σy = store_restrict σ0 {[y]}) by (symmetry; exact Hσ0y).
      pose proof (wfworld_store_dom m σ0 Hσ0) as Hdomσ0.
      rewrite Hσyeq, store_restrict_dom.
      set_solver.
    }
    assert (Hprojy_mlet : res_restrict mlet {[y]} σy).
    {
      destruct Hprojy_m as [σ0 [Hσ0 Hσ0y]].
      destruct (Hm σ0 Hσ0) as [Hσ0n _].
      destruct (Hresult σ0 Hσ0n) as [vx Hsteps].
      exists (<[x := vx]> σ0). split.
      - apply Hmlet_intro; [exact Hσ0 | exact Hsteps].
      - rewrite store_restrict_insert_notin by set_solver.
        exact Hσ0y.
    }
    specialize (Hfib σy Hprojy_mlet).
    eapply (IH Hnodup'
      ltac:(intros z Hz; apply Hsub; set_solver)
      HXdom Hx Hfv Hclosed Hlc Hres_closed Hbody
      (ρ ∪ σy)
      (res_fiber_from_projection m {[y]} σy Hprojy_m)
      (res_fiber_from_projection mlet {[y]} σy Hprojy_mlet)).
    + simpl. rewrite Hdomm. reflexivity.
    + simpl. rewrite Hdommlet. reflexivity.
    + intros σ Hσ.
      destruct Hσ as [Hσm Hσy].
      destruct (Hm σ Hσm) as [Hσn Hσρ].
      split; [exact Hσn |].
      replace (X ∖ (list_to_set xs : aset)) with
        ((X ∖ ({[y]} ∪ (list_to_set xs : aset))) ∪ {[y]}).
      rewrite (store_restrict_union_from_parts σ ρ σy
        (X ∖ ({[y]} ∪ (list_to_set xs : aset))) y).
      * reflexivity.
      * timeout 3 set_solver.
      * exact Hσρ.
      * rewrite <- Hdomσy. exact Hσy.
      * symmetry. apply difference_cons_decompose.
        -- exact HyX.
        -- rewrite elem_of_list_to_set. exact Hy_notin.
    + intros σx Hσx.
      destruct (fiber_projection_member_elim _ _ _ _ _ Hσx)
        as [Hσx_mlet Hσx_y].
      destruct (Hmlet_elim σx Hσx_mlet) as [σ [vx [Hσm [Hsteps ->]]]].
      exists σ, vx. split.
      * apply res_fiber_from_projection_member; [exact Hσm |].
        rewrite <- Hσx_y.
        rewrite Hdomσy.
        rewrite store_restrict_insert_notin by (timeout 3 set_solver).
        reflexivity.
      * split; [exact Hsteps | reflexivity].
    + intros σ vx Hσ Hsteps.
      destruct (fiber_projection_member_elim _ _ _ _ _ Hσ)
        as [Hσm Hσy].
      apply res_fiber_from_projection_member.
      * apply Hmlet_intro; [exact Hσm | exact Hsteps].
      * transitivity (store_restrict (<[x := vx]> σ) (dom σy)).
        -- rewrite Hdomσy. reflexivity.
        -- rewrite store_restrict_insert_notin.
           ++ exact Hσy.
           ++ rewrite Hdomσy. timeout 3 set_solver.
    + exact Hfib.
Qed.

(** Lifting the one-projection semantic core through the outer [X] fibers.
    This is the induction over [fib_vars_obligation X].  Its non-mechanical
    leaf is [expr_result_in_world_tlete_from_body_xfiber]; the rest is threading
    the invariant that the current fiber of [n] consists exactly of stores with
    the accumulated projection [ρ]. *)
Lemma fib_vars_obligation_tlete_from_body_normalized
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  fib_vars_obligation X
    (FFib x (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν))) ∅
    (let_result_world_on X e1 x n Hfresh Hresult) →
  fib_vars_obligation X
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)) ∅ n.
Proof.
  intros HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_obl.
  unfold fib_vars_obligation, fib_vars_acc, set_fold in *.
  assert (Hxs : (list_to_set (elements X) : aset) ⊆ X).
  {
    intros z Hz.
    rewrite elem_of_list_to_set, elem_of_elements in Hz.
    exact Hz.
  }
  pose proof (fib_vars_obligation_tlete_from_body_foldr
    (elements X) X e1 e2 x ν n Hfresh Hresult) as Hfold.
  eapply (Hfold
    (NoDup_elements X)
    Hxs
    HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody
    (∅ : Store) n (let_result_world_on X e1 x n Hfresh Hresult)).
  - reflexivity.
  - unfold let_result_world_on, let_result_raw_world_on. simpl. reflexivity.
  - intros σ Hσ. split; [exact Hσ |].
    replace (X ∖ list_to_set (elements X) : aset) with (∅ : aset).
    + apply store_restrict_empty_set.
    + apply set_eq. intros z. rewrite elem_of_difference.
      rewrite elem_of_list_to_set, elem_of_elements. set_solver.
  - intros σx Hσx.
    destruct (let_result_world_on_elim X e1 x n Hfresh Hresult σx Hσx)
      as [σ [vx [Hσ [Hsteps ->]]]].
    exists σ, vx. repeat split; eauto.
  - intros σ vx Hσ Hsteps.
    apply let_result_world_on_member; [exact Hσ | exact Hsteps].
  - exact Hbody_obl.
Qed.

Lemma fib_vars_obligation_tlete_from_body_result_world
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (n : World) →
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  fib_vars_obligation (X ∪ {[x]})
    (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)) ∅
    (let_result_world_on X e1 x n Hfresh Hresult) →
  fib_vars_obligation X
    (FAtom (expr_logic_qual_on X (tlete e1 e2) ν)) ∅ n.
Proof.
  intros HXdom Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_obl.
  eapply fib_vars_obligation_tlete_from_body_normalized; eauto.
  eapply fib_vars_obligation_insert_fresh_to_fib; [set_solver | exact Hbody_obl].
Qed.

Lemma FExprResultOn_tlete_from_body_result_world
    X e1 e2 x ν (n : WfWorld) Hfresh Hresult :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  (∀ σ, (n : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (n : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (n : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  let_result_world_on X e1 x n Hfresh Hresult ⊨
    FExprResultOn (X ∪ {[x]}) (e2 ^^ x) ν →
  n ⊨ FExprResultOn X (tlete e1 e2) ν.
Proof.
  intros Hx Hfv Hclosed Hlc Hresult_closed Hbody Hbody_model.
  unfold FExprResultOn, FExprResultOnRaw, res_models in *.
  pose proof (res_models_with_store_fuel_scoped _ _ _ _
    Hbody_model) as Hscope_body.
  assert (HXdom : X ⊆ world_dom (n : World)).
  {
    intros z Hz.
    assert (Hz_body :
      z ∈ dom (∅ : Store) ∪ formula_fv
        (fib_vars (X ∪ {[x]})
          (FAtom (expr_logic_qual_on (X ∪ {[x]}) (e2 ^^ x) ν)))).
    {
      apply elem_of_union. right.
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      set_solver.
    }
    pose proof (Hscope_body z Hz_body) as Hz_dom.
    unfold let_result_world_on, let_result_raw_world_on in Hz_dom.
    simpl in Hz_dom.
    apply elem_of_union in Hz_dom as [Hz_dom | Hzx].
    - exact Hz_dom.
    - assert (z = x) by set_solver.
      subst z. set_solver.
  }
  apply fib_vars_models_intro.
  - apply FExprResultOn_scoped_intro.
    intros z Hz.
    assert (Hz' : z ∈ X ∪ {[ν]}) by set_solver.
    unfold formula_scoped_in_world in Hscope_body.
    assert (Hz_body :
      z ∈ dom (∅ : Store) ∪ formula_fv
        (FExprResultOn (X ∪ {[x]}) (e2 ^^ x) ν)).
    {
      apply elem_of_union. right.
      unfold FExprResultOn, FExprResultOnRaw.
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      set_solver.
    }
    pose proof (Hscope_body z Hz_body) as Hz_dom.
    unfold let_result_world_on, let_result_raw_world_on in Hz_dom.
    simpl in Hz_dom.
    apply elem_of_union in Hz_dom as [Hz_dom | Hzx].
    + exact Hz_dom.
    + assert (z = x) by set_solver.
      subst z. set_solver.
  - eapply fib_vars_obligation_tlete_from_body_result_world; eauto.
    unfold FExprResultOn, FExprResultOnRaw, res_models in Hbody_model.
    exact (fib_vars_models_elim _ _ _ _ Hbody_model).
Qed.

(** Fixed-world body-to-let lifting is not strong enough for the main tlet
    proof because [denot_ty_on] contains Kripke implications.  The theorem
    below is the total-aware, Kripke-parametric bridge used by the fundamental
    theorem; this older shape is kept only as a local target while the
    structural denotation transport is being factored. *)
Lemma denot_ty_on_let_result_body_to_let
    X Σ τ e1 e2 Tx (L : aset) (m : WfWorld) :
  basic_choice_ty (dom Σ) τ →
  fv_tm (tlete e1 e2) ⊆ X →
  X ⊆ world_dom (m : World) →
  (∀ σ, (m : World) σ → ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
  m ⊨ basic_world_formula Σ (dom Σ) →
  (∀ x,
    x ∉ L →
    x ∉ world_dom (m : World) →
    x ∉ X ∪ fv_cty τ ∪ fv_tm e2 →
    ∀ Hfresh Hresult,
      let_result_world_on X e1 x m Hfresh Hresult ⊨
        denot_ty_on (X ∪ {[x]}) (<[x := Tx]> Σ) τ (e2 ^^ x)) →
  m ⊨ denot_ty_on X Σ τ (tlete e1 e2).
Proof.
Admitted.

Lemma denot_tlet_formula_at_world_given_bind_total
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1 →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e1 m →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  (∀ x (HxL : x ∉ L)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx),
    let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
      denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))) →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hm Hτ1 Htotal1 IH2 Hbind.
  destruct Htotal1 as [Hfv1 Hresult].
  set (X := dom (erase_ctx_under Σ Γ)).
  set (x := fresh_for (L ∪ world_dom (m : World) ∪ X ∪ fv_cty τ2 ∪ fv_tm e2)).
  assert (Hxfresh_all :
    x ∉ L ∪ world_dom (m : World) ∪ X ∪ fv_cty τ2 ∪ fv_tm e2)
    by (subst x; apply fresh_for_not_in).
  assert (HxL : x ∉ L) by set_solver.
  assert (Hfresh : x ∉ world_dom (m : World)) by set_solver.
  assert (Hx : x ∉ X ∪ fv_cty τ2 ∪ fv_tm e2) by set_solver.
  unfold denot_ty_in_ctx_under.
  subst X.
  eapply denot_ty_on_let_result_body_to_let with
    (Tx := erase_ty τ1) (L := L ∪ world_dom (m : World) ∪ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2).
  - pose proof Hwflet as Hwflet_basic.
    destruct Hwflet_basic as [Hwfτ _].
    pose proof (wf_choice_ty_under_basic Σ Γ τ2 Hwfτ) as Hbasicτ.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hbasicτ.
    + pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ2 Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - pose proof (choice_typing_wf_fv_tm_subset Σ Γ (tlete e1 e2) τ2 Hwflet)
      as Hfv.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hfv.
    + pose proof Hwflet as Hwflet_ctx.
      destruct Hwflet_ctx as [Hwfτ _].
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ2 Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - apply (basic_world_formula_dom_subset (erase_ctx_under Σ Γ)
      (dom (erase_ctx_under Σ Γ))).
    apply denot_ctx_in_env_erased_basic. exact Hm.
  - exact Hresult.
  - apply denot_ctx_in_env_erased_basic. exact Hm.
  - intros y HyL Hyfresh Hy.
    intros Hfresh_y Hresult_y.
    set (wy := let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 y m Hfresh_y Hresult_y).
    assert (HyL0 : y ∉ L) by set_solver.
    assert (Hctxy : wy ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τ1))).
    { subst wy. apply Hbind; exact HyL0. }
	    destruct (IH2 y HyL0 wy Hctxy) as [Hbody _].
	    assert (Hdom_ctxx :
	      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind y τ1))) : aset) =
	      dom (erase_ctx_under Σ Γ) ∪ {[y]}).
    {
      unfold erase_ctx_under. simpl.
      rewrite !dom_union_L, dom_singleton_L. set_solver.
    }
	    assert (Henv_ctxx :
	      erase_ctx_under Σ (CtxComma Γ (CtxBind y τ1)) =
	      <[y := erase_ty τ1]> (erase_ctx_under Σ Γ)).
    {
      unfold erase_ctx_under. simpl.
      apply (map_eq (M := gmap atom)). intros z.
      rewrite lookup_insert.
	      destruct (decide (z = y)) as [->|Hzx].
      - rewrite decide_True by reflexivity.
        rewrite lookup_union_r.
        + rewrite lookup_union_r.
          * rewrite lookup_singleton. rewrite decide_True by reflexivity.
            reflexivity.
          * apply not_elem_of_dom. set_solver.
        + apply not_elem_of_dom. set_solver.
      - rewrite decide_False by congruence.
        rewrite !lookup_union.
        rewrite lookup_singleton.
        rewrite decide_False by congruence.
        destruct (Σ !! z); destruct (erase_ctx Γ !! z); reflexivity.
    }
    unfold denot_ty_in_ctx_under in Hbody.
    rewrite Hdom_ctxx, Henv_ctxx in Hbody.
    exact Hbody.
Qed.

Lemma denot_tlet_formula_at_world_total
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet IH1 IH2 Hm.
  destruct (IH1 m Hm) as [Hτ1 Htotal1].
  eapply denot_tlet_formula_at_world_given_bind_total; eauto.
  intros x HxL Hfresh Hresult.
  eapply let_result_world_on_denot_ctx_in_env; eauto.
  eapply let_result_world_on_bound_fresh; eauto.
Qed.

Lemma denot_tlet_expr_total_at_world_given_bind
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e1 m →
  (∀ x (HxL : x ∉ L)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx),
    expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
      (e2 ^^ x)
      (let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult)) →
  (∀ σ, (m : World) σ →
    closed_env (store_restrict σ (dom (erase_ctx_under Σ Γ)))) →
  (∀ σ, (m : World) σ →
    lc_env (store_restrict σ (dom (erase_ctx_under Σ Γ)))) →
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m.
Proof.
  intros Hwf1 Hwflet Hm Htotal1 Hbody_total Hclosed Hlc.
  destruct Htotal1 as [Hfv1 Hresult].
  set (X := dom (erase_ctx_under Σ Γ)).
  set (x := fresh_for (L ∪ world_dom (m : World) ∪ X ∪ fv_tm e2)).
  assert (Hxfresh_all : x ∉ L ∪ world_dom (m : World) ∪ X ∪ fv_tm e2)
    by (subst x; apply fresh_for_not_in).
  assert (HxL : x ∉ L) by set_solver.
  assert (Hfresh : x ∉ world_dom (m : World)) by set_solver.
  assert (HxX : x ∉ X) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  pose proof (Hbody_total x HxL Hfresh Hresult) as Hbody.
  eapply expr_total_on_tlete_from_open with
    (Hfresh := Hfresh) (Hresult := Hresult).
  - exact HxX.
  - exact Hxe2.
  - exact Hclosed.
  - exact Hlc.
  - intros σ vx Hσ Hsteps.
    subst X.
    eapply (choice_typing_wf_result_regular_restrict_in_ctx
      Σ Γ e1 τ1 m σ vx); eauto.
  - intros σ Hσ.
    apply body_tm_msubst.
    + apply Hclosed. exact Hσ.
    + apply Hlc. exact Hσ.
    + eapply choice_typing_wf_let_body_helper; eauto.
  - subst X.
    replace (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
      with (dom (erase_ctx_under Σ Γ) ∪ {[x]}) in Hbody.
    + exact Hbody.
    + unfold erase_ctx_under. simpl.
      rewrite !dom_union_L, dom_singleton_L. set_solver.
  - pose proof (choice_typing_wf_fv_tm_subset Σ Γ (tlete e1 e2) τ2 Hwflet).
    subst X.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact H.
    + destruct Hwflet as [Hwfτ _].
      unfold erase_ctx_under.
      rewrite dom_union_L.
      rewrite (basic_ctx_erase_dom (dom Σ) Γ
        (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ2 Hwfτ))).
      reflexivity.
Qed.

Lemma denot_tlet_total_at_world_given_bind
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  (∀ x (HxL : x ∉ L)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx),
    let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
      denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))) →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros Hwf1 Hwflet IH1 IH2 Hbind Hm.
  destruct (IH1 m Hm) as [Hτ1 Htotal1].
  split.
  - eapply denot_tlet_formula_at_world_total; eauto.
  - eapply denot_tlet_expr_total_at_world_given_bind; eauto.
    + intros x HxL Hfresh Hresult.
      set (wx := let_result_world_on
        (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult).
      assert (Hctxx : wx ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))).
      { subst wx. apply Hbind; exact HxL. }
      exact (proj2 (IH2 x HxL wx Hctxx)).
    + intros σ Hσ.
      eapply basic_world_formula_store_restrict_closed_env.
      * apply denot_ctx_in_env_erased_basic. exact Hm.
      * set_solver.
      * exact Hσ.
    + intros σ Hσ.
      eapply basic_world_formula_store_restrict_lc_env.
      * apply denot_ctx_in_env_erased_basic. exact Hm.
      * set_solver.
      * exact Hσ.
Qed.

Lemma denot_tlet_total_at_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros Hwf1 Hwflet IH1 IH2 Hm.
  eapply denot_tlet_total_at_world_given_bind; eauto.
  intros x HxL Hfresh Hresult.
  eapply let_result_world_on_denot_ctx_in_env; eauto.
  - exact (proj1 (IH1 m Hm)).
  - eapply let_result_world_on_bound_fresh; eauto.
    exact (proj2 (IH1 m Hm)).
Qed.

Lemma denot_tlet_semantic
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwf IH1 IH2 m Hm.
  eapply denot_tlet_semantic_at_world; eauto.
Qed.

Lemma denot_ctx_comma_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_under Σ Γ1 ∧
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof. apply denot_ctx_under_comma. Qed.

Lemma denot_ctx_star_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof. apply denot_ctx_under_star. Qed.

Lemma denot_ctx_sum_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof. apply denot_ctx_under_sum. Qed.

Lemma ctx_res_models_mono (Γ : ctx) (m m' : WfWorld) :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.
