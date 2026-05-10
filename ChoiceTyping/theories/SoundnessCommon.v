(** * ChoiceTyping.SoundnessHelpers

    Stable formula/context helper lemmas used by the soundness proof.  Keeping
    them outside [Soundness.v] leaves the fundamental-theorem file focused on
    the proof cases themselves. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma res_models_impl_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FImpl φ ψ →
  m ⊑ m' →
  m' ⊨ FImpl φ ψ.
Proof. hauto using res_models_kripke. Qed.

Lemma res_models_and_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FAnd φ ψ →
  m ⊑ m' →
  m' ⊨ FAnd φ ψ.
Proof. hauto using res_models_kripke. Qed.

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
