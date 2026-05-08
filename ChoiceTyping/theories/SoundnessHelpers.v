(** * ChoiceTyping.SoundnessHelpers

    Stable formula/context helper lemmas used by the soundness proof.  Keeping
    them outside [Soundness.v] leaves the fundamental-theorem file focused on
    the proof cases themselves. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps.
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
  unfold res_models, res_models_with_store.
  simpl. intros [_ [Hφ _]].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_and_elim_r (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FAnd φ ψ →
  m ⊨ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ [_ Hψ]].
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_and_intro (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FAnd φ ψ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ Hψ. split; [exact Hscope |].
  split.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_and_intro_from_models (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  intros Hφ Hψ.
  eapply res_models_and_intro.
  - unfold formula_scoped_in_world. simpl.
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
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  left. eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_or_intro_r (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hψ. split; [exact Hscope |].
  right. eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
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
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Himpl. split; [exact Hscope |].
  intros m' Hle Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ + formula_measure ψ) (formula_measure φ)
    ∅ m' φ ltac:(simpl; lia) ltac:(lia) Hφ) as Hφ_exact.
  pose proof (Himpl m' Hle Hφ_exact) as Hψ_exact.
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ_exact]; simpl; lia.
Qed.

(** Kripke implication elimination at the current world. *)
Lemma res_models_impl_elim (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ Himpl] Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ) (formula_measure φ + formula_measure ψ)
    ∅ m φ ltac:(lia) ltac:(simpl; lia) Hφ) as Hφ_big.
  pose proof (Himpl m ltac:(reflexivity) Hφ_big) as Hψ_big.
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ_big]; simpl; lia.
Qed.

Lemma res_models_impl_antecedent_strengthen
    (m : WfWorld) (φ1 φ2 ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FImpl φ2 ψ) →
  (∀ m', m ⊑ m' → m' ⊨ φ2 → m' ⊨ φ1) →
  m ⊨ FImpl φ1 ψ →
  m ⊨ FImpl φ2 ψ.
Proof.
  intros Hscope Hφ Himpl.
  eapply res_models_impl_intro.
  - exact Hscope.
  - intros m' Hle Hφ2.
    eapply res_models_impl_elim.
    + eapply res_models_kripke; [exact Hle | exact Himpl].
    + eapply Hφ; eauto.
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
  m ⊨ denot_ctx_under (erase_ctx_under Σ Γ) Γ.
Proof.
  unfold denot_ctx_in_env.
  apply res_models_and_elim_r.
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
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  let X := dom Σ ∪ ctx_dom Γ in
  closed_env (store_restrict σ X) ∧
  env_has_type (erase_ctx_under Σ Γ) (store_restrict σ X).
Proof.
Admitted.

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
  destruct (denot_ctx_in_env_store_erased_typed Σ Γ m σ HΓ Hσ) as
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
  intros Hclosed Hνx Hx_fresh Hsteps Hret Hproj.
  assert (Hxσν : σν !! x = Some vx).
  {
    rewrite <- Hproj.
    apply store_restrict_lookup_some_2.
    - change ((<[x := vx]> σ : Store) !! x = Some vx).
      rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
    - set_solver.
  }
  assert (Hνσ : σ !! ν = Some vx).
  {
    assert (Hνσν : σν !! ν = Some vx).
    { eapply expr_result_in_store_ret_fvar_lookup; eauto. }
    rewrite <- Hproj in Hνσν.
    apply store_restrict_lookup_some in Hνσν as [_ Hx].
    change ((<[x := vx]> σ : Store) !! ν = Some vx) in Hx.
    rewrite lookup_insert in Hx.
    rewrite decide_False in Hx by congruence.
    exact Hx.
  }
  exists vx. split; [exact Hνσ | exact Hsteps].
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
  intros S Hclosed_vx Hνx HxS HclosedσS Hx_fresh Hsteps Hret Hproj.
  assert (Hsteps0 : subst_map σ (subst_map ∅ e) →* tret vx).
  {
    change (subst_map ∅ e) with (m{∅} e).
    rewrite msubst_empty. exact Hsteps.
  }
  assert (Hν : σ !! ν = Some vx).
  {
    assert (Hxσν : σν !! x = Some vx).
    {
      rewrite <- Hproj.
      apply store_restrict_lookup_some_2.
      - change ((<[x := vx]> σ : Store) !! x = Some vx).
        rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
      - set_solver.
    }
    assert (Hνσν : σν !! ν = Some vx).
    { eapply expr_result_in_store_ret_fvar_lookup; eauto. }
    rewrite <- Hproj in Hνσν.
    apply store_restrict_lookup_some in Hνσν as [_ Hx].
    change ((<[x := vx]> σ : Store) !! ν = Some vx) in Hx.
    rewrite lookup_insert in Hx.
    rewrite decide_False in Hx by congruence.
    exact Hx.
  }
  exists vx. split.
  - apply store_restrict_lookup_some_2; [exact Hν | set_solver].
  - change (subst_map (store_restrict σ S) (subst_map ∅ e) →* tret vx).
    change (subst_map ∅ e) with (m{∅} e).
    rewrite msubst_empty.
    change (subst_map (store_restrict σ S) e) with (m{store_restrict σ S} e).
    change (m{store_restrict σ S} e) with (m{map_restrict value σ S} e).
    change (subst_map σ e) with (m{σ} e) in Hsteps.
    erewrite (@msubst_restrict_closed_on tm stale_tm_inst subst_tm_inst _ _ _
      σ S e); [exact Hsteps | exact HclosedσS | set_solver].
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
  intros Hνx HxS Hp_dom Hdecomp Hclosed Hresult_closed Hret σS HσS.
  simpl in HσS.
  destruct HσS as [σfull [[Hn_full Hp_full] HrestrictS]].
  destruct (Hdecomp σfull Hn_full) as [σ [vx [-> [Hx_fresh Hsteps]]]].
  assert (Hσν_proj :
    (res_restrict p ({[x]} ∪ {[ν]}) : World)
      (store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}))).
  {
    simpl. exists (store_restrict (<[x := vx]> σ) (world_dom (p : World))).
    split; [exact Hp_full |].
    rewrite store_restrict_restrict.
    change ({[x]} ∪ {[ν]}) with (({[x]} ∪ {[ν]}) : aset).
    replace (world_dom (p : World) ∩ (({[x]} ∪ {[ν]}) : aset))
      with (({[x]} ∪ {[ν]}) : aset) by set_solver.
    reflexivity.
  }
  pose proof (Hret _ Hσν_proj) as Hret_store.
  assert (HclosedS : closed_env (store_restrict σ (stale e ∪ {[ν]}))).
  {
    assert (Hν_lookup : σ !! ν = Some vx).
    {
      assert (Hxσν : store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) !! x = Some vx).
      {
        apply store_restrict_lookup_some_2.
        - change ((<[x := vx]> σ : Store) !! x = Some vx).
          rewrite lookup_insert. rewrite decide_True by reflexivity. reflexivity.
        - set_solver.
      }
      assert (Hνσν : store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}) !! ν = Some vx).
      { eapply expr_result_in_store_ret_fvar_lookup; eauto. }
      apply store_restrict_lookup_some in Hνσν as [_ Hνins].
      change ((<[x := vx]> σ : Store) !! ν = Some vx) in Hνins.
      rewrite lookup_insert in Hνins.
      rewrite decide_False in Hνins by congruence.
      exact Hνins.
    }
    eapply closed_env_restrict_insert_result; eauto.
  }
  pose proof (expr_result_in_store_ret_fvar_to_source_restrict
    e x ν σ vx (store_restrict (<[x := vx]> σ) ({[x]} ∪ {[ν]}))
    (Hresult_closed σ vx Hn_full Hsteps)
    ltac:(exact Hνx) ltac:(exact HxS) HclosedS) as Hbridge.
  specialize (Hbridge Hx_fresh Hsteps Hret_store eq_refl).
  destruct Hbridge as [v [Hν HstepsS]].
  rewrite store_restrict_insert_notin in HrestrictS by exact HxS.
  exists v. split; [|].
  - rewrite <- HrestrictS. exact Hν.
  - rewrite <- HrestrictS. exact HstepsS.
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

Lemma denot_ctx_comma_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_comma. Qed.

Lemma denot_ctx_comma_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_under Σ Γ1 ∧ m ⊨ denot_ctx_under Σ Γ2.
Proof. apply denot_ctx_under_comma. Qed.

Lemma denot_ctx_in_env_comma_agree Σ Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1)
    (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1) →
  ty_env_agree_on (ctx_stale Γ2)
    (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2) →
  m ⊨ denot_ctx_in_env Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_in_env Σ Γ1 ∧ m ⊨ denot_ctx_in_env Σ Γ2.
Proof.
  intros Hagree1 Hagree2.
  unfold denot_ctx_in_env.
  split.
  - intros Hm.
    pose proof (res_models_and_elim_l m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ (CtxComma Γ1 Γ2))
        (CtxComma Γ1 Γ2)) Hm) as Hbasic.
    pose proof (res_models_and_elim_r m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ (CtxComma Γ1 Γ2))
        (CtxComma Γ1 Γ2)) Hm) as Hctx.
    apply denot_ctx_under_comma in Hctx as [HΓ1 HΓ2].
    split.
    + apply res_models_and_intro_from_models.
      * exact Hbasic.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1)
          Γ1 Hagree1) as [Hequiv _].
        apply Hequiv. exact HΓ1.
    + apply res_models_and_intro_from_models.
      * exact Hbasic.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2)
          Γ2 Hagree2) as [Hequiv _].
        apply Hequiv. exact HΓ2.
  - intros [HΓ1 HΓ2].
    pose proof (res_models_and_elim_l m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ Γ1) Γ1) HΓ1) as Hbasic.
    pose proof (res_models_and_elim_r m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ Γ1) Γ1) HΓ1) as Hctx1.
    pose proof (res_models_and_elim_r m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ Γ2) Γ2) HΓ2) as Hctx2.
    apply res_models_and_intro_from_models.
    + exact Hbasic.
    + apply denot_ctx_under_comma. split.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1)
          Γ1 Hagree1) as [_ Hequiv].
        apply Hequiv. exact Hctx1.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2)
          Γ2 Hagree2) as [_ Hequiv].
        apply Hequiv. exact Hctx2.
Qed.

Lemma denot_ctx_star_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_star. Qed.

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
