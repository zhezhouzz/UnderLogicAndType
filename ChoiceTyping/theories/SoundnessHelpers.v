(** * ChoiceTyping.SoundnessHelpers

    Stable formula/context helper lemmas used by the soundness proof.  Keeping
    them outside [Soundness.v] leaves the fundamental-theorem file focused on
    the proof cases themselves. *)

From CoreLang Require Import Instantiation InstantiationProps.
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
  exists m. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_with_store_atom_intro
    (ρ : Store) (m : WfWorld) (q : logic_qualifier) :
  formula_scoped_in_world ρ m (FAtom q) →
  logic_qualifier_denote q ρ m →
  res_models_with_store ρ m (FAtom q).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hq | reflexivity].
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
