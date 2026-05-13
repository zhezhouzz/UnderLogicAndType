(** * ChoiceTyping.SoundnessHelpers

    Stable formula/context helper lemmas used by the soundness proof.  Keeping
    them outside [Soundness.v] leaves the fundamental-theorem file focused on
    the proof cases themselves. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceLogic Require Export FormulaDerived.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma denot_ctx_in_env_world_covers_erased Σ Γ m :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  dom (erase_ctx_under Σ Γ) ⊆ world_dom (m : World).
Proof.
  intros Hbasic HΓ z Hz.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m
    (denot_ctx_in_env Σ Γ) HΓ) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  apply Hscope.
  apply elem_of_union. right.
  apply denot_ctx_in_env_dom_subset_formula_fv.
  rewrite <- (erase_ctx_under_dom_basic Σ Γ Hbasic). exact Hz.
Qed.

Lemma denot_ctx_in_env_store_restrict_env_delete_empty Σ Γ m σ :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  env_delete (store_restrict σ (dom (erase_ctx_under Σ Γ)))
    (erase_ctx_under Σ Γ) = ∅.
Proof.
  intros Hbasic HΓ Hσ.
  apply env_delete_empty_of_dom_subset.
  pose proof (denot_ctx_in_env_world_covers_erased Σ Γ m Hbasic HΓ) as Hcover.
  pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
  intros z Hz.
  apply elem_of_dom.
  assert (Hzdom : z ∈ dom σ) by (rewrite Hdomσ; set_solver).
  apply elem_of_dom in Hzdom as [v Hlookup].
  exists v. apply store_restrict_lookup_some_2; [exact Hlookup | set_solver].
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
  assert (Hstore_typed : store_has_type_on Σ X (store_restrict σ X)).
  { apply Htyped. simpl. exists σ. split; [exact Hσ | reflexivity]. }
  split.
  - eapply (store_has_type_on_closed_env Σ X (store_restrict σ X)).
    + rewrite store_restrict_dom. set_solver.
    + exact HXΣ.
    + exact Hstore_typed.
  - eapply (store_has_type_on_lc_env Σ X (store_restrict σ X)).
    + rewrite store_restrict_dom. set_solver.
    + exact HXΣ.
    + exact Hstore_typed.
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
    unfold X. rewrite (erase_ctx_under_dom_basic Σ Γ Hbasic). reflexivity.
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
  { unfold X. apply erase_ctx_under_dom_basic. exact Hbasic. }
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
  { unfold X. apply erase_ctx_under_dom_basic.
    apply (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty)). }
  assert (Hdom_del : env_delete (store_restrict σ X) (erase_ctx_under Σ Γ) = ∅).
  {
    rewrite <- Hdom_erase.
    eapply denot_ctx_in_env_store_restrict_env_delete_empty; eauto.
    apply (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hty)).
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
  { unfold X. apply erase_ctx_under_dom_basic. exact Hbasic. }
  assert (Hdom_del : env_delete (store_restrict σ X) (erase_ctx_under Σ Γ) = ∅).
  {
    rewrite <- Hdom_erase.
    eapply denot_ctx_in_env_store_restrict_env_delete_empty; eauto.
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
  { unfold X. apply erase_ctx_under_dom_basic. exact Hbasic. }
  assert (Hdom_del : env_delete (store_restrict σ X) (erase_ctx_under Σ Γ) = ∅).
  {
    rewrite <- Hdom_erase.
    eapply denot_ctx_in_env_store_restrict_env_delete_empty; eauto.
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
