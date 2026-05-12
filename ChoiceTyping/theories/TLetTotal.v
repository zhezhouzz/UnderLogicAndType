(** * ChoiceTyping.TLetTotal

    Context-preservation helpers for the [tlet] result world.

    Older graph/fiber proof experiments have been removed from this file.  The
    remaining lemmas are exactly the facts used by [TLetDenotation] to build the
    comma-extended context after evaluating the let-bound expression. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Import Naming ResultWorldClosed.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma let_result_world_on_preserves_context Σ Γ e x (w : WfWorld) Hfresh Hresult :
  w ⊨ denot_ctx_in_env Σ Γ →
  let_result_world_on e x w Hfresh Hresult ⊨ denot_ctx_in_env Σ Γ.
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
  let_result_world_on e x m Hfresh Hresult ⊨
    basic_world_formula
      (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))
      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)))).
Proof.
Admitted.

(** Result-binding compatibility for the let-result world.

    If [m] satisfies [τ] for the expression [e], then the world obtained by
    adding a fresh coordinate [x] containing exactly the possible results of
    [e] satisfies [τ] for [return x].

    This is intentionally a denotation-level transport theorem, not a
    constructor-specific typing case.  The proof should follow from a generic
    expression-result transport principle for [denot_ty_on]. *)
Lemma denot_ty_on_let_result_representative
    X Σ τ e x (m : WfWorld) Hfresh Hresult :
  basic_choice_ty (dom Σ) τ →
  fv_tm e ⊆ X →
  x ∉ X ∪ fv_cty τ ∪ fv_tm e →
  m ⊨ basic_world_formula Σ (dom Σ) →
  m ⊨ denot_ty_on Σ τ e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_on (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
Admitted.

Lemma let_result_world_on_bound_type
    Σ Γ τ e x (m : WfWorld) Hfresh Hresult :
  choice_typing_wf Σ Γ e τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e →
  let_result_world_on e x m Hfresh Hresult ⊨
    denot_ty_on
      (<[x := erase_ty τ]> (erase_ctx_under Σ Γ))
      τ (tret (vfvar x)).
Proof.
  intros Hwf Hm Hτ Hx.
  eapply (denot_ty_on_let_result_representative
    (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e x m Hfresh Hresult).
  - exact (choice_typing_wf_basic_choice_ty_erased Σ Γ e τ Hwf).
  - exact (choice_typing_wf_fv_tm_subset_erase_dom Σ Γ e τ Hwf).
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
  let_result_world_on e x m Hfresh Hresult ⊨
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
    exact (choice_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf).
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

Lemma lc_env_restrict σ X :
  lc_env σ →
  lc_env (store_restrict σ X).
Proof.
  unfold lc_env. intros Hlc.
  apply map_Forall_lookup_2. intros y v Hlookup.
  apply store_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact (map_Forall_lookup_1 _ _ _ _ Hlc Hlookup).
Qed.

Lemma expr_total_on_tlete_elim_body_strong
    X e1 e2 x (m : WfWorld) Hfresh Hresult :
  X ⊆ world_dom (m : World) →
  x ∉ X →
  x ∉ fv_tm e2 →
  world_store_closed_on X m →
  lc_tm (tlete e1 e2) →
  expr_total_on X (tlete e1 e2) m →
  expr_total_on (X ∪ {[x]}) (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult).
Proof.
  intros HXdom HxX Hxe2 Hclosed Hlclet [Hfv Hsn].
  apply lc_lete_iff_body in Hlclet as [Hlc1 Hbody2].
  split.
  - simpl in Hfv.
    pose proof (open_fv_tm e2 (vfvar x) 0) as Hopen_fv.
    simpl in Hopen_fv. set_solver.
  - intros σx Hσx.
    destruct (let_result_world_on_elim e1 x m Hfresh Hresult σx Hσx)
      as [σ [vx [Hσ [Hsteps_fv ->]]]].
    assert (HclosedX : store_closed (store_restrict σ X)).
    { exact (Hclosed σ Hσ). }
    assert (Hfv1 : fv_tm e1 ⊆ X) by (simpl in Hfv; set_solver).
    assert (HstepsX : subst_map (store_restrict σ X) e1 →* tret vx).
    {
      rewrite <- (subst_map_restrict_to_fv_from_superset e1 X σ Hfv1
        (proj1 HclosedX)).
      exact Hsteps_fv.
    }
    assert (Hvx_closed : stale vx = ∅ ∧ is_lc vx).
    {
      eapply steps_closed_result; [| exact HstepsX].
      apply msubst_closed_tm.
      - exact HclosedX.
      - exact Hlc1.
      - change (fv_tm e1 ⊆ dom (store_restrict σ X)).
        rewrite store_restrict_dom.
        pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
        set_solver.
    }
    assert (Hbody_msubst : body_tm (subst_map (store_restrict σ X) e2)).
    { apply body_tm_msubst; [exact (proj1 HclosedX) | exact (proj2 HclosedX) | exact Hbody2]. }
    assert (Hsnlet :
      strongly_normalizing
        (tlete (subst_map (store_restrict σ X) e1)
               (subst_map (store_restrict σ X) e2))).
    {
      specialize (Hsn σ Hσ).
      change (strongly_normalizing (m{store_restrict σ X} (tlete e1 e2))) in Hsn.
      rewrite msubst_lete in Hsn. exact Hsn.
    }
    pose proof (strongly_normalizing_tlete_elim_body
      (subst_map (store_restrict σ X) e1)
      (subst_map (store_restrict σ X) e2)
      vx Hbody_msubst HstepsX Hsnlet) as Hbody_sn.
    rewrite store_restrict_insert_fresh_union.
    + rewrite (msubst_open_body_result X σ e2 x vx)
        by (try exact HxX; try exact Hxe2; try exact (proj1 HclosedX);
            try exact (proj1 Hvx_closed); try exact (proj2 Hvx_closed);
            try exact (proj2 HclosedX)).
      exact Hbody_sn.
    + eapply store_lookup_none_of_dom.
      * exact (wfworld_store_dom m σ Hσ).
      * exact Hfresh.
    + exact HxX.
Qed.

Lemma basic_typing_tlete_body_for_fresh Γ e1 e2 T1 T2 x :
  Γ ⊢ₑ e1 ⋮ T1 →
  Γ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ dom Γ ∪ fv_tm e2 →
  <[x := T1]> Γ ⊢ₑ e2 ^^ x ⋮ T2.
Proof.
  intros He1 Hlet Hxfresh.
  inversion Hlet; subst.
  assert (T0 = T1) as ->.
  { eapply basic_typing_unique_tm; eauto. }
  pose (y := fresh_for (L ∪ dom Γ ∪ fv_tm e2 ∪ {[x]})).
  assert (Hy : y ∉ L ∪ dom Γ ∪ fv_tm e2 ∪ {[x]})
    by (subst y; apply fresh_for_not_in).
  match goal with
  | Hopen : ∀ z : atom, z ∉ L → <[z:=T1]> Γ ⊢ₑ e2 ^^ z ⋮ T2 |- _ =>
      pose proof (Hopen y ltac:(set_solver)) as Hybody
  end.
  eapply basic_typing_open_tm with (x := y) (U := T1).
  - set_solver.
  - constructor. apply lookup_insert_eq.
  - replace (<[y:=T1]> (<[x:=T1]> Γ))
      with (<[x:=T1]> (<[y:=T1]> Γ))
      by (rewrite insert_insert_ne by set_solver; reflexivity).
    eapply basic_typing_weaken_insert_tm.
    + rewrite dom_insert_L. set_solver.
    + exact Hybody.
Qed.
