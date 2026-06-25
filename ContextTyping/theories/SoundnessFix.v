(** * ContextTyping.SoundnessFix

    Final Fix-case proof for the direct Fundamental theorem. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  DenotationSetMapFacts
  TypeEquivCore
  TypeEquivFiberBase
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase
  SoundnessLam SoundnessFixBase SoundnessFixOpen SoundnessFixApply
  SoundnessFixSelf.

Local Ltac fix_union_left :=
  match goal with
  | H : ?x ∉ ?A ∪ ?B |- ?x ∉ ?A =>
      intros Hbad; apply H; apply elem_of_union_l; exact Hbad
  end.

Local Ltac fix_union_right :=
  match goal with
  | H : ?x ∉ ?A ∪ ?B |- ?x ∉ ?B =>
      intros Hbad; apply H; apply elem_of_union_r; exact Hbad
  end.

Local Ltac fix_build_union :=
  match goal with
  | H : ?x ∈ ?A |- ?x ∈ ?A => exact H
  | |- ?x ∈ ?A ∪ ?B =>
      first [apply elem_of_union_l; fix_build_union
            | apply elem_of_union_r; fix_build_union]
  end.

Local Ltac fix_union_side :=
  first
    [ assumption
    | fix_union_left
    | fix_union_right
    | intros Hbad;
      match goal with
      | H : ?x ∉ ?A ∪ ?B |- False => apply H
      | H : ?x ∉ ?A |- False => apply H
      end;
      repeat match goal with
      | H : _ ∈ _ ∪ _ |- _ => apply elem_of_union in H as [H|H]
      end;
      fix_build_union ].

Lemma fix_result_first_outer_result_plain
    (Σ : tyctx) Γ φx τ vf b t
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow (over_ty b φx) τ)
          (tret (vfix (TBase b →ₜ t) vf)))))
      (tm_shift 0 (tret (vfix (TBase b →ₜ t) vf))) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret (vfix (TBase b →ₜ t) vf)) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow (over_ty b φx) τ)
            (tret (vfix (TBase b →ₜ t) vf)))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow (over_ty b φx) τ)
            (tret (vfix (TBase b →ₜ t) vf)))))).
  {
    rewrite lvars_shift_from_fv.
    intros Hzbad.
    apply lvars_fv_elem in Hzbad.
    pose proof (soundness_relevant_env_arrow_value_fresh
      (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
      (vfix (TBase b →ₜ t) vf) z
      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
    exact (Hnot Hzbad).
  }
  assert (Hlc_efix :
      lc_tm (tret (vfix (TBase b →ₜ t) vf))).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vfix (TBase b →ₜ t) vf))
      (CTArrow (over_ty b φx) τ) Hwf).
  }
  assert (Hz_efix :
      z ∉ fv_tm (tret (vfix (TBase b →ₜ t) vf))).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_efix || exact Hz_efix).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf))))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret (vfix (TBase b →ₜ t) vf)))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf))))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow (over_ty b φx) τ) Hwf) as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret (vfix (TBase b →ₜ t) vf))
          (CTArrow (over_ty b φx) τ) Hwf) as Hlc.
        exfalso.
        pose proof (tm_lvars_lc _ Hlc (LVBound k) Hv) as [].
      * rewrite atom_store_to_lvar_store_dom.
        apply elem_of_map. exists a. split; [reflexivity|].
        apply Hfv.
        rewrite <- tm_lvars_fv.
        apply (proj2 (lvars_fv_elem _ _)).
        exact Hv.
    + unfold relevant_lvars. set_solver.
  - set_solver.
  - intros Hzbad.
    pose proof (soundness_relevant_env_arrow_value_fresh
      (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
      (vfix (TBase b →ₜ t) vf) z
      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
    exact (Hnot Hzbad).
  - exact Hres.
Qed.

Lemma fix_opened_arrow_result Σ Γ φx τ vf b t (L : aset)
    (m my : WfWorldT) y :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty (over_ty b φx) ∪ fv_cty τ ->
  my ⊨ ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      ((<[LVFree y := erase_ty (over_ty b φx)]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (over_ty b φx) (tret (vfvar y)) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow (over_ty b φx) τ) (tret (vfix (TBase b →ₜ t) vf)))
        (erase_ty (over_ty b φx)))
      τ
      (tapp_tm (tm_shift 0 (tret (vfix (TBase b →ₜ t) vf))) (vbvar 0))).
Proof.
  change (over_ty b φx) with (CTOver b φx) in *.
  intros Hτ Hwf Hbody_wf IH Hctx Hdom Hrestrict Hy Harg.
  set (τx := over_ty b φx) in *.
  assert (Hτx : erase_ty τx = TBase b) by (subst τx; reflexivity).
  assert (Harg_norm_full :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
        τx (tret (vfvar y))).
  { change (CTOver b φx) with τx in Harg. exact Harg. }
  assert (Harg_norm_depth :
      my ⊨ ty_denote_gas (cty_depth τx)
        ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
        τx (tret (vfvar y))).
  {
    rewrite <- (ty_denote_gas_saturate
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))
      τx (tret (vfvar y))) by lia.
    exact Harg_norm_full.
  }
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (fix_arrow_open_arg_to_comma_ctx Σ Γ τx τ vf b t m my y);
      eauto using Harg_norm_depth.
    subst τx. fix_union_side.
  }
  assert (HyL : y ∉ L) by fix_union_side.
  pose proof (IH y HyL my Hctx_comma) as Hbody_arrow.
  pose proof (fix_self_rec_call_denotation
    Σ Γ φx τ vf b t L my y
    Hτ Hwf Hbody_wf IH ltac:(fix_union_side)
    Hctx_comma Harg_norm_full) as Hself.
  pose proof (fix_body_arrow_apply_self
    Σ Γ τx τ vf b t my y Hτx Hτ Hwf (Hbody_wf y HyL)
    ltac:(fix_union_side) Hctx_comma Hbody_arrow Hself) as Hunfolded.
  pose proof (fix_arrow_opened_app_static_guard_full
    Σ Γ τx τ vf b t my y Hwf ltac:(fix_union_side)
    Hctx_comma) as Hstatic_app.
  eapply fix_unfolded_result_to_opened_goal; eauto.
  fix_union_side.
Qed.

Lemma fix_result_first_arrow_value_denotation
    Σ Γ φx τ vf b t (L : aset)
    (m mz : WfWorldT) z :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_value vf ∪ fv_cty (over_ty b φx) ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (formula_open 0 z
      (arrow_value_denote_gas_with ty_denote_gas
        (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow (over_ty b φx) τ)
            (tret (vfix (TBase b →ₜ t) vf)))
          (erase_ty (CTArrow (over_ty b φx) τ)))
        (cty_shift 0 (over_ty b φx)) (cty_shift 1 τ)
        (tret (vbvar 0)))) ->
  mz ⊨ expr_result_formula (tret (vfix (TBase b →ₜ t) vf)) (LVFree z) ->
  mz ⊨ formula_open 0 z
      (arrow_value_denote_gas_with ty_denote_gas
        (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow (over_ty b φx) τ)
            (tret (vfix (TBase b →ₜ t) vf)))
          (erase_ty (CTArrow (over_ty b φx) τ)))
        (cty_shift 0 (over_ty b φx)) (cty_shift 1 τ)
        (tret (vbvar 0))).
Proof.
  intros Hτ Hwf Hbody_wf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (τx := over_ty b φx).
  set (efix := tret (vfix (TBase b →ₜ t) vf)).
  set (vself := vfix (TBase b →ₜ t) vf).
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTArrow τx τ) efix).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ efix (CTArrow τx τ) ltac:(subst efix τx; exact Hwf))
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  eapply res_models_forall_rev_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪ fv_cty τx ∪
    fv_cty τ ∪ {[z]}).
  intros y Hy my Hdomy Hrestricty.
  assert (Hle_mz_my : mz ⊑ my).
  { rewrite <- Hrestricty. apply res_restrict_le. }
  assert (Hy_world : y ∈ world_dom (my : WorldT)).
  { rewrite Hdomy. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
  cbn [formula_open arrow_value_denote_gas_with] in Hscope_value |- *.
  pose proof (formula_scoped_forall_open_res_le
    mz my y _ Hscope_value Hle_mz_my Hy_world) as Hopened_scope.
  cbn [formula_open] in Hopened_scope |- *.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Harg_raw.
  assert (Hy_fresh :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  { clear -Hy. better_set_solver. }
  assert (Hy_rest :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_value vf ∪ fv_cty τx ∪ fv_cty τ).
  { clear -Hy_fresh. better_set_solver. }
  assert (Harg_norm :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        τx (tret (vfvar y))).
  {
    change (my ⊨ formula_open 0 y
      (formula_open 1 z
        (ty_denote_gas gas
          (typed_lty_env_bind
            (typed_lty_env_bind Σrel (erase_ty (CTArrow τx τ)))
            (erase_ty (cty_shift 0 τx)))
          (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))))
      in Harg_raw.
    rewrite (formula_open_result_first_fun_arg_two
      gas Σrel τx (erase_ty (CTArrow τx τ)) z y) in Harg_raw.
    - exact Harg_raw.
    - subst Σrel Δ. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
    - subst Σrel Δ efix τx. apply soundness_relevant_env_arrow_value_fresh.
      cbn [fv_value]. clear -Hz. better_set_solver.
    - clear -Hy_fresh. set_solver.
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. inversion Hin. subst.
        clear -Hy_fresh. set_solver.
      + exfalso.
        subst Σrel Δ efix τx.
        eapply (soundness_relevant_env_arrow_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
          (vfix (TBase b →ₜ t) vf) y).
        * cbn [fv_value]. clear -Hy_fresh. better_set_solver.
        * exact Hin.
    - exact Hτx_lc.
    - clear -Hz. better_set_solver.
    - clear -Hy_fresh. better_set_solver.
  }
  assert (Harg_old :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by (clear -Hy_fresh; set_solver).
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTArrow τx τ)) Hz_rel_arg).
      apply lam_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst efix vself τx. cbn [fv_value].
        clear -Hy_fresh. better_set_solver.
    - exact Harg_norm.
  }
  pose proof (fix_opened_arrow_result
    Σ Γ φx τ vf b t L mz my y
    Hτ Hwf Hbody_wf IH Hctx_mz Hdomy Hrestricty
    Hy_rest Harg_old) as Happ_src.
  assert (Hres_my :
      my ⊨ expr_result_formula efix (LVFree z)).
  {
    eapply res_models_kripke; [exact Hle_mz_my|exact Hres_z].
  }
  pose proof (fix_arrow_opened_app_static_guard_full
    Σ Γ τx τ vf b t my y
    ltac:(subst τx; exact Hwf)
    ltac:(clear -Hy_fresh; better_set_solver)) as Hstatic_app_need.
  assert (Harg_depth :
      my ⊨ ty_denote_gas (cty_depth τx)
        (<[LVFree y := erase_ty τx]> Δ)
        τx (tret (vfvar y))).
  {
    rewrite <- (ty_denote_gas_saturate gas
      (<[LVFree y := erase_ty τx]> Δ)
      τx (tret (vfvar y))) by lia.
    exact Harg_old.
  }
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (fix_arrow_open_arg_to_comma_ctx Σ Γ τx τ vf b t mz my y).
    - subst τx. exact Hwf.
    - exact Hctx_mz.
    - exact Hdomy.
    - exact Hrestricty.
    - clear -Hy_fresh. better_set_solver.
    - exact Harg_depth.
  }
  pose proof (Hstatic_app_need Hctx_comma) as Hstatic_app.
  assert (Hfun_basic :
      my ⊨ expr_basic_typing_formula
        (<[LVFree y := erase_ty τx]> Δ)
        efix (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
  {
    apply expr_basic_typing_formula_models_iff.
    split.
    - apply lty_env_closed_insert_free. apply atom_store_to_lvar_store_closed.
    - split.
      + pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_app)
          as Hworld_app.
        apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope _]].
        exact Hscope.
      + rewrite cty_open_preserves_erasure.
        eapply basic_tm_has_ltype_weaken.
        * subst Δ efix τx.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret (vfix (TBase b →ₜ t) vf))
            (CTArrow (over_ty b φx) τ) Hwf).
        * apply insert_subseteq. apply not_elem_of_dom.
          apply atom_env_to_lty_env_dom_free_notin.
          eapply (soundness_fresh_erase_ctx_from_context_union
            Σ Γ y (fv_value vf) (fv_cty τx) (fv_cty τ)).
          clear -Hy_fresh. better_set_solver.
  }
  assert (Hlc_vself : lc_value vself).
  {
    subst vself efix.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vfix (TBase b →ₜ t) vf))
      (CTArrow (over_ty b φx) τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    rewrite dom_insert_L.
    intros Hzdom.
    apply elem_of_union in Hzdom as [Hzdom|Hzdom].
    - apply elem_of_singleton in Hzdom. inversion Hzdom. subst.
      clear -Hy_fresh. set_solver.
    - subst Δ.
      rewrite atom_store_to_lvar_store_dom in Hzdom.
      unfold lvars_of_atoms in Hzdom.
      apply elem_of_map in Hzdom as [a [Ha_eq Ha_dom]].
      inversion Ha_eq. subst a.
      pose proof (ctx_erasure_under_erase_ctx_dom_subset Σ Γ z Ha_dom)
        as Hzctx.
      clear -Hz Hzctx. better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value vself ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    subst vself.
    pose proof (cty_open_fv_subset 0 y τ) as Hτopen.
    cbn [fv_value].
    clear -Hy_fresh Hz Hτopen. better_set_solver.
  }
  assert (Hlc_efix : lc_tm efix).
  {
    subst efix.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vfix (TBase b →ₜ t) vf))
      (CTArrow (over_ty b φx) τ) Hwf).
  }
  assert (Happ_src_mid :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y τ)
        (tapp_tm efix (vfvar y))).
  {
    assert (Happ_src_norm :
        my ⊨ ty_denote_gas gas
          (<[LVFree y := erase_ty τx]>
            (relevant_env Δ (CTArrow τx τ) efix))
          (cty_open 0 y τ)
          (tapp_tm efix (vfvar y))).
    {
      change (my ⊨ formula_open 0 y
        (ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Δ (CTArrow τx τ) efix)
            (erase_ty τx))
          τ (tapp_tm (tm_shift 0 efix) (vbvar 0)))) in Happ_src.
      rewrite (formula_open_ty_denote_gas_singleton 0 y gas
        (typed_lty_env_bind
          (relevant_env Δ (CTArrow τx τ) efix)
          (erase_ty τx))
        τ (tapp_tm (tm_shift 0 efix) (vbvar 0))) in Happ_src.
      - rewrite open_tapp_tm_shift_bvar0_lc in Happ_src by exact Hlc_efix.
        rewrite typed_lty_env_bind_open_current in Happ_src.
        exact Happ_src.
        + eapply relevant_env_arrow_fresh_free.
          * clear -Hy_fresh. better_set_solver.
          * clear -Hy_fresh. better_set_solver.
          * subst efix. cbn [fv_tm fv_value].
            clear -Hy_fresh. better_set_solver.
        + apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
      - apply soundness_typed_bind_arrow_value_fresh.
        subst efix τx.
        cbn [fv_value]. clear -Hy_fresh. better_set_solver.
      - rewrite fv_tapp_tm, tm_shift_fv.
        subst efix. cbn [fv_tm fv_value].
        clear -Hy_fresh. better_set_solver.
      - clear -Hy_fresh. better_set_solver.
    }
    pose proof (ty_equiv_arrow_result_src_mid_inserted
      gas Δ τx τ efix my y
      ltac:(subst Δ; apply atom_store_to_lvar_store_closed)
      ltac:(subst Δ; apply atom_env_to_lty_env_dom_free_notin;
        eapply (soundness_fresh_erase_ctx_from_context_union
          Σ Γ y (fv_value vf) (fv_cty τx) (fv_cty τ));
        clear -Hy_fresh; better_set_solver)
      ltac:(eapply relevant_env_arrow_fresh_free;
        [clear -Hy_fresh; better_set_solver
        |clear -Hy_fresh; better_set_solver
        |subst efix; cbn [fv_tm fv_value];
          clear -Hy_fresh; better_set_solver])
      Hlc_efix Hτ_lc1
      ltac:(clear -Hy_fresh; better_set_solver)
      Happ_src_norm) as Hmid_open.
    exact Hmid_open.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    vself y z (erase_ty τx) my
    Hz_insert_env Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_vself Hres_my Hfun_basic Hstatic_app Happ_src_mid) as Htarget_alias.
  change (my ⊨ formula_open 0 y
    (formula_open 1 z
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind Σrel (erase_ty (CTArrow τx τ)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τ)
        (tapp_tm (tret (vbvar 1)) (vbvar 0))))).
  rewrite (formula_open_result_first_fun_result_two
    gas Σrel τx τ (erase_ty (CTArrow τx τ)) z y).
  2:{ subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{ subst Σrel efix τx Δ. apply soundness_relevant_env_arrow_value_fresh.
      cbn [fv_value]. clear -Hz. better_set_solver. }
  2:{ clear -Hy_fresh. set_solver. }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst.
      clear -Hy_fresh. set_solver.
    - exfalso.
      subst Σrel efix τx Δ.
      eapply (soundness_relevant_env_arrow_value_fresh
        (atom_env_to_lty_env (erase_ctx Γ)) (over_ty b φx) τ
        (vfix (TBase b →ₜ t) vf) y).
      * cbn [fv_value]. clear -Hy_fresh. better_set_solver.
      * exact Hin.
  }
  2:{ exact Hτ_lc1. }
  2:{ clear -Hz. better_set_solver. }
  2:{ clear -Hy_fresh. better_set_solver. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := <[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
        (<[LVFree y := erase_ty τx]> Δ))
      (X := relevant_lvars (cty_open 0 y τ)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  - reflexivity.
  - apply lam_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      * intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_fresh HyD. better_set_solver.
      * reflexivity.
    + clear -Hy_fresh. set_solver.
    + clear -Hy_fresh. better_set_solver.
    + subst vself. cbn [fv_value]. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.

Lemma fundamental_fix_case Σ Γ φx τ vf b t (L : aset) :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτ Hwf Hbody_wf IH m Hctx.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (τx := over_ty b φx).
  set (vself := vfix (TBase b →ₜ t) vf).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ (CTArrow τx τ) (tret vself) m
    ltac:(subst τx vself; exact Hwf) Hctx) as Hstatic.
  pose proof (ty_denote_gas_zero_tret_of_static_guard
    Δ (CTArrow τx τ) vself m Hstatic) as Hzero.
  unfold ty_denote_under, ty_denote.
  change (m ⊨ ty_denote_gas (S gas) Δ (CTArrow τx τ) (tret vself)).
  cbn [ty_denote_gas].
  rewrite res_models_and_iff.
  split.
  - eapply ty_denote_gas_guard_of_zero. exact Hzero.
  - pose proof (ty_denote_gas_scope_from_zero_any
      (S gas) Δ (CTArrow τx τ) (tret vself) m Hzero)
      as Hscope_full.
    cbn [ty_denote_gas] in Hscope_full.
    apply (proj1 (formula_scoped_and_iff _ _ _)) in Hscope_full
      as [_ Hscope_body].
    eapply res_models_forall_rev_intro; [exact Hscope_body|].
    exists (L ∪ world_dom (m : WorldT) ∪ dom Σ ∪
      dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ).
    intros z Hz mz Hdomz Hrestrictz.
    assert (Hle_m_mz : m ⊑ mz).
    { rewrite <- Hrestrictz. apply res_restrict_le. }
    assert (Hz_world : z ∈ world_dom (mz : WorldT)).
    { rewrite Hdomz. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
    pose proof (formula_scoped_forall_open_res_le
      m mz z _ Hscope_body Hle_m_mz Hz_world) as Hopened_scope.
    cbn [formula_open] in Hopened_scope |- *.
    eapply res_models_impl_intro; [exact Hopened_scope|].
    intros Hres_raw.
    assert (Hzfresh :
        z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
          fv_value vf ∪ fv_cty τx ∪ fv_cty τ).
    { clear -Hz. better_set_solver. }
    pose proof (fix_result_first_outer_result_plain
      Σ Γ φx τ vf b t mz z
      ltac:(subst τx vself; exact Hwf)
      ltac:(subst τx; clear -Hzfresh; better_set_solver)
      Hres_raw) as Hres_plain.
    eapply (fix_result_first_arrow_value_denotation
      Σ Γ φx τ vf b t L m mz z).
    + exact Hτ.
    + exact Hwf.
    + exact Hbody_wf.
    + exact IH.
    + exact Hctx.
    + exact Hdomz.
    + exact Hrestrictz.
    + subst τx. exact Hzfresh.
    + eapply formula_scoped_impl_r. exact Hopened_scope.
    + exact Hres_plain.
Qed.
