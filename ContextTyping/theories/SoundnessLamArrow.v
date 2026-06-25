(** * ContextTyping.SoundnessLamArrow

    Arrow/Lam proof support for the direct Fundamental theorem. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier BasicTypingFormula RelevantEnv.
From Denotation Require Import Context TypeDenote TypeEquivCore DenotationSetMapFacts TypeEquivTerm TypeEquivFiberBase TypeEquivBody TypeEquivArrow TypeEquivWand TypeEquiv ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma lam_arrow_open_arg_mid_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Hmid.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hτx_fv : fv_cty τx ⊆ dom (erase_ctx Γ)).
  {
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    eapply wf_context_ty_at_fv_subset. exact Hτx.
  }
  eapply ty_denote_gas_ret_fvar_insert_ctx_erasure_under; eauto.
Qed.

Lemma lam_arrow_open_arg_normalize
  (Σ : tyctx) Γ τx τ e
  (my : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  lc_context_ty τx ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)).
Proof.
  intros Hy Hlcτx Harg.
  rewrite formula_open_ty_denote_gas_bind_ret_bvar0 in Harg.
  2:{ apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    apply relevant_env_arrow_fresh_free.
    - clear -Hy. better_set_solver.
    - clear -Hy. better_set_solver.
    - cbn [fv_tm fv_value]. clear -Hy. better_set_solver.
  }
  2:{ clear -Hy. better_set_solver. }
  2:{ exact Hlcτx. }
  exact (arrow_open_arg_to_inserted_env
    (Nat.max (cty_depth τx) (cty_depth τ))
    (atom_env_to_lty_env (erase_ctx Γ)) τx τ
    (tret (vlam (erase_ty τx) e)) my y Harg).
Qed.

Lemma lam_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  rewrite ty_denote_gas_saturate in Harg by lia.
  eapply lam_arrow_open_arg_mid_to_bind_denotation; eauto.
Qed.

Lemma lam_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ e
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (lam_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ e my y Hwf Hy Harg)
    as Hbind_den.
  assert (Hworld_bind :
      my ⊨ basic_world_formula
        (atom_env_to_lty_env (<[y := erase_ty τx]> (ctx_erasure_under Σ Γ)))).
  {
    replace (atom_env_to_lty_env (<[y := erase_ty τx]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply (basic_world_insert_of_arg
      (atom_env_to_lty_env (ctx_erasure_under Σ Γ)) τx y
      (erase_ty τx) (cty_depth τx)); eauto.
    - apply atom_env_to_lty_env_dom_free_notin.
      ctx_erasure_under_norm_in Hy. better_set_solver.
    - exact (ctx_denote_under_basic_world Σ Γ my Hctx_my).
    - rewrite <- atom_store_to_lvar_store_insert.
      exact Hbind_den.
  }
  eapply ctx_bind_from_inserted_erasure_denotation.
  - ctx_erasure_under_norm_in Hy. better_set_solver.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    destruct Hτwf as [Hτx _].
    pose proof (wf_context_ty_at_fv_subset 0 (dom (erase_ctx Γ)) τx Hτx)
      as Hτxfv.
    unfold ty_env_agree_on. intros z Hz.
    assert (HzΓ : z ∈ dom (erase_ctx Γ)).
    { apply Hτxfv. exact Hz. }
    pose proof (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
      Σ Γ z HbasicΓ HzΓ) as Herase.
    assert (HΣnone : Σ !! z = None).
    { eapply basic_ctx_erase_dom_fresh_none; eauto. }
    transitivity ((erase_ctx Γ : gmap atom ty) !! z).
    + apply lookup_union_r. exact HΣnone.
    + exact Herase.
  - exact Hworld_bind.
  - exact Hbind_den.
Qed.

Lemma lam_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ e
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hwf Hctx Hdom Hrestrict Hy Harg.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  assert (Hctx_my : my ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_my|].
  eapply lam_arrow_open_arg_to_bind_ctx; eauto.
Qed.

Lemma lam_body_to_arrow_result_mid
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
    ({0 ~> y} τ) (e ^^ y) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ) (e ^^ y).
Proof.
  intros _ Hy Hbody.
  pose proof (ty_denote_under_comma_bind_to_lvar_insert
    Σ Γ τx (cty_open 0 y τ) (e ^^ y) y my
    ltac:(ctx_erasure_under_norm_in Hy; better_set_solver) Hbody) as Hinsert.
  rewrite ty_denote_gas_saturate
    by (rewrite cty_open_preserves_depth; lia).
  rewrite cty_open_preserves_depth.
  rewrite cty_open_preserves_depth in Hinsert.
  exact Hinsert.
Qed.

Lemma lam_arrow_result_mid_app_guard
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas 0
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_guard_formula
    (relevant_env
      ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y τ)
      (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
		Proof.
		  intros Hwf Hy Hzero_body Hstatic.
	  pose proof (ty_static_guard_relevant_of_full _ _ _ _ Hstatic)
	    as Hstatic_rel.
	  unfold ty_guard_formula.
	  unfold ty_static_guard_formula in Hstatic_rel.
	  repeat rewrite res_models_and_iff in Hstatic_rel.
	  destruct Hstatic_rel as [Hwf_app [Hworld_app Hbasic_app]].
	  repeat rewrite res_models_and_iff.
	  split; [exact Hwf_app|].
	  split; [exact Hworld_app|].
	  split; [exact Hbasic_app|].
	  pose proof (ty_denote_gas_guard_of_zero _ _ _ _ Hzero_body)
	    as Hguard_body.
	  unfold ty_guard_formula in Hguard_body.
	  repeat rewrite res_models_and_iff in Hguard_body.
	  destruct Hguard_body as [_ [_ [_ Htotal_body]]].
	  apply expr_basic_typing_formula_models_iff in Hbasic_app
	    as [HlcΣ_app [_ Hbasic_ltype_app]].
	  pose proof (basic_tm_has_ltype_lc _ _ _
	    HlcΣ_app Hbasic_ltype_app) as Hlc_app.
	  pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
	    as Hfv_lvars_app.
	  assert (Hfv_app :
	      fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ⊆
	      world_dom (my : WorldT)).
	  {
	    apply basic_world_formula_models_iff in Hworld_app
	      as [_ [Hscope_app _]].
	    intros x Hx.
	    apply Hscope_app.
	    apply (proj2 (lvars_fv_elem _ x)).
	    apply Hfv_lvars_app.
	    unfold lvars_of_atoms.
	    apply elem_of_map. exists x. split; [reflexivity|exact Hx].
	  }
	  pose proof (context_typing_wf_lam_body
	    Σ Γ (erase_ty τx) e (CTArrow τx τ) Hwf) as Hbody.
		  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
		  {
		    apply Hfv_app.
		    cbn [fv_tm fv_value].
		    set_solver.
		  }
	  assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
	  {
	    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
	    eapply ty_denote_gas_guard_of_zero. exact Hzero_body.
	  }
	  assert (Hclosed_app :
	      wfworld_closed_on
	        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))) my).
	  {
	    eapply basic_world_formula_wfworld_closed_on_atoms;
	      [exact Hfv_lvars_app|exact Hworld_app].
	  }
	  assert (Hclosed :
	      wfworld_closed_on
	        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ∪
	         fv_tm (e ^^ y)) my).
	  { apply wfworld_closed_on_union; assumption. }
	  assert (Heq :
	      tm_equiv_on my (e ^^ y)
	        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
	  {
	    intros σ v Hσ.
	    pose proof (tm_equiv_lam_app_body (erase_ty τx) e y my
	      Hclosed Hbody ltac:(ctx_erasure_under_norm_in Hy; better_set_solver)
	      Hy_dom σ v Hσ) as [Happ_body Hbody_app].
		    split; [exact Hbody_app|exact Happ_body].
		  }
		  pose proof (tm_total_equiv_lam_app_body
		    (erase_ty τx) e y my Hclosed Hbody
		    ltac:(ctx_erasure_under_norm_in Hy; better_set_solver)
		    Hy_dom) as Htotal_eq.
		  eapply tm_equiv_total;
		    [ exact Htotal_eq
		    | exact Hlc_app
		    | exact Hfv_app
		    | exact Htotal_body ].
		Qed.

Lemma lam_arrow_result_mid_app_zero
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas 0
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_denote_gas 0
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hzero_body Hstatic.
	  apply ty_denote_gas_zero_of_guard.
	  eapply lam_arrow_result_mid_app_guard; eauto.
Qed.

Lemma lam_arrow_result_mid_app_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hmid Hstatic.
  assert (Hzero_body :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ) (e ^^ y)).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hmid.
  }
  assert (Hzero_app :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
	  { eapply lam_arrow_result_mid_app_zero; eauto. }
  assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard. exact Hmid.
  }
  assert (Hclosed_app :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard_of_zero. exact Hzero_app.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ∪
         fv_tm (e ^^ y)) my).
  { apply wfworld_closed_on_union; assumption. }
  pose proof (context_typing_wf_lam_body
    Σ Γ (erase_ty τx) e (CTArrow τx τ) Hwf) as Hbody.
	  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
	  {
	    pose proof Hstatic as Hstatic_app.
	    unfold ty_static_guard_formula in Hstatic_app.
	    repeat rewrite res_models_and_iff in Hstatic_app.
	    destruct Hstatic_app as [_ [Hworld_app Hbasic_app]].
	    apply expr_basic_typing_formula_models_iff in Hbasic_app
	      as [HlcΣ_app [_ Hbasic_ltype_app]].
	    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
	      as Hfv_lvars_app.
	    apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope_app _]].
	    apply Hscope_app.
	    apply (proj2 (lvars_fv_elem _ y)).
	    apply Hfv_lvars_app.
	    unfold lvars_of_atoms.
	    apply elem_of_map. exists y. split; [reflexivity|].
	    cbn [fv_tm fv_value].
	    set_solver.
	  }
  eapply lam_intro_denotation; eauto.
  ctx_erasure_under_norm_in Hy. better_set_solver.
Qed.

Lemma lam_arrow_result_mid_to_opened_goal
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hmid Hstatic.
  set (elam := tret (vlam (erase_ty τx) e)).
		  pose proof (lam_arrow_result_mid_app_denotation
		    Σ Γ τx τ e my y Hwf Hy Hmid Hstatic) as Happ_mid.
  assert (Hlc_elam : lc_tm elam).
  {
    subst elam.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  {
    pose proof (context_typing_wf_context_ty
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
      as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    eapply wf_context_ty_at_lc. exact (proj2 Hτwf).
  }
  subst elam.
	  eapply ty_equiv_arrow_result_tgt_goal.
  - exact Hlc_elam.
  - set_solver.
  - apply arrow_result_open_vars_subset; [exact Hτ_lc1|set_solver].
  - exact Happ_mid.
Qed.

Lemma lam_body_to_opened_arrow_result
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
	    ({0 ~> y} τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hbody Hstatic.
		  pose proof (lam_body_to_arrow_result_mid
		    Σ Γ τx τ e my y Hwf Hy Hbody) as Hmid.
		  eapply lam_arrow_result_mid_to_opened_goal; eauto.
Qed.

Lemma lam_opened_arrow_result
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
	  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
			  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
			      ((<[LVFree y := erase_ty τx]>
	            (atom_env_to_lty_env (erase_ctx Γ))))
		      τx (tret (vfvar y)) ->
		  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree y := erase_ty τx]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
      (cty_open 0 y τ)
      (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf IH Hctx Hdom Hrestrict Hy Harg.
  assert (Hy_rest :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
  {
    intros Hin.
    clear -Hy Hin. better_set_solver.
  }
  assert (HyL : y ∉ L).
  {
    intros Hin.
    clear -Hy Hin. better_set_solver.
  }
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (lam_arrow_open_arg_to_comma_ctx Σ Γ τx τ e m my y).
    - exact Hwf.
    - exact Hctx.
    - exact Hdom.
    - exact Hrestrict.
    - exact Hy_rest.
    - exact Harg.
  }
		  pose proof (IH y HyL my Hctx_comma) as Hbody.
		  pose proof (lam_arrow_opened_app_static_guard_full
			    Σ Γ τx τ e my y Hwf Hy_rest Hctx_comma) as Hstatic_app.
		  eapply (lam_body_to_opened_arrow_result Σ Γ τx τ e my y).
  - exact Hwf.
  - exact Hy_rest.
  - exact Hbody.
  - exact Hstatic_app.
Qed.

Lemma lam_result_first_outer_result_plain
    (Σ : tyctx) Γ τx τ e
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))))
      (tm_shift 0 (tret (vlam (erase_ty τx) e))) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret (vlam (erase_ty τx) e)) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))))).
		  {
		    rewrite lvars_shift_from_fv.
		    intros Hzbad.
		    apply lvars_fv_elem in Hzbad.
		    pose proof (soundness_relevant_env_arrow_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver))
		      as Hnot.
		    exact (Hnot Hzbad).
		  }
  assert (Hlc_elam :
      lc_tm (tret (vlam (erase_ty τx) e))).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  }
  assert (Hz_elam :
      z ∉ fv_tm (tret (vlam (erase_ty τx) e))).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_elam || exact Hz_elam).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret (vlam (erase_ty τx) e)))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
        as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
          as Hlc.
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
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
		    exact (Hnot Hzbad).
	  - exact Hres.
  Qed.

Lemma lamd_result_first_outer_result_plain
    (Σ : tyctx) Γ τx τ e
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))))
      (tm_shift 0 (tret (vlam (erase_ty τx) e))) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret (vlam (erase_ty τx) e)) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))))).
		  {
		    rewrite lvars_shift_from_fv.
		    intros Hzbad.
		    apply lvars_fv_elem in Hzbad.
		    pose proof (soundness_relevant_env_wand_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver))
		      as Hnot.
		    exact (Hnot Hzbad).
		  }
  assert (Hlc_elam :
      lc_tm (tret (vlam (erase_ty τx) e))).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  }
  assert (Hz_elam :
      z ∉ fv_tm (tret (vlam (erase_ty τx) e))).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_elam || exact Hz_elam).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret (vlam (erase_ty τx) e)))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf)
        as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf)
          as Hlc.
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
		    pose proof (soundness_relevant_env_wand_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
		    exact (Hnot Hzbad).
  - exact Hres.
Qed.

Lemma lam_result_first_arrow_value_denotation
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (formula_open 0 z
      (arrow_value_denote_gas_with ty_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty (CTArrow τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0)))) ->
  mz ⊨ expr_result_formula (tret (vlam (erase_ty τx) e)) (LVFree z) ->
  mz ⊨ formula_open 0 z
      (arrow_value_denote_gas_with ty_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty (CTArrow τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))).
Proof.
  intros Hwf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (vf := vlam (erase_ty τx) e).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret vf)).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  eapply res_models_forall_rev_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
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
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
  {
    clear -Hy. better_set_solver.
  }
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
    - subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
    - subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
      subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
    - clear -Hy. set_solver.
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hy. set_solver.
      + exfalso.
        subst Σrel.
        eapply (soundness_relevant_env_arrow_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) τx τ vf y).
        * subst vf. cbn [fv_value]. clear -Hy. better_set_solver.
        * exact Hin.
    - exact Hτx_lc.
    - clear -Hz. better_set_solver.
    - clear -Hy. better_set_solver.
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
    - rewrite lty_env_insert_free_commute by (clear -Hy; set_solver).
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTArrow τx τ)) Hz_rel_arg).
      apply lam_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst vf. clear -Hy. cbn [fv_value]. better_set_solver.
    - exact Harg_norm.
  }
	  assert (Hctx_comma :
	      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
	  {
	    eapply (lam_arrow_open_arg_to_comma_ctx Σ Γ τx τ e mz my y).
	    - exact Hwf.
    - exact Hctx_mz.
    - exact Hdomy.
	    - exact Hrestricty.
	    - exact Hy_fresh.
	    - exact Harg_old.
	  }
  assert (HyL : y ∉ L) by (clear -Hy; better_set_solver).
  pose proof (IH y HyL my Hctx_comma) as Hbody.
  pose proof (lam_arrow_opened_app_static_guard_full
    Σ Γ τx τ e my y Hwf Hy_fresh Hctx_comma) as Hstatic_app.
  pose proof (lam_body_to_arrow_result_mid
    Σ Γ τx τ e my y Hwf Hy_fresh Hbody) as Hmid.
  pose proof (lam_arrow_result_mid_app_denotation
    Σ Γ τx τ e my y Hwf Hy_fresh Hmid Hstatic_app) as Happ_src.
  assert (Hres_my :
      my ⊨ expr_result_formula (tret vf) (LVFree z)).
  {
    subst vf.
    eapply res_models_kripke; [exact Hle_mz_my|exact Hres_z].
  }
	  assert (Hfun_basic :
	      my ⊨ expr_basic_typing_formula
	        (<[LVFree y := erase_ty τx]> Δ)
	        (tret vf) (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
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
        * subst Δ vf.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
	        * apply insert_subseteq. apply not_elem_of_dom.
		          apply atom_env_to_lty_env_dom_free_notin.
		          eapply soundness_fresh_erase_ctx_from_context_union.
              exact Hy_fresh.
	  }
  assert (Hlc_vf : lc_value vf).
  {
    subst vf.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    rewrite dom_insert_L.
    intros Hzdom.
    apply elem_of_union in Hzdom as [Hzdom|Hzdom].
    - apply elem_of_singleton in Hzdom. inversion Hzdom. subst.
      clear -Hy. set_solver.
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
      z ∉ fv_value vf ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    subst vf.
    pose proof (cty_open_fv_subset 0 y τ) as Hτopen.
    cbn [fv_value].
    clear -Hy Hz Hτopen. better_set_solver.
  }
	  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
	    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
	    vf y z (erase_ty τx) my
	    Hz_insert_env
	    Hz_alias_fresh
	    ltac:(apply map_lookup_insert)
	    Hlc_vf
	    Hres_my Hfun_basic Hstatic_app Happ_src) as Htarget_alias.
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
	  2:{ subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
	      subst vf. cbn [fv_value]. clear -Hz; better_set_solver. }
  2:{ clear -Hy. set_solver. }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hy. set_solver.
	    - exfalso.
        subst Σrel.
        eapply (soundness_relevant_env_arrow_value_fresh
          (atom_env_to_lty_env (erase_ctx Γ)) τx τ vf y).
        * subst vf. cbn [fv_value]. clear -Hy. better_set_solver.
        * exact Hin.
  }
  2:{ exact Hτ_lc1. }
  2:{ clear -Hz. better_set_solver. }
  2:{ clear -Hy. better_set_solver. }
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
    + clear -Hy. set_solver.
    + clear -Hy. better_set_solver.
    + subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.
