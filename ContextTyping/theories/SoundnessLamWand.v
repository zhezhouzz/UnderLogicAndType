(** * ContextTyping.SoundnessLamWand

    Wand/LamD proof support for the direct Fundamental theorem. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier BasicTypingFormula RelevantEnv.
From Denotation Require Import Context TypeDenote TypeEquivCore DenotationSetMapFacts TypeEquivTerm TypeEquivFiberBase TypeEquivBody TypeEquivArrow TypeEquivWand TypeEquiv ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase SoundnessLamArrow.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Local Lemma union_singleton_empty_r (X : aset) y :
  X ∪ ({[y]} ∪ ∅) = X ∪ {[y]}.
Proof.
  set_solver.
Qed.

Local Lemma lam_wand_fresh_erase_ctx
    (Σ : tyctx) Γ τx τ e y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  y ∉ dom (erase_ctx Γ).
Proof.
  intros Hy.
  eapply soundness_fresh_erase_ctx_from_context_union.
  exact Hy.
Qed.

Local Lemma lam_wand_fresh_tm
    (Σ : tyctx) Γ τx τ e y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  y ∉ fv_tm e.
Proof.
  intros Hy.
  soundness_fresh_solve.
Qed.

Local Lemma lam_wand_fresh_arg_ty
    (Σ : tyctx) Γ τx τ e y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  y ∉ fv_cty τx.
Proof.
  intros Hy.
  soundness_fresh_solve.
Qed.

Local Lemma lam_wand_fresh_result_ty
    (Σ : tyctx) Γ τx τ e y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  y ∉ fv_cty τ.
Proof.
  intros Hy.
  soundness_fresh_solve.
Qed.

Local Lemma lam_wand_shifted_tapp_fresh
    (Σ : tyctx) Γ τx τ e y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  y ∉ fv_tm
    (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0)).
Proof.
  intros Hy.
  rewrite fv_tapp_tm, tm_shift_fv.
  cbn [fv_tm fv_value].
  pose proof (lam_wand_fresh_tm Σ Γ τx τ e y Hy) as Hye.
  soundness_fresh_solve.
Qed.

Local Lemma lam_wand_open_shifted_tapp_denote_iff
    gas (Σ : lty_env) τ elam (m : WfWorldT) y :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm (tapp_tm (tm_shift 0 elam) (vbvar 0)) ->
  y ∉ fv_cty τ ->
  lc_tm elam ->
  (m ⊨ formula_open 0 y
    (ty_denote_gas gas Σ τ
      (tapp_tm (tm_shift 0 elam) (vbvar 0)))) <->
  (m ⊨ ty_denote_gas gas (lty_env_open_one 0 y Σ)
    (cty_open 0 y τ) (tapp_tm elam (vfvar y))).
Proof.
  intros HΣfresh Htmfresh Hτfresh Hlc_elam.
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas Σ τ
    (tapp_tm (tm_shift 0 elam) (vbvar 0)))
    by (exact HΣfresh || exact Htmfresh || exact Hτfresh).
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc_elam.
  reflexivity.
Qed.

Lemma lamd_wand_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  n ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env
      (<[y := erase_ty τx]> (store_restrict Σ (fv_cty τx))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret (vlam (erase_ty τx) e)) τx τ Hwf) as Hτx_global.
  rewrite ty_denote_gas_saturate in Harg by
    (rewrite cty_open_preserves_depth, cty_shift_preserves_depth; lia).
  rewrite cty_open_preserves_depth, cty_shift_preserves_depth in Harg.
  assert (Hτnorm :
      cty_open 0 y (cty_shift 0 τx) = τx).
  {
	    apply cty_open_shift_from_lc_fresh.
	    - eapply wf_context_ty_at_lc. exact Hτx_global.
	    - eapply lam_wand_fresh_arg_ty. exact Hy.
  }
  rewrite Hτnorm in Harg.
  eapply ty_denote_gas_ret_fvar_insert_closed_atom_env; eauto.
Qed.

Lemma lamd_wand_open_arg_normalize
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros Hy Harg.
  assert (HΣarg_fresh :
      y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_dom_subset_direct
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
    intros Hyfv.
    apply lvars_fv_elem in Hyfv.
    pose proof (Hrel _ Hyfv) as Hatom.
    rewrite atom_store_to_lvar_store_dom in Hatom.
    rewrite <- lvars_fv_elem in Hatom.
    rewrite lvars_fv_of_atoms in Hatom.
    eapply lam_wand_fresh_erase_ctx in Hy. exact (Hy Hatom).
  }
  eapply wand_open_arg_to_inserted_env; eauto.
  - apply atom_store_to_lvar_store_closed.
  - apply atom_env_to_lty_env_dom_free_notin.
    eapply lam_wand_fresh_erase_ctx. exact Hy.
  - eapply lam_wand_fresh_arg_ty. exact Hy.
Qed.

Lemma lamd_open_arg_to_star_ctx
    (Σ : tyctx) Γ τx τ e
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	      ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
	      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
	  res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)).
	Proof.
  intros Hwf Hctx Hdom Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret (vlam (erase_ty τx) e)) τx τ Hwf) as Hτx_global.
  pose proof (lamd_wand_open_arg_to_bind_denotation
    Σ Γ τx τ e n y Hwf Hy Harg) as Harg_den.
  assert (Hbind_cropped :
      n ⊨ ctx_denote_under (store_restrict Σ (fv_cty τx))
        (CtxBind y τx)).
  {
    eapply ctx_bind_from_base_denotation.
    - eapply wf_context_ty_at_mono_env; [|exact Hτx_global].
      better_set_solver.
    - intros HyΣ.
      apply Hy.
      rewrite storeA_restrict_dom in HyΣ.
      better_set_solver.
    - exact Harg_den.
  }
  assert (Hbind : n ⊨ ctx_denote_under Σ (CtxBind y τx)).
  {
    rewrite ctx_denote_under_minimal.
    exact Hbind_cropped.
  }
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  destruct (res_product_comm_eq n m Hc) as [Hcmn Heq].
  rewrite Heq.
  eapply ctx_denote_under_star_intro_product; eauto.
Qed.

Lemma lamd_body_to_wand_result_mid
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
	    ({0 ~> y} τ) (e ^^ y) ->
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
  intros Hwf Hy Hbody Hstatic.
  set (elam := tret (vlam (erase_ty τx) e)).
  assert (HyΓ : y ∉ dom (erase_ctx Γ)).
  { eapply lam_wand_fresh_erase_ctx. exact Hy. }
  pose proof (ty_denote_under_star_bind_to_lvar_insert_direct
    Σ Γ τx ({0 ~> y} τ) (e ^^ y) y my HyΓ Hbody) as Hbody_insert.
  assert (Hmid_body :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ) (e ^^ y)).
  {
    replace ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
      with (<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))).
	    2:{ lty_env_open_bind_norm. reflexivity. }
    change (cty_open 0 y τ) with ({0 ~> y} τ).
    rewrite ty_denote_gas_saturate by
      (rewrite cty_open_preserves_depth; lia).
    exact Hbody_insert.
  }
  assert (Hzero_body :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ) (e ^^ y)).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hmid_body.
  }
  assert (Hfull_guard :
      my ⊨ ty_guard_formula
        (relevant_env
          ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
          (cty_open 0 y τ)
          (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
	  {
	    unfold ty_guard_formula.
	    pose proof (ty_static_guard_relevant_of_full _ _ _ _ Hstatic)
	      as Hstatic_rel.
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
      Σ Γ (erase_ty τx) e (CTWand τx τ) Hwf) as Hbody_lc.
    assert (Hy_dom : y ∈ world_dom (my : WorldT)).
    {
      apply Hfv_app.
      cbn [fv_tm fv_value]. better_set_solver.
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
			    pose proof (tm_total_equiv_lam_app_body
			      (erase_ty τx) e y my Hclosed Hbody_lc
			      ltac:(eapply lam_wand_fresh_tm; exact Hy)
			      Hy_dom) as Htotal_eq.
	    eapply tm_equiv_total;
	      [ exact Htotal_eq
	      | exact Hlc_app
	      | exact Hfv_app
	      | exact Htotal_body ].
	  }
  assert (Hzero_app :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
  { apply ty_denote_gas_zero_of_guard. exact Hfull_guard. }
  assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard. exact Hmid_body.
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
    Σ Γ (erase_ty τx) e (CTWand τx τ) Hwf) as Hbody_lc.
  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
  {
    pose proof Hfull_guard as Hguard_app.
    unfold ty_guard_formula in Hguard_app.
    repeat rewrite res_models_and_iff in Hguard_app.
    destruct Hguard_app as [_ [Hworld_app [Hbasic_app _]]].
    apply expr_basic_typing_formula_models_iff in Hbasic_app
      as [_ [_ Hbasic_ltype_app]].
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
      as Hfv_lvars_app.
    apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope_app _]].
    apply Hscope_app.
    apply (proj2 (lvars_fv_elem _ y)).
    apply Hfv_lvars_app.
    unfold lvars_of_atoms.
    apply elem_of_map. exists y. split; [reflexivity|].
    cbn [fv_tm fv_value]. better_set_solver.
  }
  assert (Happ_mid :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
		  {
		    eapply lam_intro_denotation; eauto.
		    eapply lam_wand_fresh_tm. exact Hy.
		  }
  exact Happ_mid.
Qed.

Lemma lamd_wand_result_mid_to_opened_goal
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
  intros Hwf Hy Happ_mid.
  set (elam := tret (vlam (erase_ty τx) e)).
  assert (Hlc_elam : lc_tm elam).
  {
    subst elam.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  }
  assert (HΣfresh :
      y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) elam)
          (erase_ty τx)))).
  {
    subst elam.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_dom_subset_direct
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
    intros Hyfv.
    apply lvars_fv_elem in Hyfv.
    pose proof (Hrel _ Hyfv) as Hatom.
    rewrite atom_store_to_lvar_store_dom in Hatom.
	    rewrite <- lvars_fv_elem in Hatom.
	    rewrite lvars_fv_of_atoms in Hatom.
	    eapply lam_wand_fresh_erase_ctx in Hy. exact (Hy Hatom).
	  }
	  assert (Htmfresh :
	      y ∉ fv_tm (tapp_tm (tm_shift 0 elam) (vbvar 0))).
		    {
		      subst elam.
		      eapply lam_wand_shifted_tapp_fresh. exact Hy.
		    }
	  subst elam.
	  assert (Happ_mid_open :
	      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 y
          (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ))
            (erase_ty τx)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current.
    - exact Happ_mid.
	    - apply atom_env_to_lty_env_dom_free_notin.
	      eapply lam_wand_fresh_erase_ctx. exact Hy.
    - apply atom_store_to_lvar_store_closed.
	  }
		  pose proof (lam_wand_open_shifted_tapp_denote_iff
	    (Nat.max (cty_depth τx) (cty_depth τ))
	    (typed_lty_env_bind
	      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
	        (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
	      (erase_ty τx))
	    τ (tret (vlam (erase_ty τx) e)) my y
	    HΣfresh Htmfresh
	    ltac:(eapply lam_wand_fresh_result_ty; exact Hy)
	    Hlc_elam) as [_ Hnorm_to_open].
	  apply Hnorm_to_open.
	  eapply ty_equiv_wand_result_tgt_goal.
	  - exact Hlc_elam.
	  - better_set_solver.
	  - exact Happ_mid_open.
Qed.

Lemma lamd_opened_wand_result
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  res_product n m Hc ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
  intros Hwf IH Hctx Hdom Hy Harg.
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
  assert (Hctx_star :
      res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx))).
  {
    eapply (lamd_open_arg_to_star_ctx Σ Γ τx τ e m n y Hc).
    - exact Hwf.
    - exact Hctx.
    - exact Hdom.
    - exact Hy_rest.
    - exact Harg.
  }
  pose proof (IH y HyL (res_product n m Hc) Hctx_star) as Hbody.
		  pose proof (lam_wand_opened_app_static_guard_full
		    Σ Γ τx τ e (res_product n m Hc) y
		    Hwf Hy_rest Hctx_star) as Hstatic_app.
  pose proof (lamd_body_to_wand_result_mid
    Σ Γ τx τ e (res_product n m Hc) y
    Hwf Hy_rest Hbody Hstatic_app) as Happ_mid.
  eapply (lamd_wand_result_mid_to_opened_goal
    Σ Γ τx τ e (res_product n m Hc) y).
  - exact Hwf.
  - exact Hy_rest.
  - exact Happ_mid.
Qed.

Lemma lam_result_first_wand_value_denotation
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (formula_open 0 z
      (wand_value_denote_gas_with ty_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty (CTWand τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0)))) ->
  mz ⊨ expr_result_formula (tret (vlam (erase_ty τx) e)) (LVFree z) ->
  mz ⊨ formula_open 0 z
      (wand_value_denote_gas_with ty_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty (CTWand τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))).
Proof.
  intros Hwf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (vf := vlam (erase_ty τx) e).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTWand τx τ) (tret vf)).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf)
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  cbn [formula_open wand_value_denote_gas_with] in Hscope_value |- *.
  eapply res_models_fbwand_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  intros η n Hc Hbind Hηfresh Hdom_prod Harg_raw.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite formula_open_env_singleton in Harg_raw |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
  rewrite open_env_atoms_empty in Hdom_prod.
	  assert (Hdom_y :
	      world_dom (res_product n mz Hc : WorldT) =
	        world_dom (mz : WorldT) ∪ ({[y]} : aset)).
	  {
	    rewrite Hdom_prod. apply union_singleton_empty_r.
	  }
  assert (Hy_fresh :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  {
    clear -Hηfresh. set_solver.
  }
	  assert (Hy_rest :
	      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
	        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
	  { clear -Hy_fresh. better_set_solver. }
		  assert (Hy_eraseΓ : y ∉ dom (erase_ctx Γ)).
		  { eapply lam_wand_fresh_erase_ctx. exact Hy_rest. }
	  assert (HyΔ : LVFree y ∉ dom Δ).
	  {
	    subst Δ. apply atom_env_to_lty_env_dom_free_notin.
	    exact Hy_eraseΓ.
	  }
	  assert (HyL : y ∉ L) by (clear -Hy_fresh; better_set_solver).
  assert (Hyz : y <> z) by (clear -Hy_fresh; set_solver).
  assert (Harg_norm :
      n ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        τx (tret (vfvar y))).
  {
    change (n ⊨ formula_open 0 y
      (formula_open 1 z
        (ty_denote_gas gas
          (typed_lty_env_bind
            (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
            (erase_ty (cty_shift 0 τx)))
          (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))))
      in Harg_raw.
    rewrite (formula_open_result_first_fun_arg_two
      gas Σrel τx (erase_ty (CTWand τx τ)) z y) in Harg_raw.
    - exact Harg_raw.
    - subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
    - subst Σrel. apply relevant_env_wand_fresh_free;
        cbn [fv_tm fv_value]; clear -Hz; better_set_solver.
    - exact Hyz.
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hyz. congruence.
      + subst Σrel. apply relevant_env_wand_fresh_free in Hin;
          cbn [fv_tm fv_value]; clear -Hy_fresh Hin; better_set_solver.
    - exact Hτx_lc.
    - clear -Hz. better_set_solver.
    - clear -Hy_fresh. better_set_solver.
  }
  assert (Harg_old :
      n ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
    rewrite cty_open_shift_from_lc_fresh by
      (exact Hτx_lc || clear -Hy_fresh; better_set_solver).
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by exact Hyz.
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTWand τx τ)) Hz_rel_arg).
      apply lamd_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst vf. clear -Hy_fresh. cbn [fv_value]. better_set_solver.
    - exact Harg_norm.
  }
  pose proof (lamd_opened_wand_result
    Σ Γ τx τ e L mz n y Hc
    Hwf IH Hctx_mz Hdom_y
    ltac:(clear -Hy_fresh; better_set_solver)
    Harg_old) as Hopened_src.
  assert (Hopened_norm :
      res_product n mz Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind Σrel (erase_ty τx)))
        (cty_open 0 y τ)
        (tapp_tm (tret vf) (vfvar y))).
  {
    subst gas Σrel vf.
    set (elam := tret (vlam (erase_ty τx) e)).
    assert (Hlc_elam : lc_tm elam).
    {
      subst elam.
      exact (context_typing_wf_lc_tm
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
    }
    assert (HΣfresh :
        y ∉ lvars_fv
          (dom (typed_lty_env_bind
            (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
              (CTWand τx τ) elam)
            (erase_ty τx)))).
    {
      subst elam.
      rewrite typed_lty_env_bind_lvars_fv_dom.
      pose proof (relevant_env_dom_subset_direct
        (atom_env_to_lty_env (erase_ctx Γ))
        (CTWand τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
      intros Hyfv.
      apply lvars_fv_elem in Hyfv.
	      pose proof (Hrel _ Hyfv) as Hatom.
	      rewrite atom_store_to_lvar_store_dom in Hatom.
	      rewrite <- lvars_fv_elem in Hatom.
	      rewrite lvars_fv_of_atoms in Hatom.
	      exact (Hy_eraseΓ Hatom).
    }
	    assert (Htmfresh :
	        y ∉ fv_tm (tapp_tm (tm_shift 0 elam) (vbvar 0))).
		    {
		      subst elam.
		      eapply lam_wand_shifted_tapp_fresh. exact Hy_rest.
		    }
	    change (res_product n mz Hc ⊨ formula_open 0 y
	      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	        (typed_lty_env_bind
	          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
	            (CTWand τx τ) elam)
	          (erase_ty τx))
	        τ (tapp_tm (tm_shift 0 elam) (vbvar 0)))) in Hopened_src.
		    pose proof (lam_wand_open_shifted_tapp_denote_iff
	      (Nat.max (cty_depth τx) (cty_depth τ))
	      (typed_lty_env_bind
	        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
	          (CTWand τx τ) elam)
	        (erase_ty τx))
	      τ elam (res_product n mz Hc) y
	      HΣfresh Htmfresh
	      ltac:(eapply lam_wand_fresh_result_ty; exact Hy_rest)
	      Hlc_elam) as [Hopen_to_norm _].
	    apply Hopen_to_norm. exact Hopened_src.
  }
  assert (Hsrc_open :
      res_product n mz Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Δ (erase_ty τx)))
        (cty_open 0 y τ)
        (tapp_tm (tret vf) (vfvar y))).
  {
    eapply ty_equiv_wand_result_src_mid.
    - subst vf.
      exact (context_typing_wf_lc_tm
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
    - clear -Hy_rest. better_set_solver.
    - exact Hopened_norm.
  }
  assert (Hsrc :
      res_product n mz Hc ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Δ)
        (cty_open 0 y τ)
        (tapp_tm (tret vf) (vfvar y))).
  {
	    rewrite <- (typed_lty_env_bind_open_current y Δ (erase_ty τx)).
	    - exact Hsrc_open.
	    - exact HyΔ.
	    - apply atom_store_to_lvar_store_closed.
  }
  assert (Hctx_star :
      res_product n mz Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx))).
  {
    eapply (lamd_open_arg_to_star_ctx Σ Γ τx τ e mz n y Hc).
    - exact Hwf.
    - exact Hctx_mz.
    - exact Hdom_y.
    - exact Hy_rest.
    - exact Harg_old.
  }
  pose proof (lam_wand_opened_app_static_guard_full
    Σ Γ τx τ e (res_product n mz Hc) y
    Hwf Hy_rest Hctx_star) as Hstatic_app.
  assert (Hres_prod :
      res_product n mz Hc ⊨ expr_result_formula (tret vf) (LVFree z)).
  {
    subst vf.
    eapply res_models_kripke; [apply res_product_le_r|exact Hres_z].
  }
  assert (Hfun_basic :
      res_product n mz Hc ⊨ expr_basic_typing_formula
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
            Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
	        * apply insert_subseteq. apply not_elem_of_dom.
	          exact HyΔ.
  }
  assert (Hlc_vf : lc_value vf).
  {
    subst vf.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    rewrite dom_insert_L.
    intros Hzdom.
    apply elem_of_union in Hzdom as [Hzdom|Hzdom].
    - apply elem_of_singleton in Hzdom. inversion Hzdom. subst.
      clear -Hyz. congruence.
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
    clear -Hy_fresh Hz Hτopen. better_set_solver.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    vf y z (erase_ty τx) (res_product n mz Hc)
    Hz_insert_env
    Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_vf
    Hres_prod Hfun_basic Hstatic_app Hsrc) as Htarget_alias.
  change (res_product n mz Hc ⊨ formula_open 0 y
    (formula_open 1 z
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τ)
        (tapp_tm (tret (vbvar 1)) (vbvar 0))))).
  rewrite (formula_open_result_first_fun_result_two
    gas Σrel τx τ (erase_ty (CTWand τx τ)) z y).
  2:{ subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{ subst Σrel. apply relevant_env_wand_fresh_free;
      cbn [fv_tm fv_value]; clear -Hz; better_set_solver. }
  2:{ exact Hyz. }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hyz. congruence.
    - subst Σrel. apply relevant_env_wand_fresh_free in Hin;
        cbn [fv_tm fv_value]; clear -Hy_fresh Hin; better_set_solver.
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
  - apply lamd_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      * intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_rest HyD. better_set_solver.
      * reflexivity.
    + exact Hyz.
    + clear -Hy_rest. better_set_solver.
    + subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.
