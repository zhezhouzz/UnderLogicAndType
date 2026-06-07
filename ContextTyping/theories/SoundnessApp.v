(** * ContextTyping.SoundnessApp

    App proof support for the direct Fundamental theorem.
    Keeping this case in a focused file makes timing diagnostics local and
    avoids re-checking the full Fundamental dispatch while proving Arrow
    application transport. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma app_arrow_arg_to_opened_antecedent
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ formula_open 0 x
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros Hwf_fun Hfresh Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hxlookup : Δ !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup (cty_depth τx) Δ τx x m Harg). }
  assert (Hopen_env_fresh :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ (CTArrow τx τ) (tret v1)) (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_fv_subset
      Δ (CTArrow τx τ) (tret v1)) as Hrel_fv.
    intros Hbad.
    apply Hrel_fv in Hbad.
    exfalso. apply Hfresh.
    cbn [fv_tm fv_value] in Hbad.
    unfold fv_cty in Hbad.
    cbn [context_ty_lvars context_ty_lvars_at] in Hbad.
    rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hbad.
    better_set_solver.
  }
  assert (Hopen_tm_fresh : x ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  assert (Hopen_ty_fresh : x ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. better_set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ (CTArrow τx τ) (tret v1)) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))
    Hopen_env_fresh Hopen_tm_fresh Hopen_ty_fresh).
  change (open_tm 0 (vfvar x) (tret (vbvar 0))) with (tret (vfvar x)).
  assert (Hτx_norm : cty_open 0 x (cty_shift 0 τx) = τx).
  {
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret v1) (CTArrow τx τ) Hwf_fun) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    apply cty_open_shift_from_lc_fresh.
    - eapply wf_context_ty_at_lc. exact Hτx.
    - better_set_solver.
  }
  rewrite Hτx_norm.
  assert (Hrel_env_fresh :
      LVFree x ∉ dom (relevant_env Δ (CTArrow τx τ) (tret v1) : lty_env)).
  {
    apply relevant_env_arrow_fresh_free; better_set_solver.
  }
  assert (Hrel_env_closed :
      lty_env_closed (relevant_env Δ (CTArrow τx τ) (tret v1))).
  { apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  rewrite (typed_lty_env_bind_open_current
    x (relevant_env Δ (CTArrow τx τ) (tret v1)) (erase_ty τx)
    Hrel_env_fresh Hrel_env_closed).
  assert (Harg_big :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        Δ τx (tret (vfvar x))).
  {
    rewrite ty_denote_gas_saturate by (cbn [cty_depth]; lia).
    exact Harg.
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    Δ
    (<[LVFree x := erase_ty τx]>
      (relevant_env Δ (CTArrow τx τ) (tret v1)))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x))) m).
  - reflexivity.
  - apply lty_env_restrict_relevant_arrow_arg_insert_eq; assumption.
  - exact Harg_big.
Qed.

Lemma app_arrow_result_to_target
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ formula_open 0 x
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))
          (erase_ty τx))
        τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))) ->
  m ⊨ ty_denote_gas (cty_depth ({0 ~> x} τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf Hfresh Harg Hopened.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  pose proof (context_typing_wf_app_fun_lc_value
    Σ Γ v1 (vfvar x) ({0 ~> x} τ) Hwf) as Hlc_v1.
  assert (HΣfresh :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ (CTArrow τx τ) (tret v1))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hxfv.
    apply lvars_fv_elem in Hxfv.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_arrow_fresh_free
      Δ τx τ (tret v1) x
      ltac:(better_set_solver) ltac:(better_set_solver) Hxv1 Hxfv).
  }
  assert (Htmfresh :
      x ∉ fv_tm (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    better_set_solver.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ (CTArrow τx τ) (tret v1))
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0)))
    in Hopened
    by (exact HΣfresh || exact Htmfresh || better_set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc in Hopened
    by (constructor; exact Hlc_v1).
  assert (Hsrc_mid :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 x (typed_lty_env_bind Δ (erase_ty τx)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    pose proof (ty_equiv_arrow_result_src_mid
      (Nat.max (cty_depth τx) (cty_depth τ))
      Δ τx τ (tret v1) m x
      ltac:(constructor; exact Hlc_v1)
      ltac:(better_set_solver) Hopened) as Hmid.
    exact Hmid.
  }
  assert (HΔx : Δ !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup (cty_depth τx) Δ τx x m Harg). }
  assert (Hzero_src :
      m ⊨ ty_denote_gas 0
        (lty_env_open_one 0 x (typed_lty_env_bind Δ (erase_ty τx)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hsrc_mid.
  }
  assert (Hequiv :
      tm_equiv_on m
        (tapp_tm (tret v1) (vfvar x))
        (tapp v1 (vfvar x))).
  {
    pose proof (denot_ty_lvar_guard_wfworld_closed_on_term
      (lty_env_open_one 0 x (typed_lty_env_bind Δ (erase_ty τx)))
      (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x)) m
      (ty_denote_gas_guard_of_zero _ _ _ _ Hzero_src))
      as Hclosed_src.
    assert (Hclosed_apps :
        wfworld_closed_on
          (fv_tm (tapp_tm (tret v1) (vfvar x)) ∪
           fv_tm (tapp v1 (vfvar x))) m).
    {
      eapply wfworld_closed_on_mono; [|exact Hclosed_src].
      rewrite fv_tapp_tm.
      cbn [fv_tm fv_value].
      better_set_solver.
    }
    exact (tm_eval_in_world_tapp_tm_ret_equiv m v1 x Hlc_v1 Hclosed_apps).
  }
  assert (Hzero_tgt :
      m ⊨ ty_denote_gas 0
        (lty_env_open_one 0 x (typed_lty_env_bind Δ (erase_ty τx)))
        (cty_open 0 x τ) (tapp v1 (vfvar x))).
  {
    pose proof (ty_denote_gas_guard_of_zero
      (lty_env_open_one 0 x (typed_lty_env_bind Δ (erase_ty τx)))
      (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x)) m Hzero_src) as Hguard_src.
    repeat rewrite res_models_and_iff in Hguard_src.
    destruct Hguard_src as [Hwf_src [Hworld_src [Hbasic_src Htotal_src]]].
    set (Σopen := lty_env_open_one 0 x
      (typed_lty_env_bind Δ (erase_ty τx))).
    assert (Hrel_env_eq :
        relevant_env Σopen (cty_open 0 x τ)
          (tapp_tm (tret v1) (vfvar x)) =
        relevant_env Σopen (cty_open 0 x τ)
          (tapp v1 (vfvar x))).
    {
      unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
      rewrite tm_lvars_tapp_tm_fvar.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
      better_set_solver.
    }
    assert (Hworld_tgt :
        m ⊨ basic_world_formula
          (relevant_env Σopen (cty_open 0 x τ)
            (tapp v1 (vfvar x)))).
    { rewrite <- Hrel_env_eq. exact Hworld_src. }
    apply ty_denote_gas_zero_of_guard.
    repeat rewrite res_models_and_iff.
    split.
    - eapply context_ty_wf_formula_relevant_env_change_term.
      + exact Hworld_tgt.
      + exact Hwf_src.
    - split.
      + exact Hworld_tgt.
      + split.
        * apply expr_basic_typing_formula_models_iff.
          apply basic_world_formula_models_iff in Hworld_tgt
            as [HlcΣ [Hscope_src _]].
          split; [exact HlcΣ|]. split; [exact Hscope_src|].
          rewrite cty_open_preserves_erasure.
          pose proof (context_typing_wf_basic_typing Σ Γ
            (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf) as Hbasic_app.
          change (erase_ty ({0 ~> x} τ)) with (erase_ty (cty_open 0 x τ)) in Hbasic_app.
          rewrite cty_open_preserves_erasure in Hbasic_app.
          pose proof (basic_tm_has_ltype_of_atom_env_typing
            (erase_ctx Γ) (tapp v1 (vfvar x)) (erase_ty τ)
            Hbasic_app) as Hbasic_lΔ.
          eapply basic_tm_has_ltype_env_agree_lc.
          -- exact Hbasic_lΔ.
          -- constructor; [exact Hlc_v1|constructor].
          -- unfold Σopen.
             apply lty_env_restrict_open_one_bind_relevant_tapp_eq;
               assumption.
        * eapply tm_equiv_total.
          -- exact Hequiv.
          -- constructor; [exact Hlc_v1|constructor].
          -- apply expr_basic_typing_formula_models_iff in Hbasic_src
               as [_ [_ Hbasic_src_lty]].
             apply basic_world_formula_models_iff in Hworld_src
               as [_ [Hscope_world_src _]].
             pose proof (basic_tm_has_ltype_lvars _ _ _
               Hbasic_src_lty) as Hsrc_lvars.
             intros z Hz.
             apply Hscope_world_src.
             apply lvars_fv_elem.
             apply Hsrc_lvars.
             cbn [fv_tm fv_value] in Hz.
             unfold lvars_of_atoms.
             apply elem_of_map.
             exists z. split; [reflexivity|].
             rewrite fv_tapp_tm.
             cbn [fv_tm fv_value].
             exact Hz.
          -- exact Htotal_src.
  }
  assert (Htarget_insert :
      m ⊨ ty_denote_gas (cty_depth (cty_open 0 x τ))
        (lty_env_open_one 0 x (typed_lty_env_bind Δ (erase_ty τx)))
        (cty_open 0 x τ) (tapp v1 (vfvar x))).
  {
    eapply ty_denote_gas_tm_equiv.
    - split; [exact Hequiv|split; [exact Hzero_src|exact Hzero_tgt]].
    - rewrite ty_denote_gas_saturate in Hsrc_mid by
        (rewrite cty_open_preserves_depth; lia).
      exact Hsrc_mid.
  }
  rewrite cty_open_preserves_depth in Htarget_insert.
  change ({0 ~> x} τ) with (cty_open 0 x τ).
  rewrite cty_open_preserves_depth.
  assert (Htarget_rel_lc :
      lc_lvars (relevant_lvars (cty_open 0 x τ)
        (tapp v1 (vfvar x)))).
  {
    unfold relevant_lvars.
    intros v Hv.
    apply elem_of_union in Hv as [Hvτ|Hve].
    - pose proof (context_typing_wf_context_ty Σ Γ
        (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf) as Hτwf.
      change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτwf.
      pose proof (cty_lc_at_lvars_bv_empty 0 (cty_open 0 x τ)
        (wf_context_ty_at_lc 0 (dom (erase_ctx Γ))
          (cty_open 0 x τ) Hτwf)) as Hbv.
      destruct v as [k|y]; [|exact I].
      exfalso.
      assert (k ∈ lvars_bv (context_ty_lvars (cty_open 0 x τ)))
        by (apply lvars_bv_elem; exact Hvτ).
      change (context_ty_lvars (cty_open 0 x τ))
        with (context_ty_lvars_at 0 (cty_open 0 x τ)) in H.
      rewrite Hbv in H. set_solver.
    - pose proof (tm_lvars_lc (tapp v1 (vfvar x))
        ltac:(constructor; [exact Hlc_v1|constructor])) as Hlc_tm.
      exact (Hlc_tm v Hve).
  }
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - exact (lty_env_restrict_open_one_bind_current_eq
      Δ (relevant_lvars (cty_open 0 x τ) (tapp v1 (vfvar x)))
      x (erase_ty τx) HΔx Htarget_rel_lc).
  - exact Htarget_insert.
Qed.

Lemma app_arrow_open_result_from_fresh_drop
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v1) ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ ty_denote_gas (cty_depth ({0 ~> x} τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf_fun Hwf Hfresh Hfun Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (mdel := res_restrict m (world_dom (m : WorldT) ∖ {[x]})).
  pose proof (ty_denote_gas_restrict_delete_fresh
    (cty_depth (CTArrow τx τ)) Δ (CTArrow τx τ) (tret v1)
    x m ltac:(unfold fv_cty; cbn [fv_tm fv_value context_ty_lvars
      context_ty_lvars_at]; rewrite lvars_fv_union,
      !context_ty_lvars_fv_at; better_set_solver) Hfun) as Hfun_del.
  cbn [cty_depth ty_denote_gas] in Hfun_del.
  rewrite res_models_and_iff in Hfun_del.
  destruct Hfun_del as [_ Hforall].
  assert (Hx_mdel : x ∉ world_dom (mdel : WorldT)).
  {
    subst mdel. apply res_restrict_delete_notin.
  }
  assert (Hdom_mdel :
      world_dom (m : WorldT) = world_dom (mdel : WorldT) ∪ {[x]}).
  {
    pose proof (ty_denote_gas_ret_fvar_world_dom
      (cty_depth τx) Δ τx x m Harg) as Hxm.
    subst mdel. exact (res_restrict_delete_insert_dom m x Hxm).
  }
  assert (Hrestrict_mdel :
      res_restrict m (world_dom (mdel : WorldT)) = mdel).
  {
    subst mdel. apply res_restrict_self_dom.
  }
  pose proof (res_models_forall_open_named_fresh
    mdel m x _ Hforall Hx_mdel Hdom_mdel Hrestrict_mdel) as Hopened.
  rewrite formula_open_impl in Hopened.
  pose proof (app_arrow_arg_to_opened_antecedent
    Σ Γ τx τ v1 x m Hwf_fun Hfresh Harg) as Harg_open.
  pose proof (res_models_impl_elim m _ _ Hopened Harg_open) as Hres_open.
  subst Δ.
  eapply app_arrow_result_to_target; eauto.
Qed.

Lemma fundamental_app_case Σ Γ τx τ v1 x :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τx (tret (vfvar x))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf_fun Hwf Hfresh HfunIH HargIH m Hctx.
  pose proof (HfunIH m Hctx) as Hfun.
  pose proof (HargIH m Hctx) as Harg.
  unfold ty_denote_under, ty_denote in Hfun, Harg |- *.
  eapply app_arrow_open_result_from_fresh_drop; eauto.
Qed.
