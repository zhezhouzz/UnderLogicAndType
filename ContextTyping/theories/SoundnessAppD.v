(** * ContextTyping.SoundnessAppD

    AppD proof support for the direct Fundamental theorem. *)

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
From ContextTyping Require Import Typing SoundnessApp.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma appd_arg_singleton_env_to_wand_arg
    Σ Γ1 Γ2 τx τ v1 x (m2 : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m2 ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ2))
        τx (tret (vfvar x)) ->
  res_restrict m2 ({[x]} : aset) ⊨ formula_open 0 x
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros Hwf_fun Hfresh Harg.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δ2 := atom_env_to_lty_env (erase_ctx Γ2)) in *.
  assert (Hτx_closed : wf_context_ty_at 0 ∅ τx).
  { exact (context_typing_wf_wand_arg_global
      Σ Γ1 (tret v1) τx τ Hwf_fun). }
  pose proof (ty_denote_gas_restrict_ret_fvar_closed
    (cty_depth τx) Δ2 τx x m2 Hτx_closed Harg) as Hargx.
  assert (Hxlookup : Δ2 !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup
      (cty_depth τx) Δ2 τx x (res_restrict m2 ({[x]} : aset)) Hargx). }
  assert (Hopen_env_fresh :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ1 (CTWand τx τ) (tret v1)) (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_wand_fresh_free
      Δ1 τx τ (tret v1) x Hxτx Hxτ Hxv1 Hbad).
  }
  assert (Hopen_tm_fresh : x ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  assert (Hopen_ty_fresh : x ∉ fv_cty (cty_shift 0 τx)).
  {
    rewrite cty_shift_fv.
    pose proof (wf_context_ty_at_fv_subset 0 ∅ τx Hτx_closed).
    better_set_solver.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ1 (CTWand τx τ) (tret v1)) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))
    Hopen_env_fresh Hopen_tm_fresh Hopen_ty_fresh).
  change (open_tm 0 (vfvar x) (tret (vbvar 0))) with (tret (vfvar x)).
  rewrite (cty_open_shift_from_lc_fresh 0 x τx).
  2:{
    eapply wf_context_ty_at_lc. exact Hτx_closed.
  }
  2:{
    pose proof (wf_context_ty_at_fv_subset 0 ∅ τx Hτx_closed).
    better_set_solver.
  }
  rewrite (typed_lty_env_bind_open_current
    x (relevant_env Δ1 (CTWand τx τ) (tret v1)) (erase_ty τx)).
  2:{
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_wand_fresh_free
      Δ1 τx τ (tret v1) x Hxτx Hxτ Hxv1).
  }
  2:{
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Harg_big :
      res_restrict m2 ({[x]} : aset) ⊨
        ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
          Δ2 τx (tret (vfvar x))).
  {
    rewrite ty_denote_gas_saturate by (cbn [cty_depth]; lia).
    exact Hargx.
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    Δ2
    (<[LVFree x := erase_ty τx]>
      (relevant_env Δ1 (CTWand τx τ) (tret v1)))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x)))
    (res_restrict m2 ({[x]} : aset))).
  - reflexivity.
  - eapply lty_env_restrict_relevant_ret_fvar_closed_eq.
    + exact Hτx_closed.
    + exact Hxlookup.
    + apply map_lookup_insert.
  - exact Harg_big.
Qed.

Lemma appd_arg_product_to_star_env
    Σ Γ1 Γ2 τx τ v1 x (m1 m2 : WfWorldT)
    (Hc : world_compat (res_restrict m2 ({[x]} : aset)) m1) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  m2 ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ2))
        τx (tret (vfvar x)) ->
  res_product (res_restrict m2 ({[x]} : aset)) m1 Hc ⊨
    ty_denote_gas (cty_depth τx)
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
      τx (tret (vfvar x)).
Proof.
  intros Hwf_fun Hwf_app Harg.
  pose proof (context_typing_wf_wand_arg_global
    Σ Γ1 (tret v1) τx τ Hwf_fun) as Hτx_closed.
  pose proof (ty_denote_gas_restrict_ret_fvar_closed
    (cty_depth τx) (atom_env_to_lty_env (erase_ctx Γ2))
    τx x m2 Hτx_closed Harg) as Hargx.
  assert (Hargx_prod :
      res_product (res_restrict m2 ({[x]} : aset)) m1 Hc ⊨
        ty_denote_gas (cty_depth τx)
          (atom_env_to_lty_env (erase_ctx Γ2))
          τx (tret (vfvar x))).
  {
    eapply res_models_kripke; [apply res_product_le_l|exact Hargx].
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (cty_depth τx)
    (atom_env_to_lty_env (erase_ctx Γ2))
    (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x)))
    (res_product (res_restrict m2 ({[x]} : aset)) m1 Hc)).
  - reflexivity.
  - pose proof (ty_denote_gas_ret_fvar_lookup
      (cty_depth τx) (atom_env_to_lty_env (erase_ctx Γ2))
      τx x m2 Harg) as HxΓ2.
    eapply lty_env_restrict_relevant_ret_fvar_closed_eq.
    + exact Hτx_closed.
    + exact HxΓ2.
    + rewrite atom_store_to_lvar_store_lookup_free.
      pose proof (context_typing_wf_ctx Σ (CtxStar Γ1 Γ2)
        (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hwfctx.
      pose proof (wf_ctx_under_basic Σ (CtxStar Γ1 Γ2) Hwfctx) as Hbasic.
      cbn [basic_ctx] in Hbasic.
      destruct Hbasic as [Hbasic1 [Hbasic2 Hdisj]].
      rewrite atom_store_to_lvar_store_lookup_free in HxΓ2.
      eapply erase_ctx_star_lookup_r_of_basic; eauto.
  - exact Hargx_prod.
Qed.

Lemma appd_open_result_env_agree
    Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 x
      (typed_lty_env_bind
        (atom_env_to_lty_env (erase_ctx Γ1)) (erase_ty τx)))
    (relevant_lvars (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 x
      (typed_lty_env_bind
        (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))) (erase_ty τx)))
    (relevant_lvars (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x))).
Proof.
  intros Hwf_fun Hwf_app.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ1 v1 (CTWand τx τ) Hwf_fun) as Hlc_v1.
  assert (Hrel_lc :
      lc_lvars (relevant_lvars (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)))).
  {
    unfold relevant_lvars. intros u Hu.
    apply elem_of_union in Hu as [Huτ|Hue].
    - pose proof (context_typing_wf_context_ty Σ (CtxStar Γ1 Γ2)
        (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hτwf.
      change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτwf.
      pose proof (cty_lc_at_lvars_bv_empty 0 (cty_open 0 x τ)
        (wf_context_ty_at_lc 0 (dom (erase_ctx (CtxStar Γ1 Γ2)))
          (cty_open 0 x τ) Hτwf)) as Hbv.
      destruct u as [k|a]; [|exact I].
      exfalso.
      assert (k ∈ lvars_bv (context_ty_lvars (cty_open 0 x τ)))
        by (apply lvars_bv_elem; exact Huτ).
      change (context_ty_lvars (cty_open 0 x τ))
        with (context_ty_lvars_at 0 (cty_open 0 x τ)) in H.
      rewrite Hbv in H. set_solver.
    - pose proof (tm_lvars_lc (tapp_tm (tret v1) (vfvar x))
        ltac:(apply lc_tapp_tm; [constructor; exact Hlc_v1|constructor])) as Hlc_tm.
      exact (Hlc_tm u Hue).
  }
  eapply lty_env_restrict_open_one_bind_agree_on.
  - exact Hrel_lc.
  - intros y HyD Hyx.
    rewrite !atom_store_to_lvar_store_lookup_free.
    destruct (decide (y ∈ fv_value v1 ∪ fv_cty τ)) as [Hyrel|Hyrel].
    + assert (HyΓ1 : y ∈ dom (erase_ctx Γ1)).
        {
          pose proof (context_typing_wf_basic_typing Σ Γ1
            (tret v1) (CTWand τx τ) Hwf_fun) as Hbasic_fun.
          pose proof (basic_tm_has_ltype_of_atom_env_typing
            (erase_ctx Γ1) (tret v1) (erase_ty (CTWand τx τ))
            Hbasic_fun) as Hbasic_fun_lty.
          pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_fun_lty)
            as Hfun_lvars.
          pose proof (context_typing_wf_context_ty Σ Γ1
            (tret v1) (CTWand τx τ) Hwf_fun) as Hτwf_fun.
          cbn [wf_context_ty_at] in Hτwf_fun.
          destruct Hτwf_fun as [_ Hτwf_res].
          pose proof (wf_context_ty_at_fv_subset 1 (dom (erase_ctx Γ1))
            τ Hτwf_res) as Hτfv.
          apply elem_of_union in Hyrel as [Hyv|Hyτ].
          - assert (LVFree y ∈ lvars_of_atoms (fv_tm (tret v1))).
            {
              cbn [fv_tm].
              unfold lvars_of_atoms.
              apply elem_of_map.
              exists y. split; [reflexivity|exact Hyv].
            }
            pose proof (Hfun_lvars (LVFree y) H) as Hy_lvar.
            apply lvars_fv_elem in Hy_lvar.
            rewrite atom_store_to_lvar_store_dom in Hy_lvar.
            rewrite lvars_fv_of_atoms in Hy_lvar.
            exact Hy_lvar.
          - apply Hτfv. exact Hyτ.
        }
      assert (HyΓ2none : (erase_ctx Γ2 : gmap atom ty) !! y = None).
        {
          pose proof (context_typing_wf_ctx Σ (CtxStar Γ1 Γ2)
            (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hwfctx.
          pose proof (wf_ctx_under_basic Σ (CtxStar Γ1 Γ2) Hwfctx) as Hbasic.
          cbn [basic_ctx] in Hbasic.
          destruct Hbasic as [Hbasic1 [Hbasic2 Hdisj]].
          pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic1) as Hdom1.
          pose proof (basic_ctx_erase_dom (dom Σ) Γ2 Hbasic2) as Hdom2.
          apply not_elem_of_dom. intros HyΓ2.
          rewrite Hdom1 in HyΓ1.
          rewrite Hdom2 in HyΓ2.
          better_set_solver.
        }
      apply elem_of_dom in HyΓ1 as [T HT].
      change ((erase_ctx Γ1 : gmap atom ty) !! y =
        (erase_ctx (CtxStar Γ1 Γ2) : gmap atom ty) !! y)
        with ((erase_ctx Γ1 : gmap atom ty) !! y =
          ((erase_ctx Γ1 ∪ erase_ctx Γ2) : gmap atom ty) !! y).
      rewrite <- (lookup_union_l' (M:=gmap atom) (A:=ty)
        (erase_ctx Γ1) (erase_ctx Γ2) y ltac:(eexists; exact HT)).
      reflexivity.
    + assert (Hy_not_R : LVFree y ∉ relevant_lvars (cty_open 0 x τ)
          (tapp_tm (tret v1) (vfvar x))).
        {
          intros HyR.
          apply lvars_fv_elem in HyR.
          rewrite relevant_lvars_fv in HyR.
          rewrite fv_tapp_tm in HyR.
          cbn [fv_tm fv_value] in HyR.
          pose proof (cty_open_fv_subset 0 x τ) as Hτopen.
          better_set_solver.
        }
      contradiction.
Qed.

Lemma appd_wand_result_to_arrow_open_result
    Σ Γ1 Γ2 τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ formula_open 0 x
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
          (CTWand τx τ) (tret v1))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))) ->
  m ⊨ formula_open 0 x
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
          (CTArrow τx τ) (tret v1))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hsrc.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δstar := atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))) in *.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ1 v1 (CTWand τx τ) Hwf_fun) as Hlc_v1.
  assert (Htmfresh :
      x ∉ fv_tm (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value]. better_set_solver.
  }
  assert (HΣfresh_src :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ1 (CTWand τx τ) (tret v1))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_wand_fresh_free
      Δ1 τx τ (tret v1) x Hxτx Hxτ Hxv1 Hbad).
  }
  assert (HΣfresh_tgt :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δstar (CTArrow τx τ) (tret v1))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_arrow_fresh_free
      Δstar τx τ (tret v1) x Hxτx Hxτ Hxv1 Hbad).
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ1 (CTWand τx τ) (tret v1))
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))) in Hsrc
    by (exact HΣfresh_src || exact Htmfresh || better_set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc in Hsrc
    by (constructor; exact Hlc_v1).
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δstar (CTArrow τx τ) (tret v1))
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0)))
    by (exact HΣfresh_tgt || exact Htmfresh || better_set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc
    by (constructor; exact Hlc_v1).
  assert (Hmid1 :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 x (typed_lty_env_bind Δ1 (erase_ty τx)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    eapply ty_equiv_wand_result_src_mid; eauto.
    better_set_solver.
  }
  assert (Hmidstar :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 x (typed_lty_env_bind Δstar (erase_ty τx)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    eapply res_models_ty_denote_gas_env_agree_on.
    - reflexivity.
    - subst Δ1 Δstar.
      exact (appd_open_result_env_agree Σ Γ1 Γ2 τx τ v1 x
        Hwf_fun Hwf_app).
    - exact Hmid1.
  }
  eapply ty_equiv_arrow_result_tgt_goal; eauto.
  better_set_solver.
Qed.

Lemma fundamental_appd_case Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  (ctx_denote_under Σ Γ1 ⊫
    ty_denote_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (ctx_denote_under Σ Γ2 ⊫
    ty_denote_under Σ Γ2 τx (tret (vfvar x))) ->
  ctx_denote_under Σ (CtxStar Γ1 Γ2) ⊫
    ty_denote_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ)
      (tapp v1 (vfvar x)).
Proof.
Admitted.
