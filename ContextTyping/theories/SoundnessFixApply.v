(** * ContextTyping.SoundnessFixApply

    Applying the opened Fix body arrow to the recursive self value. *)

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
From ContextTyping Require Import Typing SoundnessLam SoundnessFixBase
  SoundnessFixOpen.

Local Ltac fix_apply_build_union :=
  first
    [ assumption
    | apply elem_of_union_l; fix_apply_build_union
    | apply elem_of_union_r; fix_apply_build_union
    | apply elem_of_singleton_2; reflexivity ].

Local Ltac fix_apply_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  match goal with
  | H : ?x ∉ _ |- False =>
      apply H; fix_apply_build_union
  end.

Local Lemma fix_apply_fresh_erase_ctx_from_fix_union
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (erase_ctx Γ).
Proof.
  intros Hy.
  eapply ctx_erasure_under_notin_erase_ctx.
  intros Hyctx.
  apply Hy.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_r.
  exact Hyctx.
Qed.

Lemma fix_body_arrow_apply_self
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  (context_typing_wf Σ
      (CtxComma Γ (CtxBind y τx))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
    (tret ({0 ~> vfvar y} vf)) ->
  my ⊨ ty_denote_gas (cty_depth (fix_rec_call_ty b y τx τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b y τx τ)
      (tret (vfix (TBase b →ₜ t) vf)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
      (tapp_tm (tret (open_value 0 (vfvar y) vf))
        (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf Hbody_wf Hy Hctx_comma Hbody_arrow Hself.
  set (Δy := <[LVFree y := erase_ty τx]>
    (atom_env_to_lty_env (erase_ctx Γ))).
  set (τself := fix_rec_call_ty b y τx τ).
  set (τres := cty_open 0 y τ).
  set (body := open_value 0 (vfvar y) vf).
  set (self := vfix (TBase b →ₜ t) vf).
  set (gas := Nat.max (cty_depth τself) (cty_depth τres)).
  assert (HyΓ : y ∉ dom (erase_ctx Γ)).
  { eapply fix_apply_fresh_erase_ctx_from_fix_union. exact Hy. }
  assert (Hbody_mid :
      my ⊨ ty_denote_gas (cty_depth (CTArrow τself τres))
        Δy (CTArrow τself τres) (tret body)).
  {
    subst Δy τself τres body.
    eapply ty_denote_under_comma_bind_to_lvar_insert; eauto.
  }
  cbn [cty_depth ty_denote_gas] in Hbody_mid.
  rewrite res_models_and_iff in Hbody_mid.
  destruct Hbody_mid as [_ Hforall].
  destruct (res_models_forall_rev my _ Hforall) as [Lforall Hforall_open].
  pose (z := fresh_for
    (Lforall ∪ world_dom (my : WorldT) ∪ lvars_fv (dom Δy) ∪
      fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[y]})).
  assert (Hzfresh :
      z ∉ Lforall ∪ world_dom (my : WorldT) ∪ lvars_fv (dom Δy) ∪
        fv_value vf ∪ fv_cty τx ∪ fv_cty τ ∪ {[y]}).
  { subst z. apply fresh_for_not_in. }
  assert (HzL : z ∉ Lforall) by fix_apply_notin_union.
  assert (Hzmy : z ∉ world_dom (my : WorldT)) by fix_apply_notin_union.
  assert (HzΔ : LVFree z ∉ dom Δy).
  {
    intros Hz.
    apply lvars_fv_elem in Hz.
    apply Hzfresh. fix_apply_build_union.
  }
  assert (Hzτself : z ∉ fv_cty τself).
  {
    subst τself.
    apply fv_cty_fix_rec_call_ty_fresh.
    - intros ->. apply Hzfresh. fix_apply_build_union.
    - fix_apply_notin_union.
    - fix_apply_notin_union.
  }
  assert (Hzτres : z ∉ fv_cty τres).
  {
    subst τres.
    pose proof (cty_open_fv_subset 0 y τ) as Hfv.
    intros Hzτ.
    apply Hfv in Hzτ.
    apply elem_of_union in Hzτ as [Hzτ | Hzy].
    - apply Hzfresh. fix_apply_build_union.
    - apply elem_of_singleton in Hzy.
      apply Hzfresh. rewrite Hzy.
      repeat apply elem_of_union_r.
      apply elem_of_singleton_2. reflexivity.
  }
  assert (Hzbody : z ∉ fv_value body).
  {
    subst body.
    pose proof (open_fv_value vf (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    intros Hzbody.
    apply Hopen in Hzbody.
    cbn [fv_value] in Hzbody.
    apply elem_of_union in Hzbody as [Hzy | Hzvf].
    - apply elem_of_singleton in Hzy.
      apply Hzfresh. rewrite Hzy.
      repeat apply elem_of_union_r.
      apply elem_of_singleton_2. reflexivity.
    - apply Hzfresh. fix_apply_build_union.
  }
  assert (Hzself : z ∉ fv_value self).
  { subst self. cbn [fv_value]. fix_apply_notin_union. }
  assert (Hlc_self : lc_value self).
  {
    subst self.
    eapply context_typing_wf_ret_lc_value. exact Hwf.
  }
  assert (Hlc_body : lc_value body).
  {
    subst body τself τres.
    eapply context_typing_wf_ret_lc_value. exact Hbody_wf.
  }
  destruct (expr_result_extension_witness_exists (tret self) z)
    as [Fx HFx].
  { cbn [fv_tm]. exact Hzself. }
  assert (Happ : extension_applicable Fx my).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin. rewrite Hin.
      exact (ty_denote_gas_fv_tm_subset _ _ _ _ _ Hself).
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout. rewrite Hout.
      intros a Ha Hmy.
      apply Hzmy.
      apply elem_of_singleton in Ha. subst a.
      exact Hmy.
  }
  destruct (res_extend_by_exists my Fx Happ) as [mz Hext].
  pose proof (res_extend_by_dom my Fx mz Hext) as Hmz_dom.
  pose proof (res_extend_by_restrict_base my Fx mz Hext) as Hmz_restrict.
  assert (Hopened :
      mz ⊨ formula_open 0 z
        (FImpl
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Δy (CTArrow τself τres) (tret body))
              (erase_ty τself))
            (cty_shift 0 τself) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Δy (CTArrow τself τres) (tret body))
              (erase_ty τself))
            τres
            (tapp_tm (tm_shift 0 (tret body)) (vbvar 0))))).
  {
    subst gas.
    eapply Hforall_open; [exact HzL| |].
    - rewrite Hmz_dom.
      destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout. rewrite Hout. reflexivity.
    - exact Hmz_restrict.
  }
  rewrite formula_open_impl in Hopened.
  assert (Hself_z :
      mz ⊨ ty_denote_gas (cty_depth τself)
        (<[LVFree z := erase_ty τself]> Δy)
        τself (tret (vfvar z))).
  {
    eapply (ty_denote_gas_result_ext
      (cty_depth τself) Δy τself (tret self) z my mz Fx).
    - subst Δy.
      apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
    - exact HzΔ.
    - exact HFx.
    - exact Hext.
    - exact Hself.
  }
  assert (Hself_z_big :
      mz ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty τself]> Δy)
        τself (tret (vfvar z))).
  {
    subst gas.
    rewrite ty_denote_gas_saturate by lia.
    exact Hself_z.
  }
  assert (Hz_arg_fresh :
      z ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δy (CTArrow τself τres) (tret body))
          (erase_ty τself)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hzbad.
    apply lvars_fv_elem in Hzbad.
    pose proof (relevant_env_arrow_fresh_free
      Δy τself τres (tret body) z
      Hzτself Hzτres ltac:(cbn [fv_tm]; exact Hzbody)) as Hfresh_rel.
    exact (Hfresh_rel Hzbad).
  }
  assert (Hτself_lc : lc_context_ty τself).
  {
    subst τself τres body.
    pose proof (context_typing_wf_context_ty Σ
      (CtxComma Γ (CtxBind y τx))
      (tret (open_value 0 (vfvar y) vf))
      (CTArrow (fix_rec_call_ty b y τx τ) (cty_open 0 y τ))
      Hbody_wf) as Hτ_arrow.
    cbn [wf_context_ty_at] in Hτ_arrow.
    destruct Hτ_arrow as [Hτself_wf _].
    eapply wf_context_ty_at_lc. exact Hτself_wf.
  }
  assert (Harg_open :
      mz ⊨ formula_open 0 z
        (ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Δy (CTArrow τself τres) (tret body))
          (erase_ty τself))
        (cty_shift 0 τself) (tret (vbvar 0)))).
  {
    eapply (arrow_inserted_env_to_open_arg_normalized
      gas Δy τself τres (tret body) mz z).
    - subst Δy.
      apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
    - exact HzΔ.
    - exact Hzτself.
    - exact Hτself_lc.
    - exact Hz_arg_fresh.
    - exact Hself_z_big.
  }
  pose proof (res_models_impl_elim mz _ _ Hopened Harg_open)
    as Hres_open.
  assert (Hres_rel :
      mz ⊨ ty_denote_gas gas
        (lty_env_open_one 0 z
          (typed_lty_env_bind
            (relevant_env Δy (CTArrow τself τres) (tret body))
            (erase_ty τself)))
        (cty_open 0 z τres)
        (tapp_tm (tret body) (vfvar z))).
  {
	    assert (Hz_tm_fresh :
	        z ∉ fv_tm (tapp_tm (tm_shift 0 (tret body)) (vbvar 0))).
	    {
	      rewrite fv_tapp_tm, tm_shift_fv.
	      cbn [fv_tm fv_value].
	      intros Hzbad.
	      apply elem_of_union in Hzbad as [Hzbody_bad | Hzempty].
	      - exact (Hzbody Hzbody_bad).
	      - set_unfold in Hzempty. exact Hzempty.
	    }
    rewrite (formula_open_ty_denote_gas_singleton 0 z gas
      (typed_lty_env_bind
        (relevant_env Δy (CTArrow τself τres) (tret body))
        (erase_ty τself))
      τres
      (tapp_tm (tm_shift 0 (tret body)) (vbvar 0))) in Hres_open
      by (exact Hz_arg_fresh || exact Hz_tm_fresh || exact Hzτres).
    rewrite open_tapp_tm_shift_bvar0_lc in Hres_open
      by (constructor; exact Hlc_body).
    exact Hres_open.
  }
  assert (Hres_mid :
      mz ⊨ ty_denote_gas gas
        (lty_env_open_one 0 z
          (typed_lty_env_bind Δy (erase_ty τself)))
        τres
        (tapp_tm (tret body) (vfvar z))).
  {
    assert (Hres_mid_open :
        mz ⊨ ty_denote_gas gas
          (lty_env_open_one 0 z
            (typed_lty_env_bind Δy (erase_ty τself)))
          (cty_open 0 z τres)
          (tapp_tm (tret body) (vfvar z))).
    {
      eapply (ty_equiv_arrow_result_src_mid
        gas Δy τself τres (tret body) mz z).
      - constructor. exact Hlc_body.
      - exact Hzτres.
      - exact Hres_rel.
    }
    replace (cty_open 0 z τres) with τres in Hres_mid_open.
    - exact Hres_mid_open.
    - symmetry.
      apply (cty_open_above_lc_fresh 0 0 z τres);
        [lia| |exact Hzτres].
      pose proof (context_typing_wf_context_ty Σ Γ
        (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf)
        as Hτ_outer.
      cbn [wf_context_ty_at] in Hτ_outer.
      destruct Hτ_outer as [_ Hτres_outer].
      assert (Hτres_wf0 :
          wf_context_ty_at 0 (dom (erase_ctx Γ) ∪ {[y]}) τres).
      {
        unfold τres.
        apply wf_context_ty_at_open_at.
        - exact HyΓ.
        - exact Hτres_outer.
      }
      eapply wf_context_ty_at_lc.
      exact Hτres_wf0.
  }
  assert (Hres_insert :
      mz ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty τself]> Δy)
        τres
        (tapp_tm (tret body) (vfvar z))).
  {
    rewrite typed_lty_env_bind_open_current in Hres_mid.
    - exact Hres_mid.
    - exact HzΔ.
    - subst Δy.
      apply lty_env_closed_insert_free.
      apply atom_store_to_lvar_store_closed.
  }
  assert (Hres_alias :
      mz ⊨ expr_result_formula (tret self) (LVFree z)).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hself)
      as Hself_guard.
    eapply expr_result_formula_of_result_extends_from_ty_guard; eauto.
  }
  assert (Hstatic_target_my :
      my ⊨ ty_static_guard_formula Δy τres
        (tapp_tm (tret body) self)).
  {
    subst Δy τres body self.
    eapply fix_unfolded_app_static_guard_full; eauto.
  }
  assert (Hstatic_target_mz :
      mz ⊨ ty_static_guard_formula Δy τres
        (tapp_tm (tret body) self)).
  {
    eapply res_models_extend_mono; [exact Hext|exact Hstatic_target_my].
  }
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret body) (vfvar z)) ∪
         fv_tm (tapp_tm (tret body) self)) mz).
  {
    assert (Hclosed_src :
        wfworld_closed_on (fv_tm (tapp_tm (tret body) (vfvar z))) mz).
    {
      eapply denot_ty_lvar_guard_wfworld_closed_on_term.
      eapply ty_denote_gas_guard. exact Hres_insert.
    }
    assert (Hclosed_tgt :
        wfworld_closed_on (fv_tm (tapp_tm (tret body) self)) mz).
    { eapply ty_static_guard_wfworld_closed_on_term. exact Hstatic_target_mz. }
    apply wfworld_closed_on_union; assumption.
  }
  assert (Heq :
      tm_equiv_on mz
        (tapp_tm (tret body) (vfvar z))
        (tapp_tm (tret body) self)).
  {
    eapply tm_equiv_tapp_value_arg_result_alias; eauto.
  }
  assert (Hzero_src :
      mz ⊨ ty_denote_gas 0
        (<[LVFree z := erase_ty τself]> Δy)
        τres
        (tapp_tm (tret body) (vfvar z))).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hres_insert.
  }
  assert (Hzero_tgt :
      mz ⊨ ty_denote_gas 0
        (<[LVFree z := erase_ty τself]> Δy)
        τres
        (tapp_tm (tret body) self)).
  {
    assert (Hz_not_rel_tgt :
        LVFree z ∉ relevant_lvars τres (tapp_tm (tret body) self)).
    {
      unfold relevant_lvars.
      intros Hzrel.
      apply elem_of_union in Hzrel as [Hzτ_lvar|Hz_tm_lvar].
      - apply Hzτres.
        rewrite <- context_ty_lvars_fv.
        apply lvars_fv_elem. exact Hzτ_lvar.
      - apply lvars_fv_elem in Hz_tm_lvar.
        rewrite tm_lvars_fv, fv_tapp_tm in Hz_tm_lvar.
        cbn [fv_tm fv_value] in Hz_tm_lvar.
        apply elem_of_union in Hz_tm_lvar as [Hzbody_fv|Hzself_fv].
        + exact (Hzbody Hzbody_fv).
        + exact (Hzself Hzself_fv).
    }
    assert (Hworld_insert :
        mz ⊨ basic_world_formula (<[LVFree z := erase_ty τself]> Δy)).
    {
      eapply basic_world_insert_of_arg.
      - exact HzΔ.
      - eapply ty_static_guard_basic_world. exact Hstatic_target_mz.
      - exact Hself_z_big.
    }
    assert (Hstatic_target_insert :
        mz ⊨ ty_static_guard_formula
          (<[LVFree z := erase_ty τself]> Δy) τres
          (tapp_tm (tret body) self)).
    {
      eapply ty_static_guard_insert_irrelevant; eauto.
    }
    eapply ty_denote_gas_zero_transport_static_tm_equiv.
    - exact Heq.
    - eapply tm_total_equiv_of_tm_equiv_left_total.
      + exact Heq.
      + eapply ty_denote_gas_total_guard_of_zero. exact Hzero_src.
    - exact Hstatic_target_insert.
    - apply lc_tapp_tm; [constructor; exact Hlc_body|exact Hlc_self].
    - eapply ty_static_guard_fv_tm_subset. exact Hstatic_target_insert.
    - exact Hzero_src.
  }
	  assert (Htarget_insert :
	      mz ⊨ ty_denote_gas gas
	        (<[LVFree z := erase_ty τself]> Δy)
	        τres
	        (tapp_tm (tret body) self)).
	  {
	    eapply ty_denote_gas_tm_equiv.
	    - split; [exact Heq|split].
	      + eapply tm_total_equiv_of_total_formulas.
	        * eapply ty_denote_gas_total_guard_of_zero. exact Hzero_src.
	        * eapply ty_denote_gas_total_guard_of_zero. exact Hzero_tgt.
	      + split; [exact Hzero_src|exact Hzero_tgt].
	    - exact Hres_insert.
	  }
	  assert (Htarget_insert_goalgas :
	      mz ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	        (<[LVFree z := erase_ty τself]> Δy)
	        τres
	        (tapp_tm (tret body) self)).
	  {
	    rewrite ty_denote_gas_saturate by
	      (subst τres; cty_depth_solve).
	    rewrite ty_denote_gas_saturate in Htarget_insert by
	      (subst gas; lia).
	    exact Htarget_insert.
	  }
	  assert (Hfv_target_my :
	      fv_tm (tapp_tm (tret body) self) ∪ fv_cty τres ⊆
	      world_dom (my : WorldT)).
  { eapply ty_static_guard_fv_subset. exact Hstatic_target_my. }
  eapply ty_denote_gas_drop_fresh_ext with (mx := mz) (Fx := Fx).
  - exact Hfv_target_my.
  - exact HzΔ.
  - intros Hbad. apply Hzτres. apply lvars_fv_elem. exact Hbad.
	  - cbn [fv_tm]. rewrite fv_tapp_tm.
	    cbn [fv_tm].
	    intros Hzbad.
	    apply elem_of_union in Hzbad as [Habody|Haself].
	    + exact (Hzbody Habody).
	    + exact (Hzself Haself).
	  - exact Hext.
	  - exact Htarget_insert_goalgas.
Qed.
