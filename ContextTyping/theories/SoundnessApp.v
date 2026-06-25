(** * ContextTyping.SoundnessApp

    App proof support for the direct Fundamental theorem.
    Keeping this case in a focused file makes timing diagnostics local and
    avoids re-checking the full Fundamental dispatch while proving Arrow
    application transport. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension ResourceCompat.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  DenotationSetMapFacts
  ResultFirstOpen
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
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
  rewrite (cty_open_shift_from_lc_fresh 0 x τx).
  2:{
    apply (context_typing_wf_arrow_arg_lc Σ Γ (tret v1) τx τ).
    exact Hwf_fun.
  }
  2:{
    better_set_solver.
  }
  assert (Hrel_env_fresh :
      LVFree x ∉ dom (relevant_env Δ (CTArrow τx τ) (tret v1) : lty_env)).
  {
    apply soundness_relevant_env_arrow_value_fresh.
    soundness_fresh_solve.
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
  cty_lc_at 1 τ ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1)))
        (cty_open 0 x τ) (tapp_tm (tret v1) (vfvar x)) ->
  m ⊨ ty_denote_gas (cty_depth ({0 ~> x} τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf Hτ_lc1 Hfresh Harg Hopened.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  pose proof (context_typing_wf_app_fun_lc_value
    Σ Γ v1 (vfvar x) ({0 ~> x} τ) Hwf) as Hlc_v1.
  assert (Hrel_env_fresh :
      LVFree x ∉ dom (relevant_env Δ (CTArrow τx τ) (tret v1) : lty_env)).
  {
    apply soundness_relevant_env_arrow_value_fresh.
    soundness_fresh_solve.
  }
  assert (Hrel_env_closed :
      lty_env_closed (relevant_env Δ (CTArrow τx τ) (tret v1))).
  { apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  assert (HΔx : Δ !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup (cty_depth τx) Δ τx x m Harg). }
  assert (Hsrc_mid :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        Δ
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    pose proof (ty_equiv_arrow_result_src_mid_current
      (Nat.max (cty_depth τx) (cty_depth τ))
      Δ τx τ (tret v1) m x
      HΔx
	      ltac:(constructor; exact Hlc_v1)
	      Hτ_lc1
	      ltac:(better_set_solver) Hopened) as Hmid.
    exact Hmid.
  }
  assert (Hzero_src :
      m ⊨ ty_denote_gas 0
        Δ
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
	      (relevant_env
	        Δ
	        (cty_open 0 x τ)
	        (tapp_tm (tret v1) (vfvar x)))
	      (cty_open 0 x τ)
	      (tapp_tm (tret v1) (vfvar x)) m
	      (ty_denote_gas_guard_formula 0 _ _ _ _ Hzero_src))
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
	  assert (Htotal_equiv :
	      tm_total_equiv_on m
	        (tapp_tm (tret v1) (vfvar x))
	        (tapp v1 (vfvar x))).
	  {
	    pose proof (denot_ty_lvar_guard_wfworld_closed_on_term
	      (relevant_env
	        Δ
	        (cty_open 0 x τ)
	        (tapp_tm (tret v1) (vfvar x)))
	      (cty_open 0 x τ)
	      (tapp_tm (tret v1) (vfvar x)) m
	      (ty_denote_gas_guard_formula 0 _ _ _ _ Hzero_src))
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
	    exact (tm_total_equiv_tapp_tm_ret m v1 x Hclosed_apps Hlc_v1).
	  }
	  assert (Hzero_tgt :
	      m ⊨ ty_denote_gas 0
	        Δ
        (cty_open 0 x τ) (tapp v1 (vfvar x))).
  {
    pose proof (ty_denote_gas_guard_of_zero
      Δ
      (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x)) m Hzero_src) as Hguard_src.
    repeat rewrite res_models_and_iff in Hguard_src.
    destruct Hguard_src as [Hwf_src [Hworld_src [Hbasic_src Htotal_src]]].
    set (Σopen := Δ).
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
             symmetry. apply relevant_env_restrict_subset.
             unfold relevant_lvars. set_solver.
	        * eapply tm_equiv_total.
	          -- exact Htotal_equiv.
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
        Δ
        (cty_open 0 x τ) (tapp v1 (vfvar x))).
	  {
	    eapply ty_denote_gas_tm_equiv.
	    - split; [exact Hequiv|].
	      split; [exact Htotal_equiv|].
	      split; [exact Hzero_src|exact Hzero_tgt].
    - rewrite ty_denote_gas_saturate in Hsrc_mid by
        (rewrite cty_open_preserves_depth; lia).
      exact Hsrc_mid.
  }
  rewrite cty_open_preserves_depth in Htarget_insert.
  change ({0 ~> x} τ) with (cty_open 0 x τ).
  rewrite cty_open_preserves_depth.
  exact Htarget_insert.
Qed.

Lemma app_arrow_basic_world_insert_env
    Γ τx τ v1 x (m : WfWorldT) :
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v1) ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ basic_world_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))).
Proof.
  intros Hfresh Hfun Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret v1)).
  pose proof (ty_denote_gas_guard
    (cty_depth (CTArrow τx τ)) Δ (CTArrow τx τ)
    (tret v1) m Hfun) as Hfun_guard.
  repeat rewrite res_models_and_iff in Hfun_guard.
  destruct Hfun_guard as [_ [Hworld_rel [_ _]]].
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    (cty_depth τx) Δ τx x m Harg) as Hworld_x.
  pose proof (basic_world_formula_union
    (<[LVFree x := erase_ty τx]> (∅ : lty_env)) Σrel m
    Hworld_x Hworld_rel) as Hunion.
  eapply basic_world_formula_subenv; [|exact Hunion].
  intros v T Hlook.
  change ((<[LVFree x := erase_ty τx]> (Σrel : gmap logic_var ty))
    !! v = Some T) in Hlook.
  change (((<[LVFree x := erase_ty τx]> (∅ : lty_env)) ∪ Σrel
    : gmap logic_var ty) !! v = Some T).
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - apply map_lookup_union_Some_raw. left.
    rewrite !lookup_insert in Hlook |- *.
    destruct (decide (LVFree x = LVFree x)) as [_|Hneq] in Hlook |- *;
      [exact Hlook|contradiction].
  - apply map_lookup_union_Some_raw. right. split.
    + rewrite lookup_insert_ne by (symmetry; exact Hvx).
      apply lookup_empty.
    + rewrite lookup_insert_ne in Hlook by (symmetry; exact Hvx).
      exact Hlook.
Qed.

Lemma app_arrow_context_wf_insert_env
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ basic_world_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))) ->
  m ⊨ context_ty_wf_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1)))
        (cty_open 0 x τ).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hworld.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (Σins := <[LVFree x := erase_ty τx]>
    (relevant_env Δ (CTArrow τx τ) (tret v1))).
  apply context_ty_wf_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
  split; [exact Hlc|]. split; [exact Hscope|].
  pose proof (context_typing_wf_context_ty
    Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hτopen_wf.
  change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτopen_wf.
  pose proof (wf_context_ty_at_to_lvars_shape
    0 (dom (erase_ctx Γ)) (cty_open 0 x τ) Hτopen_wf)
    as [_ Hshape].
  split; [|exact Hshape].
  intros v Hv.
  destruct v as [k|y].
  - exfalso.
    pose proof (wf_context_ty_at_lc 0 (dom (erase_ctx Γ))
      (cty_open 0 x τ) Hτopen_wf) as Hlcτ.
    pose proof (cty_lc_at_lvars_bv_empty 0
      (cty_open 0 x τ) Hlcτ) as Hbv.
    apply lvars_bv_elem in Hv.
    change (context_ty_lvars (cty_open 0 x τ))
      with (context_ty_lvars_at 0 (cty_open 0 x τ)) in Hv.
    rewrite Hbv in Hv. set_solver.
  - subst Σins Δ.
    rewrite dom_insert_L.
    apply elem_of_union.
    destruct (decide (y = x)) as [->|Hyx].
    + left. set_solver.
    + right.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_dom.
      apply elem_of_intersection. split.
      * pose proof (context_typing_wf_context_ty
          Σ Γ (tret v1) (CTArrow τx τ) Hwf_fun) as Hτfun_wf.
        cbn [wf_context_ty_at] in Hτfun_wf.
        destruct Hτfun_wf as [_ Hτ_body_wf].
        pose proof (wf_context_ty_at_fv_subset
          1 (dom (erase_ctx Γ)) τ Hτ_body_wf) as Hτ_fv.
        assert (Hy_fv_open : y ∈ fv_cty (cty_open 0 x τ)).
        { apply lvars_fv_elem. exact Hv. }
        pose proof (cty_open_fv_subset 0 x τ y Hy_fv_open)
          as Hy_fv.
        apply elem_of_union in Hy_fv as [Hyτ|Hyx_single].
        -- rewrite atom_store_to_lvar_store_dom.
           unfold lvars_of_atoms. apply elem_of_map.
           exists y. split; [reflexivity|exact (Hτ_fv y Hyτ)].
        -- exfalso. apply Hyx.
           apply elem_of_singleton in Hyx_single. exact Hyx_single.
      * unfold relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
          context_ty_lvars context_ty_lvars_at].
        assert (Hy_fv_open : y ∈ fv_cty (cty_open 0 x τ)).
        { apply lvars_fv_elem. exact Hv. }
        pose proof (cty_open_fv_subset 0 x τ y Hy_fv_open)
          as Hy_fv.
        apply elem_of_union in Hy_fv as [Hyτ|Hyx_single].
        -- rewrite <- (context_ty_lvars_fv_at 1 τ) in Hyτ.
           apply elem_of_union_l. apply elem_of_union_r.
           apply lvars_fv_elem. exact Hyτ.
        -- exfalso. apply Hyx.
           apply elem_of_singleton in Hyx_single. exact Hyx_single.
Qed.

Lemma app_arrow_fun_basic_insert_env
    Γ τx τ v1 x (m : WfWorldT) :
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ basic_world_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))) ->
  m ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v1) ->
  m ⊨ expr_basic_typing_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1)))
        (tret v1) (erase_ty τx →ₜ erase_ty (cty_open 0 x τ)).
Proof.
  intros Hfresh Hworld Hfun.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret v1)).
  set (Σins := <[LVFree x := erase_ty τx]> Σrel).
  pose proof (ty_denote_gas_guard
    (cty_depth (CTArrow τx τ)) Δ (CTArrow τx τ)
    (tret v1) m Hfun) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [_ [Hbasic_rel _]]].
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
  apply expr_basic_typing_formula_models_iff in Hbasic_rel
    as [_ [_ Hty_rel]].
  split; [exact Hlc|]. split; [exact Hscope|].
  rewrite cty_open_preserves_erasure.
  change (erase_ty τx →ₜ erase_ty τ) with (erase_ty (CTArrow τx τ)).
  subst Σins.
  eapply basic_tm_has_ltype_weaken; [exact Hty_rel|].
  apply map_subseteq_spec. intros v T Hlook.
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - exfalso.
    eapply soundness_relevant_env_arrow_value_fresh.
    + soundness_fresh_solve.
    + apply elem_of_dom. eexists. exact Hlook.
  - rewrite lookup_insert_ne by (symmetry; exact Hvx).
    exact Hlook.
Qed.

Lemma app_arrow_mid_static_guard
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
  m ⊨ ty_static_guard_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hfun Harg.
  pose proof (app_arrow_basic_world_insert_env
    Γ τx τ v1 x m Hfresh Hfun Harg) as Hworld.
  eapply (ty_static_guard_tapp_fun_result_base
    (<[LVFree x := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v1)))
    (cty_open 0 x τ) v1 x (erase_ty τx) m).
  - rewrite lookup_insert.
    destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
      [reflexivity|contradiction].
  - eapply app_arrow_context_wf_insert_env; eauto.
  - exact Hworld.
  - eapply app_arrow_fun_basic_insert_env; eauto.
Qed.

Lemma app_arrow_outer_value_open
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v1) ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  exists (z : atom) (mz0 mz : WfWorldT),
    z ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪ world_dom (m : WorldT) /\
    x ∉ world_dom (mz0 : WorldT) /\
    world_dom (mz : WorldT) = world_dom (mz0 : WorldT) ∪ {[x]} /\
    world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} /\
    res_restrict mz (world_dom (m : WorldT)) = m /\
    res_restrict mz (world_dom (mz0 : WorldT)) = mz0 /\
    mz ⊨ expr_result_formula (tret v1) (LVFree z) /\
    mz0 ⊨ formula_open 0 z
      (arrow_value_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))
          (erase_ty (CTArrow τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))).
Proof.
  intros Hwf_fun Hfresh Hfun Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret v1)).
  set (m0 := res_restrict m (world_dom (m : WorldT) ∖ {[x]})).
  assert (Hfun0 :
      m0 ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        Δ (CTArrow τx τ) (tret v1)).
  {
    subst m0.
    assert (Hfresh_fun :
        x ∉ fv_tm (tret v1) ∪ fv_cty (CTArrow τx τ)).
    {
      intros Hbad.
      cbn [fv_tm fv_value] in Hbad.
      apply elem_of_union in Hbad as [Hv1|Hτarr].
      - apply Hfresh. apply elem_of_union_l.
        apply elem_of_union_l. exact Hv1.
      - cty_fv_syntax_norm_in Hτarr.
        apply elem_of_union in Hτarr as [Hτx|Hτ].
        + apply Hfresh. apply elem_of_union_l.
          apply elem_of_union_r. exact Hτx.
        + rewrite context_ty_lvars_fv_at in Hτ.
          apply Hfresh. apply elem_of_union_r. exact Hτ.
    }
    exact (ty_denote_gas_restrict_delete_fresh
      (cty_depth (CTArrow τx τ)) Δ (CTArrow τx τ) (tret v1)
      x m Hfresh_fun Hfun).
  }
  assert (Hx_m : x ∈ world_dom (m : WorldT)).
  { eapply ty_denote_gas_ret_fvar_world_dom; exact Harg. }
  assert (Hrestrict_m0 : res_restrict m (world_dom (m0 : WorldT)) = m0).
  { subst m0. apply res_restrict_self_dom. }
  assert (Hdom_m0_insert :
      world_dom (m : WorldT) =
      world_dom (m0 : WorldT) ∪ {[x]}).
  { subst m0. apply res_restrict_delete_insert_dom. exact Hx_m. }
  assert (Hx_m0 : x ∉ world_dom (m0 : WorldT)).
  { subst m0. apply res_restrict_delete_notin. }
  set (z := fresh_for
    (fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
     world_dom (m : WorldT) ∪ lvars_fv (dom Σrel) ∪ {[x]})).
  pose proof (fresh_for_not_in
    (fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
     world_dom (m : WorldT) ∪ lvars_fv (dom Σrel) ∪ {[x]}))
    as Hzfresh_all.
  assert (Hzfresh :
      z ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪ world_dom (m : WorldT)).
  { subst z. better_set_solver. }
  assert (HzΣrel : z ∉ lvars_fv (dom Σrel)).
  { subst z. better_set_solver. }
  assert (Hzx : z <> x).
  { intros ->. apply Hzfresh_all. better_set_solver. }
  assert (Hfv_v1_m0 : fv_tm (tret v1) ⊆ world_dom (m0 : WorldT)).
  { eapply ty_denote_gas_fv_tm_subset; exact Hfun0. }
  destruct (expr_result_extension_witness_on_exists
    (world_dom (m0 : WorldT)) (tret v1) z Hfv_v1_m0
    ltac:(better_set_solver)) as [Fz HFz].
  destruct (expr_result_extension_witness_on_shape _ _ _ _ HFz)
    as [HFz_in HFz_out].
  unfold ext_in, ext_out in HFz_in, HFz_out.
  assert (Happ0 : extension_applicable Fz m0).
  {
    constructor.
    - rewrite HFz_in. set_solver.
    - rewrite HFz_out. subst z. better_set_solver.
  }
  assert (Happ : extension_applicable Fz m).
  {
    constructor.
    - rewrite HFz_in. set_solver.
    - rewrite HFz_out. subst z. better_set_solver.
  }
  destruct (res_extend_by_exists m0 Fz Happ0) as [mz0 Hext0].
  destruct (res_extend_by_exists m Fz Happ) as [mz Hext].
  pose proof (res_extend_by_singleton_output_open_world
    m mz Fz z Hext HFz_out) as [Hmz_dom Hmz_restrict_m].
  assert (Hmz_restrict_mz0 :
      res_restrict mz (world_dom (mz0 : WorldT)) = mz0).
  {
    eapply res_extend_by_full_input_frame_restrict;
      [exact Hrestrict_m0|exact HFz_in|exact Hext0|exact Hext].
  }
	  assert (Hx_mz0 : x ∉ world_dom (mz0 : WorldT)).
	  {
	    eapply res_extend_by_singleton_output_preserves_notin.
	    - exact Hx_m0.
	    - intros Hxz. apply Hzx. symmetry. exact Hxz.
	    - exact HFz_out.
	    - exact Hext0.
	  }
	  assert (Hmz_dom_x :
	      world_dom (mz : WorldT) = world_dom (mz0 : WorldT) ∪ {[x]}).
	  {
	    eapply res_extend_by_same_singleton_output_open_world_frame.
	    - exact Hdom_m0_insert.
	    - intros Hxz. apply Hzx. symmetry. exact Hxz.
	    - exact HFz_out.
	    - exact Hext0.
	    - exact Hext.
	  }
  assert (Hguard0 :
      m0 ⊨ ty_guard_formula Σrel (CTArrow τx τ) (tret v1)).
  {
    subst Σrel.
    apply ty_denote_gas_guard_formula with
      (gas := cty_depth (CTArrow τx τ)).
    exact Hfun0.
  }
  assert (Hzero0 :
      m0 ⊨ ty_denote_gas 0 Δ (CTArrow τx τ) (tret v1)).
  { apply ty_denote_gas_zero_of_guard_formula. exact Hguard0. }
  assert (Htotal0 : expr_total_on_atom_world (tret v1) m0).
  { eapply ty_denote_gas_zero_total_atom_world; exact Hzero0. }
  assert (Hbody_outer :
      m0 ⊨ FForall
        (FImpl
          (expr_result_formula_at (lvars_shift_from 0 (dom Σrel))
            (tm_shift 0 (tret v1)) (LVBound 0))
          (arrow_value_denote_gas
            (Nat.max (cty_depth τx) (cty_depth τ))
            (typed_lty_env_bind Σrel (erase_ty (CTArrow τx τ)))
            (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))))).
  {
    subst Σrel.
    cbn [cty_depth ty_denote_gas] in Hfun0.
    repeat rewrite res_models_and_iff in Hfun0.
    exact (proj2 Hfun0).
  }
  pose proof (res_models_forall_open_named_fresh
    m0 mz0 z
    (FImpl
      (expr_result_formula_at (lvars_shift_from 0 (dom Σrel))
        (tm_shift 0 (tret v1)) (LVBound 0))
      (arrow_value_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind Σrel (erase_ty (CTArrow τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))))
    Hbody_outer ltac:(subst z; better_set_solver)) as Houter_open.
  pose proof (res_extend_by_singleton_output_open_world
    m0 mz0 Fz z Hext0 HFz_out) as [Hmz0_dom Hmz0_restrict].
  specialize (Houter_open Hmz0_dom Hmz0_restrict).
  cbn [formula_open] in Houter_open.
	  assert (Hres_at :
	      mz0 ⊨ expr_result_formula_at (dom Σrel) (tret v1) (LVFree z)).
	  {
	    eapply expr_result_formula_at_env_of_result_extends_from_ty_guard_on.
	    - exact HFz.
	    - exact Hext0.
	    - subst Σrel. exact Hguard0.
	  }
	  rewrite (formula_open_result_first_expr_result_formula_at_shift0
	    z (dom Σrel) (tret v1)) in Houter_open.
	  2:{ subst Σrel. apply relevant_env_closed.
	      apply atom_store_to_lvar_store_closed. }
	  2:{ exact HzΣrel. }
	  2:{ constructor. eapply context_typing_wf_ret_lc_value.
	      exact Hwf_fun. }
	  2:{ cbn [fv_tm fv_value]. clear -Hzfresh; better_set_solver. }
	  pose proof (res_models_impl_elim _ _ _ Houter_open Hres_at)
	    as Hvalue.
	  assert (Hres_expr_mz0 :
	      mz0 ⊨ expr_result_formula (tret v1) (LVFree z)).
	  {
	    eapply expr_result_formula_of_result_extends_on_from_ty_guard.
	    - exact HFz.
	    - exact Hext0.
	    - subst Σrel. exact Hguard0.
	  }
  assert (Hres_expr_mz :
      mz ⊨ expr_result_formula (tret v1) (LVFree z)).
  {
    eapply res_models_kripke; [|exact Hres_expr_mz0].
    rewrite <- Hmz_restrict_mz0.
    apply res_restrict_le.
  }
  exists z, mz0, mz.
  split; [exact Hzfresh|].
  split; [exact Hx_mz0|].
  split; [exact Hmz_dom_x|].
  split; [exact Hmz_dom|].
  split; [exact Hmz_restrict_m|].
  split; [exact Hmz_restrict_mz0|].
  split; [exact Hres_expr_mz|].
  exact Hvalue.
Qed.

Lemma app_arrow_result_first_arg_antecedent
    Σ Γ τx τ v1 x z (m mz : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  z ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪ world_dom (m : WorldT) ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  mz ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree x := erase_ty τx]>
      (<[LVFree z := erase_ty (CTArrow τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret v1))))
    τx (tret (vfvar x)).
Proof.
  intros Hwf_fun Hfresh Hzfresh Hmz_dom Hmz_restrict_m Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret v1)).
  set (Tfun := erase_ty (CTArrow τx τ)).
  assert (Hx_m : x ∈ world_dom (m : WorldT)).
  { eapply ty_denote_gas_ret_fvar_world_dom. exact Harg. }
  assert (Hzx : z <> x).
  { intros ->. apply Hzfresh. apply elem_of_union_r. exact Hx_m. }
  assert (HxΣrel : LVFree x ∉ dom Σrel).
  {
    subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
    soundness_fresh_solve.
  }
  assert (HzΣrel : LVFree z ∉ dom Σrel).
  {
    subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
    soundness_fresh_solve.
  }
  assert (Harg_big_m :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        Δ τx (tret (vfvar x))).
  {
    rewrite ty_denote_gas_saturate by lia.
    exact Harg.
  }
  assert (Harg_big_mz :
      mz ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        Δ τx (tret (vfvar x))).
  {
    eapply res_models_kripke; [|exact Harg_big_m].
    rewrite <- Hmz_restrict_m.
    apply res_restrict_le.
  }
  assert (Hxlookup : Δ !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup _ _ _ _ _ Harg). }
  eapply (res_models_ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    Δ
    (<[LVFree x := erase_ty τx]> (<[LVFree z := Tfun]> Σrel))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x))) mz).
  - reflexivity.
  - apply storeA_map_eq. intros u.
    unfold lty_env_restrict_lvars.
    rewrite !storeA_restrict_lookup.
    destruct (decide (u ∈ relevant_lvars τx (tret (vfvar x))))
      as [Hu|Hu]; [|reflexivity].
    destruct u as [k|a].
    + exfalso.
      assert (Hlc_rel :
          lc_lvars (relevant_lvars τx (tret (vfvar x)))).
      {
        apply lc_lvars_relevant_lvars; [|constructor; constructor].
        apply (context_typing_wf_arrow_arg_lc Σ Γ (tret v1) τx τ).
        exact Hwf_fun.
      }
      exact (Hlc_rel (LVBound k) Hu).
    + destruct (decide (a = x)) as [->|Hax].
      * rewrite lookup_insert_eq. exact Hxlookup.
      * rewrite lookup_insert_ne by congruence.
        destruct (decide (a = z)) as [->|Haz].
        -- exfalso.
           unfold relevant_lvars in Hu.
           cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hu.
           apply elem_of_union in Hu as [Hτx|Hxvar].
           ++ apply Hzfresh. apply elem_of_union_l.
              apply elem_of_union_l. apply elem_of_union_r.
              apply lvars_fv_elem. exact Hτx.
           ++ apply elem_of_singleton in Hxvar. inversion Hxvar. subst z.
              exact (Hzx eq_refl).
        -- rewrite lookup_insert_ne by congruence.
           subst Σrel.
           unfold relevant_env, lty_env_restrict_lvars.
           rewrite storeA_restrict_lookup.
           destruct (decide
             (LVFree a ∈ relevant_lvars (CTArrow τx τ) (tret v1)))
             as [_|Hbad]; [reflexivity|].
           exfalso. apply Hbad.
           unfold relevant_lvars in Hu |- *.
           cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
             context_ty_lvars context_ty_lvars_at] in Hu |- *.
           apply elem_of_union in Hu as [Haτx|Hax_single].
           ++ better_set_solver.
           ++ apply elem_of_singleton in Hax_single.
              inversion Hax_single. congruence.
  - exact Harg_big_mz.
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
  intros Hwf_fun Hwf_app Hfresh Hfun Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret v1)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  destruct (app_arrow_outer_value_open
    Σ Γ τx τ v1 x m Hwf_fun Hfresh Hfun Harg)
    as (z & mz0 & mz & Hzfresh & Hx_mz0 & Hmz_dom_x &
      Hmz_dom & Hmz_restrict_m & Hmz_restrict_mz0 & Hres_v1_z &
      Hvalue).
  pose proof (app_arrow_result_first_arg_antecedent
    Σ Γ τx τ v1 x z m mz Hwf_fun Hfresh Hzfresh
    Hmz_dom Hmz_restrict_m Harg) as Harg_open.
  assert (HΣrel_closed : lty_env_closed Σrel).
  { subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  assert (HzΣrel : LVFree z ∉ dom (Σrel : lty_env)).
  {
    subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
    clear -Hzfresh. better_set_solver.
  }
  assert (HxΣrel : LVFree x ∉ dom (Σrel : lty_env)).
  {
    subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
    exact Hfresh.
  }
  assert (Hzx : z <> x).
  {
    intros ->. apply Hzfresh. apply elem_of_union_r.
    eapply ty_denote_gas_ret_fvar_world_dom. exact Harg.
  }
  assert (Hlcτx : lc_context_ty τx).
  {
    apply (context_typing_wf_arrow_arg_lc Σ Γ (tret v1) τx τ).
    exact Hwf_fun.
  }
  assert (Hlcτ : cty_lc_at 1 τ).
  {
    apply (context_typing_wf_arrow_result_lc1 Σ Γ (tret v1) τx τ).
    exact Hwf_fun.
  }
  assert (Hzτ : z ∉ fv_cty τx ∪ fv_cty τ).
  { clear -Hzfresh. better_set_solver. }
  assert (Hxτ : x ∉ fv_cty τx ∪ fv_cty τ).
  { clear -Hfresh. better_set_solver. }
  pose proof (arrow_value_open_arg_to_regular_imp
    gas Σrel τx τ (erase_ty (CTArrow τx τ)) z x mz0 mz
    HΣrel_closed HzΣrel Hzx
    ltac:(rewrite dom_insert_L; intros Hbad;
      apply elem_of_union in Hbad as [Hbad|Hbad];
      [apply elem_of_singleton in Hbad; congruence|exact (HxΣrel Hbad)])
    Hlcτx Hlcτ Hzτ Hxτ Hvalue Hx_mz0 Hmz_dom_x
    Hmz_restrict_mz0) as Hinner.
  pose proof (res_models_impl_elim _ _ _ Hinner Harg_open)
    as Hres_norm.
  assert (Hfun_mz :
      mz ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        Δ (CTArrow τx τ) (tret v1)).
  {
    eapply res_models_kripke; [|exact Hfun].
    rewrite <- Hmz_restrict_m.
    apply res_restrict_le.
  }
  assert (Harg_mz :
      mz ⊨ ty_denote_gas (cty_depth τx)
        Δ τx (tret (vfvar x))).
  {
    eapply res_models_kripke; [|exact Harg].
    rewrite <- Hmz_restrict_m.
    apply res_restrict_le.
  }
  pose proof (app_arrow_mid_static_guard
    Σ Γ τx τ v1 x mz Hwf_fun Hwf_app Hfresh Hfun_mz Harg_mz)
    as Hstatic_mz.
  pose proof Hstatic_mz as Hstatic_parts.
  unfold ty_static_guard_formula in Hstatic_parts.
  repeat rewrite res_models_and_iff in Hstatic_parts.
  destruct Hstatic_parts as [_ [Hworld_insert _]].
  pose proof (app_arrow_fun_basic_insert_env
    Γ τx τ v1 x mz Hfresh Hworld_insert Hfun_mz)
    as Hbasic_fun_mz.
  assert (Hres_alias_src :
      mz ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 x τ)]>
          (<[LVFree x := erase_ty τx]> Σrel))
        (cty_open 0 x τ)
        (tapp_tm (tret (vfvar z)) (vfvar x))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree x := erase_ty τx]>
          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        (X := relevant_lvars (cty_open 0 x τ)
          (tapp_tm (tret (vfvar z)) (vfvar x))).
    - reflexivity.
    - rewrite cty_open_preserves_erasure.
      rewrite lty_env_insert_free_commute by
        (clear -Hzfresh Harg; intros ->; apply Hzfresh;
         apply elem_of_union_r;
         eapply ty_denote_gas_ret_fvar_world_dom; exact Harg).
      reflexivity.
    - exact Hres_norm.
  }
  assert (Hz_base_env :
      LVFree z ∉ dom (<[LVFree x := erase_ty τx]> Σrel)).
  {
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst.
      apply Hzfresh. apply elem_of_union_r.
      eapply ty_denote_gas_ret_fvar_world_dom. exact Harg.
    - subst Σrel. apply relevant_env_arrow_fresh_free in Hin;
        cbn [fv_tm fv_value]; clear -Hzfresh Hin; better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value v1 ∪ {[x]} ∪ fv_cty (cty_open 0 x τ)).
  {
    pose proof (cty_open_fv_subset 0 x τ) as Hopen_fv.
    assert (Hx_m : x ∈ world_dom (m : WorldT)).
    { eapply ty_denote_gas_ret_fvar_world_dom. exact Harg. }
    clear -Hzfresh Hopen_fv Hx_m. better_set_solver.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_back_from_static
    gas (<[LVFree x := erase_ty τx]> Σrel)
    (cty_open 0 x τ) v1 x z (erase_ty τx) mz
    Hz_base_env Hz_alias_fresh
    ltac:(rewrite lookup_insert;
          destruct (decide (LVFree x = LVFree x));
          [reflexivity|contradiction])
    ltac:(eapply context_typing_wf_ret_lc_value; exact Hwf_fun)
    Hres_v1_z Hbasic_fun_mz Hstatic_mz Hres_alias_src)
    as Htarget_mz.
  assert (Htarget_m :
      m ⊨ ty_denote_gas gas
        (<[LVFree x := erase_ty τx]> Σrel)
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    assert (Hfv_target :
        formula_fv (ty_denote_gas gas
          (<[LVFree x := erase_ty τx]> Σrel)
          (cty_open 0 x τ)
          (tapp_tm (tret v1) (vfvar x))) ⊆
        world_dom (m : WorldT)).
    {
      pose proof (res_models_scoped _ _ Htarget_mz) as Hscope.
      pose proof (formula_fv_ty_denote_gas_subset_relevant gas
        (<[LVFree x := erase_ty τx]> Σrel)
        (cty_open 0 x τ) (tapp_tm (tret v1) (vfvar x))) as Hfv.
      intros a Ha.
      pose proof (Hscope a Ha) as Ha_mz.
      rewrite Hmz_dom in Ha_mz.
      apply elem_of_union in Ha_mz as [Ha_m|Ha_z]; [exact Ha_m|].
      exfalso.
      apply elem_of_singleton in Ha_z. subst a.
      apply Hzfresh.
	      apply elem_of_union_l.
	      apply elem_of_union_r.
	      apply Hfv in Ha.
	      rewrite fv_tapp_tm in Ha.
	      cbn [fv_tm fv_value] in Ha.
	      pose proof (cty_open_fv_subset 0 x τ z) as Hopen_fv.
      assert (Hx_m : x ∈ world_dom (m : WorldT)).
      { eapply ty_denote_gas_ret_fvar_world_dom. exact Harg. }
	      clear -Hzfresh Ha Hopen_fv Hx_m. better_set_solver.
    }
    pose proof (proj1 (res_models_minimal_on
      (world_dom (m : WorldT)) mz
      (ty_denote_gas gas
        (<[LVFree x := erase_ty τx]> Σrel)
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)))
      Hfv_target) Htarget_mz) as Hmin.
    rewrite Hmz_restrict_m in Hmin.
    exact Hmin.
  }
  subst gas.
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
