(** * ContextTyping.SoundnessMatch

    Match proof support for the direct Fundamental theorem. *)

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
From ContextTyping Require Import Typing SoundnessLam.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma res_fiber_from_projection_empty_self (m : WfWorldT) :
  res_fiber_from_projection m ∅ (∅ : StoreT) m.
Proof.
  split.
  - destruct (world_wf m) as [[σ Hσ] _].
    exists σ. split; [exact Hσ|].
    apply storeA_restrict_empty_set.
  - apply world_ext.
    + reflexivity.
    + intros σ. split.
      * intros Hσ. split; [exact Hσ|].
        apply storeA_restrict_empty_set.
      * intros [Hσ _]. exact Hσ.
Qed.

Lemma res_models_fibvars_empty_elim
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FFibVars ∅ φ ->
  m ⊨ φ.
Proof.
  intros Hfib.
  unfold res_models in Hfib |- *.
  cbn [formula_measure res_models_fuel] in Hfib |- *.
  destruct Hfib as [_ [_ Hfib]].
  specialize (Hfib (∅ : StoreT) m (res_fiber_from_projection_empty_self m)).
  rewrite formula_msubst_store_empty in Hfib by reflexivity.
  models_fuel_irrel Hfib.
Qed.

Lemma context_typing_wf_match_inv Σ Γ x et ef τ :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  erase_ctx Γ ⊢ᵥ vfvar x ⋮ TBase TBool /\
  erase_ctx Γ ⊢ₑ et ⋮ erase_ty τ /\
  erase_ctx Γ ⊢ₑ ef ⋮ erase_ty τ.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic.
  inversion Hbasic; subst; eauto.
Qed.

Lemma ty_denote_over_ret_fvar_const_lookup
    gas (Δ : lty_env) x c (m : WfWorldT) σ :
  lty_env_closed Δ ->
  m ⊨ ty_denote_gas (S gas) Δ
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vfvar x)) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst c).
Proof.
  intros HΔclosed Hden Hσ.
  set (τc := CTOver (base_ty_of_const c)
    (mk_q_eq (vbvar 0) (vconst c))) in *.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hden) as Hguard.
  pose proof Hguard as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [_ [Hworld [Hbasic Htotal]]].
  assert (Hxdom : x ∈ world_dom (m : WorldT)).
  { exact (ty_denote_gas_ret_fvar_world_dom (S gas) Δ τc x m Hden). }
  pose proof Hden as Hden_body.
  cbn [ty_denote_gas] in Hden_body.
  rewrite res_models_and_iff in Hden_body.
  destruct Hden_body as [_ Hforall].
  destruct (res_models_forall_rev m _ Hforall) as [L Hforall_open].
  pose (y := fresh_for
    (L ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Δ) ∪ {[x]})).
  assert (Hyfresh :
      y ∉ L ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Δ) ∪ {[x]}).
  { subst y. apply fresh_for_not_in. }
  assert (HyL : y ∉ L) by better_set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by better_set_solver.
  assert (HyΔ : LVFree y ∉ dom Δ).
  {
    intros Hy.
    apply lvars_fv_elem in Hy.
    apply Hyfresh.
    better_set_solver.
  }
  assert (Hyx : y <> x) by set_solver.
  assert (Hye : y ∉ fv_tm (tret (vfvar x))).
  { cbn [fv_tm fv_value]. set_solver. }
  destruct (expr_result_extension_witness_exists (tret (vfvar x)) y Hye)
    as [Fx HFx].
  assert (Happ : extension_applicable Fx m).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin. rewrite Hin.
      cbn [fv_tm fv_value]. set_solver.
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout. rewrite Hout. set_solver.
  }
  destruct (res_extend_by_exists m Fx Happ) as [mx Hext].
  pose proof (res_extend_by_dom m Fx mx Hext) as Hmxdom.
  pose proof (res_extend_by_restrict_base m Fx mx Hext) as Hmxrestrict.
	  assert (Hopened :
	      mx ⊨ formula_open 0 y
	        (FImpl
	          (expr_result_formula (tm_shift 0 (tret (vfvar x))) (LVBound 0))
	          (FFibVars
	            (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})
	            (FOver (FAtom
	              (mk_q_eq (vbvar 0) (vconst c))))))).
  {
    eapply Hforall_open; [exact HyL| |exact Hmxrestrict].
    rewrite Hmxdom.
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in Hout. rewrite Hout. reflexivity.
	  }
	  rewrite !formula_open_impl in Hopened.
	  rewrite formula_open_expr_result_formula_shift0 in Hopened
	    by (constructor || cbn [fv_tm fv_value]; set_solver).
  rewrite formula_open_fibvars in Hopened.
  rewrite formula_open_over in Hopened.
  rewrite formula_open_atom in Hopened
    by apply const_qual_dom_bound_fresh.
  replace
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
    with
      (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
        {[LVFree y]})
    in Hopened.
  2:{
    rewrite const_qual_vars_bound, const_qual_open_vars.
    replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
      with (∅ : lvset) by better_set_solver.
    replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
      with (∅ : lvset) by better_set_solver.
    rewrite set_swap_empty. reflexivity.
  }
  assert (Hyden :
      mx ⊨ ty_denote_gas (S gas) (<[LVFree y := erase_ty τc]> Δ)
        τc (tret (vfvar y))).
  {
    eapply ty_denote_gas_result_ext; eauto.
  }
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hyden) as Hyguard.
  pose proof Hyguard as Hyguard_parts.
  repeat rewrite res_models_and_iff in Hyguard_parts.
  destruct Hyguard_parts as [_ [Hyworld _]].
  pose proof (ty_denote_gas_ret_fvar_relevant_lookup
    (S gas) (<[LVFree y := erase_ty τc]> Δ) τc y mx Hyden)
    as Hylookup_rel.
	  assert (Hexpr_y :
	      mx ⊨ expr_result_formula (tret (vfvar x)) (LVFree y)).
  {
    assert (Hfv :
        lvars_of_atoms (fv_tm (tret (vfvar x))) ⊆
        dom (relevant_env Δ τc (tret (vfvar x)))).
    {
      apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      exact (basic_tm_has_ltype_lvars _ _ _ Hty).
    }
    assert (Htotal_atom : expr_total_on_atom_world (tret (vfvar x)) m).
    { apply expr_total_formula_to_atom_world. exact Htotal. }
	    eapply expr_result_formula_of_result_extends; eauto.
	  }
	  pose proof (res_models_impl_elim mx _ _ Hopened Hexpr_y)
	    as Hfib_over.
  assert (Hfib_empty :
      mx ⊨ FFibVars ∅
        (FOver (FAtom
          (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))))).
  {
    replace (∅ : lvset)
      with (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
        {[LVFree y]})
      by (rewrite const_qual_open_vars; better_set_solver).
    exact Hfib_over.
  }
  pose proof (res_models_fibvars_empty_elim mx _ Hfib_empty) as Hover.
  unfold res_models in Hover.
  cbn [formula_measure res_models_fuel] in Hover.
  destruct Hover as [_ [mo [Hsub_mx_mo Hqual_mo]]].
  assert (Hqual_model :
      mo ⊨ FAtom
        (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))).
  {
    unfold res_models.
    models_fuel_irrel Hqual_mo.
  }
  assert (Hxσdom : x ∈ dom (σ : StoreT)).
  {
    change (x ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact Hxdom.
  }
  destruct (σ !! x) as [vx|] eqn:Hσx.
  2:{
    apply not_elem_of_dom in Hσx. contradiction.
  }
  set (σX := store_restrict σ (ext_in Fx)).
  assert (HσXdom : dom (σX : StoreT) = ext_in Fx).
  {
    subst σX.
    eapply extA_projection_dom; eauto.
  }
  destruct (extA_rel_nonempty Fx σX HσXdom)
    as [we [σe [HFrel Hσe]]].
  set (σmx := σ ∪ σe : StoreT).
  assert (Hσmx : (mx : WorldT) σmx).
  {
    apply (proj2 (resA_extend_by_store_iff m Fx mx σmx Hext)).
    exists σ, we, σe. repeat split; eauto.
  }
  destruct Hsub_mx_mo as [_ Hsub_stores].
  assert (Hσmx_mo : (mo : WorldT) σmx).
  { apply Hsub_stores. exact Hσmx. }
  pose proof (const_type_qualifier_open_lookup
    c y mo σmx Hqual_model Hσmx_mo) as Hσmx_y_c.
  assert (Hσmx_x : σmx !! x = Some vx).
  {
    subst σmx.
    apply map_lookup_union_Some_raw. left. exact Hσx.
  }
  assert (Hclosed_ret_m : wfworld_closed_on (fv_tm (tret (vfvar x))) m).
  {
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    exact (basic_tm_has_ltype_lvars _ _ _ Hty).
  }
  assert (Hrestrict_eq :
      store_restrict σmx (fv_tm (tret (vfvar x))) =
      store_restrict σ (fv_tm (tret (vfvar x)))).
  {
    apply storeA_map_eq. intros z.
    rewrite !storeA_restrict_lookup.
    destruct (decide (z ∈ fv_tm (tret (vfvar x)))) as [Hz|Hz].
    - cbn [fv_tm fv_value] in Hz.
      apply elem_of_singleton in Hz. subst z.
      transitivity (Some vx); [exact Hσmx_x|symmetry; exact Hσx].
    - reflexivity.
  }
  assert (Hclosed_ret :
      store_closed (store_restrict σmx (fv_tm (tret (vfvar x))))).
  { rewrite Hrestrict_eq. exact (Hclosed_ret_m σ Hσ). }
  assert (Heval_ret :
      tm_eval_in_store (store_restrict σmx (fv_tm (tret (vfvar x))))
        (tret (vfvar x)) vx).
  {
    apply tm_eval_in_store_ret_fvar_lookup; [exact Hclosed_ret|].
    apply storeA_restrict_lookup_some_2.
    - exact Hσmx_x.
    - cbn [fv_tm fv_value]. set_solver.
  }
  pose proof (result_extension_store_lookup_output
    (tret (vfvar x)) y Fx m mx σmx vx HFx Hext Hσmx Heval_ret)
    as Hσmx_y_vx.
  congruence.
Qed.

Lemma match_true_lookup_of_bool_precise
    Δ x (m : WfWorldT) σ :
  m ⊨ ty_denote (erase_ctx Δ) (bool_precise_ty true) (tret (vfvar x)) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst (cbool true)).
Proof.
  intros Hden Hσ.
  unfold ty_denote in Hden.
  unfold bool_precise_ty, precise_ty, over_ty, under_ty, bool_qual in Hden.
  cbn [cty_depth ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter.
  destruct Hinter as [Hover _].
  eapply ty_denote_over_ret_fvar_const_lookup with (gas := 0); eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma match_false_lookup_of_bool_precise
    Δ x (m : WfWorldT) σ :
  m ⊨ ty_denote (erase_ctx Δ) (bool_precise_ty false) (tret (vfvar x)) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst (cbool false)).
Proof.
  intros Hden Hσ.
  unfold ty_denote in Hden.
  unfold bool_precise_ty, precise_ty, over_ty, under_ty, bool_qual in Hden.
  cbn [cty_depth ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter.
  destruct Hinter as [Hover _].
  eapply ty_denote_over_ret_fvar_const_lookup with (gas := 0); eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma tm_equiv_match_true_var
    Σ Γ x et ef τ (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cbool true))) ->
  tm_equiv_on m (et) (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hlookup σ v Hσ.
  pose proof (context_typing_wf_match_inv Σ Γ x et ef τ Hwf)
    as [_ [Het Hef]].
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic_match.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx) as Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld _]].
  set (X := fv_tm (tmatch (vfvar x) et ef)).
  assert (HclosedX : wfworld_closed_on X m).
  {
    subst X.
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    pose proof (basic_tm_has_ltype_of_atom_env_typing
      (erase_ctx Γ) (tmatch (vfvar x) et ef) (erase_ty τ)
      Hbasic_match) as Hbasic_match_lty.
    exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_match_lty).
  }
  assert (Hfv_et : fv_tm et ⊆ X) by (subst X; cbn [fv_tm]; better_set_solver).
  assert (Hfv_match : fv_tm (tmatch (vfvar x) et ef) ⊆ X)
    by (subst X; better_set_solver).
  assert (HxX : x ∈ X) by (subst X; cbn [fv_tm fv_value]; better_set_solver).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (HclosedX σ Hσ). }
  assert (HσX_lookup :
      store_restrict σ X !! x = Some (vconst (cbool true))).
  { apply storeA_restrict_lookup_some_2; [apply Hlookup; exact Hσ|exact HxX]. }
  split.
  - intros Het_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    apply (proj2 (tm_eval_in_store_match_true_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ et v X Hfv_et)).
    exact Het_eval.
  - intros Hmatch_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ et v X Hfv_et)).
    apply (proj1 (tm_eval_in_store_match_true_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    exact Hmatch_eval.
Qed.

Lemma tm_equiv_match_false_var
    Σ Γ x et ef τ (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cbool false))) ->
  tm_equiv_on m (ef) (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hlookup σ v Hσ.
  pose proof (context_typing_wf_match_inv Σ Γ x et ef τ Hwf)
    as [_ [Het Hef]].
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic_match.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx) as Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld _]].
  set (X := fv_tm (tmatch (vfvar x) et ef)).
  assert (HclosedX : wfworld_closed_on X m).
  {
    subst X.
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    pose proof (basic_tm_has_ltype_of_atom_env_typing
      (erase_ctx Γ) (tmatch (vfvar x) et ef) (erase_ty τ)
      Hbasic_match) as Hbasic_match_lty.
    exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_match_lty).
  }
  assert (Hfv_ef : fv_tm ef ⊆ X) by (subst X; cbn [fv_tm]; better_set_solver).
  assert (Hfv_match : fv_tm (tmatch (vfvar x) et ef) ⊆ X)
    by (subst X; better_set_solver).
  assert (HxX : x ∈ X) by (subst X; cbn [fv_tm fv_value]; better_set_solver).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (HclosedX σ Hσ). }
  assert (HσX_lookup :
      store_restrict σ X !! x = Some (vconst (cbool false))).
  { apply storeA_restrict_lookup_some_2; [apply Hlookup; exact Hσ|exact HxX]. }
  split.
  - intros Hef_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    apply (proj2 (tm_eval_in_store_match_false_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ ef v X Hfv_ef)).
    exact Hef_eval.
  - intros Hmatch_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ ef v X Hfv_ef)).
    apply (proj1 (tm_eval_in_store_match_false_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    exact Hmatch_eval.
Qed.

Lemma match_target_zero_from_branch
    Σ Γ x τ et ef ebranch (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  tm_equiv_on m ebranch (tmatch (vfvar x) et ef) ->
  m ⊨ ty_denote (erase_ctx Γ) τ ebranch ->
  m ⊨ ty_denote (erase_ctx Γ) τ (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hequiv Hbranch.
  unfold ty_denote in Hbranch |- *.
  eapply ty_denote_gas_tm_equiv.
  - split; [exact Hequiv|].
    split.
    + apply ty_denote_gas_zero_of_guard.
      eapply ty_denote_gas_guard. exact Hbranch.
    + assert (Hstatic :
          m ⊨ ty_static_guard_formula
            (atom_env_to_lty_env (erase_ctx Γ))
            τ (tmatch (vfvar x) et ef)).
      {
        exact (context_typing_wf_denot_static_guard_full
          Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx).
      }
      assert (Htotal_branch : m ⊨ expr_total_formula ebranch).
      {
        pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch) as Hguard.
        repeat rewrite res_models_and_iff in Hguard.
        tauto.
      }
      assert (Hlc_match : lc_tm (tmatch (vfvar x) et ef)).
      {
        pose proof (context_typing_wf_basic_typing
          Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic.
        exact (typing_tm_lc _ _ _ Hbasic).
      }
      assert (Hfv_match :
          fv_tm (tmatch (vfvar x) et ef) ⊆ world_dom (m : WorldT)).
      {
        unfold ty_static_guard_formula in Hstatic.
        repeat rewrite res_models_and_iff in Hstatic.
        destruct Hstatic as [_ [Hworld Hbasic]].
        apply expr_basic_typing_formula_models_iff in Hbasic
          as [_ [_ Hbasic_lty]].
        apply basic_world_formula_models_iff in Hworld
          as [_ [Hworld_dom _]].
        pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_lty) as Hlvars.
        intros z Hz.
        apply Hworld_dom.
        apply lvars_fv_elem.
        apply Hlvars.
        unfold lvars_of_atoms. apply elem_of_map.
        exists z. split; [reflexivity|exact Hz].
      }
      apply ty_denote_gas_zero_of_guard.
      eapply ty_guard_relevant_of_static_full_total; [exact Hstatic|].
      eapply tm_equiv_total; eauto.
  - exact Hbranch.
Qed.

Lemma context_typing_wf_match_sum_l
    Σ Γt Γf x τt τf et ef (mt : WfWorldT) :
  context_typing_wf Σ (CtxSum Γt Γf)
    (tmatch (vfvar x) et ef) (CTSum τt τf) ->
  mt ⊨ ctx_denote_under Σ Γt ->
  context_typing_wf Σ Γt (tmatch (vfvar x) et ef) τt.
Proof.
  intros Hwf HΓt.
  destruct Hwf as [[Hbasic_sum _] [Hty_sum Htm]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [Hbasic_t [_ [_ _]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [Hty_t [_ _]].
  cbn [erase_ctx erase_ty] in Htm.
  split.
  - split; [exact Hbasic_t|exists mt; exact HΓt].
  - split; [exact Hty_t|exact Htm].
Qed.

Lemma context_typing_wf_match_sum_r
    Σ Γt Γf x τt τf et ef (mf : WfWorldT) :
  context_typing_wf Σ (CtxSum Γt Γf)
    (tmatch (vfvar x) et ef) (CTSum τt τf) ->
  mf ⊨ ctx_denote_under Σ Γf ->
  context_typing_wf Σ Γf (tmatch (vfvar x) et ef) τf.
Proof.
  intros Hwf HΓf.
  destruct Hwf as [[Hbasic_sum _] [Hty_sum Htm]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [Hbasic_f [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [Hty_f Herase_ty]].
  cbn [erase_ctx erase_ty] in Htm.
  split.
  - split; [exact Hbasic_f|exists mf; exact HΓf].
  - split.
    + replace (dom (erase_ctx Γf)) with (dom (erase_ctx Γt)).
      * exact Hty_f.
      * rewrite Herase_ctx. reflexivity.
    + rewrite <- Herase_ctx.
      rewrite <- Herase_ty.
      exact Htm.
Qed.

Lemma expr_total_formula_sum_intro e
    (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2) :
  m1 ⊨ expr_total_formula e ->
  m2 ⊨ expr_total_formula e ->
  res_sum m1 m2 Hdef ⊨ expr_total_formula e.
Proof.
  intros Htotal1 Htotal2.
  apply expr_total_formula_to_atom_world in Htotal1.
  apply expr_total_formula_to_atom_world in Htotal2.
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal1 as [Hdom1 Hstores1].
  destruct Htotal2 as [_ Hstores2].
  split.
  - rewrite !res_lift_free_dom in Hdom1 |- *.
    simpl. exact Hdom1.
  - intros τ Hτ.
    unfold res_lift_free in Hτ.
    cbn [worldA_stores] in Hτ.
    destruct Hτ as [σ [Hσsum ->]].
    cbn [res_sum raw_sum worldA_stores] in Hσsum.
    destruct Hσsum as [Hσ1 | Hσ2].
    + apply Hstores1.
      exists σ. split; [exact Hσ1|reflexivity].
    + apply Hstores2.
      exists σ. split; [exact Hσ2|reflexivity].
Qed.

Lemma fundamental_match_both_case Σ Γt Γf x τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf)
    (tmatch (vfvar x) et ef) (CTSum τt τf) ->
  (ctx_denote_under Σ Γt ⊫
    ty_denote_under Σ Γt (bool_precise_ty true) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γf ⊫
    ty_denote_under Σ Γf (bool_precise_ty false) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γt ⊫ ty_denote_under Σ Γt τt et) ->
  (ctx_denote_under Σ Γf ⊫ ty_denote_under Σ Γf τf ef) ->
  ctx_denote_under Σ (CtxSum Γt Γf) ⊫
    ty_denote_under Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hbool_t Hbool_f HIHt HIHf m Hctx.
  pose proof Hwf as Hwf_for_eqs.
  destruct Hwf_for_eqs as [[Hbasic_sum _] [Hty_sum _]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [_ [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [_ Herase_ty]].
  destruct (ctx_denote_under_sum_elim Σ Γt Γf m Hctx)
    as [mt [mf [Hdef [Hle [HΓt HΓf]]]]].
  pose proof (Hbool_t mt HΓt) as Hbt.
  pose proof (Hbool_f mf HΓf) as Hbf.
  pose proof (HIHt mt HΓt) as Het.
  pose proof (HIHf mf HΓf) as Hef.
  pose proof (context_typing_wf_match_sum_l
    Σ Γt Γf x τt τf et ef mt Hwf HΓt) as Hwf_t.
  pose proof (context_typing_wf_match_sum_r
    Σ Γt Γf x τt τf et ef mf Hwf HΓf) as Hwf_f.
  pose proof (match_true_lookup_of_bool_precise Γt x mt) as Hlookup_t.
  pose proof (tm_equiv_match_true_var
    Σ Γt x et ef τt mt Hwf_t HΓt
    (fun σ Hσ => Hlookup_t σ Hbt Hσ)) as Heq_t.
  pose proof (match_target_zero_from_branch
    Σ Γt x τt et ef et mt Hwf_t HΓt Heq_t Het) as Hmatch_t.
  pose proof (match_false_lookup_of_bool_precise Γf x mf) as Hlookup_f.
  pose proof (tm_equiv_match_false_var
    Σ Γf x et ef τf mf Hwf_f HΓf
    (fun σ Hσ => Hlookup_f σ Hbf Hσ)) as Heq_f.
  pose proof (match_target_zero_from_branch
    Σ Γf x τf et ef ef mf Hwf_f HΓf Heq_f Hef) as Hmatch_f.
  unfold ty_denote_under, ty_denote in Hmatch_t, Hmatch_f |- *.
  rewrite <- (ty_denote_gas_saturate
      (Nat.max (cty_depth τt) (cty_depth τf))
      (atom_env_to_lty_env (erase_ctx Γt)) τt
      (tmatch (vfvar x) et ef)) in Hmatch_t by lia.
  rewrite <- (ty_denote_gas_saturate
      (Nat.max (cty_depth τt) (cty_depth τf))
      (atom_env_to_lty_env (erase_ctx Γf)) τf
      (tmatch (vfvar x) et ef)) in Hmatch_f by lia.
  replace (atom_env_to_lty_env (erase_ctx Γf))
    with (atom_env_to_lty_env (erase_ctx Γt)) in Hmatch_f
    by (rewrite Herase_ctx; reflexivity).
  assert (Htotal_t : mt ⊨ expr_total_formula (tmatch (vfvar x) et ef)).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_t) as Hguard_t.
    repeat rewrite res_models_and_iff in Hguard_t.
    tauto.
  }
  assert (Htotal_f : mf ⊨ expr_total_formula (tmatch (vfvar x) et ef)).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_f) as Hguard_f.
    repeat rewrite res_models_and_iff in Hguard_f.
    tauto.
  }
  assert (Htotal_m : m ⊨ expr_total_formula (tmatch (vfvar x) et ef)).
  {
    eapply res_models_kripke; [exact Hle|].
    eapply expr_total_formula_sum_intro; eauto.
  }
  assert (Hstatic :
      m ⊨ ty_static_guard_formula
        (atom_env_to_lty_env (erase_ctx (CtxSum Γt Γf)))
        (CTSum τt τf) (tmatch (vfvar x) et ef)).
  {
    exact (context_typing_wf_denot_static_guard_full
      Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch (vfvar x) et ef) m Hwf Hctx).
  }
  cbn [cty_depth ty_denote_gas].
  eapply res_models_and_intro_from_models.
  - eapply ty_guard_relevant_of_static_full_total; eauto.
  - eapply res_models_plus_intro; [exact Hle|exact Hmatch_t|exact Hmatch_f].
Qed.

Lemma fundamental_match_true_case Σ Γ x τ et ef :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (bool_precise_ty true) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ et) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hbool HIH m Hctx.
  pose proof (Hbool m Hctx) as Hbt.
  pose proof (HIH m Hctx) as Het.
  pose proof (match_true_lookup_of_bool_precise Γ x m) as Hlookup.
  pose proof (tm_equiv_match_true_var
    Σ Γ x et ef τ m Hwf Hctx
    (fun σ Hσ => Hlookup σ Hbt Hσ)) as Heq.
  eapply match_target_zero_from_branch; eauto.
Qed.

Lemma fundamental_match_false_case Σ Γ x τ et ef :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (bool_precise_ty false) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ ef) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hbool HIH m Hctx.
  pose proof (Hbool m Hctx) as Hbf.
  pose proof (HIH m Hctx) as Hef.
  pose proof (match_false_lookup_of_bool_precise Γ x m) as Hlookup.
  pose proof (tm_equiv_match_false_var
    Σ Γ x et ef τ m Hwf Hctx
    (fun σ Hσ => Hlookup σ Hbf Hσ)) as Heq.
  eapply match_target_zero_from_branch; eauto.
Qed.
