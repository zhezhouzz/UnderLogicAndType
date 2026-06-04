(** * Denotation.ContextTypeDenotationSaturateMain

    Main term-result-equivalence transport theorem. *)

From Denotation Require Import Notation ContextTypeDenotationOpen.
From Denotation Require Import
  ContextTypeDenotationSaturateCore
  ContextTypeDenotationSaturateBody
  ContextTypeDenotationSaturateArrow
  ContextTypeDenotationSaturateWand.

Section ContextTypeDenotation.

Lemma denot_ty_lvar_gas_tm_result_equiv
    gas Σ τ e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e2.
Proof.
  revert Σ τ e1 e2 m.
  induction gas as [|gas IH]; intros Σ τ e1 e2 m Hequiv Hm.
  - exact (typed_total_tm_result_equiv_on_target_zero _ _ _ _ _ Hequiv).
  - pose proof (typed_total_tm_result_equiv_on_target_zero
      Σ τ m e1 e2 Hequiv) as Hzero_tgt.
    pose proof (denot_ty_lvar_gas_guard_of_zero
      Σ τ e2 m Hzero_tgt) as Hguard_tgt.
    repeat rewrite res_models_and_iff in Hguard_tgt.
	    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
	      cbn [denot_ty_lvar_gas denot_guard_formula] in Hm |- *;
	      unfold denot_guard_formula in Hm |- *;
	      repeat rewrite res_models_and_iff in Hm |- *;
	      destruct Hm as [_ Hbody]; split.
		    all: try exact Hguard_tgt.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_over_body; eauto.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_under_body; eauto.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_inter_body; eauto.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_union_body; eauto.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_sum_body; eauto.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_arrow_body; eauto.
	    + eapply denot_ty_lvar_gas_tm_result_equiv_wand_body; eauto.
	Qed.

Lemma denot_ty_lvar_gas_result_alias_to_var
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  m ⊨ denot_ty_lvar_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros HΣclosed HΣx Hres Hm.
  pose proof (denot_ty_lvar_gas_guard gas Σ τ e m Hm) as Hguard_src.
  pose proof (denot_ty_lvar_gas_result_alias_guard
    Σ τ e x m HΣclosed HΣx Hres Hguard_src) as Hguard_tgt.
  pose proof (denot_ty_lvar_gas_zero_of_guard Σ τ e m Hguard_src)
    as Hzero_src.
  pose proof (denot_ty_lvar_gas_zero_of_guard
    Σ τ (tret (vfvar x)) m Hguard_tgt) as Hzero_tgt.
  pose proof Hguard_tgt as Hguard_tgt_parts.
  repeat rewrite res_models_and_iff in Hguard_tgt_parts.
  destruct Hguard_tgt_parts as [_ [_ [_ Htotal_tgt]]].
  eapply denot_ty_lvar_gas_tm_result_equiv.
  - split.
    + eapply tm_result_equiv_on_result_alias; eauto.
    + split; [exact Hzero_src | exact Hzero_tgt].
  - exact Hm.
Qed.

Lemma denot_ty_lvar_gas_result_extension_to_var
    gas (Σ : lty_env) τ e x
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  lty_env_closed Σ ->
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  mx ⊨ denot_ty_lvar_gas gas
    (<[LVFree x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  intros HΣclosed HxΣ HFx Hext Hm.
  pose proof (denot_ty_lvar_gas_guard gas Σ τ e m Hm) as Hguard_full.
  pose proof Hguard_full as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Hxτ : LVFree x ∉ context_ty_lvars τ).
  {
    intros Hbad.
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
    destruct Hbasicτ as [Hτdom _].
    apply HxΣ.
    eapply denot_relevant_env_dom_subset_direct.
    eapply Hτdom. exact Hbad.
  }
  assert (Hxe : x ∉ fv_tm e).
  { exact (expr_result_extension_witness_fresh _ _ _ HFx). }
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ]> ∅)
        (res_restrict m (ext_in Fx)) Fx).
  {
    eapply expr_result_extension_has_ltype_from_source_guard;
      [exact HΣclosed|exact HxΣ|exact HFx|exact Hext|].
    exact Hguard_full.
  }
  pose proof (denot_ty_lvar_gas_extend_typed_extension
    gas Σ τ e x (erase_ty τ) m mx Fx
    HxΣ Hxτ Hxe HFx_ltype Hext Hm) as Hmx_source.
  assert (Hfv_e :
      lvars_of_atoms (fv_tm e) ⊆ dom (denot_relevant_env Σ τ e)).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    eapply basic_tm_has_ltype_lvars. exact Hty.
  }
  assert (Htotal_world : expr_total_on_atom_world e m).
  { eapply expr_total_formula_to_atom_world. exact Htotal. }
  assert (Hres : mx ⊨ expr_result_formula e (LVFree x)).
  {
    eapply expr_result_formula_of_result_extends
      with (Σ := denot_relevant_env Σ τ e); eauto.
  }
  eapply denot_ty_lvar_gas_result_alias_to_var; eauto.
  - apply lty_env_closed_insert_free; eauto.
  - apply map_lookup_insert.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_subset_relevant gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  rewrite <- (formula_lvars_at_fv 0).
  transitivity (lvars_fv (tm_lvars_at 0 e ∪ context_ty_lvars_at 0 τ)).
  - apply lvars_fv_mono.
    apply formula_lvars_at_denot_ty_lvar_gas_subset_relevant.
  - change (tm_lvars_at 0 e) with (tm_lvars e).
    change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ).
    replace (tm_lvars e ∪ context_ty_lvars τ)
      with (denot_relevant_lvars τ e)
      by (unfold denot_relevant_lvars; set_solver).
    rewrite denot_relevant_lvars_fv.
    set_solver.
Qed.

Lemma denot_ty_lvar_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  eapply denot_relevant_basic_world_typing_wfworld_closed_on_term; eauto.
Qed.

Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_lvar_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ denot_ty_lvar_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ denot_ty_lvar_gas gas Σ τ (e2 ^^ x) ->
  mx ⊨ denot_ty_lvar_gas gas Σ τ (tlete e1 e2).
Proof.
  intros Hx_e2 HFx Hext Hzero_body Hzero_tlet Hbody.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ τ (tlete e1 e2) mx Hzero_tlet) as Hguard_tlet.
  pose proof Hguard_tlet as Hguard_tlet_parts.
  repeat rewrite res_models_and_iff in Hguard_tlet_parts.
  destruct Hguard_tlet_parts as [_ [_ [Hbasic_tlet Htotal_tlet]]].
  apply expr_basic_typing_formula_models_iff in Hbasic_tlet
    as [HlcΣ [_ Hty_tlet]].
  pose proof (basic_tm_has_ltype_lc _ _ _ HlcΣ Hty_tlet) as Hlc_tlet.
  pose proof (denot_ty_lvar_guard_wfworld_closed_on_term
    Σ τ (tlete e1 e2) mx Hguard_tlet) as Hclosed_tlet.
  eapply denot_ty_lvar_gas_tm_result_equiv.
  - split.
    + eapply tm_result_equiv_on_tlete_body_extension; eauto.
    + split; [exact Hzero_body|exact Hzero_tlet].
  - exact Hbody.
Qed.


End ContextTypeDenotation.
