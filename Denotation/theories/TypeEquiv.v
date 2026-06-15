(** * Denotation.TypeEquiv

    Main term-result-equivalence transport theorem. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand.

Section TypeDenote.

Lemma ty_static_guard_relevant_of_full
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ ty_static_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic |- *.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [Hwf [Hworld Hbasic]].
  repeat rewrite res_models_and_iff.
  assert (Hworld_rel :
      m ⊨ basic_world_formula (relevant_env Σ τ e)).
  {
    eapply basic_world_formula_subenv; [|exact Hworld].
    intros v T Hv.
    unfold relevant_env, lty_env_restrict_lvars in Hv.
    apply storeA_restrict_lookup_some in Hv as [_ Hv].
    exact Hv.
  }
  pose proof Hworld as Hworld_full.
  apply basic_world_formula_models_iff in Hworld_full
    as [Hlc_full _].
  assert (Hlc_rel : lc_lvars (dom (relevant_env Σ τ e))).
  {
    intros v Hv.
    apply Hlc_full.
    unfold relevant_env, lty_env_restrict_lvars in Hv.
    rewrite storeA_restrict_dom in Hv.
    better_set_solver.
  }
  split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf
      as [Hlc [Hscope Hτ]].
    apply basic_world_formula_models_iff in Hworld_rel
      as [_ [Hscope_rel _]].
    split; [exact Hlc_rel|]. split; [exact Hscope_rel|].
    apply basic_context_ty_lvars_relevant_env. exact Hτ.
  - split; [exact Hworld_rel|].
    apply expr_basic_typing_formula_models_iff.
    apply expr_basic_typing_formula_models_iff in Hbasic
      as [Hlc [_ Hty]].
    apply basic_world_formula_models_iff in Hworld_rel
      as [_ [Hscope_rel _]].
    split; [exact Hlc_rel|]. split; [exact Hscope_rel|].
    unfold relevant_env.
    eapply basic_tm_has_ltype_restrict_lvars_lc.
    + exact Hty.
    + exact (basic_tm_has_ltype_lc _ _ _ Hlc Hty).
    + unfold relevant_lvars. set_solver.
Qed.

Lemma ty_guard_relevant_of_static_full_total
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ expr_total_formula e ->
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  intros Hstatic Htotal.
  pose proof (ty_static_guard_relevant_of_full Σ τ e m Hstatic)
    as Hstatic_rel.
  unfold ty_static_guard_formula in Hstatic_rel.
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff in Hstatic_rel.
  destruct Hstatic_rel as [Hwf [Hworld Hbasic]].
  repeat rewrite res_models_and_iff.
  split; [exact Hwf|].
  split; [exact Hworld|].
  split; [exact Hbasic|exact Htotal].
Qed.

Lemma ty_denote_gas_zero_transport_static_tm_equiv
    (Σ : lty_env) τ e_src e_tgt (m : WfWorldT) :
  tm_equiv_on m e_src e_tgt ->
  m ⊨ ty_static_guard_formula Σ τ e_tgt ->
  lc_tm e_tgt ->
  fv_tm e_tgt ⊆ world_dom (m : WorldT) ->
  m ⊨ ty_denote_gas 0 Σ τ e_src ->
  m ⊨ ty_denote_gas 0 Σ τ e_tgt.
Proof.
  intros Heq Hstatic Hlc Hfv Hzero_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ e_src m Hzero_src) as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [_ [_ Htotal_src]]].
  pose proof (tm_equiv_total m e_src e_tgt Heq Hlc Hfv Htotal_src)
    as Htotal_tgt.
  apply ty_denote_gas_zero_of_guard.
  eapply ty_guard_relevant_of_static_full_total; eauto.
Qed.

Lemma ty_denote_gas_zero_tret_of_static_guard
    (Σ : lty_env) τ v (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ (tret v) ->
  m ⊨ ty_denote_gas 0 Σ τ (tret v).
Proof.
  intros Hstatic.
  assert (Htotal : m ⊨ expr_total_formula (tret v)).
  {
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [_ [Hworld Hbasic]].
    eapply expr_total_formula_tret_of_basic; eauto.
  }
  apply ty_denote_gas_zero_of_guard.
  eapply ty_guard_relevant_of_static_full_total; eauto.
Qed.

Lemma ty_static_guard_fv_tm_subset
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  fv_tm e ⊆ world_dom (m : WorldT).
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld Hbasic]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty)
    as Htm_lvars.
  apply basic_world_formula_models_iff in Hworld
    as [_ [Hscope _]].
  intros a Ha.
  apply Hscope.
  apply lvars_fv_elem.
  apply Htm_lvars.
  unfold lvars_of_atoms.
  apply elem_of_map. exists a. split; [reflexivity|exact Ha].
Qed.

Lemma ty_static_guard_fv_subset
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT).
Proof.
  intros Hstatic a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - eapply ty_static_guard_fv_tm_subset; eauto.
  - unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [Hwf [Hworld _]].
    pose proof (context_ty_wf_formula_fv_cty_subset
      Σ τ m Hwf a Ha) as HΣa.
    apply basic_world_formula_models_iff in Hworld
      as [_ [Hscope _]].
    exact (Hscope _ HΣa).
Qed.

Lemma ty_denote_gas_fv_tm_subset
    gas (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  fv_tm e ⊆ world_dom (m : WorldT).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Htm_lvars.
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
  intros a Ha.
  apply Hscope.
  apply lvars_fv_elem.
  apply Htm_lvars.
  unfold lvars_of_atoms.
  apply elem_of_map. exists a. split; [reflexivity|exact Ha].
Qed.

Lemma ty_static_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld Hbasic]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [_ [_ Hty]].
  eapply basic_world_formula_wfworld_closed_on_atoms;
    [eapply basic_tm_has_ltype_lvars; exact Hty|exact Hworld].
Qed.

Lemma ty_static_guard_basic_world
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ basic_world_formula Σ.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  tauto.
Qed.

Lemma ty_static_guard_insert_irrelevant
    (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ relevant_lvars τ e ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ ty_static_guard_formula (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxrel Hworld_insert Hstatic.
  unfold ty_static_guard_formula in Hstatic |- *.
  repeat rewrite res_models_and_iff in Hstatic |- *.
  destruct Hstatic as [Hwf [Hworld Hbasic]].
  split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf
      as [_ [_ Hτwf]].
    apply basic_world_formula_models_iff in Hworld_insert
      as [Hlc_insert [Hscope_insert _]].
    split; [exact Hlc_insert|]. split; [exact Hscope_insert|].
    eapply basic_context_ty_lvars_mono; [|exact Hτwf].
    rewrite dom_insert_L. set_solver.
  - split; [exact Hworld_insert|].
    apply expr_basic_typing_formula_models_iff.
    apply expr_basic_typing_formula_models_iff in Hbasic
      as [_ [_ Hety]].
    apply basic_world_formula_models_iff in Hworld_insert
      as [Hlc_insert [Hscope_insert _]].
    split; [exact Hlc_insert|]. split; [exact Hscope_insert|].
    eapply basic_tm_has_ltype_weaken; [exact Hety|].
    apply insert_subseteq.
    apply not_elem_of_dom. exact HxΣ.
Qed.

Lemma ty_denote_gas_tm_equiv
    gas Σ τ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ e1 ->
  m ⊨ ty_denote_gas gas Σ τ e2.
Proof.
  revert Σ τ e1 e2 m.
  induction gas as [|gas IH]; intros Σ τ e1 e2 m Hequiv Hm.
  - exact (typed_total_equiv_target_zero _ _ _ _ _ Hequiv).
  - pose proof (typed_total_equiv_target_zero
      Σ τ m e1 e2 Hequiv) as Hzero_tgt.
    pose proof (ty_denote_gas_guard_of_zero
      Σ τ e2 m Hzero_tgt) as Hguard_tgt.
    repeat rewrite res_models_and_iff in Hguard_tgt.
	    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
	      cbn [ty_denote_gas ty_guard_formula] in Hm |- *;
	      unfold ty_guard_formula in Hm |- *;
	      repeat rewrite res_models_and_iff in Hm |- *;
	      destruct Hm as [_ Hbody]; split.
		    all: try exact Hguard_tgt.
	    + eapply ty_denote_gas_tm_equiv_over_body; eauto.
	    + eapply ty_denote_gas_tm_equiv_under_body; eauto.
	    + eapply ty_denote_gas_tm_equiv_inter_body; eauto.
	    + eapply ty_denote_gas_tm_equiv_union_body; eauto.
	    + eapply ty_denote_gas_tm_equiv_sum_body; eauto.
	    + eapply ty_denote_gas_tm_equiv_arrow_body; eauto.
	    + eapply ty_denote_gas_tm_equiv_wand_body; eauto.
	Qed.

Lemma ty_denote_gas_result_alias
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros HΣclosed HΣx Hres Hm.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hm) as Hguard_src.
  pose proof (ty_denote_gas_result_alias_guard
    Σ τ e x m HΣclosed HΣx Hres Hguard_src) as Hguard_tgt.
  pose proof (ty_denote_gas_zero_of_guard Σ τ e m Hguard_src)
    as Hzero_src.
  pose proof (ty_denote_gas_zero_of_guard
    Σ τ (tret (vfvar x)) m Hguard_tgt) as Hzero_tgt.
  pose proof Hguard_tgt as Hguard_tgt_parts.
  repeat rewrite res_models_and_iff in Hguard_tgt_parts.
  destruct Hguard_tgt_parts as [_ [_ [_ Htotal_tgt]]].
  eapply ty_denote_gas_tm_equiv.
  - split.
    + eapply tm_equiv_result_alias; eauto.
    + split; [exact Hzero_src | exact Hzero_tgt].
  - exact Hm.
Qed.

Lemma ty_denote_gas_result_ext
    gas (Σ : lty_env) τ e x
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  lty_env_closed Σ ->
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  mx ⊨ ty_denote_gas gas
    (<[LVFree x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof.
  intros HΣclosed HxΣ HFx Hext Hm.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hm) as Hguard_full.
  pose proof Hguard_full as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Hxτ : LVFree x ∉ context_ty_lvars τ).
  {
    intros Hbad.
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
    destruct Hbasicτ as [Hτdom _].
    apply HxΣ.
    eapply relevant_env_dom_subset_direct.
    eapply Hτdom. exact Hbad.
  }
  assert (Hxe : x ∉ fv_tm e).
  { exact (expr_result_extension_witness_fresh _ _ _ HFx). }
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ]> ∅)
        (res_restrict m (ext_in Fx)) Fx).
  {
    eapply result_ext_typed_of_guard;
      [exact HΣclosed|exact HxΣ|exact HFx|exact Hext|].
    exact Hguard_full.
  }
  pose proof (ty_denote_gas_extend_typed_extension
    gas Σ τ e x (erase_ty τ) m mx Fx
    HxΣ Hxτ Hxe HFx_ltype Hext Hm) as Hmx_source.
  assert (Hfv_e :
      lvars_of_atoms (fv_tm e) ⊆ dom (relevant_env Σ τ e)).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    eapply basic_tm_has_ltype_lvars. exact Hty.
  }
  assert (Htotal_world : expr_total_on_atom_world e m).
  { eapply expr_total_formula_to_atom_world. exact Htotal. }
  assert (Hres : mx ⊨ expr_result_formula e (LVFree x)).
  {
    eapply expr_result_formula_of_result_extends
      with (Σ := relevant_env Σ τ e); eauto.
  }
  eapply ty_denote_gas_result_alias; eauto.
  - apply lty_env_closed_insert_free; eauto.
  - apply map_lookup_insert.
Qed.

Lemma formula_fv_ty_denote_gas_subset_relevant gas Σ τ e :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  rewrite <- (formula_lvars_at_fv 0).
  transitivity (lvars_fv (tm_lvars_at 0 e ∪ context_ty_lvars_at 0 τ)).
  - apply lvars_fv_mono.
    apply ty_denote_gas_lvars_subset.
  - change (tm_lvars_at 0 e) with (tm_lvars e).
    change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ).
    replace (tm_lvars e ∪ context_ty_lvars τ)
      with (relevant_lvars τ e)
      by (unfold relevant_lvars; set_solver).
    rewrite relevant_lvars_fv.
    set_solver.
Qed.

Lemma ty_denote_gas_restrict_ret_fvar_closed
    gas (Σ : lty_env) τ x (m : WfWorldT) :
  wf_context_ty_at 0 ∅ τ ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  res_restrict m ({[x]} : aset) ⊨
    ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros Hτ_closed Hden.
  assert (Hfv :
      formula_fv (ty_denote_gas gas Σ τ (tret (vfvar x))) ⊆ {[x]}).
  {
    pose proof (formula_fv_ty_denote_gas_subset_relevant
      gas Σ τ (tret (vfvar x))) as Hrel.
    pose proof (wf_context_ty_at_fv_subset 0 ∅ τ Hτ_closed) as Hτ_fv.
    intros y Hy.
    pose proof (Hrel y Hy) as Hyrel.
    relevant_lvars_norm_in Hyrel.
    better_set_solver.
  }
  exact (proj1 (res_models_minimal_on ({[x]} : aset) m
    (ty_denote_gas gas Σ τ (tret (vfvar x))) Hfv) Hden).
Qed.

Lemma ty_denote_gas_restrict_delete_fresh
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  x ∉ fv_tm e ∪ fv_cty τ ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  res_restrict m (world_dom (m : WorldT) ∖ {[x]}) ⊨
    ty_denote_gas gas Σ τ e.
Proof.
  intros Hfresh Hden.
  assert (Hfv_drop :
      formula_fv (ty_denote_gas gas Σ τ e) ⊆
      world_dom (m : WorldT) ∖ {[x]}).
  {
    pose proof (res_models_scoped _ _ Hden) as Hscope.
    pose proof (formula_fv_ty_denote_gas_subset_relevant gas Σ τ e) as Hfv.
    intros z Hz.
    pose proof (Hscope z Hz) as Hzdom.
    pose proof (Hfv z Hz) as Hzrel.
    apply elem_of_difference. split; [exact Hzdom|].
    intros Hzx.
    apply elem_of_singleton in Hzx. subst z.
    exact (Hfresh Hzrel).
  }
  exact (proj1 (res_models_minimal_on
    (world_dom (m : WorldT) ∖ {[x]}) m
    (ty_denote_gas gas Σ τ e) Hfv_drop) Hden).
Qed.

Lemma basic_tm_has_ltype_ret_fvar_lookup
    (Σ : lty_env) x T :
  basic_tm_has_ltype Σ (tret (vfvar x)) T ->
  Σ !! LVFree x = Some T.
Proof.
  intros Hty.
  inversion Hty as [Γ v U Hval| | | | |]; subst; clear Hty.
  inversion Hval; subst; eauto.
Qed.

Lemma ty_denote_gas_ret_fvar_relevant_lookup
    gas Σ τ x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  relevant_env Σ τ (tret (vfvar x)) !! LVFree x = Some (erase_ty τ).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard_formula
    gas Σ τ (tret (vfvar x)) m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [_ [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  apply basic_tm_has_ltype_ret_fvar_lookup in Hty.
  exact Hty.
Qed.

Lemma ty_denote_gas_ret_fvar_lookup
    gas Σ τ x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  Σ !! LVFree x = Some (erase_ty τ).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_ret_fvar_relevant_lookup
    gas Σ τ x m Hden) as Hlookup.
  unfold relevant_env, lty_env_restrict_lvars in Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
  exact Hlookup.
Qed.

Lemma ty_denote_gas_ret_fvar_world_dom
    gas Σ τ x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  x ∈ world_dom (m : WorldT).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard_formula
    gas Σ τ (tret (vfvar x)) m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hty_lvars.
  apply basic_world_formula_models_iff in Hworld as [_ [Hdom _]].
  apply Hdom.
  apply lvars_fv_elem.
  apply Hty_lvars.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
  set_solver.
Qed.

Lemma ty_denote_ret_fvar_base_const
    gas Σ τ b x (m : WfWorldT) :
  erase_ty τ = TBase b ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  forall σ,
    (m : WorldT) σ ->
    exists c,
      σ !! x = Some (vconst c) /\
      base_ty_of_const c = b.
Proof.
  intros Hτ Hden σ Hσ.
  pose proof (ty_denote_gas_guard gas Σ τ (tret (vfvar x)) m Hden)
    as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  pose proof (ty_denote_gas_ret_fvar_relevant_lookup
    gas Σ τ x m Hden) as HΣx.
  pose proof (ty_denote_gas_ret_fvar_world_dom
    gas Σ τ x m Hden) as Hx_dom.
  pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
  assert (Hxσdom : x ∈ dom (σ : StoreT)).
  { better_set_solver. }
  change (x ∈ dom (σ : gmap atom value)) in Hxσdom.
  apply elem_of_dom in Hxσdom as [v Hσx].
  apply basic_world_formula_models_iff in Hworld as [_ [_ Htyped]].
  unfold lworld_has_type, worldA_has_type in Htyped.
  destruct Htyped as [_ Hstores].
  specialize (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])).
  assert (Hlookup_lift :
      (lstore_lift_free σ : LStoreT) !! LVFree x = Some v).
  { rewrite lstore_lift_free_lookup_free. exact Hσx. }
  pose proof (Hstores (LVFree x) (erase_ty τ) v HΣx Hlookup_lift)
    as HvT.
  rewrite Hτ in HvT.
  apply empty_basic_value_base_inv in HvT as [c [Hv Hc]].
  exists c.
  split; [|exact Hc].
  subst v. exact Hσx.
Qed.

Lemma ty_denote_gas_drop_fresh_ext
    gas (Σ : lty_env) τ e x T (m mx : WfWorldT) Fx :
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT) ->
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas gas (<[LVFree x := T]> Σ) τ e ->
  m ⊨ ty_denote_gas gas Σ τ e.
Proof.
  intros Hfv_world HxΣ Hxτ Hxe Hext Hmx.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq
    gas Σ τ e x T HxΣ Hxτ Hxe) in Hmx.
  eapply res_models_from_restrict_extension_on_fv
    with (X := fv_tm e ∪ fv_cty τ) (n := mx).
  - apply formula_fv_ty_denote_gas_subset_relevant.
  - transitivity (fv_tm e ∪ fv_cty τ).
    + apply formula_fv_ty_denote_gas_subset_relevant.
    + exact Hfv_world.
  - transitivity m.
    + apply res_restrict_le.
    + eapply res_extend_by_le; eauto.
  - exact Hmx.
Qed.

Lemma expr_result_formula_of_result_extends_from_ty_guard
    (Σ : lty_env) τ e x (m mx : WfWorldT) Fx :
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e ->
  mx ⊨ expr_result_formula e (LVFree x).
Proof.
  intros HFx Hext Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic Htotal]]].
  assert (Hfv :
      lvars_of_atoms (fv_tm e) ⊆ dom (relevant_env Σ τ e)).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    exact (basic_tm_has_ltype_lvars _ _ _ Hty).
  }
  assert (Htotal_atom : expr_total_on_atom_world e m).
  { apply expr_total_formula_to_atom_world. exact Htotal. }
  eapply expr_result_formula_of_result_extends; eauto.
Qed.

Lemma denot_ty_lvar_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  eapply relevant_world_typing_closed_on_term; eauto.
Qed.

Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2).
Proof.
  intros Hx_e2 HFx Hext Hzero_body Hzero_tlet Hbody.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ (tlete e1 e2) mx Hzero_tlet) as Hguard_tlet.
  pose proof Hguard_tlet as Hguard_tlet_parts.
  repeat rewrite res_models_and_iff in Hguard_tlet_parts.
  destruct Hguard_tlet_parts as [_ [_ [Hbasic_tlet Htotal_tlet]]].
  apply expr_basic_typing_formula_models_iff in Hbasic_tlet
    as [HlcΣ [_ Hty_tlet]].
  pose proof (basic_tm_has_ltype_lc _ _ _ HlcΣ Hty_tlet) as Hlc_tlet.
  pose proof (denot_ty_lvar_guard_wfworld_closed_on_term
    Σ τ (tlete e1 e2) mx Hguard_tlet) as Hclosed_tlet.
  eapply ty_denote_gas_tm_equiv.
  - split.
    + eapply tm_equiv_tlete_body_extension; eauto.
    + split; [exact Hzero_body|exact Hzero_tlet].
  - exact Hbody.
Qed.

Lemma lam_intro_denotation
    gas (Σ : lty_env) τ T e y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)) m ->
  body_tm e ->
  y ∉ fv_tm e ->
  y ∈ world_dom (m : WorldT) ->
  m ⊨ ty_denote_gas 0 Σ τ (e ^^ y) ->
  m ⊨ ty_denote_gas 0 Σ τ
    (tapp_tm (tret (vlam T e)) (vfvar y)) ->
  m ⊨ ty_denote_gas gas Σ τ (e ^^ y) ->
  m ⊨ ty_denote_gas gas Σ τ
    (tapp_tm (tret (vlam T e)) (vfvar y)).
Proof.
  intros Hclosed Hbody Hy_fresh Hy_dom Hzero_body Hzero_app Hbody_den.
  eapply ty_denote_gas_tm_equiv.
  - split.
    + intros σ v Hσ.
      pose proof (tm_equiv_lam_app_body T e y m
        Hclosed Hbody Hy_fresh Hy_dom σ v Hσ) as [Happ_body Hbody_app].
      split; [exact Hbody_app|exact Happ_body].
    + split; [exact Hzero_body|exact Hzero_app].
  - exact Hbody_den.
Qed.


End TypeDenote.
