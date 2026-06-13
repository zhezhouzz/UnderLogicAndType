(** * Denotation.TypeEquiv

    Main term-result-equivalence transport theorem. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberTransport
  TypeEquivFiberBase
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquivTLet.

Section TypeDenote.

Lemma ty_static_guard_relevant_of_full
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_static_guard_formula Σ τ e ->
  m ⊨ ty_static_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  intros Hstatic.
  unfold ty_static_guard_formula in Hstatic |- *.
  repeat rewrite res_models_and_iff in Hstatic |- *.
  destruct Hstatic as [Hwf [Hworld Hbasic]].
  assert (Hworld_rel : m ⊨ basic_world_formula (relevant_env Σ τ e)).
  {
    eapply basic_world_formula_subenv; [|exact Hworld].
    intros v T Hlook.
    unfold relevant_env, lty_env_restrict_lvars in Hlook.
    change ((storeA_restrict Σ (relevant_lvars τ e)
      : gmap logic_var ty) !! v = Some T) in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
  }
  split.
  - eapply context_ty_wf_formula_relevant_env; eauto.
  - split; [exact Hworld_rel|].
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [HlcΣ _].
    apply basic_world_formula_models_iff in Hworld_rel as [HlcRel [HscopeRel _]].
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    pose proof (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty)
      as Hlc_e.
    split; [exact HlcRel|]. split; [exact HscopeRel|].
    unfold relevant_env.
    eapply basic_tm_has_ltype_restrict_lvars_lc; [exact Hty|exact Hlc_e|].
    unfold relevant_lvars. set_solver.
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
  tm_total_equiv_on m e_src e_tgt ->
  m ⊨ ty_static_guard_formula Σ τ e_tgt ->
  lc_tm e_tgt ->
  fv_tm e_tgt ⊆ world_dom (m : WorldT) ->
  m ⊨ ty_denote_gas 0 Σ τ e_src ->
  m ⊨ ty_denote_gas 0 Σ τ e_tgt.
Proof.
  intros _ Htotal_equiv Hstatic Hlc Hfv Hzero_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ e_src m Hzero_src) as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [_ [_ Htotal_src]]].
  pose proof (tm_equiv_total m e_src e_tgt Htotal_equiv Hlc Hfv Htotal_src)
    as Htotal_tgt.
  apply ty_denote_gas_zero_of_guard.
  eapply ty_guard_relevant_of_static_full_total.
  - exact Hstatic.
  - exact Htotal_tgt.
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

Lemma ty_static_guard_ret_value_result_alias
    (Σ : lty_env) τ (m : WfWorldT) vx z :
  lty_env_closed Σ ->
  Σ !! LVFree z = Some (erase_ty τ) ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  m ⊨ ty_static_guard_formula Σ τ (tret vx) ->
  m ⊨ ty_static_guard_formula Σ τ (tret (vfvar z)).
Proof.
  intros HΣclosed Hlookup Hres Hstatic.
  assert (Htotal_vx : m ⊨ expr_total_formula (tret vx)).
  {
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [_ [Hworld Hbasic]].
    eapply expr_total_formula_tret_of_basic; eauto.
  }
  assert (Hguard_vx :
      m ⊨ FAnd
        (context_ty_wf_formula Σ τ)
        (FAnd
          (basic_world_formula Σ)
          (FAnd
            (expr_basic_typing_formula Σ (tret vx) (erase_ty τ))
            (expr_total_formula (tret vx))))).
  {
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [Hwf [Hworld Hbasic]].
    apply res_models_and_iff. split; [exact Hwf|].
    apply res_models_and_iff. split; [exact Hworld|].
    apply res_models_and_iff. split; [exact Hbasic|exact Htotal_vx].
  }
  pose proof (ty_denote_gas_result_alias_guard
    Σ τ (tret vx) z m HΣclosed Hlookup Hres Hguard_vx)
    as Hguard_z.
  unfold ty_static_guard_formula.
  repeat rewrite res_models_and_iff in Hguard_z.
  destruct Hguard_z as [Hwf [Hworld [Hbasic _]]].
  apply res_models_and_iff. split; [exact Hwf|].
  apply res_models_and_iff. split; [exact Hworld|exact Hbasic].
Qed.

Lemma typed_total_equiv_ret_value_result_alias_static
    (Σ : lty_env) τ (m : WfWorldT) vx z :
  wfworld_closed_on (fv_tm (tret (vfvar z)) ∪ fv_tm (tret vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  m ⊨ ty_static_guard_formula Σ τ (tret (vfvar z)) ->
  m ⊨ ty_denote_gas 0 Σ τ (tret vx) ->
  typed_total_equiv_on Σ τ m (tret vx) (tret (vfvar z)).
Proof.
  intros Hclosed Hvx Hres Hstatic_tgt Hzero_v.
  pose proof (tm_equiv_ret_value_result_alias
    m vx z Hclosed Hvx Hres) as Heq_zv.
  pose proof (tm_total_equiv_ret_value_result_alias
    m vx z Hclosed Hvx Hres) as Htotal_zv.
  assert (Heq_vz : tm_equiv_on m (tret vx) (tret (vfvar z))).
  {
    intros σ v Hσ.
    pose proof (Heq_zv σ v Hσ) as [Hzv Hvz].
    split; [exact Hvz|exact Hzv].
  }
  assert (Htotal_vz : tm_total_equiv_on m (tret vx) (tret (vfvar z))).
  {
    intros σ Hσ.
    pose proof (Htotal_zv σ Hσ) as [Hzv Hvz].
    split; [exact Hvz|exact Hzv].
  }
  assert (Hzero_z :
      m ⊨ ty_denote_gas 0 Σ τ (tret (vfvar z))).
  {
    eapply ty_denote_gas_zero_transport_static_tm_equiv.
    - exact Heq_vz.
    - exact Htotal_vz.
    - exact Hstatic_tgt.
    - constructor. constructor.
    - eapply ty_static_guard_fv_tm_subset. exact Hstatic_tgt.
    - exact Hzero_v.
  }
  split; [exact Heq_vz|].
  split; [exact Htotal_vz|].
  split; [exact Hzero_v|exact Hzero_z].
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

Lemma ty_denote_gas_result_alias_at
    gas (Σ : lty_env) τ e x D (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula_at D e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
Admitted.

Lemma ty_denote_gas_result_alias
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros Hclosed Hlookup Hres Hden.
  unfold expr_result_formula in Hres.
  eapply ty_denote_gas_result_alias_at; eauto.
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
    eapply result_ext_typed_of_guard
      with (Σ := relevant_env Σ τ e) (τ := τ);
      [apply relevant_env_closed; exact HΣclosed| |exact HFx|exact Hext|].
    - intros Hxrel. apply HxΣ.
      eapply relevant_env_dom_subset_direct. exact Hxrel.
    - exact Hguard_full.
  }
  pose proof (ty_denote_gas_extend_typed_extension
    gas Σ τ e x (erase_ty τ) m mx Fx
    HxΣ Hxτ Hxe HFx_ltype Hext Hm) as Hmx_source.
  assert (Hres : mx ⊨ expr_result_formula e (LVFree x)).
  {
    assert (Hfv_e :
        lvars_of_atoms (fv_tm e) ⊆ dom (relevant_env Σ τ e)).
    {
      apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      eapply basic_tm_has_ltype_lvars. exact Hty.
    }
    assert (Htotal_world : expr_total_on_atom_world e m).
    { eapply expr_total_formula_to_atom_world. exact Htotal. }
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
  apply ty_denote_gas_fv_subset.
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

Lemma ty_denote_gas_ret_fvar_relevant_lookup
    gas Σ τ x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  Σ !! LVFree x = Some (erase_ty τ).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard_formula
    gas Σ τ (tret (vfvar x)) m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [_ [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  apply basic_tm_has_ltype_ret_fvar_lookup in Hty.
  unfold relevant_env, lty_env_restrict_lvars in Hty.
  apply storeA_restrict_lookup_some in Hty as [_ Hty].
  exact Hty.
Qed.

Lemma ty_denote_gas_ret_fvar_lookup
    gas Σ τ x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  Σ !! LVFree x = Some (erase_ty τ).
Proof.
  intros Hden.
  eapply ty_denote_gas_ret_fvar_relevant_lookup. exact Hden.
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
  pose proof Hbasic as Hbasic_lookup.
  apply expr_basic_typing_formula_models_iff in Hbasic_lookup
    as [_ [_ Hty_lookup]].
  apply basic_tm_has_ltype_ret_fvar_lookup in Hty_lookup
    as HΣx_rel.
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
  pose proof (Hstores (LVFree x) (erase_ty τ) v HΣx_rel Hlookup_lift)
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
  m ⊨ ty_guard_formula Σ τ e ->
  mx ⊨ expr_result_formula e (LVFree x).
Proof.
  intros HF Hext Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic Htotal]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  pose proof (basic_tm_has_ltype_lc Σ e (erase_ty τ) HlcΣ Hty) as Hlc_e.
  pose proof (basic_tm_has_ltype_lvars Σ e (erase_ty τ) Hty) as He_lvars.
  pose proof (basic_world_formula_models_iff Σ m) as Hworld_iff.
  apply Hworld_iff in Hworld as [_ [HΣdom _]].
  unfold expr_result_formula.
  eapply expr_result_formula_at_of_result_extends_on.
  - rewrite (tm_lvars_lc_eq_atoms e Hlc_e). unfold lvars_of_atoms.
    intros z Hz. apply elem_of_map in Hz as [a [-> _]]. exact I.
  - reflexivity.
  - intros Hx_lvars.
    apply (expr_result_extension_witness_fresh _ _ _ HF).
    rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hx_lvars.
  - rewrite tm_lvars_fv.
    intros a Ha.
    apply HΣdom.
    apply lvars_fv_elem.
    apply He_lvars.
    unfold lvars_of_atoms. apply elem_of_map.
    exists a. split; [reflexivity|exact Ha].
  - rewrite tm_lvars_fv.
    apply expr_result_extension_witness_to_on. exact HF.
  - exact Hext.
  - eapply expr_total_formula_to_atom_world. exact Htotal.
Qed.

Lemma denot_ty_lvar_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  eapply basic_world_formula_wfworld_closed_on_atoms;
    [eapply basic_tm_has_ltype_lvars; exact Hty|exact Hworld].
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
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ (e ^^ y) m Hzero_body) as Hguard_body.
  pose proof (ty_denote_gas_guard_of_zero
    Σ τ (tapp_tm (tret (vlam T e)) (vfvar y)) m Hzero_app) as Hguard_app.
  pose proof Hguard_body as Hguard_body_parts.
  pose proof Hguard_app as Hguard_app_parts.
  repeat rewrite res_models_and_iff in Hguard_body_parts.
  repeat rewrite res_models_and_iff in Hguard_app_parts.
  destruct Hguard_body_parts as [_ [_ [_ Htotal_body]]].
  destruct Hguard_app_parts as [_ [_ [_ Htotal_app]]].
  eapply ty_denote_gas_tm_equiv.
  - split.
    + intros σ v Hσ.
      pose proof (tm_equiv_lam_app_body T e y m
        Hclosed Hbody Hy_fresh Hy_dom σ v Hσ) as [Happ_body Hbody_app].
      split; [exact Hbody_app|exact Happ_body].
	    + split.
	      * eapply tm_total_equiv_of_total_formulas; eauto.
	      * split.
	        -- exact Hzero_body.
	        -- exact Hzero_app.
  - exact Hbody_den.
Qed.


End TypeDenote.
