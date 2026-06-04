(** * Denotation.ContextTypeDenotationSaturateMain

    Main term-result-equivalence transport theorem. *)

From Denotation Require Import Notation ContextTypeDenotationOpen.
From Denotation Require Export ContextTypeDenotationTactics.
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
	      cbn [denot_ty_lvar_gas] in Hm |- *;
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

Lemma denot_ty_lvar_guard_extend_typed_extension
    (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))) ->
  mx ⊨ FAnd (context_ty_wf_formula (<[LVFree x := T]> Σ) τ)
    (FAnd (basic_world_formula (<[LVFree x := T]> Σ))
      (FAnd
        (expr_basic_typing_formula (<[LVFree x := T]> Σ) e (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros HxΣ HFx Hext Hguard.
  pose proof HFx as HFx_full.
  destruct HFx as [_ [_ [Hout _]]].
  assert (Houtx : ext_out Fx = {[x]}).
  {
    change (lvars_fv (dom (<[LVFree x := T]> (∅ : gmap logic_var ty))) =
      ext_out Fx) in Hout.
    rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
      lvars_fv_singleton_free in Hout.
    change (lvars_fv (∅ : lvset)) with (∅ : aset) in Hout.
    set_solver.
  }
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  repeat rewrite res_models_and_iff.
  split.
  - eapply context_ty_wf_formula_insert_fresh_lvar; eauto.
  - split.
    + eapply basic_world_formula_insert_typed_extension; eauto.
    + split.
      * eapply expr_basic_typing_formula_insert_fresh_lvar; eauto.
      * eapply res_models_extend_mono; eauto.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_subset_relevant gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  rewrite <- (formula_lvars_at_fv 0).
  transitivity (lvars_fv (tm_lvars_at 0 e ∪ context_ty_lvars_at 0 τ)).
  - apply lvars_fv_mono.
    apply formula_lvars_at_denot_ty_lvar_gas_subset_relevant.
  - rewrite lvars_fv_union.
    change (tm_lvars_at 0 e) with (tm_lvars e).
    change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ).
    rewrite tm_lvars_fv, context_ty_lvars_fv.
    reflexivity.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_subset_env_term gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
  lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ.
Proof.
  pose proof (formula_fv_denot_ty_lvar_gas_subset_relevant gas Σ τ e).
  set_solver.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_guard_subset gas Σ τ e :
  lvars_fv (dom (denot_relevant_env Σ τ e)) ∪ fv_tm e ⊆
  formula_fv (denot_ty_lvar_gas gas Σ τ e).
Proof.
  destruct gas; cbn [denot_ty_lvar_gas denot_relevant_env
    lty_env_restrict_lvars denot_relevant_lvars];
    normalize_denotation_formula_fv;
    set_solver.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_insert_fresh_upper
    gas Σ x T τ e :
  formula_fv (denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e) ⊆
  lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ∪ {[x]}.
Proof.
  transitivity
    (lvars_fv (dom (<[LVFree x := T]> Σ)) ∪ fv_tm e ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_env_term.
  - change (lvars_fv (dom (<[LVFree x := T]> (Σ : gmap logic_var ty))) ∪
      fv_tm e ∪ fv_cty τ ⊆ lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ∪ {[x]}).
    rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free.
    set_solver.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_scope_from_guard
    gas Σ τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τbig e) τbig)
    (FAnd (basic_world_formula (denot_relevant_env Σ τbig e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τbig e) e
          (erase_ty τbig))
        (expr_total_formula e))) ->
  formula_fv (denot_ty_lvar_gas gas Σ τsmall e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hτ Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal_e]]].
  transitivity (fv_tm e ∪ fv_cty τsmall).
  - apply formula_fv_denot_ty_lvar_gas_subset_relevant.
  - pose proof (res_models_fuel_scoped _ _ _ Htotal_e) as Hscope_e.
    unfold formula_scoped_in_world in Hscope_e.
    normalize_denotation_formula_fv_in Hscope_e.
    pose proof (context_ty_wf_formula_fv_cty_subset
      (denot_relevant_env Σ τbig e) τbig m Hwf) as Hτbig_fv.
    pose proof (proj1 (basic_world_formula_models_iff
      (denot_relevant_env Σ τbig e) m) Hworld) as [_ [Hworld_dom _]].
    assert (Hτsmall_fv : fv_cty τsmall ⊆ fv_cty τbig).
    {
      rewrite <- !context_ty_lvars_fv.
      apply lvars_fv_mono. exact Hτ.
    }
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

Lemma denot_ty_lvar_guard_wfworld_closed_on_term_le
    (Σ : lty_env) τ e (m n : WfWorldT) :
  m ⊑ n ->
  m ⊨ FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  wfworld_closed_on (fv_tm e) n.
Proof.
  intros Hle Hguard.
  eapply wfworld_closed_on_le.
  - repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [_ [_ [_ Htotal]]].
    pose proof (res_models_fuel_scoped _ _ _ Htotal) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    normalize_denotation_formula_fv_in Hscope.
    exact Hscope.
  - exact Hle.
  - eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    exact Hguard.
Qed.

Lemma denot_ty_lvar_gas_scope_from_guard
    gas Σ τ e (m : WfWorldT) :
  m ⊨ FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))) ->
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal]]].
  transitivity (lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_env_term.
  - pose proof (proj1 (basic_world_formula_models_iff Σ m) Hworld)
      as [_ [HΣ _]].
    pose proof (res_models_fuel_scoped _ _ _ Htotal) as He.
    pose proof (context_ty_wf_formula_fv_cty_subset Σ τ m Hwf) as Hτ.
    unfold formula_scoped_in_world in He.
    normalize_denotation_formula_fv_in He.
    intros a Ha.
    apply elem_of_union in Ha as [Ha | Ha].
    + apply elem_of_union in Ha as [Ha | Ha].
      * exact (HΣ a Ha).
      * exact (He a Ha).
    + apply HΣ. exact (Hτ a Ha).
Qed.

Lemma denot_ty_lvar_gas_scope_from_relevant_guard
    gas Σ τ e (m : WfWorldT) :
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  formula_scoped_in_world m (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal]]].
  unfold formula_scoped_in_world.
  transitivity (fv_tm e ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_relevant.
  - pose proof (proj1 (basic_world_formula_models_iff
      (denot_relevant_env Σ τ e) m) Hworld) as [_ [HΣ _]].
    pose proof (res_models_fuel_scoped _ _ _ Htotal) as He.
    pose proof (context_ty_wf_formula_fv_cty_subset
      (denot_relevant_env Σ τ e) τ m Hwf) as Hτ.
    unfold formula_scoped_in_world in He.
    normalize_denotation_formula_fv_in He.
    set_solver.
Qed.

Lemma denot_ty_lvar_gas_insert_scope_from_parts
    gas Σ τ e x T (mx : WfWorldT) :
  lvars_fv (dom Σ) ∪ {[x]} ⊆ world_dom (mx : WorldT) ->
  fv_tm e ⊆ world_dom (mx : WorldT) ->
  fv_cty τ ⊆ lvars_fv (dom Σ) ->
  formula_fv (denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e) ⊆
  world_dom (mx : WorldT).
Proof.
  intros HΣx He Hτ.
  transitivity (lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ∪ {[x]}).
  - apply formula_fv_denot_ty_lvar_gas_insert_fresh_upper.
  - intros a Ha.
    apply elem_of_union in Ha as [Ha | Ha].
    + apply elem_of_union in Ha as [Ha | Ha].
      * apply elem_of_union in Ha as [Ha | Ha].
        -- apply HΣx. apply elem_of_union_l. exact Ha.
        -- exact (He a Ha).
      * apply HΣx. apply elem_of_union_l. exact (Hτ a Ha).
    + apply HΣx. apply elem_of_union_r. exact Ha.
Qed.


End ContextTypeDenotation.
