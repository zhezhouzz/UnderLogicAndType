(** * Denotation.TypeEquiv

    Main term-result-equivalence transport theorem. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberTransport
  TypeEquivFiberBase
  TypeEquivFiber.

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
  m ⊨ ty_guard_formula Σ τ e.
Proof.
  intros Hstatic Htotal.
  unfold ty_static_guard_formula in Hstatic.
  unfold ty_guard_formula.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [Hwf [Hworld Hbasic]].
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
  intros Hequiv Hden.
  pose proof (typed_total_equiv_source_zero _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero _ _ _ _ _ Hequiv) as Hzero2.
  pose proof (typed_total_equiv_tm_equiv _ _ _ _ _ Hequiv) as Heq.
  pose proof (typed_total_equiv_total_equiv _ _ _ _ _ Hequiv) as Htotal.
  eapply ty_denote_gas_tm_fiber_equiv.
  - eapply typed_fiber_equiv_of_tm_equiv; eauto.
  - exact Hden.
Qed.

Lemma ty_denote_gas_result_alias
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula_at (dom Σ) e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
Admitted.

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
Admitted.

Lemma formula_fv_ty_denote_gas_subset_env gas Σ τ e :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆
  lvars_fv (dom Σ).
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
Admitted.

Lemma ty_denote_gas_restrict_delete_fresh
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  x ∉ fv_tm e ∪ fv_cty τ ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  res_restrict m (world_dom (m : WorldT) ∖ {[x]}) ⊨
    ty_denote_gas gas Σ τ e.
Proof.
Admitted.

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
Admitted.

Lemma expr_result_formula_of_result_extends_from_ty_guard
    (Σ : lty_env) τ e x (m mx : WfWorldT) Fx :
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_guard_formula Σ τ e ->
  mx ⊨ expr_result_formula e (LVFree x).
Proof.
Admitted.

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

Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2).
Proof.
Admitted.

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
