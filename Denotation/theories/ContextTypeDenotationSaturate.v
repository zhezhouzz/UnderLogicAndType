(** * Denotation.ContextTypeDenotationSaturate

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation.
From Denotation Require Export ContextTypeDenotationTactics.

Section ContextTypeDenotation.

Lemma denot_ty_lvar_gas_saturate gas Σ τ e :
  cty_depth τ <= gas ->
  denot_ty_lvar_gas gas Σ τ e =
  denot_ty_lvar_gas (cty_depth τ) Σ τ e.
Proof.
  assert (Hsat :
    forall gas τ Σ e,
      cty_depth τ <= gas ->
      denot_ty_lvar_gas gas Σ τ e =
      denot_ty_lvar_gas (cty_depth τ) Σ τ e).
  {
    intros fuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros τ0 Σ0 e0 Hgas.
    destruct fuel as [|gas']; destruct τ0; cbn [cty_depth] in Hgas; try lia;
      cbn [cty_depth denot_ty_lvar_gas].
    - reflexivity.
    - reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      reflexivity.
    - rewrite (IH gas' ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH gas' ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_1 Σ0 e0 ltac:(lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) τ0_2 Σ0 e0 ltac:(lia)).
      reflexivity.
	    - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH gas' ltac:(lia) τ0_2
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        τ0_2 (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      reflexivity.
	    - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH gas' ltac:(lia) τ0_2
	        (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        τ0_2 (typed_lty_env_bind
	          (denot_relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
      reflexivity.
  }
  intros Hgas. apply Hsat. exact Hgas.
Qed.

Lemma denot_ty_lvar_gas_saturate_ge gas1 gas2 Σ τ e :
  cty_depth τ <= gas1 ->
  cty_depth τ <= gas2 ->
  denot_ty_lvar_gas gas1 Σ τ e =
  denot_ty_lvar_gas gas2 Σ τ e.
Proof.
  intros Hgas1 Hgas2.
  rewrite (denot_ty_lvar_gas_saturate gas1 Σ τ e Hgas1).
  rewrite (denot_ty_lvar_gas_saturate gas2 Σ τ e Hgas2).
  reflexivity.
Qed.

Lemma context_ty_wf_formula_insert_fresh_same_world
    (Σ : lty_env) τ (m : WfWorldT) x T :
  LVFree x ∉ dom Σ ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ context_ty_wf_formula Σ τ ->
  m ⊨ context_ty_wf_formula (<[LVFree x := T]> Σ) τ.
Proof.
  intros HxΣ Hworld Hwf.
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasic]].
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hsub _]].
  apply context_ty_wf_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  apply basic_context_ty_lvars_insert_fresh. exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_insert_fresh_same_world
    (Σ : lty_env) e U (m : WfWorldT) x T :
  LVFree x ∉ dom Σ ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ expr_basic_typing_formula Σ e U ->
  m ⊨ expr_basic_typing_formula (<[LVFree x := T]> Σ) e U.
Proof.
  intros HxΣ Hworld Hbasic.
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hsub _]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  apply basic_tm_has_ltype_insert_fresh_lvar; assumption.
Qed.

Lemma denot_ty_lvar_guard_insert_fresh_lty_env
    (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  m ⊨ basic_world_formula (<[LVFree x := T]> Σ) ->
  m ⊨ FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))) ->
  m ⊨ FAnd (context_ty_wf_formula (<[LVFree x := T]> Σ) τ)
    (FAnd (basic_world_formula (<[LVFree x := T]> Σ))
      (FAnd
        (expr_basic_typing_formula (<[LVFree x := T]> Σ) e (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros HxΣ Hworldx Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [_ [Hbasic Htotal]]].
  eapply res_models_and_intro_from_models.
  - eapply context_ty_wf_formula_insert_fresh_same_world; eauto.
  - eapply res_models_and_intro_from_models; [exact Hworldx|].
    eapply res_models_and_intro_from_models; [|exact Htotal].
    eapply expr_basic_typing_formula_insert_fresh_same_world; eauto.
Qed.

Lemma denot_ty_lvar_gas_insert_fresh_lty_env_eq
    gas (Σ : lty_env) τ e x T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e =
  denot_ty_lvar_gas gas Σ τ e.
Proof.
  intros _ Hxτ Hxe.
  eapply denot_ty_lvar_gas_env_agree_on
    with (X := denot_relevant_lvars τ e).
  - reflexivity.
  - apply lty_env_restrict_lvars_insert_fresh.
    apply denot_relevant_lvars_insert_fresh; assumption.
Qed.

Lemma denot_ty_lvar_gas_zero_of_guard
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e.
Proof.
  intros Hguard.
  cbn [denot_ty_lvar_gas].
  rewrite res_models_and_iff. split.
  - exact Hguard.
  - cbn [res_models res_models_fuel formula_measure].
    split; [apply formula_scoped_true_iff; exact I | exact I].
Qed.

Lemma denot_ty_lvar_gas_guard_of_zero
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros Hzero.
  cbn [denot_ty_lvar_gas] in Hzero.
  rewrite res_models_and_iff in Hzero.
  exact (proj1 Hzero).
Qed.

Lemma denot_ty_lvar_gas_insert_fresh_lty_env
    gas (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  m ⊨ denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe Hm.
  rewrite (denot_ty_lvar_gas_insert_fresh_lty_env_eq gas Σ τ e x T);
    assumption.
Qed.

Lemma denot_ty_lvar_gas_extend_typed_extension
    gas (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  mx ⊨ denot_ty_lvar_gas gas (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe HFx Hext Hm.
  assert (Hmx_old : mx ⊨ denot_ty_lvar_gas gas Σ τ e).
  {
    eapply res_models_extend_mono; [exact Hext | exact Hm].
  }
  eapply denot_ty_lvar_gas_insert_fresh_lty_env; eauto.
Qed.

Lemma denot_ty_lvar_gas_extend_typed_extension_zero
    (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  mx ⊨ denot_ty_lvar_gas 0 (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe HFx Hext Hm.
  eapply denot_ty_lvar_gas_extend_typed_extension; eauto.
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
