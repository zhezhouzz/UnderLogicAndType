(** * Denotation.ContextTypeDenotationSaturate

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation ContextTypeDenotationMsubstCore.
From Denotation Require Export ContextTypeDenotationTactics.

Section ContextTypeDenotation.

Lemma formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  fv_tm e ∪ fv_cty τ ⊆ formula_fv (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hwf.
  transitivity (lvars_fv (tm_lvars e ∪ context_ty_lvars τ)).
  - rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
    reflexivity.
  - apply lvars_fv_mono.
    pose proof (basic_context_ty_lvars_denot_relevant_env Σ τ e Hwf)
      as [Hτ _].
    destruct gas as [|gas]; destruct τ;
      cbn [denot_ty_lvar_gas formula_lvars context_ty_wf_formula
        context_ty_wf_lqual basic_world_formula basic_world_lqual
        expr_basic_typing_formula expr_basic_typing_lqual expr_total_formula
        expr_total_lqual lqual_lvars lqual_fv lqual_dom];
      better_set_solver.
Qed.

Lemma denot_ty_lvar_gas_result_alias_scope_ret_from_source
    gas Σ τ e x (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  formula_scoped_in_world m (denot_ty_lvar_gas gas Σ τ e) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σ τ (tret (vfvar x))).
Proof.
  intros Hwf Hscope Hres.
  pose proof (res_models_scoped _ _ Hres) as Hscope_res.
  pose proof (formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ e Hwf) as Hlower.
  unfold formula_scoped_in_world in *.
  transitivity (fv_tm (tret (vfvar x)) ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
  - rewrite formula_fv_expr_result_formula in Hscope_res.
    cbn [fv_tm fv_value tm_lvars tm_lvars_at value_lvars value_lvars_at].
    assert (Hx_scope : {[x]} ⊆ world_dom (m : WorldT)).
    {
      intros z Hz.
      apply elem_of_singleton in Hz. subst z.
      apply Hscope_res.
      rewrite lvars_fv_union, lvars_fv_singleton_free.
      set_solver.
    }
    assert (Hτ_scope : fv_cty τ ⊆ world_dom (m : WorldT)).
    {
      transitivity (fv_tm e ∪ fv_cty τ).
      - set_solver.
      - transitivity (formula_fv (denot_ty_lvar_gas gas Σ τ e));
          [exact Hlower | exact Hscope].
    }
    intros z Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + exact (Hx_scope z Hz).
    + exact (Hτ_scope z Hz).
Qed.

Lemma logic_qualifier_denote_of_res_subset
    (q : LogicQualifierT) (m0 m : WfWorldT) :
  m0 ⊑ m ->
  lqual_fv q ⊆ world_dom (m0 : WorldT) ->
  logic_qualifier_denote q m ->
  logic_qualifier_denote q m0.
Proof.
  destruct q as [D P]. simpl.
  intros Hle Hfv [Hlc [Hsub HP]].
  exists Hlc.
  assert (Hsub0 : lvars_fv D ⊆ world_dom (m0 : WorldT)) by exact Hfv.
  exists Hsub0.
  enough (lworld_on_lift D m0 Hlc Hsub0 =
          lworld_on_lift D m Hlc Hsub) as Heq.
  { rewrite Heq. exact HP. }
  apply lworld_on_ext. unfold lworld_on_lift. simpl.
  rewrite (res_restrict_le_eq m0 m (lvars_fv D) Hle Hsub0).
  reflexivity.
Qed.

Lemma expr_result_formula_of_res_subset
    e x (m0 m : WfWorldT) :
  m0 ⊑ m ->
  formula_fv (expr_result_formula e (LVFree x)) ⊆ world_dom (m0 : WorldT) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m0 ⊨ expr_result_formula e (LVFree x).
Proof.
  intros Hle Hfv Hm.
  apply expr_result_formula_models_iff in Hm.
  apply expr_result_formula_models_iff.
  eapply logic_qualifier_denote_of_res_subset; eauto.
Qed.

Lemma expr_result_formula_of_res_store_subset
    e z (m0 m : WfWorldT) :
  res_subset m0 m ->
  m ⊨ expr_result_formula e z ->
  m0 ⊨ expr_result_formula e z.
Proof.
  intros [Hdom Hstores_sub] Hm.
  apply expr_result_formula_to_atom_world in Hm.
  apply expr_result_atom_world_to_formula.
  destruct Hm as [Hz [Hdom_e Hstores]].
  split; [exact Hz|].
  split.
  - rewrite res_lift_free_dom in Hdom_e |- *.
    change (tm_lvars e ∪ {[z]} ⊆ lvars_of_atoms (worldA_dom (m : WorldT)))
      in Hdom_e.
    intros v Hv.
    specialize (Hdom_e v Hv).
    change (v ∈ lvars_of_atoms (worldA_dom (m0 : WorldT))).
    replace (lvars_of_atoms (worldA_dom (m0 : WorldT)))
      with (lvars_of_atoms (worldA_dom (m : WorldT))).
    + exact Hdom_e.
    + apply f_equal. symmetry. exact Hdom.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    apply Hstores.
    exists σ. split; [apply Hstores_sub; exact Hσ | reflexivity].
Qed.

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

Lemma denot_ty_lvar_gas_guard
    gas (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))).
Proof.
  destruct gas; cbn [denot_ty_lvar_gas]; rewrite res_models_and_iff; tauto.
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

Lemma expr_result_extension_has_ltype_from_source_guard
    (Σ : lty_env) τ e x
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  lty_env_closed Σ ->
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  extension_has_ltype (<[LVFree x := erase_ty τ]> ∅)
    (res_restrict m (ext_in Fx)) Fx.
Proof.
  intros HΣclosed HxΣ HFx Hext Hguard.
  destruct HFx as [Hx_fv [Hin Hout] Hrel].
  pose proof Hguard as Hparts.
  repeat rewrite res_models_and_iff in Hparts.
  destruct Hparts as [_ [Hworld [Hbasic Htotal]]].
  apply basic_world_formula_models_iff in Hworld as [_ [_ Hworld_typed]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [Hrel_closed [_ Hty_e]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty_e) as Hfv_e.
  pose proof (expr_total_formula_to_atom_world e m Htotal) as Htotal_m.
  unfold extension_has_ltype.
  split.
  - change (world_dom (res_restrict m (ext_in Fx) : WorldT) = ext_in Fx).
    cbn [res_restrict resA_restrict rawA_restrict worldA_dom].
    pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
    set_solver.
  - split.
    + intros [k|y] Hy; cbn [lc_logic_var_key]; [|exact I].
      change (LVBound k ∈ dom ({[LVFree x := erase_ty τ]} : gmap logic_var ty))
        in Hy.
      rewrite dom_singleton_L in Hy. set_solver.
    + split.
      * change (lvars_fv (dom ({[LVFree x := erase_ty τ]} : gmap logic_var ty)) =
          ext_out Fx).
        rewrite dom_singleton_L, lvars_fv_singleton_free, Hout. set_solver.
      * intros σin mout Hσin HFrel.
        assert (Hσin_dom : dom (σin : StoreT) = fv_tm e).
        {
          pose proof (wfworld_store_dom (res_restrict m (ext_in Fx))
            σin Hσin) as Hdom.
          change (dom (σin : StoreT) =
            world_dom (res_restrict m (ext_in Fx) : WorldT)) in Hdom.
          rewrite Hdom.
          cbn [res_restrict resA_restrict rawA_restrict worldA_dom].
          rewrite Hin.
          pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
          set_solver.
        }
        assert (Hσin_typed :
            atom_store_has_ltype (denot_relevant_env Σ τ e) σin).
        {
          simpl in Hσin.
          destruct Hσin as [σm [Hσm Hrestrict]].
          subst σin.
          destruct Hworld_typed as [_ Hstores].
          specialize (Hstores (lstore_lift_free σm)).
          assert (Hlift :
            worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σm)).
          { exists σm. split; [exact Hσm|reflexivity]. }
          specialize (Hstores Hlift).
          intros a v Hlook.
          apply storeA_restrict_lookup_some in Hlook as [Ha_fv Hσm_a].
          assert (Ha_dom :
              LVFree a ∈ dom (denot_relevant_env Σ τ e)).
          {
            apply Hfv_e.
            unfold lvars_of_atoms. apply elem_of_map.
            exists a. split; [reflexivity|].
            rewrite <- Hin. exact Ha_fv.
          }
          apply elem_of_dom in Ha_dom as [Ta HΣa].
          exists Ta. split; [exact HΣa|].
          eapply Hstores; [exact HΣa|].
          change (((lstore_lift_free σm : LStoreT)
            : gmap logic_var value) !! LVFree a = Some v).
          rewrite lstore_lift_free_lookup_free. exact Hσm_a.
        }
        destruct Htotal_m as [_ Htotal_eval].
        assert (Hexists_eval : exists v, expr_eval_in_atom_store σin e v).
        {
          simpl in Hσin.
          destruct Hσin as [σm [Hσm Hrestrict]].
          subst σin.
          destruct (Htotal_eval (lstore_lift_free σm)) as [v Heval].
          { exists σm. split; [exact Hσm|reflexivity]. }
          exists v.
          pose proof (expr_eval_in_atom_store_restrict_fv_subset
            σm e v (ext_in Fx) ltac:(rewrite Hin; set_solver)) as Hequiv.
          apply (proj2 Hequiv). exact Heval.
        }
        unfold lworld_has_type, worldA_has_type.
        split.
        -- change (dom ({[LVFree x := erase_ty τ]} : gmap logic_var ty) ⊆
             worldA_dom (res_lift_free mout : LWorldT)).
           rewrite dom_singleton_L, res_lift_free_dom.
           pose proof (extA_rel_dom Fx σin mout) as Hdom_mout.
           assert (Hσdom_ext : dom (σin : StoreT) = ext_in Fx).
           { rewrite Hσin_dom, Hin. reflexivity. }
           specialize (Hdom_mout Hσdom_ext HFrel).
           change (world_dom (mout : WorldT) = ext_out Fx) in Hdom_mout.
           intros z Hz.
           rewrite elem_of_singleton in Hz. subst z.
           unfold lvars_of_atoms. apply elem_of_map.
           exists x. split; [reflexivity|].
           change (x ∈ world_dom (mout : WorldT)).
           rewrite Hdom_mout, Hout. set_solver.
        -- intros τout Hτout.
           destruct Hτout as [σout [Hσout ->]].
           pose proof (expr_result_extension_apply_total_iff
             e x Fx σin mout
             {| expr_result_extension_witness_fresh := Hx_fv;
                expr_result_extension_witness_shape := conj Hin Hout;
                expr_result_extension_witness_rel := Hrel |}
             Hσin_dom HFrel Hexists_eval σout) as Hout_iff.
           apply Hout_iff in Hσout as [v [Heval_v ->]].
           intros z U u HΣout Hu.
           change (((<[LVFree x := erase_ty τ]>
             (∅ : gmap logic_var ty) : lty_env)
              : gmap logic_var ty) !! z = Some U) in HΣout.
           destruct z as [k|y].
           ++ rewrite lookup_insert_ne in HΣout by discriminate.
              rewrite lookup_empty in HΣout. discriminate.
           ++ destruct (decide (y = x)) as [->|Hyx].
              ** change (((<[LVFree x := erase_ty τ]>
                    (∅ : gmap logic_var ty) : gmap logic_var ty) !! LVFree x) =
                    Some U) in HΣout.
                 assert (Hlookup_x :
                    ((<[LVFree x := erase_ty τ]>
                       (∅ : gmap logic_var ty) : gmap logic_var ty) !! LVFree x) =
                    Some (erase_ty τ)).
                 {
                   rewrite lookup_insert.
                   destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
                     [reflexivity|congruence].
                 }
                 rewrite Hlookup_x in HΣout.
                 injection HΣout as HU.
                 subst U.
	                 change (((lstore_lift_free ({[x := v]} : StoreT) : LStoreT)
	                   : gmap logic_var value) !! LVFree x = Some u) in Hu.
	                 rewrite lstore_lift_free_lookup_free in Hu.
	                 change (((<[x := v]> (∅ : gmap atom value) : gmap atom value)
	                   !! x) = Some u) in Hu.
	                 assert (Hlookup_v :
	                   ((<[x := v]> (∅ : gmap atom value) : gmap atom value) !! x) =
	                   Some v).
	                 {
	                   apply map_lookup_insert.
	                 }
	                 rewrite Hlookup_v in Hu. inversion Hu. subst u.
	                 eapply basic_tm_has_ltype_eval_in_atom_store_value_type;
	                   [|exact Hσin_typed|exact Hty_e|exact Heval_v|].
	                 --- exact Hrel_closed.
                 --- rewrite Hσin_dom. set_solver.
              ** rewrite lookup_insert_ne in HΣout by congruence.
                 rewrite lookup_empty in HΣout. discriminate.
Qed.

Lemma expr_basic_typing_formula_ret_fvar_from_lookup
    (Σ : lty_env) x T (m : WfWorldT) :
  lc_lvars (dom Σ) ->
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) ->
  Σ !! LVFree x = Some T ->
  m ⊨ expr_basic_typing_formula Σ (tret (vfvar x)) T.
Proof.
  intros Hlc Hsub Hlookup.
  apply expr_basic_typing_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  constructor. constructor. exact Hlookup.
Qed.

Lemma expr_total_formula_ret_fvar_from_result
    e x (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ expr_total_formula (tret (vfvar x)).
Proof.
  intros Hres.
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hres)
    as Hres_world.
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on.
  destruct Hres_world as [Hx [Hdom Hstores]].
  split.
  - cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
    intros v Hv.
    apply elem_of_singleton in Hv. subst v.
    specialize (Hdom (LVFree x) ltac:(set_solver)).
    exact Hdom.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    assert (Hτ_res :
      (res_lift_free m : LWorldT) (lstore_lift_free σ)).
    { exists σ. split; [exact Hσ|reflexivity]. }
    specialize (Hstores (lstore_lift_free σ) Hτ_res).
    destruct Hstores as [_ [v [Hx_lookup Heval]]].
    exists v.
    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
      !! LVFree x = Some v) in Hx_lookup.
    rewrite lstore_lift_free_lookup_free in Hx_lookup.
    unfold expr_eval_in_atom_store, expr_eval_in_store.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at
      lstore_instantiate_value_split_at lstore_free_part].
    rewrite lstore_free_part_lift_free.
    change (tret
      (match ((σ : StoreT) : gmap atom value) !! x with
       | Some u => u
       | None => vfvar x
       end) →* tret v).
    rewrite Hx_lookup.
    constructor.
    pose proof (steps_regular2 _ _ Heval) as Hret_lc.
    inversion Hret_lc; subst. assumption.
Qed.

Lemma basic_world_formula_result_alias_target
    (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula (denot_relevant_env Σ τ e) e
    (erase_ty τ) ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ (tret (vfvar x))).
Proof.
  intros HΣclosed HΣx Hres Hworld_src Hbasic_src.
  apply basic_world_formula_models_iff in Hworld_src
    as [Hlc_src [Hscope_src Htyped_src]].
  apply expr_basic_typing_formula_models_iff in Hbasic_src
    as [Hrel_closed [_ Hty_e]].
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hres)
    as Hres_world.
  destruct Hres_world as [Hx_fresh [Hres_dom Hres_stores]].
  apply basic_world_formula_models_iff.
  split.
  - apply denot_relevant_env_closed. exact HΣclosed.
  - split.
    + intros a Ha.
      apply lvars_fv_elem in Ha.
      unfold denot_relevant_env, lty_env_restrict_lvars in Ha.
      rewrite storeA_restrict_dom in Ha.
      apply elem_of_intersection in Ha as [HaΣ Ha_rel].
      unfold denot_relevant_lvars in Ha_rel.
      cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at] in Ha_rel.
      apply elem_of_union in Ha_rel as [Haτ|Hax].
      * apply Hscope_src. apply lvars_fv_elem.
        unfold denot_relevant_env, lty_env_restrict_lvars.
        rewrite storeA_restrict_dom.
        apply elem_of_intersection. split.
        -- exact HaΣ.
        -- unfold denot_relevant_lvars. set_solver.
      * apply elem_of_singleton in Hax. inversion Hax. subst a.
        specialize (Hres_dom (LVFree x) ltac:(set_solver)).
        rewrite res_lift_free_dom in Hres_dom.
        unfold lvars_of_atoms in Hres_dom.
        apply elem_of_map in Hres_dom as [a [Heq Ha]].
        inversion Heq. subst a. exact Ha.
    + unfold lworld_has_type, worldA_has_type in Htyped_src |- *.
      split.
      * intros z Hz.
        unfold denot_relevant_env, lty_env_restrict_lvars in Hz.
        rewrite storeA_restrict_dom in Hz.
        apply elem_of_intersection in Hz as [HzΣ Hz_rel].
        unfold denot_relevant_lvars in Hz_rel.
        cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at] in Hz_rel.
        apply elem_of_union in Hz_rel as [Hzτ|Hzx].
        -- destruct Htyped_src as [Hdom_src _].
           apply Hdom_src.
           unfold denot_relevant_env, lty_env_restrict_lvars.
           rewrite storeA_restrict_dom.
           apply elem_of_intersection. split; [exact HzΣ|].
           unfold denot_relevant_lvars. set_solver.
        -- apply elem_of_singleton in Hzx. subst z.
           apply Hres_dom. set_solver.
      * intros σl Hσl z T v Htarget_z Hσl_z.
        unfold denot_relevant_env, lty_env_restrict_lvars in Htarget_z.
        apply storeA_restrict_lookup_some in Htarget_z
          as [Hz_target HΣ_z].
        destruct (decide (z ∈ denot_relevant_lvars τ e)) as [Hz_source|Hz_not_source].
        -- destruct Htyped_src as [_ Hstores_src].
           specialize (Hstores_src σl Hσl).
           eapply Hstores_src.
           ++ apply storeA_restrict_lookup_some_2; [exact HΣ_z|exact Hz_source].
           ++ exact Hσl_z.
        -- assert (Hz_x : z = LVFree x).
           {
             unfold denot_relevant_lvars in Hz_target, Hz_not_source.
             cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at]
               in Hz_target.
             set_solver.
           }
           rewrite Hz_x in HΣ_z.
           subst z.
           change (((Σ : gmap logic_var ty) !! LVFree x) = Some T)
             in HΣ_z.
           rewrite HΣx in HΣ_z. inversion HΣ_z. subst T.
           destruct Hσl as [σ [Hσ ->]].
           change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
             !! LVFree x = Some v) in Hσl_z.
           rewrite lstore_lift_free_lookup_free in Hσl_z.
           assert (Hσtyped :
               atom_store_has_ltype (denot_relevant_env Σ τ e)
                 (store_restrict σ (fv_tm e))).
           {
             intros y u Hσy.
             apply storeA_restrict_lookup_some in Hσy as [Hyfv Hσy].
             assert (Hσl_y :
               ((lstore_lift_free σ : LStoreT) : gmap logic_var value)
                 !! LVFree y = Some u).
             { rewrite lstore_lift_free_lookup_free. exact Hσy. }
             pose proof Htyped_src as [_ Hstores_src].
             specialize (Hstores_src (lstore_lift_free σ)
               ltac:(exists σ; split; [exact Hσ|reflexivity])).
             assert (Hy_dom :
                 LVFree y ∈ dom (denot_relevant_env Σ τ e)).
             {
               pose proof (basic_tm_has_ltype_lvars _ _ _ Hty_e) as Hfv.
               apply Hfv.
               unfold lvars_of_atoms. apply elem_of_map.
               exists y. split; [reflexivity|exact Hyfv].
             }
             apply elem_of_dom in Hy_dom as [Uy HΣy].
             exists Uy. split; [exact HΣy|].
             eapply Hstores_src; [exact HΣy|exact Hσl_y].
           }
           assert (Hfv_e : fv_tm e ⊆ dom (σ : StoreT)).
           {
             pose proof (basic_tm_has_ltype_lvars _ _ _ Hty_e) as Hfv.
             pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
             change (dom (σ : StoreT) = world_dom (m : WorldT)) in Hdomσ.
             intros y Hy.
             rewrite Hdomσ.
             apply Hscope_src.
             apply lvars_fv_elem.
             apply Hfv.
             unfold lvars_of_atoms. apply elem_of_map.
             exists y. split; [reflexivity|exact Hy].
           }
           specialize (Hres_stores (lstore_lift_free σ)
             ltac:(exists σ; split; [exact Hσ|reflexivity])).
           destruct Hres_stores as [_ [vx [Hx_lookup Heval]]].
           change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
             !! LVFree x = Some vx) in Hx_lookup.
           rewrite lstore_lift_free_lookup_free in Hx_lookup.
           rewrite Hσl_z in Hx_lookup. inversion Hx_lookup. subst vx.
           change (expr_eval_in_atom_store σ e v) in Heval.
           assert (Heval_restrict :
               expr_eval_in_atom_store (store_restrict σ (fv_tm e)) e v).
           {
             apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
               σ e v (fv_tm e) ltac:(set_solver))).
             exact Heval.
           }
           eapply basic_tm_has_ltype_eval_in_atom_store_value_type;
             [exact Hrel_closed|exact Hσtyped|exact Hty_e|exact Heval_restrict|].
           intros y Hy.
           pose proof (Hfv_e y Hy) as Hyσ.
           change (y ∈ dom (σ : gmap atom value)) in Hyσ.
           rewrite elem_of_dom in Hyσ.
           destruct Hyσ as [u Hu].
           change (y ∈ dom (store_restrict σ (fv_tm e) : gmap atom value)).
           rewrite elem_of_dom. exists u.
           apply storeA_restrict_lookup_some_2; assumption.
Qed.

Lemma denot_ty_lvar_gas_result_alias_guard
    (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ (tret (vfvar x))) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ (tret (vfvar x))))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ (tret (vfvar x)))
          (tret (vfvar x)) (erase_ty τ))
        (expr_total_formula (tret (vfvar x))))).
Proof.
  intros HΣclosed HΣx Hres Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (basic_world_formula_result_alias_target
    Σ τ e x m HΣclosed HΣx Hres Hworld Hbasic) as Hworld_target.
  apply basic_world_formula_models_iff in Hworld_target
    as [Hlc_target [Hscope_target Htyped_target]].
  apply context_ty_wf_formula_models_iff in Hwf
    as [_ [_ Hbasicτ_src]].
  assert (Hbasicτ_Σ : basic_context_ty_lvars (dom Σ) τ).
  {
    eapply basic_context_ty_lvars_mono; [|exact Hbasicτ_src].
    unfold denot_relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom. set_solver.
  }
  assert (Hlookup_target :
      denot_relevant_env Σ τ (tret (vfvar x)) !! LVFree x =
      Some (erase_ty τ)).
  {
    unfold denot_relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2; [exact HΣx|].
    unfold denot_relevant_lvars.
    cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
    set_solver.
  }
  repeat rewrite res_models_and_iff.
  split.
  - apply context_ty_wf_formula_models_iff.
    split; [exact Hlc_target|].
    split; [exact Hscope_target|].
    apply basic_context_ty_lvars_denot_relevant_env.
    exact Hbasicτ_Σ.
  - split.
    + apply basic_world_formula_models_iff.
      split; [exact Hlc_target|].
      split; [exact Hscope_target|exact Htyped_target].
    + split.
      * eapply expr_basic_typing_formula_ret_fvar_from_lookup; eauto.
      * eapply expr_total_formula_ret_fvar_from_result. exact Hres.
Qed.

Lemma expr_result_formula_alias_to_var
    e x z (m : WfWorldT) :
  z ∉ tm_lvars e ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ expr_result_formula (tret (vfvar x)) z ->
  m ⊨ expr_result_formula e z.
Proof.
  intros Hz_e Hsrc Hret.
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hsrc)
    as Hsrc_world.
  pose proof (expr_result_formula_to_atom_world (tret (vfvar x)) z m Hret)
    as Hret_world.
  apply expr_result_atom_world_to_formula.
  destruct Hsrc_world as [Hx_e [Hsrc_dom Hsrc_stores]].
  destruct Hret_world as [_ [Hret_dom Hret_stores]].
  split; [exact Hz_e|].
  split.
  - intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + exact (Hsrc_dom v ltac:(set_solver)).
    + exact (Hret_dom v ltac:(cbn [tm_lvars tm_lvars_at value_lvars_at]; set_solver)).
  - intros σ Hσ.
    specialize (Hsrc_stores σ Hσ) as [_ [vx [Hx_lookup Heval_e]]].
    specialize (Hret_stores σ Hσ) as [_ [vz [Hz_lookup Heval_ret]]].
    unfold expr_result_at_store.
    split; [exact Hz_e|].
    eexists. split; [|exact Heval_e].
    unfold expr_eval_in_store in Heval_ret.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at] in Heval_ret.
    change (tret (lstore_instantiate_value_at 0 σ (vfvar x)) →*
      tret vz) in Heval_ret.
    rewrite lstore_instantiate_value_at_fvar in Heval_ret.
    assert (Hfree_x : lstore_free_part σ !! x = Some vx).
    { unfold lstore_free_part. rewrite lstore_to_store_lookup. exact Hx_lookup. }
    rewrite Hfree_x in Heval_ret.
    pose proof (value_steps_self vx (tret vz) Heval_ret) as Heq.
    inversion Heq. subst vz.
    exact Hz_lookup.
Qed.

Definition tm_result_equiv_on
    (m : WfWorldT) (e1 e2 : tm) : Prop :=
  forall σ v,
    worldA_stores (m : WorldT) σ ->
    expr_eval_in_atom_store σ e1 v <->
    expr_eval_in_atom_store σ e2 v.

Definition typed_total_tm_result_equiv_on
    (Σ : lty_env) (τ : context_ty) (m : WfWorldT)
    (e1 e2 : tm) : Prop :=
  tm_result_equiv_on m e1 e2 /\
  m ⊨ denot_ty_lvar_gas 0 Σ τ e1 /\
  m ⊨ denot_ty_lvar_gas 0 Σ τ e2.

Lemma typed_total_tm_result_equiv_on_source_zero
    Σ τ m e1 e2 :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e1.
Proof. intros [_ [Hzero _]]. exact Hzero. Qed.

Lemma typed_total_tm_result_equiv_on_target_zero
    Σ τ m e1 e2 :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e2.
Proof. intros [_ [_ Hzero]]. exact Hzero. Qed.

Lemma tm_result_equiv_on_sym m e1 e2 :
  tm_result_equiv_on m e1 e2 ->
  tm_result_equiv_on m e2 e1.
Proof.
  intros Heq σ v Hσ. symmetry. apply Heq. exact Hσ.
Qed.

Lemma typed_total_tm_result_equiv_on_sym Σ τ m e1 e2 :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ m e2 e1.
Proof.
  intros [Heq [Hz1 Hz2]].
  split; [apply tm_result_equiv_on_sym; exact Heq|].
  split; assumption.
Qed.

Lemma tm_result_equiv_on_res_subset
    (m0 m : WfWorldT) e1 e2 :
  m0 ⊑ m ->
  lc_tm e1 ->
  lc_tm e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m0 : WorldT) ->
  tm_result_equiv_on m e1 e2 ->
  tm_result_equiv_on m0 e1 e2.
Proof.
  intros Hle _ _ Hfv Heq σ v Hσ.
  pose proof (res_restrict_eq_of_le m0 m Hle) as Hrestrict.
  assert (Hσ_restrict :
      (res_restrict m (world_dom (m0 : WorldT)) : WorldT) σ).
  { rewrite Hrestrict. exact Hσ. }
  destruct Hσ_restrict as [σm [Hσm Hσm_restrict]].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (m0 : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (m0 : WorldT)) by set_solver.
  specialize (Heq σm v Hσm) as [Heq12 Heq21].
  split.
  - intros Heval1.
    rewrite <- Hσm_restrict.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
      σm e2 v (world_dom (m0 : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
      σm e1 v (world_dom (m0 : WorldT)) Hfv1)).
    rewrite Hσm_restrict. exact Heval1.
  - intros Heval2.
    rewrite <- Hσm_restrict.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
      σm e1 v (world_dom (m0 : WorldT)) Hfv1)).
    apply Heq21.
	    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
	      σm e2 v (world_dom (m0 : WorldT)) Hfv2)).
	    rewrite Hσm_restrict. exact Heval2.
Qed.

Lemma tm_result_equiv_on_res_store_subset
    (m0 m : WfWorldT) e1 e2 :
  res_subset m0 m ->
  tm_result_equiv_on m e1 e2 ->
  tm_result_equiv_on m0 e1 e2.
Proof.
  intros [_ Hstores] Heq σ v Hσ.
  apply Heq. exact (Hstores σ Hσ).
Qed.

Lemma tm_result_equiv_on_total
    m e1 e2 :
  tm_result_equiv_on m e1 e2 ->
  lc_tm e2 ->
  fv_tm e2 ⊆ world_dom (m : WorldT) ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ expr_total_formula e2.
Proof.
  intros Heq Hlc2 Hfv2 Htotal.
  apply expr_total_formula_to_atom_world in Htotal.
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal as [_ Hstores].
  split.
  - rewrite res_lift_free_dom.
    rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
    unfold lvars_of_atoms.
    intros v Hv.
    apply elem_of_map in Hv as [a [Hv_eq Ha]].
    subst v.
    apply elem_of_map. exists a. split; [reflexivity|].
    apply Hfv2. exact Ha.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (Hstores (lstore_lift_free σ)) as [v Heval1].
    { exists σ. split; [exact Hσ | reflexivity]. }
    exists v.
    apply (proj1 (Heq σ v Hσ)). exact Heval1.
Qed.

Lemma tm_result_equiv_on_tapp_fvar
    (m : WfWorldT) e1 e2 y :
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y))) m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_result_equiv_on m e1 e2 ->
  tm_result_equiv_on m
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hclosed Hlc1 Hlc2 Heq σ v Hσ.
  set (X := fv_tm (tapp_tm e1 (vfvar y)) ∪
            fv_tm (tapp_tm e2 (vfvar y))).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. apply Hclosed. exact Hσ. }
  assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X) by (subst X; set_solver).
  assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X) by (subst X; set_solver).
  assert (Hfv_e1 : fv_tm e1 ⊆ X).
  {
    subst X. cbn [fv_tm fv_value].
    unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
	  assert (Hfv_e2 : fv_tm e2 ⊆ X).
	  {
	    subst X. cbn [fv_tm fv_value].
	    unfold tapp_tm. cbn [fv_tm fv_value].
	    set_solver.
	  }
	  assert (Hfun_equiv : forall vf,
	      expr_eval_in_atom_store (store_restrict σ X) e1 vf <->
	      expr_eval_in_atom_store (store_restrict σ X) e2 vf).
	  {
	    intros vf. split; intros Heval_fun.
	    - apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
	        σ e2 vf X Hfv_e2)).
	      apply (proj1 (Heq σ vf Hσ)).
	      apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
	        σ e1 vf X Hfv_e1)).
	      exact Heval_fun.
	    - apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
	        σ e1 vf X Hfv_e1)).
	      apply (proj2 (Heq σ vf Hσ)).
	      apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
	        σ e2 vf X Hfv_e2)).
	      exact Heval_fun.
	  }
	  pose proof (expr_eval_in_atom_store_tapp_tm_fun_equiv
	    (store_restrict σ X) e1 e2 y v HσX_closed Hlc1 Hlc2
	    Hfun_equiv) as [Happ12 Happ21].
	  split.
	  - intros Heval.
	    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
	      σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
	    apply Happ12.
	    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
	        σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
	    exact Heval.
	  - intros Heval.
	    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
	      σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
	    apply Happ21.
	    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
	        σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
	    exact Heval.
	Qed.

Lemma expr_result_formula_transport_of_tm_result_equiv
    m e1 e2 z :
  tm_result_equiv_on m e1 e2 ->
  z ∉ tm_lvars e1 ->
  tm_lvars e1 ∪ {[z]} ⊆ worldA_dom (res_lift_free m : LWorldT) ->
  m ⊨ expr_result_formula e2 z ->
  m ⊨ expr_result_formula e1 z.
Proof.
  intros Heq Hz Hdom1 Hres.
  apply expr_result_formula_to_atom_world in Hres.
  apply expr_result_atom_world_to_formula.
  destruct Hres as [_ [Hdom2 Hstores2]].
  split; [|split].
  - exact Hz.
  - exact Hdom1.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    specialize (Hstores2 (lstore_lift_free σ)
      ltac:(exists σ; split; [exact Hσ | reflexivity])).
    destruct Hstores2 as [_ [v [Hz_lookup Heval2]]].
    split; [exact Hz|].
    exists v. split; [exact Hz_lookup|].
    apply (proj2 (Heq σ v Hσ)). exact Heval2.
Qed.

Lemma tm_result_equiv_on_result_alias
    e x (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ expr_total_formula (tret (vfvar x)) ->
  tm_result_equiv_on m e (tret (vfvar x)).
Proof.
  intros Hres Htotal_ret σ v Hσ.
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hres)
    as Hres_world.
  pose proof (expr_total_formula_to_atom_world (tret (vfvar x)) m Htotal_ret)
    as Htotal_world.
  destruct Hres_world as [_ [_ Hres_stores]].
  destruct Htotal_world as [_ Htotal_stores].
  specialize (Hres_stores (lstore_lift_free σ)).
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  specialize (Hres_stores Hlift).
  specialize (Htotal_stores (lstore_lift_free σ) Hlift).
  destruct Hres_stores as [_ [vx [Hx_lookup Heval_e_vx]]].
  destruct Htotal_stores as [vt Heval_ret_vt].
  unfold expr_eval_in_atom_store, expr_eval_in_store.
  unfold expr_eval_in_atom_store, expr_eval_in_store in Heval_e_vx.
  unfold expr_eval_in_store in Heval_ret_vt.
  cbn [lstore_instantiate_tm lstore_instantiate_tm_at
    lstore_instantiate_tm_split_at] in Heval_ret_vt.
  change (tret (lstore_instantiate_value_at 0
    (lstore_lift_free σ) (vfvar x)) →* tret vt) in Heval_ret_vt.
  rewrite lstore_instantiate_value_at_fvar in Heval_ret_vt.
  assert (Hx_lookup_atom : σ !! x = Some vx).
  {
    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value) !!
      LVFree x = Some vx) in Hx_lookup.
    rewrite lstore_lift_free_lookup_free in Hx_lookup. exact Hx_lookup.
  }
  rewrite lstore_free_part_lift_free in Heval_ret_vt.
  destruct (σ !! x) as [vx'|] eqn:Hσx in Heval_ret_vt.
  2:{ rewrite Hx_lookup_atom in Hσx. discriminate. }
  assert (Hvxx : vx' = vx) by congruence. subst vx'.
  replace (match σ !! x with Some u => u | None => vfvar x end)
    with vx in Heval_ret_vt by (rewrite Hσx; reflexivity).
  assert (Hvt : vt = vx).
  {
    symmetry.
    pose proof (value_steps_self vx (tret vt) Heval_ret_vt) as Heq.
    inversion Heq. reflexivity.
  }
  subst vt.
  split.
  - intros Heval_e_v.
    assert (Hv : v = vx).
    { eapply steps_result_unique; [exact Heval_e_v | exact Heval_e_vx]. }
    subst v.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at].
    change (tret (lstore_instantiate_value_at 0
      (lstore_lift_free σ) (vfvar x)) →* tret vx).
    rewrite lstore_instantiate_value_at_fvar.
    rewrite lstore_free_part_lift_free.
    replace (match σ !! x with Some u => u | None => vfvar x end)
      with vx by (rewrite Hσx; reflexivity).
    exact Heval_ret_vt.
  - intros Heval_ret_v.
    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
      lstore_instantiate_tm_split_at] in Heval_ret_v.
    change (tret (lstore_instantiate_value_at 0
      (lstore_lift_free σ) (vfvar x)) →* tret v) in Heval_ret_v.
    rewrite lstore_instantiate_value_at_fvar in Heval_ret_v.
    rewrite lstore_free_part_lift_free in Heval_ret_v.
    replace (match σ !! x with Some u => u | None => vfvar x end)
      with vx in Heval_ret_v by (rewrite Hσx; reflexivity).
    pose proof (value_steps_self vx (tret v) Heval_ret_v) as Heq.
    inversion Heq. subst v. exact Heval_e_vx.
Qed.

Lemma typed_total_tm_result_equiv_on_term_scope
    Σ τ m e1 e2 :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT).
Proof.
  intros [_ [Hzero1 Hzero2]].
  pose proof (denot_ty_lvar_gas_guard_of_zero Σ τ e1 m Hzero1)
    as Hguard1.
  pose proof (denot_ty_lvar_gas_guard_of_zero Σ τ e2 m Hzero2)
    as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [_ Htotal1]]].
  destruct Hguard2 as [_ [_ [_ Htotal2]]].
  apply expr_total_formula_models_iff in Htotal1
    as [_ [Hscope1 _]].
  apply expr_total_formula_models_iff in Htotal2
    as [_ [Hscope2 _]].
  rewrite tm_lvars_fv in Hscope1.
  rewrite tm_lvars_fv in Hscope2.
  set_solver.
Qed.

Lemma typed_total_tm_result_equiv_on_term_lc_lvars
    Σ τ m e1 e2 :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  lc_lvars (tm_lvars e1) /\ lc_lvars (tm_lvars e2).
Proof.
  intros [_ [Hzero1 Hzero2]].
  pose proof (denot_ty_lvar_gas_guard_of_zero Σ τ e1 m Hzero1)
    as Hguard1.
  pose proof (denot_ty_lvar_gas_guard_of_zero Σ τ e2 m Hzero2)
    as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [_ Htotal1]]].
  destruct Hguard2 as [_ [_ [_ Htotal2]]].
  apply expr_total_formula_models_iff in Htotal1
    as [Hlc1 _].
  apply expr_total_formula_models_iff in Htotal2
    as [Hlc2 _].
  split; assumption.
Qed.

Lemma typed_total_tm_result_equiv_on_term_lc
    Σ τ m e1 e2 :
  typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
  lc_tm e1 /\ lc_tm e2.
Proof.
  intros [_ [Hzero1 Hzero2]].
  pose proof (denot_ty_lvar_gas_guard_of_zero Σ τ e1 m Hzero1)
    as Hguard1.
  pose proof (denot_ty_lvar_gas_guard_of_zero Σ τ e2 m Hzero2)
    as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [Hbasic1 _]]].
  destruct Hguard2 as [_ [_ [Hbasic2 _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic1
    as [HlcΣ1 [_ Hty1]].
  apply expr_basic_typing_formula_models_iff in Hbasic2
    as [HlcΣ2 [_ Hty2]].
  split.
  - eapply basic_tm_has_ltype_lc; [exact HlcΣ1|exact Hty1].
  - eapply basic_tm_has_ltype_lc; [exact HlcΣ2|exact Hty2].
Qed.

Lemma tm_result_equiv_on_full_world_extend_fresh
    (m my : WfWorldT) y e1 e2 :
  tm_result_equiv_on m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT) ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  tm_result_equiv_on my e1 e2.
Proof.
  intros Heq Hfv _ _ Hrestrict σ v Hσ.
  assert (Hσm :
      (m : WorldT) (store_restrict σ (world_dom (m : WorldT)))).
  {
    assert (Hσr :
        (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ (world_dom (m : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Heq (store_restrict σ (world_dom (m : WorldT))) v Hσm)
    as [Heq12 Heq21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (m : WorldT)) by set_solver.
  split.
  - intros Heval1.
    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
      σ e2 v (world_dom (m : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
      σ e1 v (world_dom (m : WorldT)) Hfv1)).
    exact Heval1.
  - intros Heval2.
    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
      σ e1 v (world_dom (m : WorldT)) Hfv1)).
    apply Heq21.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
      σ e2 v (world_dom (m : WorldT)) Hfv2)).
    exact Heval2.
Qed.

Lemma expr_result_formula_shift0_transport_of_tm_result_equiv_open
    (m my : WfWorldT) y e1 e2 :
  tm_result_equiv_on m e1 e2 ->
  lc_lvars (tm_lvars e1) ->
  lc_lvars (tm_lvars e2) ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT) ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (expr_result_formula (tm_shift 0 e2) (LVBound 0)) ->
  my ⊨ formula_open 0 y
    (expr_result_formula (tm_shift 0 e1) (LVBound 0)).
Proof.
  intros Heq Hlc1 Hlc2 Hfv Hy Hdom Hrestrict Hmodel.
  rewrite formula_open_expr_result_formula_shift0_lvars_lc in Hmodel
    by (exact Hlc2 || set_solver).
  rewrite formula_open_expr_result_formula_shift0_lvars_lc
    by (exact Hlc1 || set_solver).
  eapply expr_result_formula_transport_of_tm_result_equiv.
  - eapply tm_result_equiv_on_full_world_extend_fresh; eauto.
  - intros Hbad. apply Hy. apply elem_of_union_l.
    apply lvars_fv_elem in Hbad.
    rewrite tm_lvars_fv in Hbad. exact Hbad.
  - rewrite res_lift_free_dom.
    assert (Htm1_atoms :
        tm_lvars e1 ⊆ lvars_of_atoms (fv_tm e1)).
    {
      intros v Hv.
      pose proof (proj1 (lc_lvars_no_bv (tm_lvars e1)) Hlc1)
        as Hbv.
      pose proof (lvars_bv_empty_subset_of_atoms_fv
        (tm_lvars e1) Hbv v Hv) as Hin.
      rewrite tm_lvars_fv in Hin. exact Hin.
    }
    intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + specialize (Htm1_atoms _ Hv).
      unfold lvars_of_atoms in *.
      apply elem_of_map in Htm1_atoms as [a [-> Ha]].
      apply elem_of_map. exists a. split; [reflexivity|].
      change (a ∈ world_dom (my : WorldT)).
      rewrite Hdom. apply elem_of_union_l. apply Hfv. set_solver.
    + rewrite elem_of_singleton in Hv. subst v.
      unfold lvars_of_atoms.
      apply elem_of_map. exists y. split; [reflexivity|].
      change (y ∈ world_dom (my : WorldT)).
      rewrite Hdom. set_solver.
  - exact Hmodel.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_over_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTOver b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e1) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e2) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_tm_result_equiv_on_term_lc_lvars
    Σ (CTOver b φ) m e1 e2 Hequiv) as [Hlc_e1 Hlc_e2].
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ (CTOver b φ) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ (CTOver b φ) e2 m Hzero_tgt) as Hguard_tgt.
  assert (Hscope_tgt :
      formula_scoped_in_world m
        (denot_ty_lvar_gas (S gas) Σ (CTOver b φ) e2)).
  {
    unfold formula_scoped_in_world.
    eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
      [reflexivity|exact Hguard_tgt].
  }
  cbn [denot_ty_lvar_gas] in Hscope_tgt.
  pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hbody_scope.
  eapply res_models_forall_full_world_impl2_map;
    [exact Hbody_scope| |exact Hsrc].
  exists (fv_tm e1 ∪ fv_tm e2).
  intros y Hy my Hdom Hrestrict.
  split.
  - intros Hworld. exact Hworld.
  - split.
    + intros Hresult.
      eapply expr_result_formula_shift0_transport_of_tm_result_equiv_open;
        [ exact (proj1 Hequiv)
        | exact Hlc_e1
        | exact Hlc_e2
        | | set_solver
        | exact Hdom
        | exact Hrestrict
        | exact Hresult ].
      eapply typed_total_tm_result_equiv_on_term_scope. exact Hequiv.
    + intros Hfib. exact Hfib.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_under_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTUnder b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e1) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e2) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_tm_result_equiv_on_term_lc_lvars
    Σ (CTUnder b φ) m e1 e2 Hequiv) as [Hlc_e1 Hlc_e2].
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ (CTUnder b φ) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ (CTUnder b φ) e2 m Hzero_tgt) as Hguard_tgt.
  assert (Hscope_tgt :
      formula_scoped_in_world m
        (denot_ty_lvar_gas (S gas) Σ (CTUnder b φ) e2)).
  {
    unfold formula_scoped_in_world.
    eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
      [reflexivity|exact Hguard_tgt].
  }
  cbn [denot_ty_lvar_gas] in Hscope_tgt.
  pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hbody_scope.
  eapply res_models_forall_full_world_impl2_map;
    [exact Hbody_scope| |exact Hsrc].
  exists (fv_tm e1 ∪ fv_tm e2).
  intros y Hy my Hdom Hrestrict.
  split.
  - intros Hworld. exact Hworld.
  - split.
    + intros Hresult.
      eapply expr_result_formula_shift0_transport_of_tm_result_equiv_open;
        [ exact (proj1 Hequiv)
        | exact Hlc_e1
        | exact Hlc_e2
        | | set_solver
        | exact Hdom
        | exact Hrestrict
        | exact Hresult ].
      eapply typed_total_tm_result_equiv_on_term_scope. exact Hequiv.
    + intros Hfib. exact Hfib.
Qed.

Lemma denot_ty_lvar_gas_zero_project_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  erase_ty τsmall = erase_ty τbig ->
  context_ty_shape_ok τsmall ->
  m ⊨ denot_ty_lvar_gas 0 Σ τbig e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τsmall e.
Proof.
  intros Hτ Herase Hshape_small Hzero.
  apply denot_ty_lvar_gas_zero_of_guard.
  apply denot_ty_lvar_gas_guard_of_zero in Hzero.
  repeat rewrite res_models_and_iff in Hzero |- *.
  destruct Hzero as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (denot_relevant_env_dom_mono_context
    Σ τsmall τbig e Hτ) as Hdom_small_big.
  assert (Hrel_small_big :
      denot_relevant_lvars τsmall e ⊆ denot_relevant_lvars τbig e).
  { unfold denot_relevant_lvars. set_solver. }
  split.
  - apply context_ty_wf_formula_models_iff in Hwf
      as [Hlc_big [Hscope_big Hbasic_big]].
    apply context_ty_wf_formula_models_iff.
    assert (HbasicΣ_small :
        basic_context_ty_lvars (dom Σ) τsmall).
    {
      destruct Hbasic_big as [Hvars_big _].
      split; [|exact Hshape_small].
      intros v Hv.
      eapply denot_relevant_env_dom_subset_direct.
      apply Hvars_big. exact (Hτ _ Hv).
    }
    split.
    + intros v Hv. apply Hlc_big. exact (Hdom_small_big _ Hv).
    + split.
      * intros a Ha.
        apply Hscope_big.
        apply lvars_fv_elem in Ha.
        apply lvars_fv_elem. exact (Hdom_small_big _ Ha).
      * apply basic_context_ty_lvars_denot_relevant_env.
        exact HbasicΣ_small.
  - split.
    + eapply basic_world_formula_denot_relevant_mono_context; eauto.
    + split.
      * apply expr_basic_typing_formula_models_iff in Hbasic
          as [Hlc_big [Hscope_big Hty_big]].
        apply expr_basic_typing_formula_models_iff.
        split.
        -- intros v Hv. apply Hlc_big. exact (Hdom_small_big _ Hv).
        -- split.
           ++ intros a Ha.
              apply Hscope_big.
              apply lvars_fv_elem in Ha.
              apply lvars_fv_elem. exact (Hdom_small_big _ Ha).
           ++ rewrite Herase.
              replace (denot_relevant_env Σ τsmall e) with
                (storeA_restrict
                  (denot_relevant_env Σ τbig e)
                  (denot_relevant_lvars τsmall e)).
              2:{
                unfold denot_relevant_env.
                rewrite <- (denot_relevant_env_restrict_subset
                  Σ τbig e (denot_relevant_lvars τsmall e) Hrel_small_big).
                reflexivity.
              }
              eapply basic_tm_has_ltype_restrict_lvars_lc.
              ** exact Hty_big.
              ** eapply basic_tm_has_ltype_lc; eauto.
              ** unfold denot_relevant_lvars. set_solver.
      * exact Htotal.
Qed.

Lemma denot_ty_lvar_gas_zero_inter_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ1 (CTInter τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply denot_ty_lvar_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma denot_ty_lvar_gas_zero_inter_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTInter τ1 τ2)).
  {
    apply denot_ty_lvar_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ2 (CTInter τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_tm_result_equiv_on_inter_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ1 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_inter_l; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_inter_l; exact Hzero_tgt.
Qed.

Lemma typed_total_tm_result_equiv_on_inter_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ2 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_inter_r; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_inter_r; exact Hzero_tgt.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_inter_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  m ⊨ denot_ty_lvar_gas gas Σ τ1 e1 /\
  m ⊨ denot_ty_lvar_gas gas Σ τ2 e1 ->
  m ⊨ denot_ty_lvar_gas gas Σ τ1 e2 /\
  m ⊨ denot_ty_lvar_gas gas Σ τ2 e2.
Proof.
  intros Hequiv [H1 H2].
  split.
  - eapply IH; [|exact H1].
    eapply typed_total_tm_result_equiv_on_inter_l; exact Hequiv.
  - eapply IH; [|exact H2].
    eapply typed_total_tm_result_equiv_on_inter_r; exact Hequiv.
Qed.

Lemma denot_ty_lvar_gas_zero_union_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ1 (CTUnion τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply denot_ty_lvar_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma denot_ty_lvar_gas_zero_union_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTUnion τ1 τ2)).
  {
    apply denot_ty_lvar_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ2 (CTUnion τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_tm_result_equiv_on_union_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ1 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_union_l; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_union_l; exact Hzero_tgt.
Qed.

Lemma typed_total_tm_result_equiv_on_union_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ2 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_union_r; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_union_r; exact Hzero_tgt.
Qed.

Lemma denot_ty_lvar_gas_scope_from_zero_any
    gas Σ τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  formula_scoped_in_world m (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hzero.
  eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open.
  - reflexivity.
  - apply denot_ty_lvar_gas_guard_of_zero. exact Hzero.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_union_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  m ⊨
    FOr
      (denot_ty_lvar_gas gas Σ τ1 e1)
      (denot_ty_lvar_gas gas Σ τ2 e1) ->
  m ⊨
    FOr
	      (denot_ty_lvar_gas gas Σ τ1 e2)
	      (denot_ty_lvar_gas gas Σ τ2 e2).
Proof.
  intros Hequiv Hbody.
  pose proof (typed_total_tm_result_equiv_on_union_l
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv1.
  pose proof (typed_total_tm_result_equiv_on_union_r
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv2.
  pose proof (res_models_scoped _ _ Hbody) as Hscope_body.
  apply (proj1 (res_models_or_iff m _ _ Hscope_body)) in Hbody.
  destruct Hbody as [H1|H2].
  - eapply res_models_or_intro_l_from_model.
    + eapply IH; [exact Hequiv1|exact H1].
    + eapply denot_ty_lvar_gas_scope_from_zero_any.
      exact (typed_total_tm_result_equiv_on_target_zero
        Σ τ2 m e1 e2 Hequiv2).
  - eapply res_models_or_intro_r_from_model.
    + eapply denot_ty_lvar_gas_scope_from_zero_any.
      exact (typed_total_tm_result_equiv_on_target_zero
        Σ τ1 m e1 e2 Hequiv1).
    + eapply IH; [exact Hequiv2|exact H2].
Qed.

Lemma denot_ty_lvar_gas_zero_res_subset
    (Σ : lty_env) τ e (m n : WfWorldT) :
  res_subset n m ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  n ⊨ denot_ty_lvar_gas 0 Σ τ e.
Proof.
  intros Hsub Hzero.
  apply denot_ty_lvar_gas_zero_of_guard.
  apply denot_ty_lvar_gas_guard_of_zero in Hzero.
  repeat rewrite res_models_and_iff in Hzero |- *.
  destruct Hzero as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof Hsub as [Hdom _].
  split.
  - apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hscope Hbasic_ty]].
    apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [set_solver|exact Hbasic_ty].
  - split.
    + eapply basic_world_formula_res_subset; eauto.
    + split.
      * apply expr_basic_typing_formula_models_iff in Hbasic
          as [Hlc [Hscope Hty]].
        apply expr_basic_typing_formula_models_iff.
        split; [exact Hlc|]. split; [set_solver|exact Hty].
      * eapply expr_total_formula_res_subset; eauto.
Qed.

Lemma denot_ty_lvar_gas_zero_sum_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ1 (CTSum τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply denot_ty_lvar_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma denot_ty_lvar_gas_zero_sum_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTSum τ1 τ2)).
  {
    apply denot_ty_lvar_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ2 (CTSum τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_l_target_zero
    (Σ : lty_env) τ1 τ2 (e1 e2 : tm) (m m1 : WfWorldT) :
  res_subset m1 m ->
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e2 ->
  m1 ⊨ denot_ty_lvar_gas 0 Σ τ1 e2.
Proof.
  intros Hsub Hzero.
  apply denot_ty_lvar_gas_zero_sum_l with (τ2 := τ2).
  eapply denot_ty_lvar_gas_zero_res_subset; eauto.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_r_target_zero
    (Σ : lty_env) τ1 τ2 (e1 e2 : tm) (m m2 : WfWorldT) :
  res_subset m2 m ->
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e2 ->
  m2 ⊨ denot_ty_lvar_gas 0 Σ τ2 e2.
Proof.
  intros Hsub Hzero.
  apply denot_ty_lvar_gas_zero_sum_r with (τ1 := τ1).
  eapply denot_ty_lvar_gas_zero_res_subset; eauto.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_l_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m1 : WfWorldT) :
  res_subset m1 m ->
  typed_total_tm_result_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m1 ⊨ denot_ty_lvar_gas gas Σ τ1 e1 ->
  typed_total_tm_result_equiv_on Σ τ1 m1 e1 e2.
Proof.
  intros Hsub [Heq [_ Hzero_tgt]] Hsrc.
  split.
  - eapply tm_result_equiv_on_res_store_subset; eauto.
  - split.
    + apply denot_ty_lvar_gas_zero_of_guard.
      eapply denot_ty_lvar_gas_guard. exact Hsrc.
    + eapply typed_total_tm_result_equiv_on_sum_l_target_zero;
        eauto.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_r_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m2 : WfWorldT) :
  res_subset m2 m ->
  typed_total_tm_result_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m2 ⊨ denot_ty_lvar_gas gas Σ τ2 e1 ->
  typed_total_tm_result_equiv_on Σ τ2 m2 e1 e2.
Proof.
  intros Hsub [Heq [_ Hzero_tgt]] Hsrc.
  split.
  - eapply tm_result_equiv_on_res_store_subset; eauto.
  - split.
    + apply denot_ty_lvar_gas_zero_of_guard.
      eapply denot_ty_lvar_gas_guard. exact Hsrc.
    + eapply typed_total_tm_result_equiv_on_sum_r_target_zero;
        eauto.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_sum_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m ⊨
    FPlus
      (denot_ty_lvar_gas gas Σ τ1 e1)
      (denot_ty_lvar_gas gas Σ τ2 e1) ->
  m ⊨
    FPlus
	      (denot_ty_lvar_gas gas Σ τ1 e2)
	      (denot_ty_lvar_gas gas Σ τ2 e2).
Proof.
  intros Hequiv Hbody.
  apply res_models_plus_iff in Hbody as
    [n1 [n2 [Hdef [Hle [Hτ1 Hτ2]]]]].
  destruct (res_sum_pullback_subset_projection_full m n1 n2 Hdef Hle)
    as [Hsub1 [Hsub2 [Hdef_full Hle_full]]].
  set (m1 := res_pullback_subset_projection m n1 Hsub1).
  set (m2 := res_pullback_subset_projection m n2 Hsub2).
  assert (Hτ1_full : m1 ⊨ denot_ty_lvar_gas gas Σ τ1 e1).
  {
    subst m1.
    eapply res_models_pullback_subset_projection. exact Hτ1.
  }
  assert (Hτ2_full : m2 ⊨ denot_ty_lvar_gas gas Σ τ2 e1).
  {
    subst m2.
    eapply res_models_pullback_subset_projection. exact Hτ2.
  }
	  eapply res_models_plus_intro; [exact Hle_full| |].
	  - eapply IH; [|exact Hτ1_full].
	    refine (typed_total_tm_result_equiv_on_sum_l_pullback
	      gas Σ τ1 τ2 e1 e2 m m1 _ Hequiv Hτ1_full).
	    subst m1. apply res_pullback_subset_projection_subset.
	  - eapply IH; [|exact Hτ2_full].
	    refine (typed_total_tm_result_equiv_on_sum_r_pullback
	      gas Σ τ1 τ2 e1 e2 m m2 _ Hequiv Hτ2_full).
	    subst m2. apply res_pullback_subset_projection_subset.
	Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_arrow_open_arg
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_tm_result_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))) ->
  my ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros _ _ _ Hyτx HyΣ1 HyΣ2 Htgt.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt
    by (exact HyΣ2 || exact Hea_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact HyΣ1 || exact Hea_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in *
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  fold τa ea in Htgt |- *.
  pose proof (denot_ty_lvar_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (denot_relevant_lvars τa ea)
    ltac:(set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 Hyτx)) as Hsrc_mid.
  pose proof (denot_ty_lvar_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (denot_relevant_lvars τa ea)
    ltac:(set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 Hyτx)) as Htgt_mid.
  rewrite Hsrc_mid.
  rewrite Htgt_mid in Htgt.
  exact Htgt.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_arrow_open_result
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_tm_result_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))) ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  my ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  my ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτr Hye HyΣ1 HyΣ2 Hworld Harg Hres.
  pose proof (typed_total_tm_result_equiv_on_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hsrc_tm_fresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 e1) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_value]. set_solver.
  }
  assert (Htgt_tm_fresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 e2) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_value]. set_solver.
  }
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) in Hres
    by (exact HyΣ1 || exact Hsrc_tm_fresh || exact Hyτr).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e2) (vbvar 0)))
    by (exact HyΣ2 || exact Htgt_tm_fresh || exact Hyτr).
  rewrite open_tapp_tm_shift_bvar0_lc in Hres by exact Hlc1.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc2.
  set (τres := cty_open 0 y τr).
  set (esrc := tapp_tm e1 (vfvar y)).
  set (etgt := tapp_tm e2 (vfvar y)).
  fold τres esrc etgt in Hres |- *.
  assert (Hres_mid :
      my ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres esrc).
  { admit. }
  assert (Htgt_mid_to_goal :
      my ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres etgt ->
      my ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e2)
            (erase_ty τx)))
        τres etgt).
  { admit. }
  apply Htgt_mid_to_goal.
  eapply IH.
  - split.
    + eapply tm_result_equiv_on_tapp_fvar.
      * admit.
      * exact Hlc1.
      * exact Hlc2.
      * eapply tm_result_equiv_on_full_world_extend_fresh.
        -- exact (proj1 Hequiv).
        -- eapply typed_total_tm_result_equiv_on_term_scope. exact Hequiv.
        -- exact Hye.
        -- exact Hdom.
        -- exact Hrestrict.
    + split.
      * admit.
      * admit.
  - exact Hres_mid.
Admitted.


Lemma denot_ty_lvar_gas_tm_result_equiv_arrow_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e1)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e1)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e1) (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e2)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e2)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e2) (vbvar 0))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hguard_tgt.
  assert (Hscope_tgt :
      formula_scoped_in_world m
        (denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr) e2)).
  {
    unfold formula_scoped_in_world.
    eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
      [reflexivity|exact Hguard_tgt].
  }
  cbn [denot_ty_lvar_gas] in Hscope_tgt.
  pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hbody_scope.
  eapply res_models_forall_full_world_impl2_map_dep;
    [exact Hbody_scope| |exact Hsrc].
  exists (fv_cty τx ∪
    fv_cty τr ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv
      (dom (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ∪
    lvars_fv
      (dom (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
  intros y Hy my Hdom Hrestrict.
  split; [intros Hworld; exact Hworld|].
  split.
  - intros Harg.
    eapply denot_ty_lvar_gas_tm_result_equiv_arrow_open_arg; eauto;
      set_solver.
  - intros Hworld Harg Hres.
    eapply denot_ty_lvar_gas_tm_result_equiv_arrow_open_result; eauto.
    all: set_solver.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_wand_open_arg
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_tm_result_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros _ _ _ Hyτx HyΣ1 HyΣ2 Htgt.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt
    by (exact HyΣ2 || exact Hea_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact HyΣ1 || exact Hea_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in *
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  fold τa ea in Htgt |- *.
  pose proof (denot_ty_lvar_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e1) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (denot_relevant_lvars τa ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 Hyτx)) as Hsrc_mid.
  pose proof (denot_ty_lvar_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (denot_relevant_lvars τa ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 Hyτx)) as Htgt_mid.
  rewrite Hsrc_mid.
  rewrite Htgt_mid in Htgt.
  exact Htgt.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_wand_open_result
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_tm_result_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  n ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  res_product n my Hc ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e1)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  res_product n my Hc ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e2)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτr Hye HyΣ1 HyΣ2 Hworld Harg Hres.
  pose proof (typed_total_tm_result_equiv_on_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hsrc_tm_fresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 e1) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_value]. set_solver.
  }
  assert (Htgt_tm_fresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 e2) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_value]. set_solver.
  }
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) in Hres
    by (exact HyΣ1 || exact Hsrc_tm_fresh || exact Hyτr).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e2) (vbvar 0)))
    by (exact HyΣ2 || exact Htgt_tm_fresh || exact Hyτr).
  rewrite open_tapp_tm_shift_bvar0_lc in Hres by exact Hlc1.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc2.
  set (τres := cty_open 0 y τr).
  set (esrc := tapp_tm e1 (vfvar y)).
  set (etgt := tapp_tm e2 (vfvar y)).
  fold τres esrc etgt in Hres |- *.
  assert (Hres_mid :
      res_product n my Hc ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres esrc).
  { admit. }
  assert (Htgt_mid_to_goal :
      res_product n my Hc ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres etgt ->
      res_product n my Hc ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e2)
            (erase_ty τx)))
        τres etgt).
  { admit. }
  apply Htgt_mid_to_goal.
  eapply IH.
  - split.
    + eapply tm_result_equiv_on_tapp_fvar.
      * admit.
      * exact Hlc1.
      * exact Hlc2.
      * eapply tm_result_equiv_on_res_store_subset.
        -- admit.
        -- eapply tm_result_equiv_on_full_world_extend_fresh.
           ++ exact (proj1 Hequiv).
           ++ eapply typed_total_tm_result_equiv_on_term_scope. exact Hequiv.
           ++ exact Hye.
           ++ exact Hdom.
           ++ exact Hrestrict.
    + split.
      * admit.
      * admit.
  - exact Hres_mid.
Admitted.

Lemma denot_ty_lvar_gas_tm_result_equiv_wand_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e1)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e1)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e1) (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e2)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e2)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e2) (vbvar 0))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_tgt) as Hguard_tgt.
  assert (Hscope_tgt :
      formula_scoped_in_world m
        (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) e2)).
  {
    unfold formula_scoped_in_world.
    eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
      [reflexivity|exact Hguard_tgt].
  }
  cbn [denot_ty_lvar_gas] in Hscope_tgt.
  pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hbody_scope.
  eapply res_models_forall_full_world_impl_wand_map_dep;
    [exact Hbody_scope| |exact Hsrc].
  exists (fv_cty τx ∪
    fv_cty τr ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv
      (dom (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ∪
    lvars_fv
      (dom (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))).
  intros y Hy my Hdom Hrestrict.
  split; [intros Hworld; exact Hworld|].
  split.
  - intros n Hc Harg.
    eapply denot_ty_lvar_gas_tm_result_equiv_wand_open_arg; eauto;
      set_solver.
  - intros Hworld n Hc Harg Hres.
    eapply denot_ty_lvar_gas_tm_result_equiv_wand_open_result; eauto.
    all: set_solver.
Qed.

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
