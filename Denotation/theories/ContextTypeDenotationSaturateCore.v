(** * Denotation.ContextTypeDenotationSaturateCore

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation ContextTypeDenotationOpen.
From Denotation Require Export ContextTypeDenotationTactics.

Section ContextTypeDenotation.

Lemma formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  fv_tm e ∪ fv_cty τ ⊆ formula_fv (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hwf.
  transitivity (lvars_fv (denot_relevant_lvars τ e)).
  - rewrite denot_relevant_lvars_fv. set_solver.
  - apply lvars_fv_mono.
    unfold denot_relevant_lvars.
    pose proof (basic_context_ty_lvars_denot_relevant_env Σ τ e Hwf)
      as [Hτ _].
    destruct gas as [|gas]; destruct τ;
      cbn [denot_ty_lvar_gas formula_lvars context_ty_wf_formula
        context_ty_wf_lqual basic_world_formula basic_world_lqual
        expr_basic_typing_formula expr_basic_typing_lqual expr_total_formula
        expr_total_lqual lqual_lvars lqual_fv lqual_dom];
      better_set_solver.
Qed.

Lemma expr_result_formula_free_in_world
    e x (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree x) ->
  x ∈ world_dom (m : WorldT).
Proof.
  intros Hres.
  pose proof (res_models_scoped _ _ Hres) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  apply Hscope.
  normalize_denotation_formula_fv.
  set_solver.
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
  pose proof (formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ e Hwf) as Hlower.
  unfold formula_scoped_in_world in *.
  transitivity (fv_tm (tret (vfvar x)) ∪ fv_cty τ).
  - apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
  - cbn [fv_tm fv_value tm_lvars tm_lvars_at value_lvars value_lvars_at].
    assert (Hx_scope : {[x]} ⊆ world_dom (m : WorldT)).
    {
      intros z Hz.
      apply elem_of_singleton in Hz. subst z.
      eapply expr_result_formula_free_in_world. exact Hres.
    }
    assert (Hτ_scope : fv_cty τ ⊆ world_dom (m : WorldT)).
    {
      transitivity (fv_tm e ∪ fv_cty τ).
      - set_solver.
      - transitivity (formula_fv (denot_ty_lvar_gas gas Σ τ e));
          [exact Hlower | exact Hscope].
    }
    set_solver.
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

Lemma atom_store_has_ltype_restrict_fv_from_source_guard
    (Σ : lty_env) τ e (m : WfWorldT) σ :
  m ⊨ basic_world_formula (denot_relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula (denot_relevant_env Σ τ e) e
    (erase_ty τ) ->
  worldA_stores (m : WorldT) σ ->
  atom_store_has_ltype (denot_relevant_env Σ τ e)
    (store_restrict σ (fv_tm e)).
Proof.
  intros Hworld Hbasic Hσ y u Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [Hyfv Hσy].
  apply basic_world_formula_models_iff in Hworld as [_ [_ Htyped]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  destruct Htyped as [_ Hstores].
  specialize (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])).
  assert (Hy_dom : LVFree y ∈ dom (denot_relevant_env Σ τ e)).
  {
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hfv.
    apply Hfv. unfold lvars_of_atoms. set_solver.
  }
  apply elem_of_dom in Hy_dom as [Uy HΣy].
  exists Uy. split; [exact HΣy|].
  eapply Hstores; [exact HΣy|].
  change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
    !! LVFree y = Some u).
  rewrite lstore_lift_free_lookup_free. exact Hσy.
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
  pose proof Hworld as Hworld_model.
  pose proof Hbasic as Hbasic_model.
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
          replace (store_restrict σm (ext_in Fx))
            with (store_restrict σm (fv_tm e))
            by (rewrite Hin; reflexivity).
          eapply atom_store_has_ltype_restrict_fv_from_source_guard;
            [exact Hworld_model|exact Hbasic_model|exact Hσm].
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
  pose proof Hworld_src as Hworld_src_model.
  pose proof Hbasic_src as Hbasic_src_model.
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
             eapply atom_store_has_ltype_restrict_fv_from_source_guard;
               [exact Hworld_src_model|exact Hbasic_src_model|exact Hσ].
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
             unfold lvars_of_atoms. set_solver.
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
           better_store_solver.
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
    apply denot_relevant_env_dom_subset_direct.
  }
  assert (Hlookup_target :
      denot_relevant_env Σ τ (tret (vfvar x)) !! LVFree x =
      Some (erase_ty τ)).
  {
    unfold denot_relevant_env, lty_env_restrict_lvars.
    assert (Hin :
        LVFree x ∈ denot_relevant_lvars τ (tret (vfvar x))).
    {
      unfold denot_relevant_lvars.
      cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
      set_solver.
    }
    better_store_solver.
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
  - cbn [tm_lvars tm_lvars_at value_lvars_at] in Hret_dom.
    set_solver.
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

Lemma tm_result_equiv_on_tlete_body_extension
    e1 e2 x Fx m mx :
  lc_tm (tlete e1 e2) ->
  wfworld_closed_on (fv_tm (tlete e1 e2)) mx ->
  mx ⊨ expr_total_formula (tlete e1 e2) ->
  x ∉ fv_tm e2 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  tm_result_equiv_on mx (e2 ^^ x) (tlete e1 e2).
Proof.
  intros Hlc Hclosed Htotal Hx_e2 HFx Hext σ v Hσmx.
  pose proof HFx as HFx_parts.
  destruct HFx_parts as [Hx_fv [Hin Hout] Hrel].
  pose proof (expr_total_formula_to_atom_world (tlete e1 e2) mx Htotal)
    as Htotal_world.
  destruct Htotal_world as [Htotal_dom Htotal_stores].
  assert (Hscope_body :
      tm_lvars (e2 ^^ x) ⊆ lvars_of_atoms (dom (σ : StoreT))).
  {
    pose proof (wfworldA_store_dom mx σ Hσmx) as Hσdom.
    change (dom (σ : StoreT) = world_dom (mx : WorldT)) in Hσdom.
    rewrite Hσdom.
    pose proof (res_extend_by_dom m Fx mx Hext) as Hmx_dom.
    change (world_dom (mx : WorldT) =
      world_dom (m : WorldT) ∪ ext_out Fx) in Hmx_dom.
    rewrite Hmx_dom, Hout.
    intros z Hz.
    pose proof (tm_lvars_tlete_open_body_subset e1 e2 x Hlc Hx_e2 z Hz)
      as Hz_cases.
    apply elem_of_union in Hz_cases as [Hz_tlet|Hzx].
    - specialize (Htotal_dom z Hz_tlet).
      unfold lvars_of_atoms in *.
      apply elem_of_map in Htotal_dom as [a [-> Ha]].
      apply elem_of_map. exists a. split; [reflexivity|set_solver].
    - rewrite elem_of_singleton in Hzx. subst z.
      unfold lvars_of_atoms. apply elem_of_map.
      exists x. split; [reflexivity|set_solver].
  }
  assert (Hstore_result :
      forall vx,
        expr_eval_in_atom_store (store_restrict σ (fv_tm e1)) e1 vx ->
        σ !! x = Some vx).
  {
    intros vx He1σ.
    apply (proj1 (resA_extend_by_store_iff m Fx mx σ Hext)) in Hσmx.
    destruct Hσmx as [σm [we [σe [Hσm [HFrel [Hσe ->]]]]]].
    set (σX := store_restrict σm (fv_tm e1)).
    assert (HσX_dom : dom (σX : StoreT) = fv_tm e1).
    {
      subst σX.
      change (dom (storeA_restrict σm (fv_tm e1) : gmap atom value) = fv_tm e1).
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
      pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
      unfold ext_in in Hin. rewrite Hin in Hin_sub.
      set_solver.
    }
    assert (HFσX : ext_rel Fx σX we).
    {
      subst σX.
      replace (store_restrict σm (fv_tm e1))
        with (store_restrict σm (ext_in Fx)) by
        (unfold ext_in; unfold ext_in in Hin; rewrite Hin; reflexivity).
      exact HFrel.
    }
    assert (He1σX : expr_eval_in_atom_store σX e1 vx).
    {
      subst σX.
      apply (proj2 (expr_eval_in_atom_store_restrict_fv_exact σm e1 vx)).
      pose proof (expr_eval_in_atom_store_agree_on_fv
        (σm ∪ σe) σm e1 vx) as Hagree_eval.
      apply Hagree_eval.
      + apply storeA_map_eq. intros a.
        rewrite !storeA_restrict_lookup.
        destruct (decide (a ∈ fv_tm e1)) as [Ha|Ha]; [|reflexivity].
        pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh_out.
        change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh_out.
        rewrite Hout in Hfresh_out.
        pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
        change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
        assert (a ∈ dom (σm : StoreT)).
        {
          pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
          unfold ext_in in Hin. rewrite Hin in Hin_sub.
          rewrite Hdomσm. set_solver.
        }
        change (a ∈ dom (σm : gmap atom value)) in H.
        apply elem_of_dom in H as [u Hu].
        apply lookup_union_l'. exists u. exact Hu.
      + apply (proj1 (expr_eval_in_atom_store_agree_on_fv
          (store_restrict (σm ∪ σe) (fv_tm e1)) (σm ∪ σe) e1 vx
          ltac:(apply storeA_restrict_twice_same))).
        exact He1σ.
    }
    pose proof (expr_result_extension_apply_total_iff
      e1 x Fx σX we
      {| expr_result_extension_witness_fresh := Hx_fv;
         expr_result_extension_witness_shape := conj Hin Hout;
         expr_result_extension_witness_rel := Hrel |}
      HσX_dom HFσX (ex_intro _ vx He1σX) σe) as Hσe_iff.
    apply Hσe_iff in Hσe as [u [He1_u ->]].
    assert (u = vx).
    {
      unfold expr_eval_in_atom_store, expr_eval_in_store in He1_u, He1σX.
      eapply steps_result_unique; eauto.
    }
    subst u.
    assert (Hxσm : x ∉ dom (σm : gmap atom value)).
    {
      pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh_out.
      change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh_out.
      rewrite Hout in Hfresh_out.
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : StoreT) = world_dom (m : WorldT)) in Hdomσm.
      rewrite <- Hdomσm in Hfresh_out. set_solver.
    }
    change (((σm : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! x =
      Some vx).
    transitivity (({[x := vx]} : gmap atom value) !! x).
    - apply (lookup_union_r (M:=gmap atom) (A:=value)
        (σm : gmap atom value) ({[x := vx]} : gmap atom value) x).
      apply not_elem_of_dom. exact Hxσm.
    - apply map_lookup_singleton.
  }
  assert (Hinsert_restrict_y :
      forall y vx,
        y ∉ dom (σ : StoreT) ->
        y ∉ fv_tm (tlete e1 e2) ->
        store_restrict (<[y := vx]> σ) (fv_tm (e2 ^^ y)) =
        store_restrict
          (<[y := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
          (fv_tm (e2 ^^ y))).
  {
    intros y vx Hyσ Hylet.
    change (e2 ^^ y) with (open_tm 0 (vfvar y) e2).
    change (store_restrict (<[y := vx]> (σ : gmap atom value) : gmap atom value)
        (fv_tm (open_tm 0 (vfvar y) e2)) =
      store_restrict
        (<[y := vx]> (store_restrict σ (fv_tm (tlete e1 e2)) : gmap atom value)
          : gmap atom value)
        (fv_tm (open_tm 0 (vfvar y) e2))).
    replace (store_restrict
        (<[y := vx]> (σ : gmap atom value) : gmap atom value)
        (fv_tm (open_tm 0 (vfvar y) e2)))
      with (store_restrict
        ((σ : gmap atom value) ∪ ({[y := vx]} : gmap atom value))
        (fv_tm (open_tm 0 (vfvar y) e2))).
    2:{
      f_equal.
      apply storeA_union_singleton_insert_fresh. exact Hyσ.
    }
    eapply store_insert_restrict_agree_on_open_fv.
    - cbn [fv_tm]. set_solver.
    - exact Hylet.
    - exact Hyσ.
  }
  split.
  - intros Hbody.
    pose (y := fresh_for (dom (σ : StoreT) ∪ fv_tm e2 ∪
      fv_tm (tlete e1 e2))).
    assert (Hyfresh : y ∉ dom (σ : StoreT) ∪ fv_tm e2 ∪
      fv_tm (tlete e1 e2)).
    { unfold y. apply fresh_for_not_in. }
    assert (Hyσ : y ∉ dom (σ : StoreT)) by set_solver.
    assert (Hye2 : y ∉ fv_tm e2) by set_solver.
    assert (Hylet : y ∉ fv_tm (tlete e1 e2)) by set_solver.
    destruct (Htotal_stores (lstore_lift_free σ)) as [v0 Htlet0].
    { exists σ. split; [exact Hσmx|reflexivity]. }
    destruct (expr_eval_in_atom_store_tlete_elim_closed_on
      e1 e2 y σ v0 (Hclosed σ Hσmx) Hylet Hye2 Htlet0)
      as [vx [He1σ _]].
    pose proof (Hstore_result vx He1σ) as Hx_lookup.
    eapply expr_eval_in_atom_store_tlete_intro_closed_on with (x := y) (vx := vx).
    + exact (Hclosed σ Hσmx).
    + exact Hlc.
    + set_solver.
    + apply (proj1 (expr_eval_in_atom_store_agree_on_fv
        (store_restrict σ (fv_tm e1))
        (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx
        ltac:(
          rewrite storeA_restrict_twice_same;
          rewrite storeA_restrict_twice_subset by (cbn [fv_tm]; set_solver);
          reflexivity))).
      exact He1σ.
    + apply (proj1 (expr_eval_in_atom_store_agree_on_fv
        (<[y := vx]> σ)
        (<[y := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ y) v (Hinsert_restrict_y y vx Hyσ Hylet))).
      apply (proj1 (expr_eval_in_atom_store_open_alias
          e2 σ x y vx v Hx_lookup Hyσ Hx_e2 Hye2 Hscope_body)).
      exact Hbody.
  - intros Hlet.
    pose (y := fresh_for (dom (σ : StoreT) ∪ fv_tm e2 ∪
      fv_tm (tlete e1 e2))).
    assert (Hyfresh : y ∉ dom (σ : StoreT) ∪ fv_tm e2 ∪
      fv_tm (tlete e1 e2)).
    { unfold y. apply fresh_for_not_in. }
    assert (Hyσ : y ∉ dom (σ : StoreT)) by set_solver.
    assert (Hye2 : y ∉ fv_tm e2) by set_solver.
    assert (Hylet : y ∉ fv_tm (tlete e1 e2)) by set_solver.
    destruct (expr_eval_in_atom_store_tlete_elim_closed_on
      e1 e2 y σ v (Hclosed σ Hσmx) Hylet Hye2 Hlet)
      as [vx [He1σ Hbody_y]].
    pose proof (Hstore_result vx He1σ) as Hx_lookup.
    apply (proj2 (expr_eval_in_atom_store_open_alias
      e2 σ x y vx v Hx_lookup Hyσ Hx_e2 Hye2 Hscope_body)).
    apply (proj2 (expr_eval_in_atom_store_agree_on_fv
        (<[y := vx]> σ)
        (<[y := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ y) v (Hinsert_restrict_y y vx Hyσ Hylet))).
    exact Hbody_y.
Qed.

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

Lemma tm_result_equiv_on_res_store_subset
    (m0 m : WfWorldT) e1 e2 :
  res_subset m0 m ->
  tm_result_equiv_on m e1 e2 ->
  tm_result_equiv_on m0 e1 e2.
Proof.
  intros [_ Hstores] Heq σ v Hσ.
  apply Heq. exact (Hstores σ Hσ).
Qed.

Lemma tm_result_equiv_on_res_product_right
    (n my : WfWorldT) (Hc : world_compat n my) e1 e2 :
  tm_result_equiv_on my e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT) ->
  tm_result_equiv_on (res_product n my Hc) e1 e2.
Proof.
  intros Heq Hfv σ v Hσ.
  pose proof (res_restrict_eq_of_le my (res_product n my Hc)
    (res_product_le_r n my Hc)) as Hrestrict.
  assert (Hσmy :
      (my : WorldT) (store_restrict σ (world_dom (my : WorldT)))).
  {
    assert (Hσr :
        (res_restrict (res_product n my Hc)
          (world_dom (my : WorldT)) : WorldT)
          (store_restrict σ (world_dom (my : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Heq (store_restrict σ (world_dom (my : WorldT))) v Hσmy)
    as [Heq12 Heq21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (my : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (my : WorldT)) by set_solver.
  split.
  - intros Heval1.
    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
      σ e2 v (world_dom (my : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
      σ e1 v (world_dom (my : WorldT)) Hfv1)).
    exact Heval1.
  - intros Heval2.
    apply (proj1 (expr_eval_in_atom_store_restrict_fv_subset
      σ e1 v (world_dom (my : WorldT)) Hfv1)).
    apply Heq21.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
      σ e2 v (world_dom (my : WorldT)) Hfv2)).
    exact Heval2.
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
    unfold lvars_of_atoms. set_solver.
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

Lemma tm_lvars_tapp_tm_fvar_without_arg_shift_lc e y :
  lc_tm e ->
  tm_lvars (tapp_tm e (vfvar y)) ∖ {[LVFree y]} ⊆
    lvars_shift_from 0 (tm_lvars e).
Proof.
  intros Hlc.
  rewrite (tm_lvars_lc_eq_atoms e Hlc).
  intros v Hv.
  apply elem_of_difference in Hv as [Hv Hvy].
  rewrite tm_lvars_tapp_tm_fvar in Hv.
  apply elem_of_union in Hv as [Hv|Hv].
  - rewrite (tm_lvars_lc_eq_atoms e Hlc) in Hv.
    unfold lvars_shift_from.
    apply elem_of_map.
    exists v. split; [|exact Hv].
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> _]].
    reflexivity.
  - rewrite elem_of_singleton in Hv. subst v.
    exfalso. apply Hvy. set_solver.
Qed.

Lemma lty_env_open_one_typed_bind_lookup_free_ne
    (Σ : lty_env) T y z :
  z <> y ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) !! LVFree z =
  Σ !! LVFree z.
Proof.
  intros Hzy.
  unfold lty_env_open_one, lvar_store_open_one.
  change ((kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (logic_var_open 0 y) (typed_lty_env_bind Σ T) : gmap logic_var ty) !!
    LVFree z =
    Σ !! LVFree z).
  replace (LVFree z) with (logic_var_open 0 y (LVFree z)) at 1.
  - rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=swap_inj (LVBound 0) (LVFree y))
      (logic_var_open 0 y) (typed_lty_env_bind Σ T) (LVFree z)).
    apply typed_lty_env_bind_lookup_free.
  - rewrite logic_var_open_sym.
    unfold swap.
    repeat case_decide; congruence.
Qed.

Lemma lty_env_open_one_typed_bind_lookup_current
    (Σ : lty_env) T y :
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) !! LVFree y =
  Some T.
Proof.
  unfold lty_env_open_one, lvar_store_open_one.
  change ((kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (logic_var_open 0 y) (typed_lty_env_bind Σ T) : gmap logic_var ty) !!
    LVFree y =
    Some T).
  replace (LVFree y) with (logic_var_open 0 y (LVBound 0)) at 1.
    - rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=swap_inj (LVBound 0) (LVFree y))
      (logic_var_open 0 y) (typed_lty_env_bind Σ T) (LVBound 0)).
    unfold typed_lty_env_bind, lvar_store_bind.
    rewrite lookup_insert.
    destruct (decide (LVBound 0 = LVBound 0)); [reflexivity|congruence].
  - rewrite logic_var_open_sym.
    unfold swap.
    repeat case_decide; try congruence.
Qed.

Lemma basic_tm_has_ltype_tapp_tm_lvar
    (Σ : lty_env) ef vx Tx T :
  lc_lvars (dom (Σ : gmap logic_var ty)) ->
  basic_tm_has_ltype Σ ef (Tx →ₜ T) ->
  basic_value_has_ltype Σ vx Tx ->
  basic_tm_has_ltype Σ (tapp_tm ef vx) T.
Proof.
  intros HlcΣ Hef Hvx.
  pose proof (basic_value_has_ltype_lc Σ vx Tx HlcΣ Hvx) as Hlc_vx.
  unfold tapp_tm.
  eapply BTT_Let with (L := lvars_fv (dom (Σ : gmap logic_var ty)) ∪ fv_value vx).
  - exact Hef.
  - intros z Hz.
    change (basic_tm_has_ltype (<[LVFree z := Tx →ₜ T]> Σ)
      (tapp (vfvar z)
        (open_value 0 (vfvar z) (value_shift 0 vx))) T).
    assert (Hshift_lc : lc_value (value_shift 0 vx)).
    { rewrite value_shift_lc_id by exact Hlc_vx. exact Hlc_vx. }
    rewrite (open_rec_lc_value (value_shift 0 vx) Hshift_lc 0 (vfvar z)).
    rewrite value_shift_lc_id by exact Hlc_vx.
    eapply BTT_App.
    + constructor.
      rewrite lookup_insert.
      destruct (decide (LVFree z = LVFree z)); [reflexivity|congruence].
    + eapply basic_value_has_ltype_weaken; [exact Hvx|].
      apply map_subseteq_spec. intros v U Hlook.
      rewrite lookup_insert_ne.
      * exact Hlook.
      * intros Hvz. subst v.
        apply Hz. apply elem_of_union_l.
        apply lvars_fv_elem. eapply elem_of_dom_2. exact Hlook.
Qed.

Lemma basic_tm_has_ltype_open_result_target_fun
    (Σ : lty_env) τtop τx τr e1 e2
    (m : WfWorldT) y :
  erase_ty τtop = erase_ty τx →ₜ erase_ty τr ->
  typed_total_tm_result_equiv_on Σ τtop m e1 e2 ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  basic_tm_has_ltype
    (denot_relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    e2 (erase_ty τx →ₜ erase_ty τr).
Proof.
  intros Herase Hequiv Hye.
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ τtop m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ τtop e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [_ [_ [Hbasic_top_tgt _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic_top_tgt
    as [Hlc_top [_ Hty_fun_top]].
  rewrite Herase in Hty_fun_top.
  pose proof (basic_tm_has_ltype_lc _ _ _ Hlc_top Hty_fun_top) as Hlc2.
  eapply basic_tm_has_ltype_weaken.
  - eapply basic_tm_has_ltype_restrict_lvars_lc.
    + exact Hty_fun_top.
    + exact Hlc2.
    + rewrite (tm_lvars_lc_eq_atoms e2 Hlc2). set_solver.
  - apply map_subseteq_spec. intros v U Hlook.
    apply storeA_restrict_lookup_some in Hlook as [Hvfv Htop].
    unfold denot_relevant_env, lty_env_restrict_lvars in Htop.
    apply storeA_restrict_lookup_some in Htop as [_ HΣv].
    destruct v as [k|z].
    + unfold lvars_of_atoms in Hvfv. set_solver.
    + assert (Hzy : z <> y).
      {
        intros ->. apply Hye.
        unfold lvars_of_atoms in Hvfv. set_solver.
      }
      unfold denot_relevant_env, lty_env_restrict_lvars.
      assert (Hlook_open :
          lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx))
            !! LVFree z = Some U).
      { rewrite lty_env_open_one_typed_bind_lookup_free_ne by exact Hzy.
        exact HΣv. }
      assert (Hin :
          LVFree z ∈ denot_relevant_lvars (cty_open 0 y τr)
            (tapp_tm e2 (vfvar y))).
      {
        unfold denot_relevant_lvars.
        rewrite tm_lvars_tapp_tm_fvar.
        rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
        unfold lvars_of_atoms in *. set_solver.
      }
      better_store_solver.
Qed.

Lemma basic_value_has_ltype_open_result_target_arg
    (Σ : lty_env) τx τr e y :
  basic_value_has_ltype
    (denot_relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e (vfvar y)))
    (vfvar y) (erase_ty τx).
Proof.
  constructor.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  assert (Hlook :
      lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx))
        !! LVFree y = Some (erase_ty τx)).
  { apply lty_env_open_one_typed_bind_lookup_current. }
  assert (Hin :
      LVFree y ∈ denot_relevant_lvars (cty_open 0 y τr)
        (tapp_tm e (vfvar y))).
  {
    unfold denot_relevant_lvars.
    rewrite tm_lvars_tapp_tm_fvar.
    set_solver.
  }
  better_store_solver.
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
    { apply tm_lvars_lc_subset_atoms_fv. exact Hlc1. }
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

End ContextTypeDenotation.
