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

Lemma denot_ty_lvar_gas_result_alias_over_body
    (gas : nat) (Σ : lty_env) b φ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (TBase b) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ))))).
Proof.
Admitted.

Lemma denot_ty_lvar_gas_result_alias_under_body
    (gas : nat) (Σ : lty_env) b φ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (TBase b) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ))))).
Proof.
Admitted.

Lemma denot_ty_lvar_gas_result_alias_union_body
    gas (Σ : lty_env) τ1 τ2 e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty (CTUnion τ1 τ2)) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨
    FOr
      (denot_ty_lvar_gas gas Σ τ1 e)
      (denot_ty_lvar_gas gas Σ τ2 e) ->
  m ⊨
    FOr
      (denot_ty_lvar_gas gas Σ τ1 (tret (vfvar x)))
      (denot_ty_lvar_gas gas Σ τ2 (tret (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_lvar_gas_result_alias_sum_body
    gas (Σ : lty_env) τ1 τ2 e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty (CTSum τ1 τ2)) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨
    FPlus
      (denot_ty_lvar_gas gas Σ τ1 e)
      (denot_ty_lvar_gas gas Σ τ2 e) ->
  m ⊨
    FPlus
      (denot_ty_lvar_gas gas Σ τ1 (tret (vfvar x)))
      (denot_ty_lvar_gas gas Σ τ2 (tret (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_lvar_gas_result_alias_arrow_body
    gas (Σ : lty_env) τx τr e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty (CTArrow τx τr)) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) (tret (vfvar x)))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) (tret (vfvar x)))
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 (tret (vfvar x))) (vbvar 0))))).
Proof.
Admitted.

Lemma denot_ty_lvar_gas_result_alias_wand_body
    gas (Σ : lty_env) τx τr e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty (CTWand τx τr)) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) (tret (vfvar x)))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) (tret (vfvar x)))
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 (tret (vfvar x))) (vbvar 0))))).
Proof.
Admitted.

Lemma denot_ty_lvar_gas_result_alias_to_var
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  m ⊨ denot_ty_lvar_gas gas Σ τ (tret (vfvar x)).
Proof.
  revert Σ τ e x m.
  induction gas as [|gas IH]; intros Σ τ e x m HΣclosed HΣx Hres Hm.
  - apply denot_ty_lvar_gas_zero_of_guard.
    eapply denot_ty_lvar_gas_result_alias_guard; eauto.
    eapply denot_ty_lvar_gas_guard_of_zero. exact Hm.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas] in Hm |- *;
      repeat rewrite res_models_and_iff in Hm |- *;
      destruct Hm as [Hguard Hbody];
      split.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + eapply denot_ty_lvar_gas_result_alias_over_body; eauto.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + eapply denot_ty_lvar_gas_result_alias_under_body; eauto.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + destruct Hbody as [H1 H2].
      split.
      * eapply IH; eauto.
      * assert (Herase : erase_ty τ1 = erase_ty τ2).
        {
          pose proof (proj1 Hguard) as Hwf_guard.
          apply context_ty_wf_formula_models_iff in Hwf_guard as [_ [_ Hbasic]].
          destruct Hbasic as [_ Hshape].
          cbn [context_ty_shape_ok] in Hshape. tauto.
        }
        eapply IH; eauto.
        rewrite <- Herase. exact HΣx.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + eapply denot_ty_lvar_gas_result_alias_union_body; eauto.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + eapply denot_ty_lvar_gas_result_alias_sum_body; eauto.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + eapply denot_ty_lvar_gas_result_alias_arrow_body; eauto.
    + repeat rewrite <- res_models_and_iff.
      eapply denot_ty_lvar_gas_result_alias_guard; eauto.
      repeat rewrite res_models_and_iff. exact Hguard.
    + eapply denot_ty_lvar_gas_result_alias_wand_body; eauto.
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
