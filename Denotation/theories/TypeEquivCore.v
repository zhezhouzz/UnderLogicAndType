(** * Denotation.TypeEquivCore

    Core support for result-equivalence and result-extension transport. *)

From Denotation Require Import Notation TypeDenote.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Lemma ty_denote_gas_saturate gas Σ τ e :
  cty_depth τ <= gas ->
  ty_denote_gas gas Σ τ e =
  ty_denote_gas (cty_depth τ) Σ τ e.
Proof.
  assert (Hsat :
    forall gas τ Σ e,
      cty_depth τ <= gas ->
      ty_denote_gas gas Σ τ e =
      ty_denote_gas (cty_depth τ) Σ τ e).
  {
    intros fuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros τ0 Σ0 e0 Hgas.
    destruct fuel as [|gas']; destruct τ0; cbn [cty_depth] in Hgas; try lia;
      cbn [cty_depth ty_denote_gas].
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
	          (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH gas' ltac:(lia) τ0_2
	        (typed_lty_env_bind
	          (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        τ0_2 (typed_lty_env_bind
	          (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      reflexivity.
	    - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        (cty_shift 0 τ0_1)
	        (typed_lty_env_bind
	          (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1)) (tret (vbvar 0))
	        ltac:(rewrite cty_shift_preserves_depth; lia)).
	      rewrite (IH gas' ltac:(lia) τ0_2
	        (typed_lty_env_bind
	          (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
	      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	        τ0_2 (typed_lty_env_bind
	          (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty τ0_1))
	        (tapp_tm (tm_shift 0 e0) (vbvar 0)) ltac:(lia)).
      reflexivity.
  }
  intros Hgas. apply Hsat. exact Hgas.
Qed.

Lemma ty_denote_gas_insert_fresh_lty_env_eq
    gas (Σ : lty_env) τ e x T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  ty_denote_gas gas (<[LVFree x := T]> Σ) τ e =
  ty_denote_gas gas Σ τ e.
Proof.
  intros _ Hxτ Hxe.
  eapply ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ e).
  - reflexivity.
  - apply lty_env_restrict_lvars_insert_fresh.
    apply relevant_lvars_insert_fresh; assumption.
Qed.

Lemma ty_denote_gas_zero_of_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e ->
  m ⊨ ty_denote_gas 0 Σ τ e.
Proof.
  intros Hguard.
  cbn [ty_denote_gas].
  rewrite res_models_and_iff. split.
  - exact Hguard.
  - cbn [res_models res_models_fuel formula_measure].
    split; [apply formula_scoped_true_iff; exact I | exact I].
Qed.

Lemma ty_denote_gas_guard_formula
    gas (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e.
Proof.
  destruct gas; cbn [ty_denote_gas]; rewrite res_models_and_iff; tauto.
Qed.

Lemma ty_denote_gas_zero_of_guard
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  m ⊨ ty_denote_gas 0 Σ τ e.
Proof.
  intros Hguard.
  apply ty_denote_gas_zero_of_guard_formula.
  unfold ty_guard_formula. exact Hguard.
Qed.

Lemma ty_denote_gas_guard
    gas (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard_formula gas Σ τ e m Hden) as Hguard.
  unfold ty_guard_formula in Hguard. exact Hguard.
Qed.

Lemma ty_denote_gas_guard_of_zero
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_formula 0 Σ τ e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard. exact Hguard.
Qed.

Lemma ty_denote_gas_total_guard_of_zero
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  m ⊨ expr_total_formula e.
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [_ [_ Htotal]]].
  exact Htotal.
Qed.

Lemma ty_denote_gas_insert_fresh_lty_env
    gas (Σ : lty_env) τ e x T (m : WfWorldT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe Hm.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas Σ τ e x T);
    assumption.
Qed.

Lemma ty_denote_gas_extend_typed_extension
    gas (Σ : lty_env) τ e x T
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  extension_has_ltype (<[LVFree x := T]> ∅)
    (res_restrict m (ext_in Fx)) Fx ->
  res_extend_by m Fx mx ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  mx ⊨ ty_denote_gas gas (<[LVFree x := T]> Σ) τ e.
Proof.
  intros HxΣ Hxτ Hxe HFx Hext Hm.
  assert (Hmx_old : mx ⊨ ty_denote_gas gas Σ τ e).
  {
    eapply res_models_extend_mono; [exact Hext | exact Hm].
  }
  eapply ty_denote_gas_insert_fresh_lty_env; eauto.
Qed.

Lemma store_typed_restrict_fv_of_guard
    (Σ : lty_env) τ e (m : WfWorldT) σ :
  m ⊨ basic_world_formula (relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula (relevant_env Σ τ e) e
    (erase_ty τ) ->
  worldA_stores (m : WorldT) σ ->
  atom_store_has_ltype (relevant_env Σ τ e)
    (store_restrict σ (fv_tm e)).
Proof.
  intros Hworld Hbasic Hσ y u Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [Hyfv Hσy].
  apply basic_world_formula_models_iff in Hworld as [_ [_ Htyped]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  destruct Htyped as [_ Hstores].
  specialize (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])).
  assert (Hy_dom : LVFree y ∈ dom (relevant_env Σ τ e)).
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

Lemma result_ext_typed_of_guard
    (Σ : lty_env) τ e x
    (m mx : WfWorldT) (Fx : FiberExtensionT) :
  lty_env_closed Σ ->
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e x Fx ->
  res_extend_by m Fx mx ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τ e) e
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
            atom_store_has_ltype (relevant_env Σ τ e) σin).
        {
          simpl in Hσin.
          destruct Hσin as [σm [Hσm Hrestrict]].
          subst σin.
          replace (store_restrict σm (ext_in Fx))
            with (store_restrict σm (fv_tm e))
            by (rewrite Hin; reflexivity).
          eapply store_typed_restrict_fv_of_guard;
            [exact Hworld_model|exact Hbasic_model|exact Hσm].
        }
        destruct Htotal_m as [_ Htotal_eval].
        assert (Hexists_eval : exists v, tm_eval_in_store σin e v).
        {
          simpl in Hσin.
          destruct Hσin as [σm [Hσm Hrestrict]].
          subst σin.
          pose proof (Htotal_eval (lstore_lift_free σm)
            ltac:(exists σm; split; [exact Hσm|reflexivity])) as Hsn.
          destruct (must_terminating_reaches_result _ Hsn) as [v Heval].
          exists v.
          pose proof (tm_eval_in_store_restrict_fv_subset
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
	                 eapply basic_tm_eval_value_type;
	                   [|exact Hσin_typed|exact Hty_e|exact Heval_v|].
	                 --- exact Hrel_closed.
                 --- rewrite Hσin_dom. set_solver.
              ** rewrite lookup_insert_ne in HΣout by congruence.
                 rewrite lookup_empty in HΣout. discriminate.
Qed.

Lemma ret_fvar_typing_of_lookup
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
	    pose proof (steps_regular2 _ _ Heval) as Hret_lc.
	    apply lc_ret_iff_value in Hret_lc as Hv_lc.
	    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value)
	      !! LVFree x = Some v) in Hx_lookup.
	    rewrite lstore_lift_free_lookup_free in Hx_lookup.
	    cbn [lstore_instantiate_tm lstore_instantiate_tm_at
	      lstore_instantiate_tm_split_at
	      lstore_instantiate_value_at lstore_instantiate_value_split_at
	      lstore_free_part].
	    rewrite lstore_free_part_lift_free.
	    change (must_terminating
	      (tret
	        (match ((σ : StoreT) : gmap atom value) !! x with
	         | Some u => u
	         | None => vfvar x
	         end))).
	    rewrite Hx_lookup.
	    apply must_terminating_tret. exact Hv_lc.
Qed.

Lemma expr_total_formula_tret_of_basic
    Σ v T (m : WfWorldT) :
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ (tret v) T ->
  m ⊨ expr_total_formula (tret v).
Proof.
  intros Hworld Hbasic.
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars Σ (tret v) T Hty) as HfvΣ.
  assert (HfvΣ_value : lvars_of_atoms (fv_value v) ⊆ dom Σ).
  { cbn [fv_tm] in HfvΣ. exact HfvΣ. }
  pose proof (basic_tm_has_ltype_lc Σ (tret v) T HlcΣ Hty) as Hlc_tm.
  assert (Hlc : lc_value v).
  { inversion Hlc_tm; subst; assumption. }
  pose proof (basic_world_formula_models_iff Σ m) as Hworld_iff.
  destruct (proj1 Hworld_iff Hworld) as [_ [Hworld_dom _]].
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on.
  split.
  - rewrite (tm_lvars_lc_eq_atoms (tret v)) by exact Hlc_tm.
    rewrite res_lift_free_dom.
    intros z Hz.
    apply elem_of_map in Hz as [a [-> Ha]].
    apply elem_of_map.
    exists a. split; [reflexivity|].
    apply Hworld_dom.
    apply lvars_fv_elem.
    apply HfvΣ.
    apply elem_of_map.
    exists a. split; [reflexivity|exact Ha].
	  - intros τ Hτ.
	    destruct Hτ as [σ [Hσ ->]].
	    set (X := fv_value v).
	    assert (Hagree :
	      store_restrict σ (fv_tm (tret v)) =
	      store_restrict (store_restrict σ X) (fv_tm (tret v))).
	    {
	      subst X. cbn [fv_tm].
	      symmetry. apply storeA_restrict_twice_same.
	    }
	    apply (proj2 (tm_must_terminating_agree_on_fv
	      σ (store_restrict σ X) (tret v) Hlc_tm Hagree)).
	    rewrite lstore_instantiate_tm_no_bvars.
	    2:{ apply lc_lstore_lift_free. }
	    2:{
	      rewrite lstore_free_part_lift_free.
	      subst X.
      pose proof (basic_world_formula_wfworld_closed_on_atoms
        Σ (fv_value v) m HfvΣ_value Hworld σ Hσ) as Hclosed.
      exact (proj1 Hclosed).
	    }
	    rewrite lstore_free_part_lift_free.
	    replace (subst_map (store_restrict σ X) (tret v))
	      with (tret (subst_map (store_restrict σ X) v))
	      by (symmetry; apply msubst_ret).
	    apply must_terminating_tret.
	    apply msubst_lc.
	    + subst X.
	      pose proof (basic_world_formula_wfworld_closed_on_atoms
	        Σ (fv_value v) m HfvΣ_value Hworld σ Hσ) as Hclosed.
      exact (proj2 Hclosed).
    + exact Hlc.
Qed.

Lemma basic_world_formula_result_alias_target
    (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ basic_world_formula (relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula (relevant_env Σ τ e) e
    (erase_ty τ) ->
  m ⊨ basic_world_formula (relevant_env Σ τ (tret (vfvar x))).
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
  - apply relevant_env_closed. exact HΣclosed.
  - split.
    + intros a Ha.
      apply lvars_fv_elem in Ha.
      unfold relevant_env, lty_env_restrict_lvars in Ha.
      rewrite storeA_restrict_dom in Ha.
      apply elem_of_intersection in Ha as [HaΣ Ha_rel].
      unfold relevant_lvars in Ha_rel.
      cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at] in Ha_rel.
      apply elem_of_union in Ha_rel as [Haτ|Hax].
      * apply Hscope_src. apply lvars_fv_elem.
        unfold relevant_env, lty_env_restrict_lvars.
        rewrite storeA_restrict_dom.
        apply elem_of_intersection. split.
        -- exact HaΣ.
        -- unfold relevant_lvars. set_solver.
      * apply elem_of_singleton in Hax. inversion Hax. subst a.
        specialize (Hres_dom (LVFree x) ltac:(set_solver)).
        rewrite res_lift_free_dom in Hres_dom.
        unfold lvars_of_atoms in Hres_dom.
        apply elem_of_map in Hres_dom as [a [Heq Ha]].
        inversion Heq. subst a. exact Ha.
    + unfold lworld_has_type, worldA_has_type in Htyped_src |- *.
      split.
      * intros z Hz.
        unfold relevant_env, lty_env_restrict_lvars in Hz.
        rewrite storeA_restrict_dom in Hz.
        apply elem_of_intersection in Hz as [HzΣ Hz_rel].
        unfold relevant_lvars in Hz_rel.
        cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at] in Hz_rel.
        apply elem_of_union in Hz_rel as [Hzτ|Hzx].
        -- destruct Htyped_src as [Hdom_src _].
           apply Hdom_src.
           unfold relevant_env, lty_env_restrict_lvars.
           rewrite storeA_restrict_dom.
           apply elem_of_intersection. split; [exact HzΣ|].
           unfold relevant_lvars. set_solver.
        -- apply elem_of_singleton in Hzx. subst z.
           apply Hres_dom. set_solver.
      * intros σl Hσl z T v Htarget_z Hσl_z.
        unfold relevant_env, lty_env_restrict_lvars in Htarget_z.
        apply storeA_restrict_lookup_some in Htarget_z
          as [Hz_target HΣ_z].
        destruct (decide (z ∈ relevant_lvars τ e)) as [Hz_source|Hz_not_source].
        -- destruct Htyped_src as [_ Hstores_src].
           specialize (Hstores_src σl Hσl).
           eapply Hstores_src.
           ++ apply storeA_restrict_lookup_some_2; [exact HΣ_z|exact Hz_source].
           ++ exact Hσl_z.
        -- assert (Hz_x : z = LVFree x).
           {
             unfold relevant_lvars in Hz_target, Hz_not_source.
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
               atom_store_has_ltype (relevant_env Σ τ e)
                 (store_restrict σ (fv_tm e))).
           {
             eapply store_typed_restrict_fv_of_guard;
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
           change (tm_eval_in_store σ e v) in Heval.
           assert (Heval_restrict :
               tm_eval_in_store (store_restrict σ (fv_tm e)) e v).
           {
             apply (proj2 (tm_eval_in_store_restrict_fv_subset
               σ e v (fv_tm e) ltac:(set_solver))).
             exact Heval.
           }
           eapply basic_tm_eval_value_type;
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

Lemma ty_denote_gas_result_alias_guard
    (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τ (tret (vfvar x))) τ)
    (FAnd
      (basic_world_formula (relevant_env Σ τ (tret (vfvar x))))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τ (tret (vfvar x)))
          (tret (vfvar x)) (erase_ty τ))
        (expr_total_formula (tret (vfvar x))))).
Proof.
  intros HΣclosed HΣx Hres Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (basic_world_formula_result_alias_target
    Σ τ e x m HΣclosed HΣx Hres Hworld Hbasic) as Hworld_target.
  pose proof Hworld_target as Hworld_target_parts.
  apply basic_world_formula_models_iff in Hworld_target_parts
    as [Hlc_target [Hscope_target Htyped_target]].
  pose proof (context_ty_wf_formula_relevant_env_change_term
    Σ τ e (tret (vfvar x)) m Hworld_target Hwf) as Hwf_target.
  assert (Hlookup_target :
      relevant_env Σ τ (tret (vfvar x)) !! LVFree x =
      Some (erase_ty τ)).
  {
    unfold relevant_env, lty_env_restrict_lvars.
    assert (Hin :
        LVFree x ∈ relevant_lvars τ (tret (vfvar x))).
    {
      unfold relevant_lvars.
      cbn [tm_lvars tm_lvars_at value_lvars value_lvars_at].
      set_solver.
    }
    better_store_solver.
  }
  repeat rewrite res_models_and_iff.
  split.
  - exact Hwf_target.
  - split.
    + apply basic_world_formula_models_iff.
      split; [exact Hlc_target|].
      split; [exact Hscope_target|exact Htyped_target].
    + split.
      * eapply ret_fvar_typing_of_lookup; eauto.
      * eapply expr_total_formula_ret_fvar_from_result. exact Hres.
Qed.

Definition tm_equiv_on
    (m : WfWorldT) (e1 e2 : tm) : Prop :=
  forall σ v,
    worldA_stores (m : WorldT) σ ->
    tm_eval_in_store σ e1 v <->
    tm_eval_in_store σ e2 v.

Definition tm_total_equiv_on
    (m : WfWorldT) (e1 e2 : tm) : Prop :=
  forall σ,
    worldA_stores (m : WorldT) σ ->
    must_terminating
      (lstore_instantiate_tm (lstore_lift_free σ) e1) <->
    must_terminating
      (lstore_instantiate_tm (lstore_lift_free σ) e2).

Definition typed_total_equiv_on
    (Σ : lty_env) (τ : context_ty) (m : WfWorldT)
    (e1 e2 : tm) : Prop :=
  tm_equiv_on m e1 e2 /\
  tm_total_equiv_on m e1 e2 /\
  m ⊨ ty_denote_gas 0 Σ τ e1 /\
  m ⊨ ty_denote_gas 0 Σ τ e2.

Lemma tm_total_equiv_of_total_formulas
    (m : WfWorldT) e1 e2 :
  m ⊨ expr_total_formula e1 ->
  m ⊨ expr_total_formula e2 ->
  tm_total_equiv_on m e1 e2.
Proof.
  intros Htotal1 Htotal2 σ Hσ.
  apply expr_total_formula_to_atom_world in Htotal1.
  apply expr_total_formula_to_atom_world in Htotal2.
  destruct Htotal1 as [_ Hstores1].
  destruct Htotal2 as [_ Hstores2].
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  split; intros _.
  - exact (Hstores2 (lstore_lift_free σ) Hlift).
  - exact (Hstores1 (lstore_lift_free σ) Hlift).
Qed.

Lemma tm_total_equiv_of_tm_equiv_left_total
    (m : WfWorldT) e1 e2 :
  tm_equiv_on m e1 e2 ->
  m ⊨ expr_total_formula e1 ->
  tm_total_equiv_on m e1 e2.
Proof.
  intros Heq Htotal1 σ Hσ.
  apply expr_total_formula_to_atom_world in Htotal1.
  destruct Htotal1 as [_ Hstores1].
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  specialize (Hstores1 (lstore_lift_free σ) Hlift) as Htotal1σ.
  split.
  - intros _.
    destruct (must_terminating_reaches_result _ Htotal1σ) as [v Heval1].
    eapply must_terminating_of_steps_result.
    apply (proj1 (Heq σ v Hσ)). exact Heval1.
  - intros _. exact Htotal1σ.
Qed.

Lemma tm_equiv_tlete_body_extension
    e1 e2 x Fx m mx :
  lc_tm (tlete e1 e2) ->
  wfworld_closed_on (fv_tm (tlete e1 e2)) mx ->
  mx ⊨ expr_total_formula (tlete e1 e2) ->
  x ∉ fv_tm e2 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  tm_equiv_on mx (e2 ^^ x) (tlete e1 e2).
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
        tm_eval_in_store (store_restrict σ (fv_tm e1)) e1 vx ->
        σ !! x = Some vx).
  {
    intros vx He1σ.
    eapply result_extension_store_lookup_output; eauto.
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
	    pose proof (Htotal_stores (lstore_lift_free σ)
	      ltac:(exists σ; split; [exact Hσmx|reflexivity])) as Hsn_tlet.
	    destruct (must_terminating_reaches_result _ Hsn_tlet) as [v0 Htlet0].
    destruct (tm_eval_in_store_tlete_elim_closed_on
      e1 e2 y σ v0 (Hclosed σ Hσmx) Hylet Hye2 Htlet0)
      as [vx [He1σ _]].
    pose proof (Hstore_result vx He1σ) as Hx_lookup.
    eapply tm_eval_in_store_tlete_intro_closed_on with (x := y) (vx := vx).
    + exact (Hclosed σ Hσmx).
    + exact Hlc.
    + set_solver.
    + apply (proj1 (tm_eval_in_store_agree_on_fv
        (store_restrict σ (fv_tm e1))
        (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx
        ltac:(
          rewrite storeA_restrict_twice_same;
          rewrite storeA_restrict_twice_subset by (cbn [fv_tm]; set_solver);
          reflexivity))).
      exact He1σ.
    + apply (proj1 (tm_eval_in_store_agree_on_fv
        (<[y := vx]> σ)
        (<[y := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ y) v (Hinsert_restrict_y y vx Hyσ Hylet))).
      apply (proj1 (tm_eval_in_store_open_alias
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
    destruct (tm_eval_in_store_tlete_elim_closed_on
      e1 e2 y σ v (Hclosed σ Hσmx) Hylet Hye2 Hlet)
      as [vx [He1σ Hbody_y]].
    pose proof (Hstore_result vx He1σ) as Hx_lookup.
    apply (proj2 (tm_eval_in_store_open_alias
      e2 σ x y vx v Hx_lookup Hyσ Hx_e2 Hye2 Hscope_body)).
    apply (proj2 (tm_eval_in_store_agree_on_fv
        (<[y := vx]> σ)
        (<[y := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ y) v (Hinsert_restrict_y y vx Hyσ Hylet))).
    exact Hbody_y.
Qed.

Lemma tm_equiv_lam_app_body
    T e y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)) m ->
  body_tm e ->
  y ∉ fv_tm e ->
  y ∈ world_dom (m : WorldT) ->
  tm_equiv_on m
    (tapp_tm (tret (vlam T e)) (vfvar y))
    (e ^^ y).
Proof.
  intros Hclosed Hbody Hy_fresh Hy_dom σ v Hσ.
  set (X := fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ∪ fv_tm (e ^^ y)).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. apply Hclosed. exact Hσ. }
  assert (Hfv_app : fv_tm (tapp_tm (tret (vlam T e)) (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_body : fv_tm (e ^^ y) ⊆ X)
    by (subst X; set_solver).
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  assert (Hyσ : y ∈ dom (σ : StoreT)).
  { rewrite <- Hσdom in Hy_dom. exact Hy_dom. }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{ apply not_elem_of_dom in Hσy. set_solver. }
  assert (HyX : y ∈ X).
  {
    subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    set_solver.
  }
  assert (HσXy : store_restrict σ X !! y = Some vy).
  { apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyX]. }
  split.
  - intros Happ.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset σ (e ^^ y) v X Hfv_body)).
    apply (proj1 (tm_eval_in_store_tapp_tm_lam_body
      (store_restrict σ X) T e y vy v HσX_closed Hbody Hy_fresh HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vlam T e)) (vfvar y)) v X Hfv_app)).
    exact Happ.
  - intros Hbody_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vlam T e)) (vfvar y)) v X Hfv_app)).
    apply (proj2 (tm_eval_in_store_tapp_tm_lam_body
      (store_restrict σ X) T e y vy v HσX_closed Hbody Hy_fresh HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (e ^^ y) v X Hfv_body)).
    exact Hbody_eval.
Qed.

Lemma tm_equiv_fix_unfold
    Tf vf y (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))) m ->
  body_val vf ->
  y ∈ world_dom (m : WorldT) ->
  tm_equiv_on m
    (tapp_tm (tret (vfix Tf vf)) (vfvar y))
    (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf)).
Proof.
  intros Hclosed Hbody Hy_dom σ v Hσ.
  set (X := fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ∪
            fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
              (vfix Tf vf))).
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { subst X. apply Hclosed. exact Hσ. }
  assert (Hfv_src :
      fv_tm (tapp_tm (tret (vfix Tf vf)) (vfvar y)) ⊆ X)
    by (subst X; better_set_solver).
  assert (Hfv_tgt :
      fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
        (vfix Tf vf)) ⊆ X)
    by (subst X; better_set_solver).
  pose proof (wfworld_store_dom m σ Hσ) as Hσdom.
  assert (Hyσ : y ∈ dom (σ : StoreT)).
  { rewrite <- Hσdom in Hy_dom. exact Hy_dom. }
  destruct (σ !! y) as [vy|] eqn:Hσy.
  2:{ apply not_elem_of_dom in Hσy. set_solver. }
  assert (HyX : y ∈ X).
  {
    subst X. unfold tapp_tm. cbn [fv_tm fv_value].
    better_set_solver.
  }
  assert (HσXy : store_restrict σ X !! y = Some vy).
  { apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyX]. }
  split.
  - intros Hsrc.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))
      v X Hfv_tgt)).
    apply (proj1 (tm_eval_in_store_tapp_tm_fix_unfold
      (store_restrict σ X) Tf vf y vy v HσX_closed Hbody HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vfix Tf vf)) (vfvar y)) v X Hfv_src)).
    exact Hsrc.
  - intros Htgt.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (vfix Tf vf)) (vfvar y)) v X Hfv_src)).
    apply (proj2 (tm_eval_in_store_tapp_tm_fix_unfold
      (store_restrict σ X) Tf vf y vy v HσX_closed Hbody HσXy)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm (tret (open_value 0 (vfvar y) vf)) (vfix Tf vf))
      v X Hfv_tgt)).
    exact Htgt.
Qed.

Lemma typed_total_equiv_source_zero
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1.
Proof. intros [_ [_ [Hzero _]]]. exact Hzero. Qed.

Lemma typed_total_equiv_target_zero
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e2.
Proof. intros [_ [_ [_ Hzero]]]. exact Hzero. Qed.

Lemma typed_total_equiv_tm_equiv
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  tm_equiv_on m e1 e2.
Proof. intros [Heq _]. exact Heq. Qed.

Lemma typed_total_equiv_total_equiv
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  tm_total_equiv_on m e1 e2.
Proof. intros [_ [Htotal _]]. exact Htotal. Qed.

Lemma tm_equiv_res_store_subset
    (m0 m : WfWorldT) e1 e2 :
  res_subset m0 m ->
  tm_equiv_on m e1 e2 ->
  tm_equiv_on m0 e1 e2.
Proof.
  intros [_ Hstores] Heq σ v Hσ.
  apply Heq. exact (Hstores σ Hσ).
Qed.

Lemma tm_total_equiv_res_store_subset
    (m0 m : WfWorldT) e1 e2 :
  res_subset m0 m ->
  tm_total_equiv_on m e1 e2 ->
  tm_total_equiv_on m0 e1 e2.
Proof.
  intros [_ Hstores] Htotal σ Hσ.
  apply Htotal. exact (Hstores σ Hσ).
Qed.

Lemma tm_equiv_res_product_right
    (n my : WfWorldT) (Hc : world_compat n my) e1 e2 :
  tm_equiv_on my e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT) ->
  tm_equiv_on (res_product n my Hc) e1 e2.
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
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (my : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (my : WorldT)) Hfv1)).
    exact Heval1.
  - intros Heval2.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (my : WorldT)) Hfv1)).
    apply Heq21.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (my : WorldT)) Hfv2)).
    exact Heval2.
Qed.

Lemma tm_total_equiv_res_product_right
    (n my : WfWorldT) (Hc : world_compat n my) e1 e2 :
  tm_total_equiv_on my e1 e2 ->
  lc_tm e1 ->
  lc_tm e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT) ->
  tm_total_equiv_on (res_product n my Hc) e1 e2.
Proof.
  intros Htotal Hlc1 Hlc2 Hfv σ Hσ.
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
  specialize (Htotal (store_restrict σ (world_dom (my : WorldT))) Hσmy)
    as [Htotal12 Htotal21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (my : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (my : WorldT)) by set_solver.
  assert (Hagree1 :
    store_restrict (store_restrict σ (world_dom (my : WorldT))) (fv_tm e1) =
    store_restrict σ (fv_tm e1)).
  { rewrite storeA_restrict_twice_subset by exact Hfv1. reflexivity. }
  assert (Hagree2 :
    store_restrict (store_restrict σ (world_dom (my : WorldT))) (fv_tm e2) =
    store_restrict σ (fv_tm e2)).
  { rewrite storeA_restrict_twice_subset by exact Hfv2. reflexivity. }
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e2 Hlc2 Hagree2)).
    apply Htotal12.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e1 Hlc1 Hagree1)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e1 Hlc1 Hagree1)).
    apply Htotal21.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (my : WorldT))) σ e2 Hlc2 Hagree2)).
    exact Hsn.
Qed.

Lemma tm_total_equiv_full_world_extend_fresh
    (m my : WfWorldT) y e1 e2 :
  tm_total_equiv_on m e1 e2 ->
  lc_tm e1 ->
  lc_tm e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT) ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  tm_total_equiv_on my e1 e2.
Proof.
  intros Htotal Hlc1 Hlc2 Hfv _ _ Hrestrict σ Hσ.
  assert (Hσm :
      (m : WorldT) (store_restrict σ (world_dom (m : WorldT)))).
  {
    assert (Hσr :
        (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ (world_dom (m : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hrestrict in Hσr. exact Hσr.
  }
  specialize (Htotal (store_restrict σ (world_dom (m : WorldT))) Hσm)
    as [Htotal12 Htotal21].
  assert (Hfv1 : fv_tm e1 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hfv2 : fv_tm e2 ⊆ world_dom (m : WorldT)) by set_solver.
  assert (Hagree1 :
    store_restrict (store_restrict σ (world_dom (m : WorldT))) (fv_tm e1) =
    store_restrict σ (fv_tm e1)).
  { rewrite storeA_restrict_twice_subset by exact Hfv1. reflexivity. }
  assert (Hagree2 :
    store_restrict (store_restrict σ (world_dom (m : WorldT))) (fv_tm e2) =
    store_restrict σ (fv_tm e2)).
  { rewrite storeA_restrict_twice_subset by exact Hfv2. reflexivity. }
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e2 Hlc2 Hagree2)).
    apply Htotal12.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e1 Hlc1 Hagree1)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e1 Hlc1 Hagree1)).
    apply Htotal21.
    apply (proj2 (tm_must_terminating_agree_on_fv
      (store_restrict σ (world_dom (m : WorldT))) σ e2 Hlc2 Hagree2)).
    exact Hsn.
Qed.

Lemma tm_equiv_total
    m e1 e2 :
  tm_total_equiv_on m e1 e2 ->
  lc_tm e2 ->
  fv_tm e2 ⊆ world_dom (m : WorldT) ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ expr_total_formula e2.
Proof.
  intros Htotal_equiv Hlc2 Hfv2 Htotal.
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
    apply (proj1 (Htotal_equiv σ Hσ)).
    apply Hstores. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma tm_equiv_tapp_fvar
    (m : WfWorldT) e1 e2 y :
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y))) m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_equiv_on m e1 e2 ->
  tm_equiv_on m
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
	      tm_eval_in_store (store_restrict σ X) e1 vf <->
	      tm_eval_in_store (store_restrict σ X) e2 vf).
	  {
	    intros vf. split; intros Heval_fun.
	    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ e2 vf X Hfv_e2)).
	      apply (proj1 (Heq σ vf Hσ)).
	      apply (proj1 (tm_eval_in_store_restrict_fv_subset
	        σ e1 vf X Hfv_e1)).
	      exact Heval_fun.
	    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ e1 vf X Hfv_e1)).
	      apply (proj2 (Heq σ vf Hσ)).
	      apply (proj1 (tm_eval_in_store_restrict_fv_subset
	        σ e2 vf X Hfv_e2)).
	      exact Heval_fun.
	  }
	  pose proof (tm_eval_in_store_tapp_tm_fun_equiv
	    (store_restrict σ X) e1 e2 y v HσX_closed Hlc1 Hlc2
	    Hfun_equiv) as [Happ12 Happ21].
	  split.
	  - intros Heval.
	    apply (proj1 (tm_eval_in_store_restrict_fv_subset
	      σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
	    apply Happ12.
	    apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
	    exact Heval.
	  - intros Heval.
	    apply (proj1 (tm_eval_in_store_restrict_fv_subset
	      σ (tapp_tm e1 (vfvar y)) v X Hfv_app1)).
	    apply Happ21.
	    apply (proj2 (tm_eval_in_store_restrict_fv_subset
	        σ (tapp_tm e2 (vfvar y)) v X Hfv_app2)).
      exact Heval.
Qed.

Lemma tm_total_equiv_tapp_fvar
    (m : WfWorldT) e1 e2 y :
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪ fv_tm (tapp_tm e2 (vfvar y))) m ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_equiv_on m e1 e2 ->
  tm_total_equiv_on m e1 e2 ->
  tm_total_equiv_on m
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hclosed Hlc1 Hlc2 Heq Htotal σ Hσ.
  set (X := fv_tm (tapp_tm e1 (vfvar y)) ∪
            fv_tm (tapp_tm e2 (vfvar y))).
  set (σX := store_restrict σ X : StoreT).
  assert (HσX_closed : store_closed σX).
  { subst σX X. apply Hclosed. exact Hσ. }
  assert (Hfv_app1 : fv_tm (tapp_tm e1 (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_app2 : fv_tm (tapp_tm e2 (vfvar y)) ⊆ X)
    by (subst X; set_solver).
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
      tm_eval_in_store σX e1 vf <->
      tm_eval_in_store σX e2 vf).
  {
    intros vf. split; intros Heval_fun.
    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ e2 vf X Hfv_e2)).
      apply (proj1 (Heq σ vf Hσ)).
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σ e1 vf X Hfv_e1)).
      subst σX. exact Heval_fun.
    - apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σ e1 vf X Hfv_e1)).
      apply (proj2 (Heq σ vf Hσ)).
      apply (proj1 (tm_eval_in_store_restrict_fv_subset
        σ e2 vf X Hfv_e2)).
      subst σX. exact Heval_fun.
  }
  assert (Hfun_total :
      must_terminating (lstore_instantiate_tm (lstore_lift_free σX) e1) <->
      must_terminating (lstore_instantiate_tm (lstore_lift_free σX) e2)).
  {
    specialize (Htotal σ Hσ) as [Htotal12 Htotal21].
    assert (Hagree1 : store_restrict σX (fv_tm e1) =
      store_restrict σ (fv_tm e1)).
    { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_e1.
      reflexivity. }
    assert (Hagree2 : store_restrict σX (fv_tm e2) =
      store_restrict σ (fv_tm e2)).
    { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_e2.
      reflexivity. }
    split; intros Hsn.
    - apply (proj2 (tm_must_terminating_agree_on_fv
        σX σ e2 Hlc2 Hagree2)).
      apply Htotal12.
      apply (proj1 (tm_must_terminating_agree_on_fv
        σX σ e1 Hlc1 Hagree1)).
      exact Hsn.
    - apply (proj2 (tm_must_terminating_agree_on_fv
        σX σ e1 Hlc1 Hagree1)).
      apply Htotal21.
      apply (proj1 (tm_must_terminating_agree_on_fv
        σX σ e2 Hlc2 Hagree2)).
      exact Hsn.
  }
  assert (HappsX :
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm e1 (vfvar y))) <->
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm e2 (vfvar y)))).
  {
    unfold tm_eval_in_store, expr_eval_in_store in Hfun_equiv.
    rewrite !lstore_instantiate_tm_no_bvars in Hfun_equiv by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free in Hfun_equiv.
    rewrite !lstore_instantiate_tm_no_bvars in Hfun_total by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free in Hfun_total.
    rewrite !lstore_instantiate_tm_no_bvars by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite !msubst_tapp_tm_lc_arg by
      (constructor || exact (proj2 HσX_closed)).
    eapply must_terminating_tapp_tm_fun_equiv.
    - change (lc_tm (m{σX} e1)).
      apply msubst_lc; [exact (proj2 HσX_closed)|exact Hlc1].
    - change (lc_tm (m{σX} e2)).
      apply msubst_lc; [exact (proj2 HσX_closed)|exact Hlc2].
    - change (lc_value (m{σX} (vfvar y))).
      apply msubst_lc; [exact (proj2 HσX_closed)|constructor].
    - exact Hfun_equiv.
    - exact Hfun_total.
  }
  assert (Hagree_app1 : store_restrict σX (fv_tm (tapp_tm e1 (vfvar y))) =
    store_restrict σ (fv_tm (tapp_tm e1 (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_app1.
    reflexivity. }
  assert (Hagree_app2 : store_restrict σX (fv_tm (tapp_tm e2 (vfvar y))) =
    store_restrict σ (fv_tm (tapp_tm e2 (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_app2.
    reflexivity. }
  pose proof (lc_tapp_tm e1 (vfvar y) Hlc1 ltac:(constructor)) as Hlc_app1.
  pose proof (lc_tapp_tm e2 (vfvar y) Hlc2 ltac:(constructor)) as Hlc_app2.
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e2 (vfvar y)) Hlc_app2 Hagree_app2)).
    apply (proj1 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e1 (vfvar y)) Hlc_app1 Hagree_app1)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e1 (vfvar y)) Hlc_app1 Hagree_app1)).
    apply (proj2 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm e2 (vfvar y)) Hlc_app2 Hagree_app2)).
    exact Hsn.
Qed.

Lemma tm_total_equiv_tapp_tm_ret
    (m : WfWorldT) vf y :
  wfworld_closed_on
    (fv_tm (tapp_tm (tret vf) (vfvar y)) ∪
     fv_tm (tapp vf (vfvar y))) m ->
  lc_value vf ->
  tm_total_equiv_on m
    (tapp_tm (tret vf) (vfvar y))
    (tapp vf (vfvar y)).
Proof.
  intros Hclosed Hvf σ Hσ.
  set (X := fv_tm (tapp_tm (tret vf) (vfvar y)) ∪
            fv_tm (tapp vf (vfvar y))).
  set (σX := store_restrict σ X : StoreT).
  assert (HσX_closed : store_closed σX).
  { subst σX X. apply Hclosed. exact Hσ. }
  assert (Hfv_src : fv_tm (tapp_tm (tret vf) (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (Hfv_tgt : fv_tm (tapp vf (vfvar y)) ⊆ X)
    by (subst X; set_solver).
  assert (HappsX :
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp_tm (tret vf) (vfvar y))) <->
      must_terminating
        (lstore_instantiate_tm (lstore_lift_free σX)
          (tapp vf (vfvar y)))).
  {
    rewrite !lstore_instantiate_tm_no_bvars by
      (try apply lc_lstore_lift_free;
       rewrite ?lstore_free_part_lift_free; exact (proj1 HσX_closed)).
    rewrite !lstore_free_part_lift_free.
    rewrite !subst_map_tm_eq_msubst.
    rewrite msubst_tapp_tm_lc_arg by
      (constructor || exact (proj2 HσX_closed)).
    rewrite msubst_tapp, msubst_ret.
    eapply must_terminating_tapp_tm_ret_equiv.
    - change (lc_value (m{σX} vf)).
      apply msubst_lc; [exact (proj2 HσX_closed)|exact Hvf].
    - change (lc_value (m{σX} (vfvar y))).
      apply msubst_lc; [exact (proj2 HσX_closed)|constructor].
  }
  assert (Hagree_src : store_restrict σX
      (fv_tm (tapp_tm (tret vf) (vfvar y))) =
    store_restrict σ (fv_tm (tapp_tm (tret vf) (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_src.
    reflexivity. }
  assert (Hagree_tgt : store_restrict σX (fv_tm (tapp vf (vfvar y))) =
    store_restrict σ (fv_tm (tapp vf (vfvar y)))).
  { subst σX. rewrite storeA_restrict_twice_subset by exact Hfv_tgt.
    reflexivity. }
  pose proof (lc_tapp_tm (tret vf) (vfvar y)
    ltac:(constructor; exact Hvf) ltac:(constructor)) as Hlc_src.
  assert (Hlc_tgt : lc_tm (tapp vf (vfvar y))).
  { constructor; [exact Hvf|constructor]. }
  split; intros Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp vf (vfvar y)) Hlc_tgt Hagree_tgt)).
    apply (proj1 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret vf) (vfvar y)) Hlc_src Hagree_src)).
    exact Hsn.
  - apply (proj1 (tm_must_terminating_agree_on_fv
      σX σ (tapp_tm (tret vf) (vfvar y)) Hlc_src Hagree_src)).
    apply (proj2 HappsX).
    apply (proj2 (tm_must_terminating_agree_on_fv
      σX σ (tapp vf (vfvar y)) Hlc_tgt Hagree_tgt)).
    exact Hsn.
Qed.

Lemma tm_equiv_tapp_value_arg_eq_on
    (m : WfWorldT) X e vx1 vx2 :
  fv_tm (tapp_tm e vx1) ∪ fv_tm (tapp_tm e vx2) ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx1 ->
  lc_value vx2 ->
  (forall σ,
    (m : WorldT) σ ->
    m{store_restrict σ X} vx1 = m{store_restrict σ X} vx2) ->
  tm_equiv_on m (tapp_tm e vx1) (tapp_tm e vx2).
Proof.
  intros HfvX Hclosed Hvx1 Hvx2 Heq σ v Hσ.
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (Hclosed σ Hσ). }
  assert (Hfv_app1 : fv_tm (tapp_tm e vx1) ⊆ X) by better_set_solver.
  assert (Hfv_app2 : fv_tm (tapp_tm e vx2) ⊆ X) by better_set_solver.
  pose proof (tm_eval_in_store_tapp_tm_arg_eq
    (store_restrict σ X) e vx1 vx2 v
    HσX_closed Hvx1 Hvx2 (Heq σ Hσ)) as Hequiv.
  split.
  - intros Heval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx2) v X Hfv_app2)).
    apply (proj1 Hequiv).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx1) v X Hfv_app1)).
    exact Heval.
  - intros Heval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx1) v X Hfv_app1)).
    apply (proj2 Hequiv).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tapp_tm e vx2) v X Hfv_app2)).
    exact Heval.
Qed.

Lemma expr_result_formula_ret_value_inst_eq_on
    (m : WfWorldT) X vx z :
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  forall σ,
    (m : WorldT) σ ->
    m{store_restrict σ X} (vfvar z) =
    m{store_restrict σ X} vx.
Proof.
  intros HzX Hfvx Hclosed Hvx Hres σ Hσ.
  pose proof (expr_result_formula_to_atom_world
    (tret vx) (LVFree z) m Hres) as Hres_world.
  destruct Hres_world as [_ [_ Hstores]].
  specialize (Hstores (lstore_lift_free σ)).
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  destruct (Hstores Hlift) as [_ [vz [Hz_lookup Heval_full]]].
  assert (HclosedX : store_closed (store_restrict σ X)).
  { exact (Hclosed σ Hσ). }
  assert (Hz_lookup_restrict :
      (store_restrict σ X : StoreT) !! z = Some vz).
  {
    apply storeA_restrict_lookup_some_2; [|exact HzX].
    change (((lstore_lift_free σ : LStoreT) : gmap logic_var value) !!
      LVFree z = Some vz) in Hz_lookup.
    rewrite lstore_lift_free_lookup_free in Hz_lookup.
    exact Hz_lookup.
  }
  assert (Heval_restrict :
      tm_eval_in_store (store_restrict σ X) (tret vx) vz).
  {
    pose proof (tm_eval_in_store_restrict_fv_subset
      σ (tret vx) vz X ltac:(cbn [fv_tm]; exact Hfvx)) as Hiff.
    apply (proj2 Hiff). exact Heval_full.
  }
  pose proof (tm_eval_in_store_ret_value_inv
    (store_restrict σ X) vx vz HclosedX Hvx Heval_restrict)
    as Hvz.
  rewrite (msubst_fvar_lookup_closed
    (store_restrict σ X) z vz)
    by (exact (proj1 HclosedX) || exact Hz_lookup_restrict).
  exact Hvz.
Qed.

Lemma tm_equiv_tapp_value_arg_result_alias_on
    (m : WfWorldT) X e vx z :
  fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx) ⊆ X ->
  z ∈ X ->
  fv_value vx ⊆ X ->
  wfworld_closed_on X m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_equiv_on m (tapp_tm e (vfvar z)) (tapp_tm e vx).
Proof.
  intros HfvX HzX Hfvx Hclosed Hvx Hres.
  assert (Heq :
      forall σ,
        (m : WorldT) σ ->
        m{store_restrict σ X} (vfvar z) =
        m{store_restrict σ X} vx).
  { eapply expr_result_formula_ret_value_inst_eq_on; eauto. }
  exact (tm_equiv_tapp_value_arg_eq_on
    m X e (vfvar z) vx HfvX Hclosed ltac:(constructor) Hvx Heq).
Qed.

Lemma tm_equiv_tapp_value_arg_result_alias
    (m : WfWorldT) e vx z :
  wfworld_closed_on
    (fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx)) m ->
  lc_value vx ->
  m ⊨ expr_result_formula (tret vx) (LVFree z) ->
  tm_equiv_on m (tapp_tm e (vfvar z)) (tapp_tm e vx).
Proof.
  intros Hclosed Hvx Hres.
  eapply (tm_equiv_tapp_value_arg_result_alias_on
    m (fv_tm (tapp_tm e (vfvar z)) ∪ fv_tm (tapp_tm e vx)) e vx z).
  - intros a Ha. exact Ha.
  - apply elem_of_union_l.
    rewrite fv_tapp_tm.
    cbn [fv_tm fv_value].
    apply elem_of_union_r.
    apply elem_of_singleton_2. reflexivity.
  - intros a Ha.
    apply elem_of_union_r.
    rewrite fv_tapp_tm.
    cbn [fv_tm].
    apply elem_of_union_r. exact Ha.
  - exact Hclosed.
  - exact Hvx.
  - exact Hres.
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
    cbn [open_one open_tm_atom_inst open_tm].
    assert (Hshift_lc : lc_value (value_shift 0 vx)).
    { rewrite value_shift_lc_id by exact Hlc_vx. exact Hlc_vx. }
    rewrite (open_rec_lc_value (value_shift 0 vx) Hshift_lc 0 (vfvar z)).
    rewrite value_shift_lc_id by exact Hlc_vx.
    eapply BTT_App.
    + eapply BVT_FVar.
      apply lty_env_open_one_typed_bind_lookup_current.
    + eapply basic_value_has_ltype_weaken; [exact Hvx|].
      apply map_subseteq_spec. intros v U Hlook.
      destruct v as [n|a].
      * exfalso.
        assert (LVBound n ∈ dom Σ) as Hdom.
        { eapply elem_of_dom_2. exact Hlook. }
        exact (HlcΣ (LVBound n) Hdom).
      * rewrite lty_env_open_one_typed_bind_lookup_free_ne.
        -- exact Hlook.
        -- intros Haz. subst a.
           apply Hz. apply elem_of_union_l.
           apply lvars_fv_elem. eapply elem_of_dom_2. exact Hlook.
Qed.

Lemma basic_tm_has_ltype_open_result_target_fun
    (Σ : lty_env) τtop τx τr e1 e2
    (m : WfWorldT) y :
  erase_ty τtop = erase_ty τx →ₜ erase_ty τr ->
  typed_total_equiv_on Σ τtop m e1 e2 ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  basic_tm_has_ltype
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    e2 (erase_ty τx →ₜ erase_ty τr).
Proof.
  intros Herase Hequiv Hye.
  pose proof (typed_total_equiv_target_zero
    Σ τtop m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
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
    unfold relevant_env, lty_env_restrict_lvars in Htop.
    apply storeA_restrict_lookup_some in Htop as [_ HΣv].
    destruct v as [k|z].
    + unfold lvars_of_atoms in Hvfv. set_solver.
    + assert (Hzy : z <> y).
      {
        intros ->. apply Hye.
        unfold lvars_of_atoms in Hvfv. set_solver.
      }
      unfold relevant_env, lty_env_restrict_lvars.
      assert (Hlook_open :
          lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx))
            !! LVFree z = Some U).
      { rewrite lty_env_open_one_typed_bind_lookup_free_ne by exact Hzy.
        exact HΣv. }
      assert (Hin :
          LVFree z ∈ relevant_lvars (cty_open 0 y τr)
            (tapp_tm e2 (vfvar y))).
      {
        unfold relevant_lvars.
        rewrite tm_lvars_tapp_tm_fvar.
        rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
        unfold lvars_of_atoms in *. set_solver.
      }
      better_store_solver.
Qed.

Lemma basic_value_has_ltype_open_result_target_arg
    (Σ : lty_env) τx τr e y :
  basic_value_has_ltype
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e (vfvar y)))
    (vfvar y) (erase_ty τx).
Proof.
  constructor.
  unfold relevant_env, lty_env_restrict_lvars.
  assert (Hlook :
      lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx))
        !! LVFree y = Some (erase_ty τx)).
  { apply lty_env_open_one_typed_bind_lookup_current. }
  assert (Hin :
      LVFree y ∈ relevant_lvars (cty_open 0 y τr)
        (tapp_tm e (vfvar y))).
  {
    unfold relevant_lvars.
    rewrite tm_lvars_tapp_tm_fvar.
    set_solver.
  }
  better_store_solver.
Qed.

Lemma expr_result_of_tm_equiv
    m e1 e2 z :
  tm_equiv_on m e1 e2 ->
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

Lemma tm_equiv_result_alias
    e x (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ expr_total_formula (tret (vfvar x)) ->
  tm_equiv_on m e (tret (vfvar x)).
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
  destruct (must_terminating_reaches_result _ Htotal_stores)
    as [vt Heval_ret_vt].
  unfold tm_eval_in_store, expr_eval_in_store.
  unfold tm_eval_in_store, expr_eval_in_store in Heval_e_vx.
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

Lemma tm_total_equiv_result_alias
    e x (m : WfWorldT) :
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ expr_total_formula (tret (vfvar x)) ->
  tm_total_equiv_on m e (tret (vfvar x)).
Proof.
  intros Hres Htotal_ret σ Hσ.
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hres)
    as Hres_world.
  pose proof (expr_total_formula_to_atom_world (tret (vfvar x)) m Htotal_ret)
    as Htotal_world.
  destruct Hres_world as [_ [_ Hres_stores]].
  destruct Htotal_world as [_ Htotal_stores].
  assert (Hlift :
      worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  specialize (Hres_stores (lstore_lift_free σ) Hlift)
    as [_ [vx [_ Heval_e_vx]]].
  specialize (Htotal_stores (lstore_lift_free σ) Hlift)
    as Htotal_ret_store.
  split.
  - intros _. exact Htotal_ret_store.
  - intros _.
    unfold expr_eval_in_store in Heval_e_vx.
    eapply must_terminating_of_steps_result. exact Heval_e_vx.
Qed.

Lemma typed_total_equiv_term_scope
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT).
Proof.
  intros [_ [_ [Hzero1 Hzero2]]].
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1)
    as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2)
    as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [_ Htotal1]]].
  destruct Hguard2 as [_ [_ [_ Htotal2]]].
  apply expr_total_formula_models_iff in Htotal1
    as [Hscope1 [_ _]].
  apply expr_total_formula_models_iff in Htotal2
    as [Hscope2 [_ _]].
  unfold formula_scoped_in_world in Hscope1, Hscope2.
  rewrite formula_fv_expr_total_formula in Hscope1.
  rewrite formula_fv_expr_total_formula in Hscope2.
  rewrite tm_lvars_fv in Hscope1.
  rewrite tm_lvars_fv in Hscope2.
  better_set_solver.
Qed.

Lemma typed_total_equiv_term_lc_lvars
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  lc_lvars (tm_lvars e1) /\ lc_lvars (tm_lvars e2).
Proof.
  intros [_ [_ [Hzero1 Hzero2]]].
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1)
    as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2)
    as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [_ [_ Htotal1]]].
  destruct Hguard2 as [_ [_ [_ Htotal2]]].
  apply expr_total_formula_models_iff in Htotal1
    as [_ [Hlc1 _]].
  apply expr_total_formula_models_iff in Htotal2
    as [_ [Hlc2 _]].
  split; assumption.
Qed.

Lemma typed_total_equiv_term_lc
    Σ τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  lc_tm e1 /\ lc_tm e2.
Proof.
  intros [_ [_ [Hzero1 Hzero2]]].
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1)
    as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2)
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

Lemma tm_equiv_full_world_extend_fresh
    (m my : WfWorldT) y e1 e2 :
  tm_equiv_on m e1 e2 ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT) ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  tm_equiv_on my e1 e2.
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
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (m : WorldT)) Hfv2)).
    apply Heq12.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (m : WorldT)) Hfv1)).
    exact Heval1.
  - intros Heval2.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ e1 v (world_dom (m : WorldT)) Hfv1)).
    apply Heq21.
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ e2 v (world_dom (m : WorldT)) Hfv2)).
    exact Heval2.
Qed.

Lemma expr_result_shift0_of_tm_equiv_open
    (m my : WfWorldT) y e1 e2 :
  tm_equiv_on m e1 e2 ->
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
  rewrite open_expr_result_shift0_lvars_lc in Hmodel
    by (exact Hlc2 || set_solver).
  rewrite open_expr_result_shift0_lvars_lc
    by (exact Hlc1 || set_solver).
  eapply expr_result_of_tm_equiv.
  - eapply tm_equiv_full_world_extend_fresh; eauto.
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

End TypeDenote.
