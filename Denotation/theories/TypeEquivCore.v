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
Admitted.

Lemma ty_denote_gas_insert_fresh_lty_env_eq
    gas (Σ : lty_env) τ e x T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  ty_denote_gas gas (<[LVFree x := T]> Σ) τ e =
  ty_denote_gas gas Σ τ e.
Proof.
Admitted.

Lemma ty_denote_gas_zero_of_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
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
  m ⊨ ty_guard_formula Σ τ e.
Proof.
  destruct gas; cbn [ty_denote_gas]; rewrite res_models_and_iff; tauto.
Qed.

Lemma ty_denote_gas_zero_of_guard
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ FAnd
    (context_ty_wf_formula Σ τ)
    (FAnd
      (basic_world_formula Σ)
      (FAnd
        (expr_basic_typing_formula Σ e
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
    (context_ty_wf_formula Σ τ)
    (FAnd
      (basic_world_formula Σ)
      (FAnd
        (expr_basic_typing_formula Σ e
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
    (context_ty_wf_formula Σ τ)
    (FAnd
      (basic_world_formula Σ)
      (FAnd
        (expr_basic_typing_formula Σ e
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
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ e
    (erase_ty τ) ->
  worldA_stores (m : WorldT) σ ->
  atom_store_has_ltype Σ
    (store_restrict σ (fv_tm e)).
Proof.
  intros Hworld Hbasic Hσ y u Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [Hyfv Hσy].
  apply basic_world_formula_models_iff in Hworld as [_ [_ Htyped]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  destruct Htyped as [_ Hstores].
  specialize (Hstores (lstore_lift_free σ)
    ltac:(exists σ; split; [exact Hσ|reflexivity])).
  assert (Hy_dom : LVFree y ∈ dom Σ).
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
    (context_ty_wf_formula Σ τ)
    (FAnd
      (basic_world_formula Σ)
      (FAnd
        (expr_basic_typing_formula Σ e
          (erase_ty τ))
        (expr_total_formula e))) ->
  extension_has_ltype (<[LVFree x := erase_ty τ]> ∅)
    (res_restrict m (ext_in Fx)) Fx.
Proof.
Admitted.

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
  m ⊨ basic_world_formula Σ ->
  m ⊨ expr_basic_typing_formula Σ e
    (erase_ty τ) ->
  m ⊨ basic_world_formula Σ.
Proof.
  intros _ _ _ Hworld_src _.
  exact Hworld_src.
Qed.

Lemma ty_denote_gas_result_alias_guard
    (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ FAnd
    (context_ty_wf_formula Σ τ)
    (FAnd
      (basic_world_formula Σ)
      (FAnd
        (expr_basic_typing_formula Σ e
          (erase_ty τ))
        (expr_total_formula e))) ->
  m ⊨ FAnd
    (context_ty_wf_formula Σ τ)
    (FAnd
      (basic_world_formula Σ)
      (FAnd
        (expr_basic_typing_formula Σ
          (tret (vfvar x)) (erase_ty τ))
        (expr_total_formula (tret (vfvar x))))).
Proof.
Admitted.


End TypeDenote.
