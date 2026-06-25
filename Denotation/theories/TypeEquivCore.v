(** * Denotation.TypeEquivCore

    Core support for result-equivalence and result-extension transport. *)

From Denotation Require Import Notation TypeDenote.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Lemma res_models_lift_projection_eq
    (m my : WfWorldT) (φ : FormulaT) :
  res_restrict my (world_dom (m : WorldT)) = m ->
  m ⊨ φ ->
  my ⊨ φ.
Proof.
  intros Hproj Hm.
  eapply res_models_kripke; [|exact Hm].
  apply res_le_of_projection_eq. exact Hproj.
Qed.

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
    - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_1)
        (typed_lty_env_bind
          (relevant_env Σ0 (CTSum τ0_1 τ0_2) e0)
          (erase_ty τ0_1)) (tret (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) (cty_shift 0 τ0_1)
        (typed_lty_env_bind
          (relevant_env Σ0 (CTSum τ0_1 τ0_2) e0)
          (erase_ty τ0_1)) (tret (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
      rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0_2)
        (typed_lty_env_bind
          (relevant_env Σ0 (CTSum τ0_1 τ0_2) e0)
          (erase_ty τ0_1)) (tret (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2))
        ltac:(lia) (cty_shift 0 τ0_2)
        (typed_lty_env_bind
          (relevant_env Σ0 (CTSum τ0_1 τ0_2) e0)
          (erase_ty τ0_1)) (tret (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
      reflexivity.
    - unfold arrow_value_denote_gas_with.
      rewrite (IH gas' ltac:(lia)
        (cty_shift 0 (cty_shift 0 τ0_1))
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
            (erase_ty (CTArrow τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tret (vbvar 0))
        ltac:(rewrite !cty_shift_preserves_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        (cty_shift 0 (cty_shift 0 τ0_1))
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
            (erase_ty (CTArrow τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tret (vbvar 0))
        ltac:(rewrite !cty_shift_preserves_depth; lia)).
      rewrite (IH gas' ltac:(lia) (cty_shift 1 τ0_2)
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
            (erase_ty (CTArrow τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        (cty_shift 1 τ0_2)
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTArrow τ0_1 τ0_2) e0)
            (erase_ty (CTArrow τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
      reflexivity.
    - unfold wand_value_denote_gas_with.
      rewrite (IH gas' ltac:(lia)
        (cty_shift 0 (cty_shift 0 τ0_1))
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
            (erase_ty (CTWand τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tret (vbvar 0))
        ltac:(rewrite !cty_shift_preserves_depth; lia)).
      rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
        (cty_shift 0 (cty_shift 0 τ0_1))
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
            (erase_ty (CTWand τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tret (vbvar 0))
        ltac:(rewrite !cty_shift_preserves_depth; lia)).
      rewrite (IH gas' ltac:(lia) (cty_shift 1 τ0_2)
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
            (erase_ty (CTWand τ0_1 τ0_2)))
          (erase_ty (cty_shift 0 τ0_1)))
        (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))
        ltac:(rewrite cty_shift_preserves_depth; lia)).
	    rewrite (IH (Nat.max (cty_depth τ0_1) (cty_depth τ0_2)) ltac:(lia)
	      (cty_shift 1 τ0_2)
	      (typed_lty_env_bind
	        (typed_lty_env_bind
	          (relevant_env Σ0 (CTWand τ0_1 τ0_2) e0)
	          (erase_ty (CTWand τ0_1 τ0_2)))
	        (erase_ty (cty_shift 0 τ0_1)))
	      (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))
	      ltac:(rewrite cty_shift_preserves_depth; lia)).
	    reflexivity.
		  - rewrite (IH gas' ltac:(lia) (cty_shift 0 τ0)
		      (typed_lty_env_bind
		        (relevant_env Σ0 (CTPersist τ0) e0)
            (erase_ty (CTPersist τ0)))
		      (tret (vbvar 0))
		      ltac:(rewrite cty_shift_preserves_depth; lia)).
		    rewrite (IH (cty_depth τ0) ltac:(lia) (cty_shift 0 τ0)
		      (typed_lty_env_bind
		        (relevant_env Σ0 (CTPersist τ0) e0)
            (erase_ty (CTPersist τ0)))
		      (tret (vbvar 0))
		      ltac:(rewrite cty_shift_preserves_depth; lia)).
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

Lemma ty_guard_formula_context_wf
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  m ⊨ context_ty_wf_formula Σ τ.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  tauto.
Qed.

Lemma ty_guard_formula_basic_world
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  m ⊨ basic_world_formula Σ.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  tauto.
Qed.

Lemma ty_guard_formula_basic_typing
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  m ⊨ expr_basic_typing_formula Σ e (erase_ty τ).
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  tauto.
Qed.

Lemma ty_guard_formula_total
    (Σ : lty_env) (τ : context_ty) (e : tm) (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  m ⊨ expr_total_formula e.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  tauto.
Qed.

Lemma ty_denote_gas_type_lvars_world
    gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  lvars_fv (context_ty_lvars τ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard gas Σ τ e m Hden) as Hguard.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard) as Hwf.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard) as Hworld.
  pose proof (context_ty_wf_formula_fv_cty_subset
    (relevant_env Σ τ e) τ m Hwf) as Hτ.
  pose proof (proj1 (basic_world_formula_models_iff
    (relevant_env Σ τ e) m) Hworld) as [_ [Hdom _]].
  rewrite context_ty_lvars_fv.
  set_solver.
Qed.

Lemma ty_denote_gas_fv_cty_world
    gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  fv_cty τ ⊆ world_dom (m : WorldT).
Proof.
  intros Hden.
  rewrite <- context_ty_lvars_fv.
  exact (ty_denote_gas_type_lvars_world gas Σ τ e m Hden).
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

Lemma ty_denote_gas_ret_fvar_basic_world_singleton
    gas Σ τ x (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)) ->
  m ⊨ basic_world_formula
    (<[LVFree x := erase_ty τ]> (∅ : lty_env)).
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard_formula
    gas Σ τ (tret (vfvar x)) m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [_ _]]].
  pose proof (ty_denote_gas_ret_fvar_lookup gas Σ τ x m Hden)
    as Hlookup.
  eapply basic_world_formula_subenv; [|exact Hworld].
  intros v T Hsmall.
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - rewrite lookup_insert in Hsmall.
    destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
      [|contradiction].
    inversion Hsmall; subst.
    unfold relevant_env, lty_env_restrict_lvars.
    apply storeA_restrict_lookup_some_2.
    + exact Hlookup.
    + unfold relevant_lvars.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
      set_solver.
  - rewrite lookup_insert_ne in Hsmall by (symmetry; exact Hvx).
    rewrite lookup_empty in Hsmall. discriminate.
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
  intros HΣclosed HxΣ HFx Hext Hguard.
  destruct HFx as [Hx_fv [Hin Hout] Hrel].
  pose proof Hguard as Hparts.
  repeat rewrite res_models_and_iff in Hparts.
  destruct Hparts as [_ [Hworld [Hbasic Htotal]]].
  pose proof Hworld as Hworld_model.
  pose proof Hbasic as Hbasic_model.
  apply basic_world_formula_models_iff in Hworld as [_ [_ Hworld_typed]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HΣ_closed [_ Hty_e]].
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
            atom_store_has_ltype Σ σin).
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
                 --- exact HΣ_closed.
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

Lemma ty_denote_gas_result_alias_guard
    (Σ : lty_env) τ e x (m : WfWorldT) :
  Σ !! LVFree x = Some (erase_ty τ) ->
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
  intros Hlookup Hguard.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf [Hworld [_ _]]].
  split; [exact Hwf|].
  split; [exact Hworld|].
  pose proof (proj1 (basic_world_formula_models_iff Σ m) Hworld)
    as [HlcΣ [HsubΣ _]].
  assert (Hbasic_ret :
      m ⊨ expr_basic_typing_formula Σ (tret (vfvar x)) (erase_ty τ)).
  {
    eapply ret_fvar_typing_of_lookup; eauto.
  }
  split; [exact Hbasic_ret|].
  eapply expr_total_formula_tret_of_basic; eauto.
Qed.


End TypeDenote.
