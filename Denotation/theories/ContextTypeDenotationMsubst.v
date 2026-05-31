(** * Denotation.ContextTypeDenotationMsubst

    Models-level transport for substituting a fixed atom store into context-type
    denotations.  This is the shared route used by fibered implication
    elimination in Soundness; case-specific msubst bridges should reduce to
    this theorem rather than re-proving formula-shape facts. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationLvars.

Section ContextTypeDenotationMsubst.

Definition denot_msubst_relevant_store
    (σ : StoreT) (τ : context_ty) (e : tm) : StoreT :=
  store_restrict σ (lvars_fv (denot_relevant_lvars τ e)).

Lemma atom_store_has_ltype_denot_relevant_env Σ σ τ e :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  atom_store_has_ltype (denot_relevant_env Σ τ e) σ.
Proof.
  intros Hrel Hty.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  apply atom_store_has_ltype_restrict_lvars; assumption.
Qed.

Lemma denot_guard_msubst_store_models
    σ Σ τ e (m : WfWorldT) :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m
    (formula_msubst_store σ
      (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
        (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
          (FAnd
            (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
              (erase_ty τ))
            (expr_total_formula e))))) ->
  res_models m
    (FAnd
      (context_ty_wf_formula
        (denot_relevant_env (lty_env_msubst_store σ Σ)
          (context_ty_msubst_store σ τ)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (context_ty_msubst_store σ τ))
      (FAnd
        (basic_world_formula
          (denot_relevant_env (lty_env_msubst_store σ Σ)
            (context_ty_msubst_store σ τ)
            (lstore_instantiate_tm (lstore_lift_free σ) e)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env (lty_env_msubst_store σ Σ)
              (context_ty_msubst_store σ τ)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (lstore_instantiate_tm (lstore_lift_free σ) e)
            (erase_ty (context_ty_msubst_store σ τ)))
          (expr_total_formula
            (lstore_instantiate_tm (lstore_lift_free σ) e))))).
Proof.
  intros Hσrel Hσty Hm.
  pose proof (atom_store_has_ltype_denot_relevant_env Σ σ τ e
    Hσrel Hσty) as Hσty_g.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  cbn [formula_msubst_store formula_mlsubst] in Hm.
  repeat rewrite res_models_and_iff in Hm.
  destruct Hm as [Hwf [Hworld [Hbasic Htotal]]].
  repeat rewrite res_models_and_iff.
  rewrite <- (denot_relevant_env_msubst_store σ Σ τ e Hclosed).
  split.
  - apply context_ty_wf_formula_msubst_store_models;
      [apply atom_store_has_ltype_dom_subset; exact Hσty_g|exact Hwf].
  - split.
    + apply basic_world_formula_msubst_store_models; [exact Hσty_g|exact Hworld].
    + split.
      * rewrite erase_ty_context_ty_msubst_store.
        apply expr_basic_typing_formula_msubst_store_models;
          [exact Hσty_g|exact Hbasic].
      * apply (expr_total_formula_msubst_store_models σ Σ e m);
          [exact Hσty|exact Htotal].
Qed.

Lemma denot_ty_lvar_gas_msubst_store_models_relevant
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_models
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store (denot_msubst_relevant_store σ τ e) Σ)
    (context_ty_msubst_store (denot_msubst_relevant_store σ τ e) τ)
    (lstore_instantiate_tm
      (lstore_lift_free (denot_msubst_relevant_store σ τ e)) e)).
Proof.
  intros Hscope Hty Hmodels.
  eapply denot_ty_lvar_gas_msubst_store_models_relevant.
  - exact Hscope.
  - unfold denot_msubst_relevant_store.
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply storeA_restrict_dom_subset in Hx.
    rewrite lvars_fv_elem in Hx. exact Hx.
  - unfold denot_msubst_relevant_store.
    intros x v Hxv.
    apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
    exact (Hty x v Hxv).
  - unfold denot_msubst_relevant_store.
    rewrite <- (formula_msubst_store_restrict_fv_subset σ
      (denot_ty_lvar_gas gas Σ τ e)
      (lvars_fv (denot_relevant_lvars τ e))).
    + exact Hmodels.
    + transitivity (fv_tm e ∪ fv_cty τ).
      * apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
      * unfold denot_relevant_lvars.
        rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
        set_solver.
Qed.

End ContextTypeDenotationMsubst.
