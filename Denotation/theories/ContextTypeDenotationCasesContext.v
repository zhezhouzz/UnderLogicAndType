(** * Denotation.ContextTypeDenotationCasesContext

    Small context-introduction and relevant-environment helpers used by
    direct Fundamental cases. *)

From Denotation Require Import Context ContextTypeDenotationSaturate.

Section ContextTypeDenotationCasesContext.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma basic_world_formula_empty (m : WfWorldT) :
  m ⊨ basic_world_formula (∅ : lty_env).
Proof.
  apply basic_world_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold lworld_has_type, worldA_has_type, storeA_has_type.
      split; [rewrite dom_empty_L; set_solver|].
      intros σ _ v T val Hlookup _.
      rewrite lookup_empty in Hlookup. discriminate.
Qed.

Lemma lvars_of_atoms_empty :
  lvars_of_atoms (∅ : aset) = (∅ : lvset).
Proof.
  unfold lvars_of_atoms.
  rewrite set_map_empty. reflexivity.
Qed.

Lemma denot_relevant_lvars_basic_ret_fvar_subset x τ :
  basic_context_ty ∅ τ ->
  denot_relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  rewrite lvars_of_atoms_empty in Hτ.
  unfold denot_relevant_lvars in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  set_solver.
Qed.

Lemma denot_relevant_lvars_basic_open_tprim_fvar_subset op x τ :
  basic_context_ty ∅ τ ->
  denot_relevant_lvars ({0 ~> x} τ) (tprim op (vfvar x)) ⊆ {[LVFree x]}.
Proof.
  intros Hbasic v Hv.
  pose proof (basic_context_ty_to_lvars _ _ Hbasic) as [Hτ _].
  rewrite lvars_of_atoms_empty in Hτ.
  assert (Hempty : context_ty_lvars τ = (∅ : lvset)) by set_solver.
  unfold denot_relevant_lvars in Hv.
  rewrite cty_open_vars in Hv.
  unfold context_ty_open_lvars in Hv.
  rewrite Hempty, set_swap_empty in Hv.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
  set_solver.
Qed.

Lemma atom_env_to_lty_env_restrict_singleton_lookup_eq
    (Δ1 Δ2 : gmap atom ty) x T :
  Δ1 !! x = Some T ->
  Δ2 !! x = Some T ->
  lty_env_restrict_lvars (atom_env_to_lty_env Δ1) ({[LVFree x]}) =
  lty_env_restrict_lvars (atom_env_to_lty_env Δ2) ({[LVFree x]}).
Proof.
  intros Hlookup1 Hlookup2.
  unfold lty_env_restrict_lvars.
  rewrite (storeA_restrict_singleton_lookup
    (atom_env_to_lty_env Δ1 : gmap logic_var ty) (LVFree x) T).
  2:{ rewrite atom_store_to_lvar_store_lookup_free. exact Hlookup1. }
  rewrite (storeA_restrict_singleton_lookup
    (atom_env_to_lty_env Δ2 : gmap logic_var ty) (LVFree x) T).
  2:{ rewrite atom_store_to_lvar_store_lookup_free. exact Hlookup2. }
  reflexivity.
Qed.

Lemma atom_env_to_lty_env_restrict_singleton_lookup
    (Δ : gmap atom ty) x T :
  Δ !! x = Some T ->
  lty_env_restrict_lvars (atom_env_to_lty_env Δ) ({[LVFree x]}) =
  lty_env_restrict_lvars
    (atom_env_to_lty_env (<[x := T]> (∅ : gmap atom ty))) ({[LVFree x]}).
Proof.
  intros Hlookup.
  eapply (atom_env_to_lty_env_restrict_singleton_lookup_eq
    Δ (<[x := T]> (∅ : gmap atom ty)) x T);
    [exact Hlookup|].
  exact (map_lookup_insert (∅ : gmap atom ty) x T).
Qed.

Lemma denot_ctx_bind_from_arg_denotation
    (Σ : gmap atom ty) x τ (m : WfWorldT) :
  basic_context_ty ∅ τ ->
  Σ !! x = Some (erase_ty τ) ->
  m ⊨ denot_ty_lvar_gas (cty_depth τ) (atom_env_to_lty_env Σ)
    τ (tret (vfvar x)) ->
  m ⊨ denot_ctx (CtxBind x τ).
Proof.
  intros Hbasic Hlookup Harg.
  pose proof (res_models_denot_ty_lvar_gas_env_agree_on
    (cty_depth τ)
    (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty)))
    τ (tret (vfvar x)) ({[LVFree x]}) m
    (denot_relevant_lvars_basic_ret_fvar_subset x τ Hbasic)
    (atom_env_to_lty_env_restrict_singleton_lookup
      Σ x (erase_ty τ) Hlookup)
    Harg) as Harg_single.
  unfold denot_ctx.
  cbn [denot_ctx_under].
  rewrite res_models_and_iff. split.
  - replace (erase_ctx_under ∅ (CtxBind x τ))
      with (<[x := erase_ty τ]> (∅ : gmap atom ty)).
    2:{
      unfold erase_ctx_under. cbn [erase_ctx].
      unfold store_union, store_singleton, store_empty.
      rewrite map_empty_union. reflexivity.
    }
    replace (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty)))
      with (<[LVFree x := erase_ty τ]> (∅ : lty_env)).
    2:{
      unfold store_insert, store_empty.
      rewrite atom_store_to_lvar_store_insert.
      unfold atom_store_to_lvar_store.
      rewrite kmap_empty.
      reflexivity.
    }
    eapply basic_world_formula_insert_from_arg_denotation
      with (τ := τ) (gas := cty_depth τ)
        (y := x) (T := erase_ty τ) (Σ := ∅).
    + rewrite dom_empty_L. set_solver.
    + apply basic_world_formula_empty.
    + replace (<[LVFree x := erase_ty τ]> (∅ : lty_env))
        with (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty))).
      * exact Harg_single.
      * symmetry.
        unfold store_insert, store_empty.
        rewrite atom_store_to_lvar_store_insert.
        unfold atom_store_to_lvar_store.
        rewrite kmap_empty.
        reflexivity.
  - unfold denot_ty.
    exact Harg_single.
Qed.
End ContextTypeDenotationCasesContext.
