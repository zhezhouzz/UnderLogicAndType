(** * Denotation.ContextTypeDenotationCasesContext

    Small context-introduction and relevant-environment helpers used by
    direct Fundamental cases. *)

From Denotation Require Import Context ContextTypeDenotationSaturateCore.

Section ContextTypeDenotationCasesContext.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

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
