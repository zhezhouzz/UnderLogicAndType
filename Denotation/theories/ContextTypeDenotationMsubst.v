(** * Denotation.ContextTypeDenotationMsubst

    Models-level transport for substituting a fixed atom store into context-type
    denotations.  This is the shared route used by fibered implication
    elimination in Soundness; case-specific msubst bridges should reduce to
    this theorem rather than re-proving formula-shape facts. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition.

Section ContextTypeDenotationMsubst.

Lemma denot_ty_lvar_gas_msubst_store_models
    gas σ Σ τ e (m : WfWorldT) :
  subseteq (denot_relevant_lvars τ e) (dom Σ) ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Admitted.

End ContextTypeDenotationMsubst.
