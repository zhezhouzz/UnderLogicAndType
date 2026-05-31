(** * BasicDenotation.MsubstTransport

    Transport lemmas for freezing ordinary atom stores into formulas.  These
    are the BasicDenotation-facing bridge between [formula_msubst_store] and
    the TypeLanguage-level substitution operations on contexts, qualifiers,
    and terms. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermEval
  BasicTypingFormula RelevantEnv.
From ContextLogic Require Import FormulaConnectives.

Section MsubstTransport.

Local Notation LWorldOnT := (LWorldOn (V := value)) (only parsing).

Lemma lworld_has_type_msubst_store_from_back
    σ Σ (w : LWorldOnT (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))) :
  atom_store_has_ltype Σ σ ->
  lworld_has_type Σ
    (@lw value _ (lworld_on_mlsubst_back (dom Σ) (lstore_lift_free σ) w)
      : LWorldT) ->
  lworld_has_type
    (storeA_restrict Σ (dom Σ ∖ dom (lstore_lift_free σ : LStoreT)))
    (@lw value _ w : LWorldT).
Admitted.

Lemma context_ty_wf_formula_msubst_store_models
    σ Σ τ (m : WfWorldT) :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ dom Σ ->
  res_models m (formula_msubst_store σ (context_ty_wf_formula Σ τ)) ->
  res_models m (context_ty_wf_formula
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)).
Proof.
  intros HσΣ Hm.
  change (formula_msubst_store σ (context_ty_wf_formula Σ τ))
    with (FAtom (lqual_msubst_store σ (context_ty_wf_lqual Σ τ))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, context_ty_wf_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hbasic]].
  rewrite dom_lstore_lift_free in Hlc, Hsub.
  apply context_ty_wf_formula_models_iff.
  split.
  - rewrite lty_env_msubst_store_dom. exact Hlc.
  - split.
    + rewrite lty_env_msubst_store_dom. exact Hsub.
    + rewrite lty_env_msubst_store_dom.
      apply basic_context_ty_lvars_msubst_store.
      exact Hbasic.
Qed.

Lemma basic_world_formula_msubst_store_models
    σ Σ (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (basic_world_formula Σ)) ->
  res_models m (basic_world_formula (lty_env_msubst_store σ Σ)).
Proof.
  intros Hσtyped Hm.
  change (formula_msubst_store σ (basic_world_formula Σ))
    with (FAtom (lqual_msubst_store σ (basic_world_lqual Σ))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, basic_world_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Htyped]].
  apply res_models_atom_intro.
  unfold basic_world_lqual, logic_qualifier_denote.
  rewrite lty_env_msubst_store_dom.
  rewrite <- dom_lstore_lift_free.
  exists Hlc, Hsub.
  change (lworld_has_type (lty_env_msubst_store σ Σ)
    (@lw value _
      (lworld_on_lift
        (dom Σ ∖ dom (lstore_lift_free σ : LStoreT)) m Hlc Hsub) : LWorldT)).
  assert (Henv :
    lty_env_msubst_store σ Σ =
    storeA_restrict Σ (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))).
  {
    unfold lty_env_msubst_store.
    rewrite dom_lstore_lift_free.
    reflexivity.
  }
  rewrite Henv.
  eapply lworld_has_type_msubst_store_from_back; [exact Hσtyped|].
  exact Htyped.
Qed.

Lemma expr_basic_typing_formula_msubst_store_models
    σ Σ e T (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (expr_basic_typing_formula Σ e T)) ->
  res_models m (expr_basic_typing_formula
    (lty_env_msubst_store σ Σ)
    (lstore_instantiate_tm (lstore_lift_free σ) e) T).
Admitted.

Lemma expr_total_formula_msubst_store_models
    σ Σ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (expr_total_formula e)) ->
  res_models m (expr_total_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Admitted.

End MsubstTransport.
