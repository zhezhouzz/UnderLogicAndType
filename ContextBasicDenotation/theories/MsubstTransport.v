(** * BasicDenotation.MsubstTransport

    Transport lemmas for freezing ordinary atom stores into formulas.  These
    are the BasicDenotation-facing bridge between [formula_msubst_store] and
    the TypeLanguage-level substitution operations on contexts, qualifiers,
    and terms. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermEval TermOpen Qualifier
  BasicTypingFormula RelevantEnv.
From ContextLogic Require Import FormulaConnectives.
From ContextAlgebra Require Import ResourceAlgebra.

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
Proof.
  intros _ [Hdom Hstores]. split.
  - intros v Hv.
    rewrite storeA_restrict_dom in Hv.
    assert (Hv' : v ∈ dom Σ ∖ dom (lstore_lift_free σ : LStoreT)) by set_solver.
    change (v ∈ lworld_dom (@lw value _ w : LWorldT)).
    rewrite (@lw_dom value _ w). exact Hv'.
  - intros τ Hτ.
    intros v T u HΣv Hτv.
    apply storeA_restrict_lookup_some in HΣv as [HvD HΣv].
    apply elem_of_difference in HvD as [_ Hvfresh].
    assert (Hτdom : dom (τ : LStoreT) =
      dom Σ ∖ dom (lstore_lift_free σ : LStoreT)).
    {
      pose proof (wfworldA_store_dom (@lw value _ w : LWfWorld) τ Hτ) as Hdomτ.
      change (dom (τ : LStoreT) = lworld_dom (@lw value _ w : LWorldT)) in Hdomτ.
      rewrite (@lw_dom value _ w) in Hdomτ. exact Hdomτ.
    }
    set (ρD := storeA_restrict (lstore_lift_free σ : LStoreT) (dom Σ)).
    assert (HρDdom : dom (ρD : LStoreT) =
      dom (lstore_lift_free σ : LStoreT) ∩ dom Σ).
    {
      unfold ρD.
      apply (@storeA_restrict_dom value logic_var _ _
        (lstore_lift_free σ : LStoreT) (dom Σ)).
    }
    assert (Hcompat : storeA_compat τ ρD).
    {
      unfold storeA_compat, map_compat.
      intros z a b Hzτ Hzρ.
      apply elem_of_dom_2 in Hzτ.
      apply elem_of_dom_2 in Hzρ.
      change (z ∈ dom (τ : LStoreT)) in Hzτ.
      change (z ∈ dom (ρD : LStoreT)) in Hzρ.
      rewrite Hτdom in Hzτ.
      rewrite HρDdom in Hzρ.
      set_solver.
    }
    assert (Hback_store :
      worldA_stores
        (@lw value _ (lworld_on_mlsubst_back (dom Σ)
          (lstore_lift_free σ) w) : LWorldT)
        (τ ∪ ρD)).
    {
      unfold lworld_on_mlsubst_back.
      cbn [lw resA_product rawA_product singleton_worldA worldA_stores].
      exists τ, ρD.
      repeat split; try exact Hτ; try exact Hcompat; try reflexivity.
      all: unfold ρD; reflexivity.
    }
    specialize (Hstores _ Hback_store v T u HΣv).
    apply Hstores.
    apply map_lookup_union_Some_raw. left. exact Hτv.
Qed.

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
Proof.
  intros Hσtyped Hm.
  change (formula_msubst_store σ (expr_basic_typing_formula Σ e T))
    with (FAtom (lqual_msubst_store σ (expr_basic_typing_lqual Σ e T))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, expr_basic_typing_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split.
  - rewrite lty_env_msubst_store_dom.
    rewrite <- dom_lstore_lift_free.
    exact Hlc.
  - split.
    + rewrite lty_env_msubst_store_dom.
      rewrite <- dom_lstore_lift_free. exact Hsub.
    + apply basic_tm_has_ltype_msubst_store; assumption.
Qed.

Lemma expr_total_formula_msubst_store_models
    σ Σ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (expr_total_formula e)) ->
  res_models m (expr_total_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hσtyped Hm.
  change (formula_msubst_store σ (expr_total_formula e))
    with (FAtom (lqual_msubst_store σ (expr_total_lqual e))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, expr_total_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Htotal]].
  pose proof (atom_store_has_ltype_closed _ _ Hσtyped) as Hclosed.
  pose proof (expr_total_on_msubst_store_from_back σ e
    (lworld_on_lift (tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT))
      m Hlc Hsub) Hclosed Htotal) as Htotal'.
  apply res_models_atom_intro.
  unfold expr_total_lqual, logic_qualifier_denote.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  exists Hlc, Hsub. exact Htotal'.
Qed.

Lemma type_qualifier_formula_msubst_store_models
    σ q (m : WfWorldT) :
  res_models m (formula_msubst_store σ (type_qualifier_formula q)) ->
  res_models m (type_qualifier_formula (qual_msubst_store σ q)).
Proof.
  intros Hm.
  destruct q as [D P].
  change (formula_msubst_store σ
    (type_qualifier_formula {| qual_lvars := D; qual_prop := P |}))
    with (FAtom (lqual_msubst_store σ
      (type_qualifier_lqual {| qual_lvars := D; qual_prop := P |}))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, type_qualifier_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop] in Hden.
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  destruct Hden as [Hlc [Hsub Hholds]].
  apply res_models_atom_intro.
  unfold type_qualifier_formula, type_qualifier_lqual,
    qual_msubst_store, qual_mlsubst, logic_qualifier_denote.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop].
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  exists Hlc, Hsub.
  intros s.
  specialize (Hholds (lstore_on_mlsubst_back D (lstore_lift_free σ) s)).
  split; intros HP.
  - apply (proj1 (lstore_in_lworld_on_mlsubst_back D
      (lstore_lift_free σ) s
      (lworld_on_lift (D ∖ dom (lstore_lift_free σ : LStoreT))
        m Hlc Hsub))).
    apply Hholds. exact HP.
  - apply Hholds.
    apply (proj2 (lstore_in_lworld_on_mlsubst_back D
      (lstore_lift_free σ) s
      (lworld_on_lift (D ∖ dom (lstore_lift_free σ : LStoreT))
        m Hlc Hsub))).
    exact HP.
Qed.

Lemma expr_result_formula_msubst_store_models
    σ e x (m : WfWorldT) :
  store_closed σ ->
  x ∉ dom (lstore_lift_free σ : LStoreT) ->
  res_models m (formula_msubst_store σ (expr_result_formula e x)) ->
  res_models m (expr_result_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e) x).
Proof.
  intros Hclosed Hxρ Hm.
  change (formula_msubst_store σ (expr_result_formula e x))
    with (FAtom (lqual_msubst_store σ (expr_result_lqual e x))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, expr_result_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hresult]].
  pose proof (expr_result_at_world_msubst_store_from_back σ e x
    (lworld_on_lift ((tm_lvars e ∪ {[x]})
      ∖ dom (lstore_lift_free σ : LStoreT)) m Hlc Hsub)
    Hclosed Hxρ Hresult) as Hresult'.
  apply res_models_atom_intro.
  unfold expr_result_lqual, logic_qualifier_denote.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  replace ((tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT)) ∪ {[x]})
    with ((tm_lvars e ∪ {[x]}) ∖ dom (lstore_lift_free σ : LStoreT))
    by set_solver.
  exists Hlc, Hsub. exact Hresult'.
Qed.

End MsubstTransport.
