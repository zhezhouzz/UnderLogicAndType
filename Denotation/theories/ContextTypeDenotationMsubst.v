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

Definition denot_msubst_induction_hyp (gas : nat) : Prop :=
  forall σ0 Σ0 τ0 e0 (m0 : WfWorldT),
    denot_relevant_lvars τ0 e0 ⊆ dom Σ0 ->
    atom_store_has_ltype Σ0 σ0 ->
    m0 ⊨ formula_msubst_store σ0 (denot_ty_lvar_gas gas Σ0 τ0 e0) ->
    m0 ⊨ denot_ty_lvar_gas gas
      (lty_env_msubst_store σ0 Σ0)
      (context_ty_msubst_store σ0 τ0)
      (lstore_instantiate_tm (lstore_lift_free σ0) e0).

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

Lemma denot_ty_lvar_gas_zero_msubst_store_models_relevant
    σ Σ τ e (m : WfWorldT) :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (denot_ty_lvar_gas 0 Σ τ e)) ->
  res_models m (denot_ty_lvar_gas 0
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hσrel Hσty Hm.
  cbn [denot_ty_lvar_gas] in Hm |- *.
  cbn [formula_msubst_store formula_mlsubst] in Hm.
  rewrite res_models_and_iff in Hm.
  destruct Hm as [Hguard _].
  rewrite res_models_and_iff.
  split.
  - apply denot_guard_msubst_store_models; assumption.
  - unfold res_models. cbn [formula_measure res_models_fuel].
    split; [apply formula_scoped_true_iff; trivial|trivial].
Qed.

Lemma denot_ty_lvar_gas_msubst_store_agree_relevant
    gas σ1 σ2 Σ τ e (m : WfWorldT) :
  storeA_restrict σ1 (lvars_fv (denot_relevant_lvars τ e)) =
  storeA_restrict σ2 (lvars_fv (denot_relevant_lvars τ e)) ->
  store_closed σ1 ->
  store_closed σ2 ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ1 Σ)
    (context_ty_msubst_store σ1 τ)
    (lstore_instantiate_tm (lstore_lift_free σ1) e)) ->
  res_models m (denot_ty_lvar_gas gas
    (lty_env_msubst_store σ2 Σ)
    (context_ty_msubst_store σ2 τ)
    (lstore_instantiate_tm (lstore_lift_free σ2) e)).
Proof.
  intros Hagree Hclosed1 Hclosed2 Hmodels.
  set (R := denot_relevant_lvars τ e).
  assert (Hτ :
    context_ty_msubst_store σ1 τ =
    context_ty_msubst_store σ2 τ).
  {
    fold R in Hagree.
    rewrite (context_ty_msubst_store_restrict_subset σ1 τ (lvars_fv R)).
    2:{
      unfold R, denot_relevant_lvars.
      rewrite lvars_fv_union, context_ty_lvars_fv. set_solver.
    }
    rewrite (context_ty_msubst_store_restrict_subset σ2 τ (lvars_fv R)).
    2:{
      unfold R, denot_relevant_lvars.
      rewrite lvars_fv_union, context_ty_lvars_fv. set_solver.
    }
    change (store_restrict σ1 (lvars_fv R) =
      store_restrict σ2 (lvars_fv R)) in Hagree.
    rewrite Hagree. reflexivity.
  }
  assert (He :
    lstore_instantiate_tm (lstore_lift_free σ1) e =
    lstore_instantiate_tm (lstore_lift_free σ2) e).
  {
    apply lstore_instantiate_tm_lift_free_agree_subset
      with (X := lvars_fv R).
    - unfold R, denot_relevant_lvars.
      rewrite lvars_fv_union, tm_lvars_fv. set_solver.
    - exact Hagree.
  }
  rewrite <- Hτ.
  rewrite <- He.
  eapply res_models_denot_ty_lvar_gas_env_agree_on.
  - reflexivity.
  - apply lty_env_restrict_lvars_msubst_store_agree
      with (R := R).
    + unfold R.
      rewrite (denot_relevant_lvars_msubst_store σ1 τ e Hclosed1).
      set_solver.
    + exact Hagree.
  - exact Hmodels.
Qed.

Lemma formula_fv_over_msubst_store_body
    σ b φ e :
  store_closed σ ->
  formula_fv
    (formula_msubst_store σ
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))) =
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula (qual_msubst_store σ φ)))))).
Proof.
  intros Hclosed.
  formula_msubst_syntax_norm.
  formula_fv_syntax_norm.
  assert (Hbasic_src :
    lvars_fv
      (formula_lvars
        (formula_msubst_store σ
          (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))) = ∅).
  {
    change (formula_fv
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅))) = ∅).
    apply set_eq. intros a. split; [|set_solver].
    intros Ha.
    pose proof (formula_msubst_store_fv_subset σ
      (basic_world_formula (<[LVBound 0 := TBase b]> ∅)) a Ha) as Hsub.
    rewrite formula_fv_basic_world_formula in Hsub.
    rewrite dom_insert_L, dom_empty_L in Hsub.
    rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty in Hsub.
    set_solver.
  }
  rewrite Hbasic_src.
  rewrite formula_lvars_fv_basic_world_formula.
  rewrite dom_insert_L, dom_empty_L.
  rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty.
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ
        (expr_result_formula (tm_shift 0 e) (LVBound 0)))))
    with (lvars_fv
      ((tm_lvars (tm_shift 0 e) ∪ {[LVBound 0]})
        ∖ dom (lstore_lift_free σ : LStoreT))).
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ (type_qualifier_formula φ))))
    with (lvars_fv
      (qual_vars φ ∖ dom (lstore_lift_free σ : LStoreT))).
  rewrite formula_lvars_fv_expr_result_formula.
  rewrite formula_lvars_fv_type_qualifier_formula.
  unfold qual_dom.
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_union, !lvars_fv_singleton_bound.
  rewrite ?tm_lvars_shift_fv.
  rewrite ?(tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  change (qual_lvars (qual_msubst_store σ φ))
    with (qual_vars (qual_msubst_store σ φ)).
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_difference_singleton_bound.
  apply set_eq. intros a.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !elem_of_union, !elem_of_difference, !elem_of_empty.
  rewrite (elem_of_union (lvars_fv (tm_lvars e)) ∅ a).
  rewrite elem_of_empty.
  tauto.
Qed.

Lemma formula_fv_under_msubst_store_body
    σ b φ e :
  store_closed σ ->
  formula_fv
    (formula_msubst_store σ
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ)))))) =
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars
          (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula (qual_msubst_store σ φ)))))).
Proof.
  intros Hclosed.
  formula_msubst_syntax_norm.
  formula_fv_syntax_norm.
  assert (Hbasic_src :
    lvars_fv
      (formula_lvars
        (formula_msubst_store σ
          (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))) = ∅).
  {
    change (formula_fv
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅))) = ∅).
    apply set_eq. intros a. split; [|set_solver].
    intros Ha.
    pose proof (formula_msubst_store_fv_subset σ
      (basic_world_formula (<[LVBound 0 := TBase b]> ∅)) a Ha) as Hsub.
    rewrite formula_fv_basic_world_formula in Hsub.
    rewrite dom_insert_L, dom_empty_L in Hsub.
    rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty in Hsub.
    set_solver.
  }
  rewrite Hbasic_src.
  rewrite formula_lvars_fv_basic_world_formula.
  rewrite dom_insert_L, dom_empty_L.
  rewrite lvars_fv_union, lvars_fv_singleton_bound, lvars_fv_empty.
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ
        (expr_result_formula (tm_shift 0 e) (LVBound 0)))))
    with (lvars_fv
      ((tm_lvars (tm_shift 0 e) ∪ {[LVBound 0]})
        ∖ dom (lstore_lift_free σ : LStoreT))).
  change (lvars_fv
    (formula_lvars
      (formula_msubst_store σ (type_qualifier_formula φ))))
    with (lvars_fv
      (qual_vars φ ∖ dom (lstore_lift_free σ : LStoreT))).
  rewrite formula_lvars_fv_expr_result_formula.
  rewrite formula_lvars_fv_type_qualifier_formula.
  unfold qual_dom.
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_union, !lvars_fv_singleton_bound.
  rewrite ?tm_lvars_shift_fv.
  rewrite ?(tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  change (qual_lvars (qual_msubst_store σ φ))
    with (qual_vars (qual_msubst_store σ φ)).
  rewrite qual_msubst_store_vars.
  rewrite dom_lstore_lift_free.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !lvars_fv_difference_singleton_bound.
  apply set_eq. intros a.
  rewrite !lvars_fv_difference_of_atoms.
  rewrite !elem_of_union, !elem_of_difference, !elem_of_empty.
  rewrite (elem_of_union (lvars_fv (tm_lvars e)) ∅ a).
  rewrite elem_of_empty.
  tauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_over_body
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (type_qualifier_formula φ))))))) ->
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars
            (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula (qual_msubst_store σ φ))))))).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_under_body
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ))))))) ->
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars
            (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula (qual_msubst_store σ φ))))))).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_arrow_body
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_induction_hyp gas ->
  denot_relevant_lvars (CTArrow τx τr) e ⊆ dom Σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆
    denot_relevant_lvars (CTArrow τx τr) e ->
  atom_store_has_ltype Σ σ ->
  let Σg := denot_relevant_env Σ (CTArrow τx τr) e in
  let Σx := typed_lty_env_bind Σg (erase_ty τx) in
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FImpl
            (denot_ty_lvar_gas gas Σx
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx τr
              (tapp_tm (tm_shift 0 e) (vbvar 0))))))) ->
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let τx' := context_ty_msubst_store σ τx in
  let τr' := context_ty_msubst_store σ τr in
  let Σg' := denot_relevant_env (lty_env_msubst_store σ Σ)
    (CTArrow τx' τr') e' in
  let Σx' := typed_lty_env_bind Σg' (erase_ty τx') in
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx']> ∅))
        (FImpl
          (denot_ty_lvar_gas gas Σx'
            (cty_shift 0 τx') (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx' τr'
            (tapp_tm (tm_shift 0 e') (vbvar 0)))))).
Admitted.

Lemma denot_ty_lvar_gas_msubst_store_wand_body
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_induction_hyp gas ->
  denot_relevant_lvars (CTWand τx τr) e ⊆ dom Σ ->
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆
    denot_relevant_lvars (CTWand τx τr) e ->
  atom_store_has_ltype Σ σ ->
  let Σg := denot_relevant_env Σ (CTWand τx τr) e in
  let Σx := typed_lty_env_bind Σg (erase_ty τx) in
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FWand
            (denot_ty_lvar_gas gas Σx
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas Σx τr
              (tapp_tm (tm_shift 0 e) (vbvar 0))))))) ->
  let e' := lstore_instantiate_tm (lstore_lift_free σ) e in
  let τx' := context_ty_msubst_store σ τx in
  let τr' := context_ty_msubst_store σ τr in
  let Σg' := denot_relevant_env (lty_env_msubst_store σ Σ)
    (CTWand τx' τr') e' in
  let Σx' := typed_lty_env_bind Σg' (erase_ty τx') in
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx']> ∅))
        (FWand
          (denot_ty_lvar_gas gas Σx'
            (cty_shift 0 τx') (tret (vbvar 0)))
          (denot_ty_lvar_gas gas Σx' τr'
            (tapp_tm (tm_shift 0 e') (vbvar 0)))))).
Admitted.

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
Proof.
  induction gas as [|gas IH] in σ, Σ, τ, e, m |- *.
  - intros _ Hσrel Hσty Hm.
    eapply denot_ty_lvar_gas_zero_msubst_store_models_relevant; eauto.
  - intros Hscope Hσrel Hσty Hm.
    assert (IHfull : denot_msubst_induction_hyp gas).
    {
      intros σ0 Σ0 τ0 e0 m0 Hscope0 Hty0 Hmodels0.
      set (σr := denot_msubst_relevant_store σ0 τ0 e0).
      eapply denot_ty_lvar_gas_msubst_store_agree_relevant
        with (σ1 := σr).
      - unfold σr, denot_msubst_relevant_store.
        rewrite storeA_restrict_twice_same. reflexivity.
      - unfold σr, denot_msubst_relevant_store.
        apply store_closed_restrict.
        eapply atom_store_has_ltype_closed; exact Hty0.
      - eapply atom_store_has_ltype_closed; exact Hty0.
      - eapply IH.
        + exact Hscope0.
        + unfold σr, denot_msubst_relevant_store.
          intros v Hv.
          unfold lvars_of_atoms in Hv.
          apply elem_of_map in Hv as [x [-> Hx]].
          apply storeA_restrict_dom_subset in Hx.
          rewrite lvars_fv_elem in Hx. exact Hx.
        + unfold σr, denot_msubst_relevant_store.
          intros x v Hxv.
          apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
          exact (Hty0 x v Hxv).
        + unfold σr, denot_msubst_relevant_store.
          rewrite <- (formula_msubst_store_restrict_fv_subset σ0
            (denot_ty_lvar_gas gas Σ0 τ0 e0)
            (lvars_fv (denot_relevant_lvars τ0 e0))).
          * exact Hmodels0.
          * transitivity (fv_tm e0 ∪ fv_cty τ0).
            -- apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
            -- unfold denot_relevant_lvars.
               rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
               set_solver.
    }
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas] in Hm |- *;
      cbn [formula_msubst_store formula_mlsubst] in Hm;
      rewrite res_models_and_iff in Hm;
      destruct Hm as [Hguard Hbody].
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * apply denot_ty_lvar_gas_msubst_store_over_body with (Σ := Σ);
          assumption.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * apply denot_ty_lvar_gas_msubst_store_under_body with (Σ := Σ);
          assumption.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store].
        rewrite res_models_and_iff in Hbody.
        destruct Hbody as [Hτ1 Hτ2].
        cbn [denot_ty_lvar_gas].
        rewrite res_models_and_iff. split.
        -- set (σ1 := denot_msubst_relevant_store σ τ1 e).
           eapply denot_ty_lvar_gas_msubst_store_agree_relevant
             with (σ1 := σ1).
           ++ unfold σ1, denot_msubst_relevant_store.
              rewrite storeA_restrict_twice_same. reflexivity.
           ++ unfold σ1, denot_msubst_relevant_store.
              apply store_closed_restrict.
              eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply IH.
              ** intros v Hv. apply Hscope.
                 unfold denot_relevant_lvars, context_ty_lvars in *.
                 cbn [context_ty_lvars_at] in *.
                 apply elem_of_union in Hv as [Hv|Hv].
                 --- apply elem_of_union_l. apply elem_of_union_l. exact Hv.
                 --- apply elem_of_union_r. exact Hv.
              ** unfold σ1, denot_msubst_relevant_store.
                 intros v Hv.
                 unfold lvars_of_atoms in Hv.
                 apply elem_of_map in Hv as [x [-> Hx]].
                 apply storeA_restrict_dom_subset in Hx.
                 rewrite lvars_fv_elem in Hx. exact Hx.
              ** unfold σ1, denot_msubst_relevant_store.
                 intros x v Hxv.
                 apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
                 exact (Hσty x v Hxv).
              ** unfold σ1, denot_msubst_relevant_store.
                 rewrite <- (formula_msubst_store_restrict_fv_subset σ
                   (denot_ty_lvar_gas gas Σ τ1 e)
                   (lvars_fv (denot_relevant_lvars τ1 e))).
                 --- change (m ⊨ formula_msubst_store σ
                       (denot_ty_lvar_gas gas Σ τ1 e)).
                     exact Hτ1.
                 --- transitivity (fv_tm e ∪ fv_cty τ1).
                     +++ apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
                     +++ unfold denot_relevant_lvars.
                         rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
                         set_solver.
        -- set (σ2 := denot_msubst_relevant_store σ τ2 e).
           eapply denot_ty_lvar_gas_msubst_store_agree_relevant
             with (σ1 := σ2).
           ++ unfold σ2, denot_msubst_relevant_store.
              rewrite storeA_restrict_twice_same. reflexivity.
           ++ unfold σ2, denot_msubst_relevant_store.
              apply store_closed_restrict.
              eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply atom_store_has_ltype_closed; exact Hσty.
           ++ eapply IH.
              ** intros v Hv. apply Hscope.
                 unfold denot_relevant_lvars, context_ty_lvars in *.
                 cbn [context_ty_lvars_at] in *.
                 apply elem_of_union in Hv as [Hv|Hv].
                 --- apply elem_of_union_l. apply elem_of_union_r. exact Hv.
                 --- apply elem_of_union_r. exact Hv.
              ** unfold σ2, denot_msubst_relevant_store.
                 intros v Hv.
                 unfold lvars_of_atoms in Hv.
                 apply elem_of_map in Hv as [x [-> Hx]].
                 apply storeA_restrict_dom_subset in Hx.
                 rewrite lvars_fv_elem in Hx. exact Hx.
              ** unfold σ2, denot_msubst_relevant_store.
                 intros x v Hxv.
                 apply storeA_restrict_lookup_some in Hxv as [_ Hxv].
                 exact (Hσty x v Hxv).
              ** unfold σ2, denot_msubst_relevant_store.
                 rewrite <- (formula_msubst_store_restrict_fv_subset σ
                   (denot_ty_lvar_gas gas Σ τ2 e)
                   (lvars_fv (denot_relevant_lvars τ2 e))).
                 --- change (m ⊨ formula_msubst_store σ
                       (denot_ty_lvar_gas gas Σ τ2 e)).
                     exact Hτ2.
                 --- transitivity (fv_tm e ∪ fv_cty τ2).
                     +++ apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
                     +++ unfold denot_relevant_lvars.
                         rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
                         set_solver.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * pose proof (denot_guard_msubst_store_models σ Σ (CTUnion τ1 τ2) e m
          Hσrel Hσty Hguard) as Hguard'.
        cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply res_models_or_transport_between_worlds.
        -- eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open
             with (τbig := context_ty_msubst_store σ (CTUnion τ1 τ2)).
           ++ cbn [context_ty_msubst_store context_ty_lvars context_ty_lvars_at].
              set_solver.
           ++ exact Hguard'.
        -- eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open
             with (τbig := context_ty_msubst_store σ (CTUnion τ1 τ2)).
           ++ cbn [context_ty_msubst_store context_ty_lvars context_ty_lvars_at].
              set_solver.
           ++ exact Hguard'.
        -- intros Hτ1.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_l. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ1 e)).
              exact Hτ1.
        -- intros Hτ2.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_r. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ2 e)).
              exact Hτ2.
        -- exact Hbody.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply res_models_plus_map; [| | exact Hbody].
        -- intros m' Hτ1.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_l. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m' ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ1 e)).
              exact Hτ1.
        -- intros m' Hτ2.
           eapply IHfull.
           ++ intros v Hv. apply Hscope.
              unfold denot_relevant_lvars, context_ty_lvars in *.
              cbn [context_ty_lvars_at] in *.
              apply elem_of_union in Hv as [Hv|Hv].
              ** apply elem_of_union_l. apply elem_of_union_r. exact Hv.
              ** apply elem_of_union_r. exact Hv.
           ++ exact Hσty.
           ++ change (m' ⊨ formula_msubst_store σ
                (denot_ty_lvar_gas gas Σ τ2 e)).
              exact Hτ2.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply denot_ty_lvar_gas_msubst_store_arrow_body;
          [exact IHfull|exact Hscope|exact Hσrel|exact Hσty|].
        exact Hbody.
    + rewrite res_models_and_iff. split.
      * eapply denot_guard_msubst_store_models;
          [exact Hσrel|exact Hσty|exact Hguard].
      * cbn [context_ty_msubst_store denot_ty_lvar_gas].
        eapply denot_ty_lvar_gas_msubst_store_wand_body;
          [exact IHfull|exact Hscope|exact Hσrel|exact Hσty|].
        exact Hbody.
Qed.

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
