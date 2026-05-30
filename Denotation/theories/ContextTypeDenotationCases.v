(** * Denotation.ContextTypeDenotationCases

    Direct case-level semantic obligations for the Fundamental theorem.

    These lemmas are deliberately below [ContextTyping]: they mention context
    denotation and erased/basic terms, but not the typing judgment itself.  The
    typing proof should only unpack [context_typing_wf], instantiate induction
    hypotheses, and then call one of these gas-level obligations. *)

From Denotation Require Import Context ContextTypeDenotationSaturate.

Section ContextTypeDenotationCases.

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

Lemma context_ty_wf_formula_const_precise_empty c (m : WfWorldT) :
  m ⊨ context_ty_wf_formula (∅ : lty_env)
    (CTInter
      (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
      (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))).
Proof.
  apply context_ty_wf_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold const_precise_ty, precise_ty, over_ty, under_ty, mk_q_eq,
        basic_context_ty_lvars.
      cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars
        lvar_value_keys lvars_at_depth context_ty_shape_ok erase_ty].
      rewrite !lvars_at_depth_union, !lvars_at_depth_singleton_bound0_succ,
        !lvars_at_depth_empty.
      split; [set_solver|].
      repeat split; reflexivity.
Qed.

Lemma denot_relevant_env_empty τ e :
  denot_relevant_env (∅ : lty_env) τ e = (∅ : lty_env).
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  apply storeA_restrict_empty.
Qed.

Lemma context_ty_wf_formula_const_over_empty c (m : WfWorldT) :
  m ⊨ context_ty_wf_formula (∅ : lty_env)
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))).
Proof.
  apply context_ty_wf_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold mk_q_eq, basic_context_ty_lvars.
      cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars
        lvar_value_keys lvars_at_depth context_ty_shape_ok erase_ty].
      rewrite !lvars_at_depth_union, !lvars_at_depth_singleton_bound0_succ,
        !lvars_at_depth_empty.
      split; [set_solver|].
      reflexivity.
Qed.

Lemma context_ty_wf_formula_const_under_empty c (m : WfWorldT) :
  m ⊨ context_ty_wf_formula (∅ : lty_env)
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))).
Proof.
  apply context_ty_wf_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold mk_q_eq, basic_context_ty_lvars.
      cbn [context_ty_lvars context_ty_lvars_at qual_vars qual_lvars
        lvar_value_keys lvars_at_depth context_ty_shape_ok erase_ty].
      rewrite !lvars_at_depth_union, !lvars_at_depth_singleton_bound0_succ,
        !lvars_at_depth_empty.
      split; [set_solver|].
      reflexivity.
Qed.

Lemma expr_basic_typing_formula_ret_const_empty c (m : WfWorldT) :
  m ⊨ expr_basic_typing_formula (∅ : lty_env)
    (tret (vconst c)) (TBase (base_ty_of_const c)).
Proof.
  apply expr_basic_typing_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold basic_tm_has_ltype.
      split; [cbn [tm_lvars lvar_value_keys]; set_solver|].
      intros η _ _.
      change (lty_env_open_lvars η (∅ : lty_env))
        with (storeA_rekey (logic_var_open_env η) (∅ : gmap logic_var ty)).
      rewrite storeA_rekey_empty.
      rewrite open_tm_env_lc by (constructor; constructor).
      cbn [lty_env_to_atom_env].
      constructor. constructor.
Qed.

Lemma expr_total_formula_ret_const c (m : WfWorldT) :
  m ⊨ expr_total_formula (tret (vconst c)).
Proof.
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on.
  split.
  - cbn [tm_lvars lvar_value_keys]. set_solver.
  - intros σ _.
    exists (vconst c).
    unfold expr_eval_in_store, lstore_instantiate_tm,
      lstore_instantiate_tm_at, lstore_instantiate_value_at.
    cbn [lstore_instantiate_tm_split_at
      lstore_instantiate_value_split_at].
    apply Steps_refl. constructor. constructor.
Qed.

Lemma denot_relevant_env_const_precise_atom_env_empty Σ c :
  denot_relevant_env (atom_env_to_lty_env Σ)
    (CTInter
      (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
      (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
    (tret (vconst c)) = (∅ : lty_env).
Proof.
  apply map_eq. intros v.
  destruct v as [k|x].
  - unfold denot_relevant_env, lty_env_restrict_lvars.
    apply eq_None_not_Some. intros [T Hlookup].
    apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
    rewrite atom_store_to_lvar_store_lookup_bound_none in Hlookup.
    discriminate.
  - apply eq_None_not_Some. intros [T Hlookup].
    unfold denot_relevant_env, lty_env_restrict_lvars in Hlookup.
    apply storeA_restrict_lookup_some in Hlookup as [Hin _].
    apply lvars_fv_elem in Hin.
    unfold denot_relevant_lvars, precise_ty, over_ty, under_ty, mk_q_eq in Hin.
    cty_lvars_syntax_norm_in Hin.
    unfold qual_vars in Hin.
    cbn [qual_lvars tm_lvars tm_lvars_at value_lvars_at
      lvar_value_keys] in Hin.
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union,
      ?lvars_fv_singleton_bound, ?lvars_fv_empty in Hin.
    set_solver.
Qed.

Lemma denot_relevant_env_const_over_atom_env_empty Σ c :
  denot_relevant_env (atom_env_to_lty_env Σ)
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)) = (∅ : lty_env).
Proof.
  apply map_eq. intros v.
  destruct v as [k|x].
  - unfold denot_relevant_env, lty_env_restrict_lvars.
    apply eq_None_not_Some. intros [T Hlookup].
    apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
    rewrite atom_store_to_lvar_store_lookup_bound_none in Hlookup.
    discriminate.
  - apply eq_None_not_Some. intros [T Hlookup].
    unfold denot_relevant_env, lty_env_restrict_lvars in Hlookup.
    apply storeA_restrict_lookup_some in Hlookup as [Hin _].
    apply lvars_fv_elem in Hin.
    unfold denot_relevant_lvars, mk_q_eq in Hin.
    cty_lvars_syntax_norm_in Hin.
    unfold qual_vars in Hin.
    cbn [qual_lvars tm_lvars tm_lvars_at value_lvars_at
      lvar_value_keys] in Hin.
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union,
      ?lvars_fv_singleton_bound, ?lvars_fv_empty in Hin.
    set_solver.
Qed.

Lemma denot_relevant_env_const_under_atom_env_empty Σ c :
  denot_relevant_env (atom_env_to_lty_env Σ)
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)) = (∅ : lty_env).
Proof.
  apply map_eq. intros v.
  destruct v as [k|x].
  - unfold denot_relevant_env, lty_env_restrict_lvars.
    apply eq_None_not_Some. intros [T Hlookup].
    apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
    rewrite atom_store_to_lvar_store_lookup_bound_none in Hlookup.
    discriminate.
  - apply eq_None_not_Some. intros [T Hlookup].
    unfold denot_relevant_env, lty_env_restrict_lvars in Hlookup.
    apply storeA_restrict_lookup_some in Hlookup as [Hin _].
    apply lvars_fv_elem in Hin.
    unfold denot_relevant_lvars, mk_q_eq in Hin.
    cty_lvars_syntax_norm_in Hin.
    unfold qual_vars in Hin.
    cbn [qual_lvars tm_lvars tm_lvars_at value_lvars_at
      lvar_value_keys] in Hin.
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union,
      ?lvars_fv_singleton_bound, ?lvars_fv_empty in Hin.
    set_solver.
Qed.

Lemma const_qual_open_vars c y :
  qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) =
  {[LVFree y]}.
Proof.
  unfold qual_open_atom, mk_q_eq, qual_vars.
  cbn [qual_lvars lvar_value_keys].
  base_swap_normalize.
  set_solver.
Qed.

Lemma const_qual_vars_bound c :
  qual_vars (mk_q_eq (vbvar 0) (vconst c)) = {[LVBound 0]}.
Proof.
  unfold mk_q_eq, qual_vars.
  cbn [qual_lvars lvar_value_keys].
  set_solver.
Qed.

Lemma const_qual_open_fv c y :
  qual_dom (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) =
  {[y]}.
Proof.
  unfold qual_dom.
  rewrite const_qual_open_vars.
  apply lvars_fv_singleton_free.
Qed.

Lemma expr_result_formula_ret_const_lookup c y (m : WfWorldT) σ :
  m ⊨ expr_result_formula (tret (vconst c)) (LVFree y) ->
  (m : WorldT) σ ->
  σ !! y = Some (vconst c).
Proof.
  intros Hexpr Hσ.
  pose proof (expr_result_formula_to_atom_world
    (tret (vconst c)) (LVFree y) m Hexpr) as Hres.
  destruct Hres as [_ [_ Hstores]].
  specialize (Hstores (lstore_lift_free σ)).
  assert (Hlift :
      (res_lift_free m : LWorldT) (lstore_lift_free σ)).
  { exists σ. split; [exact Hσ | reflexivity]. }
  specialize (Hstores Hlift).
  destruct Hstores as [_ [v [Hlookup Heval]]].
  rewrite lstore_lift_free_lookup_free in Hlookup.
  enough (v = vconst c) as -> by exact Hlookup.
  unfold expr_eval_in_store, lstore_instantiate_tm,
    lstore_instantiate_tm_at, lstore_instantiate_value_at in Heval.
  cbn [lstore_instantiate_tm_split_at
    lstore_instantiate_value_split_at] in Heval.
  symmetry.
  eapply steps_result_unique; [| exact Heval].
  apply Steps_refl. constructor. constructor.
Qed.

Lemma const_qual_open_prop_iff c y
    (s : LStoreOnT
      (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))) :
  qual_prop (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) s <->
  (lso_store s : LStoreT) !! LVFree y = Some (vconst c).
Proof.
  unfold qual_open_atom, mk_q_eq.
  cbn [qual_prop qual_lvars lvar_value_keys denote_lvar_value
    lstore_on_open_back lso_store].
  unfold lstore_on_open_back.
  cbn [lso_store storeAO_store].
  rewrite lstore_swap_lookup_inv_value.
  base_swap_normalize.
  tauto.
Qed.

Lemma const_type_qualifier_open_from_lookup c y (m : WfWorldT) :
  (forall σ, (m : WorldT) σ -> σ !! y = Some (vconst c)) ->
  m ⊨ type_qualifier_formula
    (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))).
Proof.
  intros Hlookup.
  apply type_qualifier_formula_models_iff.
  unfold logic_qualifier_denote, type_qualifier_lqual.
  cbn [lqual_dom lqual_prop].
  assert (Hlc :
      lc_lvars
        (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
  { rewrite const_qual_open_vars. unfold lc_lvars. set_solver. }
  assert (Hsub :
      lvars_fv
        (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))) ⊆
      world_dom (m : WorldT)).
  {
    rewrite const_qual_open_vars, lvars_fv_singleton_free;
    intros z Hz; apply elem_of_singleton in Hz; subst z;
    destruct (world_wf m) as [[σ Hσ] Hdom];
    pose proof (Hlookup σ Hσ) as Hy;
    assert (Hy_dom : y ∈ dom σ) by (apply elem_of_dom; eexists; exact Hy);
    rewrite (Hdom σ Hσ) in Hy_dom; exact Hy_dom.
  }
  exists Hlc. exists Hsub.
  unfold type_qualifier_holds_lworld.
  intros s. split.
  - intros Hprop.
    apply const_qual_open_prop_iff in Hprop.
    unfold lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lraw_world raw_worldA worldA_stores].
    destruct (world_wf m) as [[σ Hσ] _].
    exists (lstore_lift_free
      (storeA_restrict σ
        (lvars_fv
          (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))))).
    split.
    + exists (storeA_restrict σ
        (lvars_fv
          (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))))).
      split.
      * exists σ. split; [exact Hσ|reflexivity].
      * reflexivity.
    + transitivity (storeA_restrict (lstore_lift_free σ : LStoreT)
          (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
      * apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
      * apply map_eq. intros z.
        destruct (decide (z = LVFree y)) as [->|Hz].
        -- transitivity (Some (vconst c)).
           ++ apply storeA_restrict_lookup_some_2.
              ** rewrite lstore_lift_free_lookup_free.
                 apply Hlookup. exact Hσ.
              ** rewrite const_qual_open_vars. set_solver.
           ++ symmetry. exact Hprop.
        -- transitivity (@None value).
           ++ apply storeA_restrict_lookup_none_r.
              rewrite const_qual_open_vars. set_solver.
           ++ symmetry. apply not_elem_of_dom.
              rewrite lso_dom, const_qual_open_vars. set_solver.
  - intros Hmem.
    apply const_qual_open_prop_iff.
    unfold lstore_in_lworld_on, lworld_on_lift in Hmem.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hmem.
    destruct Hmem as [τ [Hτ Hs]].
    destruct Hτ as [σD [HσD ->]].
    destruct HσD as [σm [Hσm HσD]].
    rewrite <- HσD in Hs.
    rewrite (lstore_lift_free_restrict_fv_lvars_eq σm
      (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))
      Hlc) in Hs.
    rewrite <- Hs.
    apply storeA_restrict_lookup_some_2.
    + rewrite lstore_lift_free_lookup_free.
      apply Hlookup. exact Hσm.
    + rewrite const_qual_open_vars. set_solver.
Qed.

Lemma lqual_mlsubst_empty (q : LogicQualifierT) :
  lqual_mlsubst (∅ : LStoreT) q = q.
Proof.
  destruct q as [D P].
  cbn [lqual_mlsubst].
  apply logic_qualifier_ext.
  - change (D ∖ (∅ : lvset) = D).
    apply difference_empty_L.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    cbn [lqual_dom] in Hlw.
    enough (lworld_on_mlsubst_back D (∅ : LStoreT) w1 = w2) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    unfold lworld_on_mlsubst_back.
    cbn [lw].
    transitivity (@lw value (D ∖ dom (∅ : LStoreT)) w1).
    + apply wfworldA_ext. apply worldA_ext.
      * simpl.
        unfold storeA_restrict.
        replace (map_restrict value (∅ : LStoreT) D) with (∅ : LStoreT)
          by (symmetry; apply map_restrict_idemp;
              rewrite dom_empty_L; apply empty_subseteq).
        change (dom (∅ : LStoreT)) with (∅ : lvset).
        apply set_eq. intros z.
        rewrite elem_of_union, elem_of_empty. tauto.
      * intros σ. simpl.
        unfold storeA_restrict.
        replace (map_restrict value (∅ : LStoreT) D) with (∅ : LStoreT)
          by (symmetry; apply map_restrict_idemp;
              rewrite dom_empty_L; apply empty_subseteq).
        split.
        -- intros (σ1 & σ2 & Hσ1 & -> & _ & ->).
           replace (σ1 ∪ ∅) with σ1 by (symmetry; apply map_union_empty).
           exact Hσ1.
        -- intros Hσ.
           exists σ, (∅ : LStoreT). repeat split; try exact Hσ; try reflexivity.
           ++ exact (ResourceAlgebra.rawA_compat_unit_r
                (@lw value _ w1 : LWorldT) σ (∅ : LStoreT) Hσ eq_refl).
           ++ symmetry. apply map_union_empty.
    + exact Hlw.
Qed.

Lemma formula_msubst_store_empty (σ : StoreT) (φ : FormulaT) :
  dom (σ : gmap atom value) = ∅ ->
  formula_msubst_store σ φ = φ.
Proof.
  intros Hdom.
  assert (Hσ : (σ : gmap atom value) = ∅).
  {
    apply (map_eq (M:=gmap atom)). intros x.
    apply not_elem_of_dom.
    rewrite Hdom. set_solver.
  }
  rewrite Hσ.
  unfold formula_msubst_store, lstore_lift_free.
  rewrite kmap_empty.
  induction φ; cbn [formula_mlsubst];
    try (rewrite ?IHφ1, ?IHφ2, ?IHφ; reflexivity).
  - rewrite lqual_mlsubst_empty. reflexivity.
  - rewrite dom_empty_L, difference_empty_L, IHφ. reflexivity.
Qed.

Lemma res_fiber_from_projection_empty_store_dom
    (m mfib : WfWorldT) σ :
  res_fiber_from_projection m ∅ σ mfib ->
  dom (σ : StoreT) = ∅.
Proof.
  intros [Hproj _].
  pose proof (wfworld_store_dom (res_restrict m ∅) σ Hproj) as Hdom.
  change (dom (σ : StoreT) = world_dom (res_restrict m ∅ : WorldT)) in Hdom.
  simpl in Hdom. set_solver.
Qed.

Lemma res_fiber_from_projection_store_source
    (m mfib : WfWorldT) X σ τ :
  res_fiber_from_projection m X σ mfib ->
  (mfib : WorldT) τ ->
  (m : WorldT) τ.
Proof.
  intros [_ Hfib] Hτ.
  destruct mfib as [wmfib Hwfib].
  cbn [raw_world raw_worldA world_stores] in Hτ, Hfib.
  change (wmfib = rawA_fiber (m : WorldT) σ) in Hfib.
  change (wmfib τ) in Hτ.
  rewrite Hfib in Hτ.
  exact (proj1 Hτ).
Qed.

Lemma const_fib_over_from_expr c y (m : WfWorldT) :
  m ⊨ expr_result_formula (tret (vconst c)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
      {[LVFree y]})
    (FOver (type_qualifier_formula
      (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
Proof.
  intros Hexpr.
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    pose proof (res_models_scoped _ _ Hexpr) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars, formula_fv_over,
      formula_fv_type_qualifier_formula.
    unfold qual_dom.
    rewrite !const_qual_open_vars.
    replace ({[LVFree y]} ∖ {[LVFree y]} : lvset) with (∅ : lvset)
      by set_solver.
    rewrite lvars_fv_empty, lvars_fv_singleton_free.
    rewrite formula_fv_expr_result_formula in Hscope.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hscope.
    rewrite lvars_fv_union, lvars_fv_empty, lvars_fv_singleton_free in Hscope.
    set_solver.
  - rewrite const_qual_open_vars.
    unfold lc_lvars. set_solver.
  - intros σ mfib Hproj.
    assert (HD :
        lvars_fv
          (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
            {[LVFree y]}) = ∅).
    {
      rewrite const_qual_open_vars.
      replace ({[LVFree y]} ∖ {[LVFree y]} : lvset) with (∅ : lvset)
        by set_solver.
      rewrite lvars_fv_empty. reflexivity.
    }
    rewrite formula_msubst_store_empty.
    + eapply res_models_over_intro_same_from_model.
      apply const_type_qualifier_open_from_lookup.
      intros τ Hτ.
      eapply expr_result_formula_ret_const_lookup; [exact Hexpr|].
      eapply res_fiber_from_projection_store_source; eauto.
    + eapply res_fiber_from_projection_empty_store_dom.
      rewrite <- HD. exact Hproj.
Qed.

Lemma const_fib_under_from_expr c y (m : WfWorldT) :
  m ⊨ expr_result_formula (tret (vconst c)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
      {[LVFree y]})
    (FUnder (type_qualifier_formula
      (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
Proof.
  intros Hexpr.
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    pose proof (res_models_scoped _ _ Hexpr) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars, formula_fv_under,
      formula_fv_type_qualifier_formula.
    unfold qual_dom.
    rewrite !const_qual_open_vars.
    replace ({[LVFree y]} ∖ {[LVFree y]} : lvset) with (∅ : lvset)
      by set_solver.
    rewrite lvars_fv_empty, lvars_fv_singleton_free.
    rewrite formula_fv_expr_result_formula in Hscope.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hscope.
    rewrite lvars_fv_union, lvars_fv_empty, lvars_fv_singleton_free in Hscope.
    set_solver.
  - rewrite const_qual_open_vars.
    unfold lc_lvars. set_solver.
  - intros σ mfib Hproj.
    assert (HD :
        lvars_fv
          (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
            {[LVFree y]}) = ∅).
    {
      rewrite const_qual_open_vars.
      replace ({[LVFree y]} ∖ {[LVFree y]} : lvset) with (∅ : lvset)
        by set_solver.
      rewrite lvars_fv_empty. reflexivity.
    }
    rewrite formula_msubst_store_empty.
    + eapply res_models_under_intro_same_from_model.
      apply const_type_qualifier_open_from_lookup.
      intros τ Hτ.
      eapply expr_result_formula_ret_const_lookup; [exact Hexpr|].
      eapply res_fiber_from_projection_store_source; eauto.
    + eapply res_fiber_from_projection_empty_store_dom.
      rewrite <- HD. exact Hproj.
Qed.

Local Ltac solve_const_guard :=
  repeat rewrite res_models_and_iff;
  repeat split;
  try apply context_ty_wf_formula_const_over_empty;
  try apply context_ty_wf_formula_const_under_empty;
  try apply context_ty_wf_formula_const_precise_empty;
  try apply basic_world_formula_empty;
  try apply expr_basic_typing_formula_ret_const_empty;
  try apply expr_total_formula_ret_const;
  try (unfold res_models; cbn; tauto).

Local Ltac solve_const_over_guard :=
  cbn [erase_ty];
  eapply res_models_and_intro_from_models;
  [apply context_ty_wf_formula_const_over_empty|];
  eapply res_models_and_intro_from_models;
  [apply basic_world_formula_empty|];
  eapply res_models_and_intro_from_models;
  [apply expr_basic_typing_formula_ret_const_empty|];
  apply expr_total_formula_ret_const.

Local Ltac solve_const_under_guard :=
  cbn [erase_ty];
  eapply res_models_and_intro_from_models;
  [apply context_ty_wf_formula_const_under_empty|];
  eapply res_models_and_intro_from_models;
  [apply basic_world_formula_empty|];
  eapply res_models_and_intro_from_models;
  [apply expr_basic_typing_formula_ret_const_empty|];
  apply expr_total_formula_ret_const.

Lemma res_models_true (m : WfWorldT) :
  m ⊨ FTrue.
Proof.
  unfold res_models. cbn.
  split.
  - unfold formula_scoped_in_world, formula_fv. cbn [formula_lvars].
    rewrite lvars_fv_empty. set_solver.
  - trivial.
Qed.

Local Lemma lvset_singleton_difference_self (v : logic_var) :
  ({[v]} ∖ {[v]} : lvset) = ∅.
Proof.
  apply set_eq. intros z.
  rewrite elem_of_difference, !elem_of_singleton, elem_of_empty.
  split; [intros [-> Hneq]; contradiction|tauto].
Qed.

Local Ltac const_scope_set :=
  intros z Hz;
  repeat rewrite elem_of_union in Hz;
  repeat rewrite elem_of_empty in Hz;
  repeat rewrite elem_of_singleton in Hz;
  repeat rewrite elem_of_union;
  repeat rewrite elem_of_empty;
  repeat rewrite elem_of_singleton;
  intuition subst; eauto.

Local Ltac const_forall_scope_norm :=
  unfold formula_scoped_in_world;
  rewrite ?formula_fv_forall, ?formula_fv_impl, ?formula_fv_fibvars,
    ?formula_fv_over, ?formula_fv_under, ?formula_fv_expr_result_formula,
    ?formula_fv_type_qualifier_formula, ?formula_fv_basic_world_formula;
  unfold qual_dom;
  cbn [tm_shift value_shift tm_lvars tm_lvars_at value_lvars_at lvar_value_keys];
  rewrite ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?dom_insert_L, ?dom_empty_L;
  rewrite ?const_qual_open_vars;
  rewrite ?const_qual_vars_bound;
  rewrite ?set_swap_empty;
  rewrite ?lvset_singleton_difference_self;
  rewrite ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free.

Local Ltac solve_const_forall_closed_scope :=
  const_forall_scope_norm;
  try replace (lvars_fv ({[LVBound 0]} ∪ ∅ : lvset)) with (∅ : aset)
    by (rewrite lvars_fv_union, lvars_fv_singleton_bound,
          lvars_fv_empty; set_solver);
  try replace (lvars_fv ({[LVBound 0]} : lvset)) with (∅ : aset)
    by apply lvars_fv_singleton_bound;
  try replace (lvars_fv ({[(#ₗ0)%ctx]} : lvset)) with (∅ : aset)
    by apply lvars_fv_singleton_bound;
  try rewrite (lvars_fv_singleton_bound 0);
  match goal with
  | |- _ ⊆ world_dom (?m : WorldT) =>
      const_scope_set
  end.

Local Ltac solve_const_forall_open_scope :=
  const_forall_scope_norm;
  lazymatch goal with
  | |- context[lvars_fv ({[LVFree ?y]} ∪ ∅ : lvset)] =>
      replace (lvars_fv ({[LVFree y]} ∪ ∅ : lvset)) with ({[y]} : aset)
        by (rewrite lvars_fv_union, lvars_fv_singleton_free,
              lvars_fv_empty; set_solver)
  | _ => idtac
  end;
  lazymatch goal with
  | |- context[lvars_fv ({[LVFree ?y]} : lvset)] =>
      replace (lvars_fv ({[LVFree y]} : lvset)) with ({[y]} : aset)
        by (symmetry; apply lvars_fv_singleton_free)
  | _ => idtac
  end;
  lazymatch goal with
  | |- context[lvars_fv (set_swap ?a ?b ∅)] =>
      replace (lvars_fv (set_swap a b ∅)) with (∅ : aset)
        by (rewrite set_swap_empty, lvars_fv_empty; reflexivity)
  | _ => idtac
  end;
  match goal with
  | Hdom : world_dom (?n : WorldT) = world_dom (?m : WorldT) ∪ extA_out ?F,
    HFout : ext_out ?F = {[?y]} |- _ =>
      unfold ext_out in HFout;
      rewrite Hdom, HFout;
      const_scope_set
  | |- _ => const_scope_set
  end.

Lemma const_over_denotation_gas gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Σ)
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
  induction gas as [|gas IH]; cbn [denot_ty_lvar_gas].
  - rewrite denot_relevant_env_const_over_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [solve_const_over_guard | apply res_models_true].
  - rewrite denot_relevant_env_const_over_atom_env_empty.
    eapply res_models_and_intro_from_models; [solve_const_over_guard|].
    eapply res_models_forall_intro.
    + solve_const_forall_closed_scope.
    + exists (∅ : aset). intros y _ F HFin HFout my Hext.
      pose proof (res_extend_by_dom m F my Hext) as Hdom.
      rewrite !formula_open_impl.
      rewrite formula_open_basic_world_formula.
      rewrite lvar_store_open_one_bound0_singleton.
      rewrite formula_open_expr_result_formula_shift0.
      2:{ constructor. constructor. }
      2:{ cbn [fv_tm fv_value]. set_solver. }
      rewrite formula_open_fibvars, formula_open_over.
      rewrite type_qualifier_formula_open
        by (unfold mk_q_eq, qual_dom, qual_vars;
            cbn [qual_lvars lvar_value_keys];
            rewrite lvars_fv_union, lvars_fv_singleton_bound,
              lvars_fv_empty; set_solver).
      eapply res_models_impl_intro_scoped.
      * solve_const_forall_open_scope.
      * solve_const_forall_open_scope.
      * intros _.
        eapply res_models_impl_intro_scoped.
        -- solve_const_forall_open_scope.
        -- solve_const_forall_open_scope.
        -- intros Hexpr.
           replace
             (set_swap (LVBound 0) (LVFree y)
                (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
             with
             (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
             {[LVFree y]}).
           2:{
             rewrite const_qual_vars_bound, const_qual_open_vars.
             replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
               with (∅ : lvset)
               by (symmetry; apply lvset_singleton_difference_self).
             replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
               with (∅ : lvset)
               by (symmetry; apply lvset_singleton_difference_self).
             rewrite set_swap_empty.
             reflexivity.
           }
           exact (const_fib_over_from_expr c y my Hexpr).
Qed.

Lemma const_under_denotation_gas gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas gas (atom_env_to_lty_env Σ)
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
  induction gas as [|gas IH]; cbn [denot_ty_lvar_gas].
  - rewrite denot_relevant_env_const_under_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [solve_const_under_guard | apply res_models_true].
  - rewrite denot_relevant_env_const_under_atom_env_empty.
    eapply res_models_and_intro_from_models; [solve_const_under_guard|].
    eapply res_models_forall_intro.
    + solve_const_forall_closed_scope.
    + exists (∅ : aset). intros y _ F HFin HFout my Hext.
      pose proof (res_extend_by_dom m F my Hext) as Hdom.
      rewrite !formula_open_impl.
      rewrite formula_open_basic_world_formula.
      rewrite lvar_store_open_one_bound0_singleton.
      rewrite formula_open_expr_result_formula_shift0.
      2:{ constructor. constructor. }
      2:{ cbn [fv_tm fv_value]. set_solver. }
      rewrite formula_open_fibvars, formula_open_under.
      rewrite type_qualifier_formula_open
        by (unfold mk_q_eq, qual_dom, qual_vars;
            cbn [qual_lvars lvar_value_keys];
            rewrite lvars_fv_union, lvars_fv_singleton_bound,
              lvars_fv_empty; set_solver).
      eapply res_models_impl_intro_scoped.
      * solve_const_forall_open_scope.
      * solve_const_forall_open_scope.
      * intros _.
        eapply res_models_impl_intro_scoped.
        -- solve_const_forall_open_scope.
        -- solve_const_forall_open_scope.
        -- intros Hexpr.
           replace
             (set_swap (LVBound 0) (LVFree y)
                (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
             with
             (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
             {[LVFree y]}).
           2:{
             rewrite const_qual_vars_bound, const_qual_open_vars.
             replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
               with (∅ : lvset)
               by (symmetry; apply lvset_singleton_difference_self).
             replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
               with (∅ : lvset)
               by (symmetry; apply lvset_singleton_difference_self).
             rewrite set_swap_empty.
             reflexivity.
           }
           exact (const_fib_under_from_expr c y my Hexpr).
Qed.

Lemma const_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ denot_ctx_under Σ CtxEmpty ->
  erase_ctx_under Σ CtxEmpty ⊢ₑ
    tret (vconst c) ⋮ erase_ty (const_precise_ty c) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ CtxEmpty))
    (const_precise_ty c) (tret (vconst c)).
Proof.
  intros _ _.
  unfold const_precise_ty, precise_ty, over_ty, under_ty.
  destruct gas as [|gas'].
  - unfold erase_ctx_under. cbn [erase_ctx].
    replace (Σ ∪ erase_ctx CtxEmpty) with Σ
      by (change (erase_ctx CtxEmpty) with (∅ : gmap atom ty);
          symmetry; apply map_union_empty).
    change (m ⊨
      FAnd
        (FAnd
          (context_ty_wf_formula
            (denot_relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c)))
            (CTInter
              (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
              (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))))
          (FAnd (basic_world_formula
            (denot_relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c))))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env (atom_env_to_lty_env Σ)
                  (CTInter
                    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
                  (tret (vconst c)))
                (tret (vconst c)) (TBase (base_ty_of_const c)))
              (expr_total_formula (tret (vconst c))))))
        FTrue).
    rewrite denot_relevant_env_const_precise_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [ eapply res_models_and_intro_from_models;
        [ exact (context_ty_wf_formula_const_precise_empty c m)
        | eapply res_models_and_intro_from_models;
          [ exact (basic_world_formula_empty m)
          | eapply res_models_and_intro_from_models;
            [ exact (expr_basic_typing_formula_ret_const_empty c m)
            | exact (expr_total_formula_ret_const c m) ] ] ]
      | exact (res_models_true m) ].
  - unfold erase_ctx_under. cbn [erase_ctx].
    replace (Σ ∪ erase_ctx CtxEmpty) with Σ
      by (change (erase_ctx CtxEmpty) with (∅ : gmap atom ty);
          symmetry; apply map_union_empty).
    change (m ⊨
      FAnd
        (FAnd
          (context_ty_wf_formula
            (denot_relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c)))
            (CTInter
              (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
              (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))))
          (FAnd (basic_world_formula
            (denot_relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c))))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env (atom_env_to_lty_env Σ)
                  (CTInter
                    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
                  (tret (vconst c)))
                (tret (vconst c)) (TBase (base_ty_of_const c)))
              (expr_total_formula (tret (vconst c))))))
        (FAnd
          (denot_ty_lvar_gas gas' (atom_env_to_lty_env Σ)
            (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
            (tret (vconst c)))
          (denot_ty_lvar_gas gas' (atom_env_to_lty_env Σ)
            (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
            (tret (vconst c))))).
    rewrite denot_relevant_env_const_precise_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [ eapply res_models_and_intro_from_models;
        [ exact (context_ty_wf_formula_const_precise_empty c m)
        | eapply res_models_and_intro_from_models;
          [ exact (basic_world_formula_empty m)
          | eapply res_models_and_intro_from_models;
            [ exact (expr_basic_typing_formula_ret_const_empty c m)
            | exact (expr_total_formula_ret_const c m) ] ] ]
      | eapply res_models_and_intro_from_models;
        [ exact (const_over_denotation_gas gas' Σ c m)
        | exact (const_under_denotation_gas gas' Σ c m) ] ].
Qed.

Lemma letd_intro_denotation
    gas (Σ1 Σ2 : lty_env) τ1 τ2 e1 e2
    (m m1 m2 mx1 mbody : WfWorldT)
    (Hc : world_compat m1 m2) (Hcbody : world_compat m2 mx1)
    (Fx : FiberExtensionT) (x : atom) :
  lty_env_to_atom_env (Σ1 ∪ Σ2) ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  res_product m1 m2 Hc ⊑ m ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m1 Fx mx1 ->
  res_product m2 mx1 Hcbody ⊑ mbody ->
  m1 ⊨ denot_ty_lvar_gas (cty_depth τ1) Σ1 τ1 e1 ->
  mbody ⊨ denot_ty_lvar_gas gas
    (<[LVFree x := erase_ty τ1]> Σ2) τ2 (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas gas
    (Σ1 ∪ Σ2) τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma lam_intro_denotation
    gas (Σ : lty_env) τx τ e (L : aset) (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ
    tret (vlam (erase_ty τx) e) ⋮ erase_ty (CTArrow τx τ) ->
  (forall y F my, y ∉ L ->
    res_extend_by m F my ->
    my ⊨ denot_ty_lvar_gas (cty_depth τx)
      (<[LVFree y := erase_ty τx]> Σ) τx (tret (vfvar y)) ->
    my ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := erase_ty τx]> Σ) ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ denot_ty_lvar_gas gas
    Σ (CTArrow τx τ) (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma lamd_intro_denotation
    gas (Σ : lty_env) τx τ e (L : aset) (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ
    tret (vlam (erase_ty τx) e) ⋮ erase_ty (CTWand τx τ) ->
  (forall y marg Hc, y ∉ L ->
    marg ⊨ denot_ty_lvar_gas (cty_depth τx)
      (<[LVFree y := erase_ty τx]> Σ) τx (tret (vfvar y)) ->
    res_product marg m Hc ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := erase_ty τx]> Σ) ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ denot_ty_lvar_gas gas
    Σ (CTWand τx τ) (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma app_elim_denotation
    gas (Σ : lty_env) τx τ v1 x (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ tapp v1 (vfvar x) ⋮ erase_ty ({0 ~> x} τ) ->
  m ⊨ denot_ty_lvar_gas (cty_depth (CTArrow τx τ))
    Σ (CTArrow τx τ) (tret v1) ->
  m ⊨ denot_ty_lvar_gas (cty_depth τx) Σ τx (tret (vfvar x)) ->
  m ⊨ denot_ty_lvar_gas gas
    Σ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma appd_elim_denotation
    gas (Σ1 Σ2 : lty_env) τx τ v1 x
    (m mfun marg : WfWorldT) (Hc : world_compat mfun marg) :
  lty_env_to_atom_env (Σ1 ∪ Σ2) ⊢ₑ
    tapp v1 (vfvar x) ⋮ erase_ty ({0 ~> x} τ) ->
  res_product mfun marg Hc ⊑ m ->
  mfun ⊨ denot_ty_lvar_gas (cty_depth (CTWand τx τ))
    Σ1 (CTWand τx τ) (tret v1) ->
  marg ⊨ denot_ty_lvar_gas (cty_depth τx) Σ2 τx (tret (vfvar x)) ->
  m ⊨ denot_ty_lvar_gas gas
    (Σ1 ∪ Σ2) ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fix_intro_denotation
    gas (Σ : lty_env) τx τ vf b t (L : aset) (m : WfWorldT) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  lty_env_to_atom_env Σ ⊢ₑ
    tret (vfix (TBase b →ₜ t) vf) ⋮ erase_ty (CTArrow τx τ) ->
  (forall y F my, y ∉ L ->
    res_extend_by m F my ->
    my ⊨ denot_ty_lvar_gas (cty_depth τx)
      (<[LVFree y := erase_ty τx]> Σ) τx (tret (vfvar y)) ->
    my ⊨ denot_ty_lvar_gas
      (cty_depth (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)))
      (<[LVFree y := erase_ty τx]> Σ)
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
      (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ denot_ty_lvar_gas gas
    Σ (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

Lemma fixd_intro_denotation
    gas (Σ : lty_env) τx τ vf b t (L : aset) (m : WfWorldT) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  lty_env_to_atom_env Σ ⊢ₑ
    tret (vfix (TBase b →ₜ t) vf) ⋮ erase_ty (CTWand τx τ) ->
  (forall y marg Hc, y ∉ L ->
    marg ⊨ denot_ty_lvar_gas (cty_depth τx)
      (<[LVFree y := erase_ty τx]> Σ) τx (tret (vfvar y)) ->
    res_product marg m Hc ⊨ denot_ty_lvar_gas
      (cty_depth (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)))
      (<[LVFree y := erase_ty τx]> Σ)
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
      (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ denot_ty_lvar_gas gas
    Σ (CTWand τx τ) (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

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
  unfold basic_context_ty, basic_context_ty_lvars in Hbasic.
  destruct Hbasic as [Hτ _].
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
  unfold basic_context_ty, basic_context_ty_lvars in Hbasic.
  destruct Hbasic as [Hτ _].
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
Admitted.

Lemma appop_intro_denotation
    gas (Σ : gmap atom ty) op x τarg τres (m : WfWorldT) :
  cty_depth ({0 ~> x} τres) <= gas ->
  basic_context_ty ∅ τarg ->
  basic_context_ty ∅ τres ->
  Σ !! x = Some (erase_ty τarg) ->
  Σ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (denot_ctx (CtxBind x τarg) ⊫
    denot_ty_in_ctx (CtxBind x τarg) ({0 ~> x} τres)
      (tprim op (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas (cty_depth τarg) (atom_env_to_lty_env Σ)
    τarg (tret (vfvar x)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env Σ) ({0 ~> x} τres) (tprim op (vfvar x)).
Proof.
  intros Hgas Hbasic_arg Hbasic_res Hlookup _ Hop Harg.
  rewrite denot_ty_lvar_gas_saturate by exact Hgas.
  pose proof (res_models_denot_ty_lvar_gas_env_agree_on
    (cty_depth τarg)
    (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
    τarg (tret (vfvar x)) ({[LVFree x]}) m
    (denot_relevant_lvars_basic_ret_fvar_subset x τarg Hbasic_arg)
    (atom_env_to_lty_env_restrict_singleton_lookup
      Σ x (erase_ty τarg) Hlookup)
    Harg) as Harg_single.
  assert (Harg_bind : m ⊨ denot_ctx (CtxBind x τarg)).
  {
    eapply denot_ctx_bind_from_arg_denotation; eauto.
  }
  pose proof (Hop m Harg_bind) as Hres_single.
  unfold denot_ty_in_ctx, denot_ty in Hres_single.
  change (erase_ctx (CtxBind x τarg))
    with (<[x := erase_ty τarg]> (∅ : gmap atom ty)) in Hres_single.
  eapply res_models_denot_ty_lvar_gas_env_agree_on
    with (Σ1 := atom_env_to_lty_env
        (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
      (X := {[LVFree x]});
    [ apply denot_relevant_lvars_basic_open_tprim_fvar_subset;
      exact Hbasic_res
    | symmetry;
      apply atom_env_to_lty_env_restrict_singleton_lookup;
      exact Hlookup
    | exact Hres_single ].
Qed.

Lemma match_both_intro_denotation
    (Σ : lty_env) v τt τf et ef
    (m mt mf : WfWorldT) (Hdef : raw_sum_defined mt mf) :
  lty_env_to_atom_env Σ ⊢ₑ
    tmatch v et ef ⋮ erase_ty (CTSum τt τf) ->
  res_sum mt mf Hdef ⊑ m ->
  mt ⊨ denot_ty_lvar_gas (cty_depth (bool_precise_ty true)) Σ
    (bool_precise_ty true) (tret v) ->
  mf ⊨ denot_ty_lvar_gas (cty_depth (bool_precise_ty false)) Σ
    (bool_precise_ty false) (tret v) ->
  mt ⊨ denot_ty_lvar_gas (cty_depth τt) Σ τt et ->
  mf ⊨ denot_ty_lvar_gas (cty_depth τf) Σ τf ef ->
  m ⊨ denot_ty_lvar_gas (cty_depth (CTSum τt τf))
    Σ (CTSum τt τf) (tmatch v et ef).
Proof.
Admitted.

Lemma match_true_intro_denotation
    gas (Σ : lty_env) v τ et ef (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ tmatch v et ef ⋮ erase_ty τ ->
  m ⊨ FImpl
    (denot_ty_lvar_gas (cty_depth (bool_precise_ty false)) Σ
      (bool_precise_ty false) (tret v))
    FFalse ->
  m ⊨ denot_ty_lvar_gas (cty_depth (bool_precise_ty true)) Σ
    (bool_precise_ty true) (tret v) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ et ->
  lty_env_to_atom_env Σ ⊢ₑ ef ⋮ erase_ty τ ->
  m ⊨ denot_ty_lvar_gas gas
    Σ τ (tmatch v et ef).
Proof.
Admitted.

Lemma match_false_intro_denotation
    gas (Σ : lty_env) v τ et ef (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ tmatch v et ef ⋮ erase_ty τ ->
  m ⊨ FImpl
    (denot_ty_lvar_gas (cty_depth (bool_precise_ty true)) Σ
      (bool_precise_ty true) (tret v))
    FFalse ->
  m ⊨ denot_ty_lvar_gas (cty_depth (bool_precise_ty false)) Σ
    (bool_precise_ty false) (tret v) ->
  lty_env_to_atom_env Σ ⊢ₑ et ⋮ erase_ty τ ->
  m ⊨ denot_ty_lvar_gas gas Σ τ ef ->
  m ⊨ denot_ty_lvar_gas gas
    Σ τ (tmatch v et ef).
Proof.
Admitted.

End ContextTypeDenotationCases.
