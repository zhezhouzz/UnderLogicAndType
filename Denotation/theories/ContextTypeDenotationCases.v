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
Admitted.

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

Local Ltac solve_const_forall_scope :=
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
  try match goal with
  | |- context[lvars_fv ({[LVFree ?y]} ∖ {[LVFree ?y]})] =>
      replace ({[LVFree y]} ∖ {[LVFree y]} : lvset) with (∅ : lvset)
        by set_solver;
      rewrite lvars_fv_empty
  | |- context[lvars_fv ({[LVBound ?k]} ∖ {[LVBound ?k]})] =>
      replace ({[LVBound k]} ∖ {[LVBound k]} : lvset) with (∅ : lvset)
        by set_solver;
      rewrite lvars_fv_empty
  end;
  set_solver.

Lemma const_over_denotation_gas gas (Σ : lty_env) c (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas gas Σ
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
Admitted.

Lemma const_under_denotation_gas gas (Σ : lty_env) c (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas gas Σ
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
Admitted.

Lemma const_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ CtxEmpty ->
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
        [ exact (const_over_denotation_gas gas' (atom_env_to_lty_env Σ) c m)
        | exact (const_under_denotation_gas gas' (atom_env_to_lty_env Σ) c m) ] ].
Qed.

Lemma letd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ1 Γ2 τ1 τ2 e1 e2 (L : aset)
    (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ->
  erase_ctx_under Σ (CtxStar Γ1 Γ2) ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxStar Γ1 Γ2)))
    τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma lam_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ e (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vlam (erase_ty τx) e) ⋮ erase_ty (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTArrow τx τ) (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma lamd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ e (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vlam (erase_ty τx) e) ⋮ erase_ty (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTWand τx τ) (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma app_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ v1 x (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ tapp v1 (vfvar x) ⋮ erase_ty ({0 ~> x} τ) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τx (tret (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma appd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ1 Γ2 τx τ v1 x (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ->
  erase_ctx_under Σ (CtxStar Γ1 Γ2) ⊢ₑ
    tapp v1 (vfvar x) ⋮ erase_ty ({0 ~> x} τ) ->
  (denot_ctx_in_env Σ Γ1 ⊫
    denot_ty_in_ctx_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (denot_ctx_in_env Σ Γ2 ⊫
    denot_ty_in_ctx_under Σ Γ2 τx (tret (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxStar Γ1 Γ2)))
    ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fix_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ vf (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vfix (erase_ty (CTArrow τx τ)) vf) ⋮ erase_ty (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (CTArrow τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTArrow τx τ) (tret (vfix (erase_ty (CTArrow τx τ)) vf)).
Proof.
Admitted.

Lemma fixd_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ τx τ vf (L : aset) (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tret (vfix (erase_ty (CTWand τx τ)) vf) ⋮ erase_ty (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        (CTWand (CTWand τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    (CTWand τx τ) (tret (vfix (erase_ty (CTWand τx τ)) vf)).
Proof.
Admitted.

Lemma appop_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ op x τarg τres (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (denot_ctx (CtxBind x τarg) ⊫
    denot_ty_in_ctx (CtxBind x τarg) ({0 ~> x} τres)
      (tprim op (vfvar x))) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τarg (tret (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ))
    ({0 ~> x} τres) (tprim op (vfvar x)).
Proof.
Admitted.

Lemma match_both_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γt Γf v τt τf et ef (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ (CtxSum Γt Γf) ->
  erase_ctx_under Σ (CtxSum Γt Γf) ⊢ₑ
    tmatch v et ef ⋮ erase_ty (CTSum τt τf) ->
  (denot_ctx_in_env Σ Γt ⊫
    denot_ty_in_ctx_under Σ Γt (bool_precise_ty true) (tret v)) ->
  (denot_ctx_in_env Σ Γf ⊫
    denot_ty_in_ctx_under Σ Γf (bool_precise_ty false) (tret v)) ->
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt τt et) ->
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf τf ef) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ (CtxSum Γt Γf)))
    (CTSum τt τf) (tmatch v et ef).
Proof.
Admitted.

Lemma match_true_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ v τ et ef (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ tmatch v et ef ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty true) (tret v)) ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ et) ->
  erase_ctx_under Σ Γ ⊢ₑ ef ⋮ erase_ty τ ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ (tmatch v et ef).
Proof.
Admitted.

Lemma match_false_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) Γ v τ et ef (m : WfWorldT) :
  m ⊨ denot_ctx_in_env Σ Γ ->
  erase_ctx_under Σ Γ ⊢ₑ tmatch v et ef ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty false) (tret v)) ->
  erase_ctx_under Σ Γ ⊢ₑ et ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ ef) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ (tmatch v et ef).
Proof.
Admitted.

End ContextTypeDenotationCases.
