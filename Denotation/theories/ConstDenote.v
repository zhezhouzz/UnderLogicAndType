(** * Denotation.ConstDenote

    Constant and primitive-operation direct denotation support for
    Fundamental. *)

From Denotation Require Import Context TypeEquivCore
  TypeEquiv.

Section ConstDenote.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

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
    + constructor. constructor.
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

Lemma relevant_env_const_precise_atom_env_empty Σ c :
  relevant_env (atom_env_to_lty_env Σ)
    (CTInter
      (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
    (tret (vconst c)) = (∅ : lty_env).
Proof.
  apply relevant_env_empty.
  unfold relevant_lvars, precise_ty, over_ty, under_ty, mk_q_eq.
  cty_lvars_syntax_norm.
  unfold qual_vars.
  cbn [qual_lvars tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_singleton_bound0,
    ?lvars_at_depth_singleton_bound0_succ, ?lvars_at_depth_empty.
  set_solver.
Qed.

Lemma relevant_env_const_over_atom_env_empty Σ c :
  relevant_env (atom_env_to_lty_env Σ)
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)) = (∅ : lty_env).
Proof.
  apply relevant_env_empty.
  unfold relevant_lvars, mk_q_eq.
  cty_lvars_syntax_norm.
  unfold qual_vars.
  cbn [qual_lvars tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_singleton_bound0,
    ?lvars_at_depth_singleton_bound0_succ, ?lvars_at_depth_empty.
  set_solver.
Qed.

Lemma relevant_env_const_under_atom_env_empty Σ c :
  relevant_env (atom_env_to_lty_env Σ)
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)) = (∅ : lty_env).
Proof.
  apply relevant_env_empty.
  unfold relevant_lvars, mk_q_eq.
  cty_lvars_syntax_norm.
  unfold qual_vars.
  cbn [qual_lvars tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_singleton_bound0,
    ?lvars_at_depth_singleton_bound0_succ, ?lvars_at_depth_empty.
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

Lemma const_qual_dom_bound_fresh c y :
  y ∉ qual_dom (mk_q_eq (vbvar 0) (vconst c)).
Proof.
  unfold qual_dom.
  rewrite const_qual_vars_bound, lvars_fv_singleton_bound.
  set_solver.
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
      * apply lstore_lift_free_restrict_fv_lvars_eq.
      * apply map_eq. intros z.
        destruct (decide (z = LVFree y)) as [->|Hz].
        -- transitivity (Some (vconst c)).
           ++ assert (Hlook_y :
                  (lstore_lift_free σ : LStoreT) !! LVFree y =
                  Some (vconst c)).
              { rewrite lstore_lift_free_lookup_free. apply Hlookup. exact Hσ. }
              assert (Hin_y :
                  LVFree y ∈
                  qual_vars (qual_open_atom 0 y
                    (mk_q_eq (vbvar 0) (vconst c)))).
              { rewrite const_qual_open_vars. set_solver. }
              better_store_solver.
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
      (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))) in Hs.
    rewrite <- Hs.
    assert (Hlook_y :
        (lstore_lift_free σm : LStoreT) !! LVFree y =
        Some (vconst c)).
    { rewrite lstore_lift_free_lookup_free. apply Hlookup. exact Hσm. }
    assert (Hin_y :
        LVFree y ∈
        qual_vars (qual_open_atom 0 y
          (mk_q_eq (vbvar 0) (vconst c)))).
    { rewrite const_qual_open_vars. set_solver. }
    better_store_solver.
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

Local Ltac const_scope_set :=
  intros z Hz; set_solver.

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
  repeat match goal with
  | |- context[({[?v]} ∖ {[?v]} : lvset)] =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) by set_solver
  | H : context[({[?v]} ∖ {[?v]} : lvset)] |- _ =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) in H by set_solver
  end;
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
  m ⊨ ty_denote_gas gas (atom_env_to_lty_env Σ)
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - rewrite relevant_env_const_over_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [solve_const_over_guard | apply res_models_true].
  - rewrite relevant_env_const_over_atom_env_empty.
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
        by apply const_qual_dom_bound_fresh.
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
               by set_solver.
             replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
               with (∅ : lvset)
               by set_solver.
             rewrite set_swap_empty.
             reflexivity.
           }
           exact (const_fib_over_from_expr c y my Hexpr).
Qed.

Lemma const_under_denotation_gas gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ ty_denote_gas gas (atom_env_to_lty_env Σ)
    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vconst c)).
Proof.
  induction gas as [|gas IH]; cbn [ty_denote_gas].
  - rewrite relevant_env_const_under_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [solve_const_under_guard | apply res_models_true].
  - rewrite relevant_env_const_under_atom_env_empty.
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
        by apply const_qual_dom_bound_fresh.
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
               by set_solver.
             replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
               with (∅ : lvset)
               by set_solver.
             rewrite set_swap_empty.
             reflexivity.
           }
           exact (const_fib_under_from_expr c y my Hexpr).
Qed.

Lemma const_direct_denotation_gas_in_ctx
    gas (Σ : gmap atom ty) c (m : WfWorldT) :
  m ⊨ ctx_denote_under Σ CtxEmpty ->
  ctx_erasure_under Σ CtxEmpty ⊢ₑ
    tret (vconst c) ⋮ erase_ty (const_precise_ty c) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (ctx_erasure_under Σ CtxEmpty))
    (const_precise_ty c) (tret (vconst c)).
Proof.
  intros _ _.
  unfold const_precise_ty, precise_ty, over_ty, under_ty.
  destruct gas as [|gas'].
  - unfold ctx_erasure_under. cbn [erase_ctx].
    replace (Σ ∪ erase_ctx CtxEmpty) with Σ
      by (change (erase_ctx CtxEmpty) with (∅ : gmap atom ty);
          symmetry; apply map_union_empty).
    change (m ⊨
      FAnd
        (FAnd
          (context_ty_wf_formula
            (relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c)))
            (CTInter
              (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
              (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))))
          (FAnd (basic_world_formula
            (relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c))))
            (FAnd
              (expr_basic_typing_formula
                (relevant_env (atom_env_to_lty_env Σ)
                  (CTInter
                    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
                  (tret (vconst c)))
                (tret (vconst c)) (TBase (base_ty_of_const c)))
              (expr_total_formula (tret (vconst c))))))
        FTrue).
    rewrite relevant_env_const_precise_atom_env_empty.
    eapply res_models_and_intro_from_models;
      [ eapply res_models_and_intro_from_models;
        [ exact (context_ty_wf_formula_const_precise_empty c m)
        | eapply res_models_and_intro_from_models;
          [ exact (basic_world_formula_empty m)
          | eapply res_models_and_intro_from_models;
            [ exact (expr_basic_typing_formula_ret_const_empty c m)
            | exact (expr_total_formula_ret_const c m) ] ] ]
      | exact (res_models_true m) ].
  - unfold ctx_erasure_under. cbn [erase_ctx].
    replace (Σ ∪ erase_ctx CtxEmpty) with Σ
      by (change (erase_ctx CtxEmpty) with (∅ : gmap atom ty);
          symmetry; apply map_union_empty).
    change (m ⊨
      FAnd
        (FAnd
          (context_ty_wf_formula
            (relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c)))
            (CTInter
              (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
              (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))))
          (FAnd (basic_world_formula
            (relevant_env (atom_env_to_lty_env Σ)
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c))))
            (FAnd
              (expr_basic_typing_formula
                (relevant_env (atom_env_to_lty_env Σ)
                  (CTInter
                    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
                  (tret (vconst c)))
                (tret (vconst c)) (TBase (base_ty_of_const c)))
              (expr_total_formula (tret (vconst c))))))
        (FAnd
          (ty_denote_gas gas' (atom_env_to_lty_env Σ)
            (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
            (tret (vconst c)))
          (ty_denote_gas gas' (atom_env_to_lty_env Σ)
            (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
            (tret (vconst c))))).
    rewrite relevant_env_const_precise_atom_env_empty.
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

Lemma appop_intro_denotation
    gas (Σ : gmap atom ty) op x τarg τres (m : WfWorldT) :
  cty_depth ({0 ~> x} τres) <= gas ->
  basic_context_ty ∅ τarg ->
  basic_context_ty ∅ τres ->
  Σ !! x = Some (erase_ty τarg) ->
  Σ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (ctx_denote (CtxBind x τarg) ⊫
    ty_denote_ctx (CtxBind x τarg) ({0 ~> x} τres)
      (tprim op (vfvar x))) ->
  m ⊨ ty_denote_gas (cty_depth τarg) (atom_env_to_lty_env Σ)
    τarg (tret (vfvar x)) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env Σ) ({0 ~> x} τres) (tprim op (vfvar x)).
Proof.
  intros Hgas Hbasic_arg Hbasic_res Hlookup _ Hop Harg.
  rewrite ty_denote_gas_saturate by exact Hgas.
  pose proof (res_models_ty_denote_gas_env_agree_on
    (cty_depth τarg)
    (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
    τarg (tret (vfvar x)) ({[LVFree x]}) m
    (relevant_lvars_basic_ret_fvar_subset x τarg Hbasic_arg)
    (atom_env_restrict_singleton_lookup
      Σ x (erase_ty τarg) Hlookup)
    Harg) as Harg_single.
  assert (Harg_bind : m ⊨ ctx_denote (CtxBind x τarg)).
  {
    eapply ctx_denote_bind_from_arg_denotation; eauto.
  }
  pose proof (Hop m Harg_bind) as Hres_single.
  unfold ty_denote_ctx, ty_denote in Hres_single.
  change (erase_ctx (CtxBind x τarg))
    with (<[x := erase_ty τarg]> (∅ : gmap atom ty)) in Hres_single.
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := atom_env_to_lty_env
        (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
      (X := {[LVFree x]});
    [ apply relevant_lvars_basic_open_tprim_fvar_subset;
      exact Hbasic_res
    | symmetry;
      apply atom_env_restrict_singleton_lookup;
      exact Hlookup
    | exact Hres_single ].
Qed.
End ConstDenote.
