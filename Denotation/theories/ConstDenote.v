(** * Denotation.ConstDenote

    Constant and primitive-operation direct denotation support for
    Fundamental. *)

From Denotation Require Import Context TypeEquivCore
  TypeEquiv.

Section ConstDenote.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Local Ltac const_fast_set_side :=
  cbn [fv_tm fv_value] in *;
  repeat match goal with
  | H : ?a ∈ {[?b]} |- _ =>
      apply elem_of_singleton in H; subst
  end;
  repeat match goal with
  | |- ?a ∈ {[?a]} => apply elem_of_singleton; reflexivity
  end.

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

Lemma const_type_qualifier_open_lookup c y (m : WfWorldT) σ :
  m ⊨ FAtom
      (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ->
  (m : WorldT) σ ->
  σ !! y = Some (vconst c).
Proof.
  intros Hqual Hσ.
  apply res_models_atom_exact_iff in Hqual.
  destruct Hqual as [Hlc [Hscope Hholds]].
  set (q := qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))).
  set (D := qual_vars q).
  set (s_store := storeA_restrict (lstore_lift_free σ : LStoreT) D).
  assert (Hs_dom : dom (s_store : gmap logic_var value) = D).
  {
    assert (Hscope_y : y ∈ dom (σ : StoreT)).
    {
	      change (y ∈ dom (σ : gmap atom value)).
	      rewrite (wfworld_store_dom m σ Hσ).
	      apply Hscope.
	      subst D q.
	      change (y ∈ lvars_fv
	        (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
	      rewrite const_qual_open_vars, lvars_fv_singleton_free.
	      better_set_solver.
	    }
	    subst s_store D q.
	    rewrite storeA_restrict_dom.
	    fold (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))).
	    rewrite const_qual_open_vars, dom_lstore_lift_free.
	    assert (Hlv_y : LVFree y ∈ lvars_of_atoms (dom (σ : StoreT))).
	    {
	      unfold lvars_of_atoms. apply elem_of_map.
	      exists y. split; [reflexivity|exact Hscope_y].
	    }
	    better_set_solver.
	  }
  pose (s :=
    ({| storeAO_store := s_store; storeAO_dom := Hs_dom |}
      : StoreAOn (K := logic_var) (V := value) D)).
  assert (Hmem : lstore_in_lworld_on s (lworld_on_lift D m Hlc Hscope)).
  {
    unfold s, lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lso_store lraw_world raw_worldA worldA_stores storeAO_store].
    exists (lstore_lift_free (store_restrict σ (lvars_fv D))).
    split.
    - exists (store_restrict σ (lvars_fv D)).
      split.
      + exists σ. split; [exact Hσ|reflexivity].
      + reflexivity.
    - apply lstore_lift_free_restrict_fv_lvars_eq.
  }
  pose proof (proj2 (Hholds s) Hmem) as Hprop.
  apply const_qual_open_prop_iff in Hprop.
  change ((s_store : LStoreT) !! LVFree y = Some (vconst c)) in Hprop.
  subst s_store.
  change (((storeA_restrict (lstore_lift_free σ : LStoreT) D
      : gmap logic_var value) !! LVFree y) =
    Some (vconst c)) in Hprop.
  unfold storeA_restrict, map_restrict in Hprop.
  apply map_lookup_filter_Some in Hprop as [Hprop _].
  rewrite lstore_lift_free_lookup_free in Hprop.
  subst D q.
  destruct (decide (LVFree y ∈
      qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))))
    as [_|Hy].
  - exact Hprop.
  - rewrite const_qual_open_vars in Hy.
    set_solver.
Defined.

Lemma const_type_qualifier_open_from_lookup c y (m : WfWorldT) :
  (forall σ, (m : WorldT) σ -> σ !! y = Some (vconst c)) ->
  m ⊨ FAtom
    (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))).
Proof.
  intros Hlookup.
  apply res_models_atom_exact_iff.
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
	              rewrite lso_dom.
	              unfold qual_open_atom, mk_q_eq.
	              cbn [qual_lvars lvar_value_keys].
	              base_swap_normalize.
	              set_solver.
  - intros Hmem.
    apply const_qual_open_prop_iff.
    unfold lstore_in_lworld_on, lworld_on_lift in Hmem.
	    cbn [lw lraw_world raw_worldA worldA_stores] in Hmem.
	    destruct Hmem as [τ [Hτ Hs]].
	    destruct Hτ as [σD [HσD ->]].
	    destruct HσD as [σm [Hσm HσD]].
	    change ((lso_store s : LStoreT) !! LVFree y = Some (vconst c)).
	    rewrite <- Hs.
	    rewrite <- HσD.
	    apply storeA_restrict_lookup_some_2.
	    + rewrite lstore_lift_free_lookup_free.
	      apply storeA_restrict_lookup_some_2.
	      * apply Hlookup. exact Hσm.
	      * unfold qual_open_atom, mk_q_eq.
	        cbn [qual_lvars lvar_value_keys].
	        base_swap_normalize.
	        apply lvars_fv_elem.
	        better_set_solver.
	    + unfold qual_open_atom, mk_q_eq.
	      cbn [qual_lvars lvar_value_keys].
	      base_swap_normalize.
	      better_set_solver.
Qed.

Lemma ty_denote_over_ret_fvar_const_lookup
    gas (Δ : lty_env) x c (m : WfWorldT) σ :
  lty_env_closed Δ ->
  m ⊨ ty_denote_gas (S gas) Δ
    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
    (tret (vfvar x)) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst c).
Proof.
  intros HΔclosed Hden Hσ.
  set (τc := CTOver (base_ty_of_const c)
    (mk_q_eq (vbvar 0) (vconst c))) in *.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hden) as Hguard.
  pose proof Hguard as Hguard_parts.
  repeat rewrite res_models_and_iff in Hguard_parts.
  destruct Hguard_parts as [_ [Hworld [Hbasic Htotal]]].
  assert (Hxdom : x ∈ world_dom (m : WorldT)).
  { exact (ty_denote_gas_ret_fvar_world_dom (S gas) Δ τc x m Hden). }
  pose proof Hden as Hden_body.
  cbn [ty_denote_gas] in Hden_body.
  rewrite res_models_and_iff in Hden_body.
  destruct Hden_body as [_ Hforall].
  destruct (res_models_forall_rev m _ Hforall) as [L Hforall_open].
  pose (y := fresh_for
    (L ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Δ) ∪ {[x]})).
  assert (Hyfresh :
      y ∉ L ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Δ) ∪ {[x]}).
  { subst y. apply fresh_for_not_in. }
  assert (HyL : y ∉ L) by better_set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by better_set_solver.
  assert (HyΔ : LVFree y ∉ dom Δ).
  {
    intros Hy.
    apply lvars_fv_elem in Hy.
    apply Hyfresh.
    better_set_solver.
  }
  assert (Hyx : y <> x).
  {
    intros ->. apply Hyfresh.
    apply elem_of_union_r. const_fast_set_side.
  }
  assert (Hye : y ∉ fv_tm (tret (vfvar x))).
  {
    intros Hyfv. apply Hyfresh.
    cbn [fv_tm fv_value] in Hyfv.
    apply elem_of_singleton in Hyfv as ->.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  destruct (expr_result_extension_witness_exists (tret (vfvar x)) y Hye)
    as [Fx HFx].
  assert (Happ : extension_applicable Fx m).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin. rewrite Hin.
      intros z Hz. const_fast_set_side. exact Hxdom.
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout. rewrite Hout.
      intros z Hz Hzm. const_fast_set_side. exact (Hym Hzm).
  }
  destruct (res_extend_by_exists m Fx Happ) as [mx Hext].
  pose proof (res_extend_by_dom m Fx mx Hext) as Hmxdom.
  pose proof (res_extend_by_restrict_base m Fx mx Hext) as Hmxrestrict.
  assert (Hopened :
      mx ⊨ formula_open 0 y
        (FImpl
          (expr_result_formula (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FFibVars
            (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})
            (FOver (FAtom
              (mk_q_eq (vbvar 0) (vconst c))))))).
  {
    eapply Hforall_open; [exact HyL| |exact Hmxrestrict].
    rewrite Hmxdom.
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in Hout. rewrite Hout. reflexivity.
  }
  rewrite !formula_open_impl in Hopened.
  rewrite formula_open_expr_result_formula_shift0 in Hopened.
  2:{ apply lc_ret_iff_value; constructor. }
  2:{
    intros Hyfv. apply Hyfresh.
    cbn [fv_tm fv_value] in Hyfv.
    apply elem_of_singleton in Hyfv as ->.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  rewrite formula_open_fibvars in Hopened.
  rewrite formula_open_over in Hopened.
  rewrite formula_open_atom in Hopened.
  replace
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]}))
    with
      (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
        {[LVFree y]})
    in Hopened.
  2:{
    rewrite const_qual_vars_bound, const_qual_open_vars.
    replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset)
      with (∅ : lvset) by better_set_solver.
    replace ({[LVFree y]} ∖ {[LVFree y]} : lvset)
      with (∅ : lvset) by better_set_solver.
    rewrite set_swap_empty. reflexivity.
  }
  assert (Hyden :
      mx ⊨ ty_denote_gas (S gas) (<[LVFree y := erase_ty τc]> Δ)
        τc (tret (vfvar y))).
  {
    eapply ty_denote_gas_result_ext; eauto.
  }
  pose proof (ty_denote_gas_ret_fvar_relevant_lookup
    (S gas) (<[LVFree y := erase_ty τc]> Δ) τc y mx Hyden)
    as Hylookup_rel.
  assert (Hexpr_y :
      mx ⊨ expr_result_formula (tret (vfvar x)) (LVFree y)).
  {
    assert (Hfv :
        lvars_of_atoms (fv_tm (tret (vfvar x))) ⊆
        dom (relevant_env Δ τc (tret (vfvar x)))).
    {
      apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      exact (basic_tm_has_ltype_lvars _ _ _ Hty).
    }
    assert (Htotal_atom : expr_total_on_atom_world (tret (vfvar x)) m).
    { apply expr_total_formula_to_atom_world. exact Htotal. }
    eapply expr_result_formula_of_result_extends; eauto.
  }
  pose proof (res_models_impl_elim mx _ _ Hopened Hexpr_y)
    as Hfib_over.
  assert (Hfib_empty :
      mx ⊨ FFibVars ∅
        (FOver (FAtom
          (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))))).
  {
    replace (∅ : lvset)
      with (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
        {[LVFree y]})
      by (rewrite const_qual_open_vars; better_set_solver).
    exact Hfib_over.
  }
  pose proof (res_models_fibvars_empty_elim mx _ Hfib_empty) as Hover.
  unfold res_models in Hover.
  cbn [formula_measure res_models_fuel] in Hover.
  destruct Hover as [_ [mo [Hsub_mx_mo Hqual_mo]]].
  assert (Hqual_model :
      mo ⊨ FAtom
        (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)))).
  {
    unfold res_models.
    models_fuel_irrel Hqual_mo.
  }
  assert (Hxσdom : x ∈ dom (σ : StoreT)).
  {
    change (x ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ). exact Hxdom.
  }
  destruct (σ !! x) as [vx|] eqn:Hσx.
  2:{
    apply not_elem_of_dom in Hσx. contradiction.
  }
  set (σX := store_restrict σ (ext_in Fx)).
  assert (HσXdom : dom (σX : StoreT) = ext_in Fx).
  {
    subst σX.
    eapply extA_projection_dom; eauto.
  }
  destruct (extA_rel_nonempty Fx σX HσXdom)
    as [we [σe [HFrel Hσe]]].
  set (σmx := σ ∪ σe : StoreT).
  assert (Hσmx : (mx : WorldT) σmx).
  {
    apply (proj2 (resA_extend_by_store_iff m Fx mx σmx Hext)).
    exists σ, we, σe. repeat split; eauto.
  }
  destruct Hsub_mx_mo as [_ Hsub_stores].
  assert (Hσmx_mo : (mo : WorldT) σmx).
  { apply Hsub_stores. exact Hσmx. }
  pose proof (const_type_qualifier_open_lookup
    c y mo σmx Hqual_model Hσmx_mo) as Hσmx_y_c.
  assert (Hσmx_x : σmx !! x = Some vx).
  {
    subst σmx.
    apply map_lookup_union_Some_raw. left. exact Hσx.
  }
  assert (Hclosed_ret_m : wfworld_closed_on (fv_tm (tret (vfvar x))) m).
  {
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
    exact (basic_tm_has_ltype_lvars _ _ _ Hty).
  }
  assert (Hrestrict_eq :
      store_restrict σmx (fv_tm (tret (vfvar x))) =
      store_restrict σ (fv_tm (tret (vfvar x)))).
  {
    apply storeA_map_eq. intros z.
    rewrite !storeA_restrict_lookup.
    destruct (decide (z ∈ fv_tm (tret (vfvar x)))) as [Hz|Hz].
    - cbn [fv_tm fv_value] in Hz.
      apply elem_of_singleton in Hz. subst z.
      transitivity (Some vx); [exact Hσmx_x|symmetry; exact Hσx].
    - reflexivity.
  }
  assert (Hclosed_ret :
      store_closed (store_restrict σmx (fv_tm (tret (vfvar x))))).
  { rewrite Hrestrict_eq. exact (Hclosed_ret_m σ Hσ). }
  assert (Heval_ret :
      tm_eval_in_store (store_restrict σmx (fv_tm (tret (vfvar x))))
        (tret (vfvar x)) vx).
  {
    apply tm_eval_in_store_ret_fvar_lookup; [exact Hclosed_ret|].
    apply storeA_restrict_lookup_some_2.
    - exact Hσmx_x.
    - const_fast_set_side.
  }
  pose proof (result_extension_store_lookup_output
    (tret (vfvar x)) y Fx m mx σmx vx HFx Hext Hσmx Heval_ret)
    as Hσmx_y_vx.
  congruence.
Qed.

Lemma bool_precise_true_ret_fvar_lookup
    Δ x (m : WfWorldT) σ :
  m ⊨ ty_denote (erase_ctx Δ) (bool_precise_ty true) (tret (vfvar x)) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst (cbool true)).
Proof.
  intros Hden Hσ.
  unfold ty_denote in Hden.
  unfold bool_precise_ty, precise_ty, over_ty, under_ty, bool_qual in Hden.
  cbn [cty_depth ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter.
  destruct Hinter as [Hover _].
  eapply ty_denote_over_ret_fvar_const_lookup with (gas := 0); eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma bool_precise_false_ret_fvar_lookup
    Δ x (m : WfWorldT) σ :
  m ⊨ ty_denote (erase_ctx Δ) (bool_precise_ty false) (tret (vfvar x)) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst (cbool false)).
Proof.
  intros Hden Hσ.
  unfold ty_denote in Hden.
  unfold bool_precise_ty, precise_ty, over_ty, under_ty, bool_qual in Hden.
  cbn [cty_depth ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hinter].
  rewrite res_models_and_iff in Hinter.
  destruct Hinter as [Hover _].
  eapply ty_denote_over_ret_fvar_const_lookup with (gas := 0); eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma const_fib_over_from_expr c y (m : WfWorldT) :
  m ⊨ expr_result_formula (tret (vconst c)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))) ∖
      {[LVFree y]})
    (FOver (FAtom
      (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
Proof.
  intros Hexpr.
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    pose proof (res_models_scoped _ _ Hexpr) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars, formula_fv_over,
      formula_fv_atom.
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
    (FUnder (FAtom
      (qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c))))).
Proof.
  intros Hexpr.
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    pose proof (res_models_scoped _ _ Hexpr) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars, formula_fv_under,
      formula_fv_atom.
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
  intros z Hz; better_set_solver.

Local Ltac const_forall_scope_norm :=
  unfold formula_scoped_in_world;
	  rewrite ?formula_fv_atom, ?formula_fv_forall, ?formula_fv_impl, ?formula_fv_fibvars,
	    ?formula_fv_over, ?formula_fv_under, ?formula_fv_expr_result_formula,
	    ?formula_fv_atom, ?formula_fv_basic_world_formula;
	  unfold basic_world_formula, expr_result_formula;
	  unfold FFiberAtom, qual_dom, qual_vars;
	  cbn [formula_lvars formula_lvars_at
	    tm_shift value_shift tm_lvars tm_lvars_at value_lvars_at
	    lvar_value_keys qual_lvars];
  repeat rewrite ?lvars_at_depth_union;
  rewrite ?lvars_at_depth_empty;
  rewrite ?lvars_at_depth_singleton_bound0_succ;
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
  try unfold formula_scoped_in_world;
  try const_forall_scope_norm;
  first [const_scope_set | better_set_solver].

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
	    + unfold formula_scoped_in_world.
	      replace (formula_fv
	        (FForall
	          (FImpl
	            (expr_result_formula (tm_shift 0 (tret (vconst c))) (LVBound 0))
	            (FFibVars
	              (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})
	              (FOver (FAtom
	                (mk_q_eq (vbvar 0) (vconst c)))))))) with (∅ : aset).
	      * set_solver.
	      * unfold formula_fv, formula_lvars.
	        unfold expr_result_formula, FFiberAtom,
	          expr_result_qual, qual_vars.
	        cbn [formula_lvars_at qual_lvars tm_shift value_shift
	          tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	        rewrite ?const_qual_vars_bound.
	        replace (∅ ∪ {[LVBound 0]} : lvset) with ({[LVBound 0]} : lvset)
	          by set_solver.
	        replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset) with (∅ : lvset)
	          by set_solver.
	        rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
	          ?lvars_at_depth_singleton_bound0_succ.
	        rewrite ?lvars_fv_union, ?lvars_fv_empty,
	          ?lvars_fv_singleton_bound.
	        set_solver.
    + exists (∅ : aset). intros y _ F HFin HFout my Hext.
	      pose proof (res_extend_by_dom m F my Hext) as Hdom.
	      rewrite !formula_open_impl.
	      rewrite formula_open_expr_result_formula_shift0.
	      2:{ constructor. constructor. }
	      2:{ cbn [fv_tm fv_value]. set_solver. }
	      rewrite formula_open_fibvars, formula_open_over.
		      rewrite formula_open_atom.
	      eapply res_models_impl_intro_scoped.
	      * solve_const_forall_open_scope.
	      * solve_const_forall_open_scope.
	      * intros Hexpr.
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
	    + unfold formula_scoped_in_world.
	      replace (formula_fv
	        (FForall
	          (FImpl
	            (expr_result_formula (tm_shift 0 (tret (vconst c))) (LVBound 0))
	            (FFibVars
	              (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})
	              (FUnder (FAtom
	                (mk_q_eq (vbvar 0) (vconst c)))))))) with (∅ : aset).
	      * set_solver.
	      * unfold formula_fv, formula_lvars.
	        unfold expr_result_formula, FFiberAtom,
	          expr_result_qual, qual_vars.
	        cbn [formula_lvars_at qual_lvars tm_shift value_shift
	          tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
	        rewrite ?const_qual_vars_bound.
	        replace (∅ ∪ {[LVBound 0]} : lvset) with ({[LVBound 0]} : lvset)
	          by set_solver.
	        replace ({[LVBound 0]} ∖ {[LVBound 0]} : lvset) with (∅ : lvset)
	          by set_solver.
	        rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
	          ?lvars_at_depth_singleton_bound0_succ.
	        rewrite ?lvars_fv_union, ?lvars_fv_empty,
	          ?lvars_fv_singleton_bound.
	        set_solver.
    + exists (∅ : aset). intros y _ F HFin HFout my Hext.
	      pose proof (res_extend_by_dom m F my Hext) as Hdom.
	      rewrite !formula_open_impl.
	      rewrite formula_open_expr_result_formula_shift0.
	      2:{ constructor. constructor. }
	      2:{ cbn [fv_tm fv_value]. set_solver. }
	      rewrite formula_open_fibvars, formula_open_under.
		      rewrite formula_open_atom.
	      eapply res_models_impl_intro_scoped.
	      * solve_const_forall_open_scope.
	      * solve_const_forall_open_scope.
	      * intros Hexpr.
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
  - unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    replace (store_restrict Σ (∅ : aset) ∪ (∅ : gmap atom ty))
      with (∅ : gmap atom ty)
      by (rewrite storeA_restrict_empty_set; symmetry; apply map_union_empty).
    change (m ⊨
      FAnd
        (FAnd
          (context_ty_wf_formula
            (relevant_env (atom_env_to_lty_env (∅ : gmap atom ty))
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c)))
            (CTInter
              (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
              (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))))
          (FAnd (basic_world_formula
            (relevant_env (atom_env_to_lty_env (∅ : gmap atom ty))
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c))))
            (FAnd
              (expr_basic_typing_formula
                (relevant_env (atom_env_to_lty_env (∅ : gmap atom ty))
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
  - unfold ctx_erasure_under. cbn [ctx_fv erase_ctx].
    replace (store_restrict Σ (∅ : aset) ∪ (∅ : gmap atom ty))
      with (∅ : gmap atom ty)
      by (rewrite storeA_restrict_empty_set; symmetry; apply map_union_empty).
    change (m ⊨
      FAnd
        (FAnd
          (context_ty_wf_formula
            (relevant_env (atom_env_to_lty_env (∅ : gmap atom ty))
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c)))
            (CTInter
              (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
              (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))))
          (FAnd (basic_world_formula
            (relevant_env (atom_env_to_lty_env (∅ : gmap atom ty))
              (CTInter
                (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
              (tret (vconst c))))
            (FAnd
              (expr_basic_typing_formula
                (relevant_env (atom_env_to_lty_env (∅ : gmap atom ty))
                  (CTInter
                    (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
                    (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
                  (tret (vconst c)))
                (tret (vconst c)) (TBase (base_ty_of_const c)))
              (expr_total_formula (tret (vconst c))))))
        (FAnd
          (ty_denote_gas gas' (atom_env_to_lty_env (∅ : gmap atom ty))
            (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
            (tret (vconst c)))
          (ty_denote_gas gas' (atom_env_to_lty_env (∅ : gmap atom ty))
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
        [ exact (const_over_denotation_gas gas' ∅ c m)
        | exact (const_under_denotation_gas gas' ∅ c m) ] ].
Qed.

Lemma appop_intro_denotation
    gas (Σ : gmap atom ty) op x τarg τres (m : WfWorldT) :
  cty_depth ({0 ~> x} τres) <= gas ->
  basic_context_ty ∅ τarg ->
  wf_context_ty_at 1 ∅ τres ->
  Σ !! x = Some (erase_ty τarg) ->
  Σ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (ctx_denote (CtxBind x τarg) ⊫
    ty_denote (erase_ctx (CtxBind x τarg)) ({0 ~> x} τres)
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
  unfold ty_denote in Hres_single.
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
