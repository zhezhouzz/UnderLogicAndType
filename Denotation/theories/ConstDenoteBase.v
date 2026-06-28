(** * Denotation.ConstDenoteBase

    Constant and primitive-operation direct denotation support for
    Fundamental. *)

From Denotation Require Import Context DenotationSetMapFacts TypeEquivCore
  TypeEquivTermBase TypeEquivTermResult TypeEquivFiberBaseCore TypeEquivFiberBaseProjected TypeEquiv
  TypePersistBase.
From CoreLang Require Import StrongNormalization.

Section ConstDenoteBase.

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
    unfold lstore_instantiate_tm,
      lstore_instantiate_tm_at, lstore_instantiate_value_at.
    cbn [lstore_instantiate_tm_split_at
      lstore_instantiate_value_split_at].
    apply must_terminating_tret. constructor.
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
  qual_vars (mk_q_eq (vfvar y) (vconst c)) =
  {[LVFree y]}.
Proof.
  unfold mk_q_eq, qual_vars.
  cbn [qual_lvars lvar_value_keys].
  set_solver.
Qed.

Lemma const_qual_open_eq c y :
  qual_open_atom 0 y (mk_q_eq (vbvar 0) (vconst c)) =
  mk_q_eq (vfvar y) (vconst c).
Proof.
  apply qual_ext.
  - rewrite qual_open_atom_vars.
    unfold mk_q_eq, qual_vars.
    cbn [qual_lvars lvar_value_keys].
    change (set_swap (LVBound 0) (LVFree y) ({[LVBound 0]} ∪ ∅) =
      {[LVFree y]} ∪ ∅).
    rewrite set_swap_union, set_swap_singleton, set_swap_empty.
    base_swap_normalize.
    set_solver.
  - intros s1 s2 Hs.
    cbn [qual_open_atom mk_q_eq qual_prop qual_lvars lvar_value_keys
      denote_lvar_value].
    unfold lstore_on_open_back.
    cbn [lso_store storeAO_store].
    rewrite lstore_swap_lookup_inv_value.
    base_swap_normalize.
    replace (lso_store s2 !! LVFree y) with
      (lso_store s1 !! LVFree y) by (rewrite Hs; reflexivity).
    tauto.
Qed.

Lemma const_qual_vars_bound c :
  qual_vars (mk_q_eq (vbvar 0) (vconst c)) = {[LVBound 0]}.
Proof.
  unfold mk_q_eq, qual_vars.
  cbn [qual_lvars lvar_value_keys].
  set_solver.
Qed.

Lemma const_qual_bound_no_free c y :
  LVFree y ∉ qual_vars (mk_q_eq (vbvar 0) (vconst c)).
Proof.
  rewrite const_qual_vars_bound.
  apply not_elem_of_singleton_2. discriminate.
Qed.

Lemma const_qual_vars_bound_without_bound c :
  qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]} = ∅.
Proof.
  rewrite const_qual_vars_bound.
  set_solver.
Qed.

Lemma const_swapped_removed_vars_fv_empty c y :
  lvars_fv
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars (mk_q_eq (vbvar 0) (vconst c)) ∖ {[LVBound 0]})) = ∅.
Proof.
  rewrite const_qual_vars_bound_without_bound, set_swap_empty, lvars_fv_empty.
  reflexivity.
Qed.

Lemma const_open_qual_vars_fv c y :
  lvars_fv (qual_vars (mk_q_eq (vfvar y) (vconst c))) = {[y]}.
Proof.
  rewrite const_qual_open_vars, lvars_fv_singleton_free.
  reflexivity.
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
  apply val_steps_self in Heval.
  inversion Heval. reflexivity.
Qed.

Lemma const_qual_open_prop_iff c y
    (s : LStoreOnT
      (qual_vars (mk_q_eq (vfvar y) (vconst c)))) :
  qual_prop (mk_q_eq (vfvar y) (vconst c)) s <->
  (lso_store s : LStoreT) !! LVFree y = Some (vconst c).
Proof.
  unfold mk_q_eq.
  cbn [qual_prop qual_lvars lvar_value_keys denote_lvar_value].
  tauto.
Qed.

Lemma const_type_qualifier_open_lookup c y (m : WfWorldT) σ :
  m ⊨ FAtom (mk_q_eq (vfvar y) (vconst c)) ->
  (m : WorldT) σ ->
  σ !! y = Some (vconst c).
Proof.
  intros Hqual Hσ.
  apply res_models_atom_exact_iff in Hqual.
  destruct Hqual as [Hlc [Hscope Hholds]].
  set (q := mk_q_eq (vfvar y) (vconst c)).
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
	      change (y ∈ lvars_fv (qual_vars (mk_q_eq (vfvar y) (vconst c)))).
	      rewrite const_qual_open_vars, lvars_fv_singleton_free.
	      better_set_solver.
	    }
	    subst s_store D q.
	    rewrite storeA_restrict_dom.
	    fold (qual_vars (mk_q_eq (vfvar y) (vconst c))).
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
      qual_vars (mk_q_eq (vfvar y) (vconst c))))
    as [_|Hy].
  - exact Hprop.
  - rewrite const_qual_open_vars in Hy.
    set_solver.
Defined.

Lemma const_type_qualifier_open_from_lookup c y (m : WfWorldT) :
  (forall σ, (m : WorldT) σ -> σ !! y = Some (vconst c)) ->
  m ⊨ FAtom (mk_q_eq (vfvar y) (vconst c)).
Proof.
  intros Hlookup.
  apply res_models_atom_exact_iff.
  assert (Hlc :
      lc_lvars
        (qual_vars (mk_q_eq (vfvar y) (vconst c)))).
  { rewrite const_qual_open_vars. unfold lc_lvars. set_solver. }
  assert (Hsub :
      lvars_fv
        (qual_vars (mk_q_eq (vfvar y) (vconst c))) ⊆
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
          (qual_vars (mk_q_eq (vfvar y) (vconst c)))))).
    split.
    + exists (storeA_restrict σ
        (lvars_fv
          (qual_vars (mk_q_eq (vfvar y) (vconst c))))).
      split.
      * exists σ. split; [exact Hσ|reflexivity].
      * reflexivity.
    + transitivity (storeA_restrict (lstore_lift_free σ : LStoreT)
          (qual_vars (mk_q_eq (vfvar y) (vconst c)))).
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
                  qual_vars (mk_q_eq (vfvar y) (vconst c))).
              { rewrite const_qual_open_vars. set_solver. }
              better_store_solver.
           ++ symmetry. exact Hprop.
        -- transitivity (@None value).
	           ++ apply storeA_restrict_lookup_none_r.
	              rewrite const_qual_open_vars. set_solver.
	           ++ symmetry. apply not_elem_of_dom.
	              rewrite lso_dom.
              unfold mk_q_eq.
              cbn [qual_lvars lvar_value_keys].
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
	      * unfold mk_q_eq.
	        cbn [qual_lvars lvar_value_keys].
	        apply lvars_fv_elem.
	        better_set_solver.
	    + unfold mk_q_eq.
	      cbn [qual_lvars lvar_value_keys].
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
  assert (Hmxdom_forall :
      world_dom (mx : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  {
    rewrite Hmxdom.
    destruct HFx as [_ [_ Hout] _].
    unfold ext_out in Hout. rewrite Hout. reflexivity.
  }
  pose proof (Hforall_open y HyL mx Hmxdom_forall Hmxrestrict) as Hopened.
  rewrite !formula_open_impl in Hopened.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened.
  2:{ apply lvars_shift_from_lc.
      apply relevant_env_closed. exact HΔclosed. }
  2:{
    rewrite lvars_shift_from_fv.
    intros Hyrel.
    assert (HyΔfv : y ∈ lvars_fv (dom Δ)).
    {
      apply lvars_fv_elem.
      pose proof (relevant_env_dom_subset_direct Δ τc (tret (vfvar x))) as Hsub.
      apply Hsub.
      apply (proj1 (lvars_fv_elem _ _)). exact Hyrel.
    }
    apply Hyfresh. better_set_solver.
  }
  2:{ apply lc_ret_iff_value; constructor. }
  2:{
    intros Hyfv. apply Hyfresh.
    cbn [fv_tm fv_value] in Hyfv.
    apply elem_of_singleton in Hyfv as ->.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
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
  assert (Hlc_rel : lc_lvars
      (dom (relevant_env Δ τc (tret (vfvar x))))).
  { apply relevant_env_closed. exact HΔclosed. }
  assert (Hexpr_y :
      mx ⊨ expr_result_formula_at
        (dom (relevant_env Δ τc (tret (vfvar x))))
        (tret (vfvar x)) (LVFree y)).
  {
    assert (Hfv_rel :
        tm_lvars (tret (vfvar x)) ⊆
        dom (relevant_env Δ τc (tret (vfvar x)))).
    {
      apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hsub_lvars.
      intros v Hv.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
      apply elem_of_singleton in Hv as ->.
      apply Hsub_lvars.
      unfold lvars_of_atoms.
      apply elem_of_map.
      exists x. split; [reflexivity|].
      cbn [fv_tm fv_value]. apply elem_of_singleton. reflexivity.
    }
    assert (Htotal_atom : expr_total_on_atom_world (tret (vfvar x)) m).
    { apply expr_total_formula_to_atom_world. exact Htotal. }
    pose proof Hworld as Hworld_parts.
    apply basic_world_formula_models_iff in Hworld_parts
      as [_ [Hscope_world _]].
    eapply expr_result_formula_at_coarsen_domain with
      (Dbig := dom (relevant_env Δ τc (tret (vfvar x))) ∪
        tm_lvars (tret (vfvar x))).
    - intros v Hv. apply elem_of_union_l. exact Hv.
    - exact Hfv_rel.
    - intros Hybig.
      apply elem_of_union in Hybig as [Hyrel|Hytm].
      + apply HyΔ.
        pose proof (relevant_env_dom_subset_direct Δ τc (tret (vfvar x))) as Hsub.
        exact (Hsub _ Hyrel).
      + apply Hye.
        rewrite <- tm_lvars_fv.
        apply (proj2 (lvars_fv_elem _ _)). exact Hytm.
    - eapply (expr_result_formula_at_of_result_extends
        (dom (relevant_env Δ τc (tret (vfvar x))))
        (tret (vfvar x)) y Fx m).
      + exact Hlc_rel.
      + apply lc_ret_iff_value. constructor.
      + intros a Ha.
        apply Hscope_world.
        exact Ha.
      + intros a Ha.
        cbn [fv_tm fv_value] in Ha.
        apply elem_of_singleton in Ha as ->.
        exact Hxdom.
      + intros Hbad.
        apply elem_of_union in Hbad as [Hyrel|Hyfv].
        * apply Hyfresh.
          assert (HyΔfv : y ∈ lvars_fv (dom Δ)).
          {
            apply lvars_fv_elem.
            pose proof (relevant_env_dom_subset_direct Δ τc (tret (vfvar x))) as Hsub.
            apply Hsub. apply (proj1 (lvars_fv_elem _ _)). exact Hyrel.
          }
          better_set_solver.
        * apply Hye. exact Hyfv.
      + exact HFx.
      + exact Hext.
      + exact Htotal_atom.
      + eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
        apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
        exact (basic_tm_has_ltype_lvars _ _ _ Hty).
  }
	  rewrite (lvars_shift_from_lc_eq 0
	    (dom (relevant_env Δ τc (tret (vfvar x)))) Hlc_rel) in Hopened.
	  pose proof (res_models_impl_elim mx _ _ Hopened Hexpr_y)
	    as Hfib_over.
	  rewrite formula_open_over_typed_body_normalize in Hfib_over.
	  2:{ apply const_qual_bound_no_free. }
  pose proof (over_open_body_from_typed
    (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)) y mx Hfib_over)
    as Hbody_y.
  unfold over_open_body in Hbody_y.
  rewrite const_qual_open_eq in Hbody_y.
  assert (Hfib_empty :
      mx ⊨ FFibVars ∅
        (FOver (FAtom
          (mk_q_eq (vfvar y) (vconst c))))).
  {
    replace (∅ : lvset)
      with (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
        {[LVFree y]})
      by (rewrite const_qual_open_vars; better_set_solver).
    exact Hbody_y.
  }
  pose proof (res_models_fibvars_empty_elim mx _ Hfib_empty) as Hover.
  unfold res_models in Hover.
  cbn [formula_measure res_models_fuel] in Hover.
  destruct Hover as [_ [mo [Hsub_mx_mo Hqual_mo]]].
  assert (Hqual_model :
      mo ⊨ FAtom (mk_q_eq (vfvar y) (vconst c))).
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
  destruct (result_extension_store_lookup_output
    (tret (vfvar x)) y Fx m mx σmx HFx Hext Hσmx
    ltac:(exists vx; exact Heval_ret))
    as [vy [Hσmx_y_vy Heval_vy]].
  assert (Hx_restrict_dom :
      x ∈ dom (store_restrict σmx (fv_tm (tret (vfvar x))) : StoreT)).
  {
    change (x ∈ dom
      (storeA_restrict σmx (fv_tm (tret (vfvar x))) : gmap atom value)).
    apply elem_of_dom. exists vx.
    apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσmx_x).
    const_fast_set_side.
  }
  pose proof (tm_eval_in_store_ret_fvar_inv
    (store_restrict σmx (fv_tm (tret (vfvar x)))) x vy
    Hclosed_ret Hx_restrict_dom Heval_vy) as Hrestrict_x_vy.
  change ((storeA_restrict σmx (fv_tm (tret (vfvar x))) :
    gmap atom value) !! x = Some vy) in Hrestrict_x_vy.
  apply storeA_restrict_lookup_some in Hrestrict_x_vy as [_ Hσmx_x_vy].
  assert (Hvy_c : vy = vconst c) by congruence.
  change (((σ ∪ σe : StoreT) : gmap atom value) !! x = Some vy)
    in Hσmx_x_vy.
  change (((σ ∪ σe : StoreT) : gmap atom value) !! x = Some vx)
    in Hσmx_x.
  rewrite Hσmx_x in Hσmx_x_vy.
  inversion Hσmx_x_vy; subst vy.
  subst vx.
  reflexivity.
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
    (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
      {[LVFree y]})
    (FOver (FAtom (mk_q_eq (vfvar y) (vconst c)))).
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
          (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
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
    (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
      {[LVFree y]})
    (FUnder (FAtom (mk_q_eq (vfvar y) (vconst c)))).
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
          (qual_vars (mk_q_eq (vfvar y) (vconst c)) ∖
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
End ConstDenoteBase.
