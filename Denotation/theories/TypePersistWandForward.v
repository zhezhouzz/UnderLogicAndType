(** * Denotation.TypePersistWandForward

    Forward Wand facts for persistent-over arguments. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivCore TypeEquivFiberBase TypeEquivBody TypeEquiv
  TypePersistBase TypePersistArrow TypePersistSingleton.
From ContextAlgebra Require Import ResourceAlgebra.

Section TypePersist.

Local Ltac persist_eta_fresh_from H :=
  clear -H; set_solver.

Local Ltac persist_outer_fresh_from H :=
  clear -H; set_solver.

Local Ltac persist_lvar_fresh_from H :=
  intros Hbad; apply lvars_fv_elem in Hbad; clear -H Hbad; set_solver.

Local Lemma empty_union_singleton_l y :
  ∅ ∪ {[y]} = ({[y]} : aset).
Proof.
  set_solver.
Qed.

Local Lemma over_y_fiber_store_dom
    bx φx y σy (n nfib : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  y ∈ world_dom (n : WorldT) ->
  res_fiber_from_projection n {[y]} σy nfib ->
  dom (σy : StoreT) = fv_cty (CTOver bx φx) ∪ {[y]}.
Proof.
  intros Hbasic_over Hy_world Hproj.
  pose proof (basic_over_empty_fv bx φx Hbasic_over) as Hfv_empty.
  destruct Hproj as [Hσproj _].
  pose proof (wfworld_store_dom (res_restrict n {[y]}) σy Hσproj)
    as Hdom.
  change (dom (σy : StoreT) =
    world_dom (res_restrict n {[y]} : WorldT)) in Hdom.
  rewrite res_restrict_dom in Hdom.
  rewrite Hdom, Hfv_empty.
  set_solver.
Qed.

Local Lemma over_y_fiber_restrict_singleton
    bx φx y σy (n nfib : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  y ∈ world_dom (n : WorldT) ->
  res_fiber_from_projection n {[y]} σy nfib ->
  res_restrict nfib (fv_cty (CTOver bx φx) ∪ {[y]}) =
    (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT).
Proof.
  intros Hbasic_over Hy_world Hproj.
  pose proof (basic_over_empty_fv bx φx Hbasic_over) as Hfv_empty.
  pose proof (over_y_fiber_store_dom
    bx φx y σy n nfib Hbasic_over Hy_world Hproj) as Hdomσ.
  rewrite Hfv_empty.
  replace (∅ ∪ {[y]} : aset) with ({[y]} : aset)
    by (symmetry; apply empty_union_singleton_l).
  eapply res_fiber_from_projection_restrict_singleton.
  - rewrite Hdomσ, Hfv_empty. set_solver.
  - exact Hproj.
Qed.

Lemma ty_denote_gas_over_ret_fvar_fiber_stable
    gas (Σ : lty_env) b φ y X σ
    (my mfib : WfWorldT) :
  lty_env_closed Σ ->
  y ∉ qual_dom φ ->
  formula_fv (over_open_body φ y) ⊆ X ->
  res_fiber_from_projection my X σ mfib ->
  my ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) (tret (vfvar y)) ->
  mfib ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) (tret (vfvar y)).
Proof.
  intros HΣclosed Hyφ HbodyX Hproj Hden.
  apply ty_denote_gas_over_ret_fvar_self_body_iff.
  - exact HΣclosed.
  - exact Hyφ.
  - split.
    + eapply ty_denote_gas_zero_res_subset.
      * eapply res_subset_fiber_source; eauto.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hden.
    + eapply fiberwise_stable_on_over_open_body; eauto.
      eapply ty_denote_gas_over_ret_fvar_self_body; eauto.
Qed.

Lemma wand_arg_fiber_models_persist_over_arg
    gas (Σ : lty_env) bx φx y σy
    (n nfib : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed Σ ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ qual_dom φx ->
  res_fiber_from_projection n {[y]} σy nfib ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := TBase bx]> Σ)
    (CTOver bx φx) (tret (vfvar y)) ->
  nfib ⊨ ty_denote_gas (S gas)
    (<[LVFree y := TBase bx]> Σ)
    (CTPersist (CTOver bx φx)) (tret (vfvar y)).
Proof.
  intros Hbasic_over HΣclosed HyΣ Hyφ Hproj Harg_over.
  pose proof (basic_over_empty_fv bx φx Hbasic_over) as Hfv_empty.
  assert (HΣy_closed : lty_env_closed (<[LVFree y := TBase bx]> Σ)).
  { apply lty_env_closed_insert_free. exact HΣclosed. }
  assert (Hy_world : y ∈ world_dom (n : WorldT)).
  {
    pose proof (ty_denote_gas_guard_formula gas
      (<[LVFree y := TBase bx]> Σ)
      (CTOver bx φx) (tret (vfvar y)) n Harg_over) as Hguard.
    unfold ty_guard_formula in Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [_ [Hworld _]].
    pose proof (res_models_scoped _ _ Hworld) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    apply Hscope.
    rewrite formula_fv_basic_world_formula.
    apply lvars_fv_elem.
    unfold relevant_env, relevant_lvars, lty_env_restrict_lvars.
    cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
      value_lvars_at lvar_value_keys].
    change (LVFree y ∈
      dom (storeA_restrict (<[LVFree y := TBase bx]> Σ)
        (lvars_at_depth 1 (qual_vars φx) ∪ {[LVFree y]}) : lty_env)).
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    - apply elem_of_dom. exists (TBase bx). rewrite lookup_insert_eq. reflexivity.
    - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  pose proof (over_y_fiber_store_dom
    bx φx y σy n nfib Hbasic_over Hy_world Hproj) as Hdomσ.
  pose proof (over_y_fiber_restrict_singleton
    bx φx y σy n nfib Hbasic_over Hy_world Hproj) as Hsingle.
  assert (Harg_over_fib :
      nfib ⊨ ty_denote_gas gas
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y))).
  {
    destruct gas as [|gas'].
    - eapply ty_denote_gas_zero_res_subset.
      + eapply res_subset_fiber_source; eauto.
      + exact Harg_over.
    - eapply ty_denote_gas_over_ret_fvar_fiber_stable.
      + exact HΣy_closed.
      + exact Hyφ.
      + eapply over_open_body_closed_arg_fv. exact Hbasic_over.
      + exact Hproj.
      + exact Harg_over.
  }
  eapply ty_denote_gas_persist_over_ret_fvar_intro_singleton.
  - exact HΣy_closed.
  - exact Hyφ.
  - exact Hdomσ.
  - exact Hsingle.
  - exact Harg_over_fib.
Qed.

Lemma fiberwise_joinable_on_ty_denote_gas_over
    X gas (Σ : lty_env) b φ e :
  lty_env_closed Σ ->
  lc_tm e ->
  tm_lvars e ⊆ dom (relevant_env Σ (CTOver b φ) e) ->
  X ⊆ lvars_fv (dom (relevant_env Σ (CTOver b φ) e)) ->
  fiberwise_joinable_on X (ty_denote_gas gas Σ (CTOver b φ) e).
Proof.
  intros HΣclosed Hlce HeD HXD.
  destruct gas as [|gas].
  - cbn [ty_denote_gas].
    apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_ty_guard_formula.
    + apply fiberwise_joinable_on_true.
  - cbn [ty_denote_gas].
    apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_ty_guard_formula.
    + apply fiberwise_joinable_on_forall.
      exists (X ∪ fv_tm e ∪ qual_dom φ ∪
        lvars_fv (dom (relevant_env Σ (CTOver b φ) e))).
      intros r Hr.
      rewrite formula_open_impl.
      apply fiberwise_joinable_on_impl.
      * rewrite formula_open_expr_result_formula_at_shift0.
        2:{ apply lvars_shift_from_lc. apply relevant_env_closed. exact HΣclosed. }
        2:{ rewrite lvars_shift_from_fv. clear -Hr. set_solver. }
        2:{ exact Hlce. }
        2:{ clear -Hr. set_solver. }
        rewrite (lvars_shift_from_lc_eq 0
          (dom (relevant_env Σ (CTOver b φ) e)))
          by (apply relevant_env_closed; exact HΣclosed).
        intros m σ mfib Hproj Hres.
        eapply expr_result_formula_at_fiber_stable.
        -- exact HXD.
        -- exact HeD.
        -- intros HrD.
           assert (HrDfv : r ∈
             lvars_fv (dom (relevant_env Σ (CTOver b φ) e))).
           { apply lvars_fv_elem. exact HrD. }
           apply Hr. clear -HrDfv. set_solver.
        -- exact Hproj.
        -- exact Hres.
      * rewrite formula_open_over_self_body_normalize.
        -- apply fiberwise_joinable_on_over_open_body.
           clear -Hr. set_solver.
        -- intros Hrvars.
           assert (Hrφ : r ∈ qual_dom φ).
           { unfold qual_dom. apply lvars_fv_elem. exact Hrvars. }
           apply Hr. clear -Hrφ. set_solver.
Qed.

Lemma fiberwise_joinable_on_ty_denote_gas_under
    X gas (Σ : lty_env) b φ e :
  lty_env_closed Σ ->
  lc_tm e ->
  tm_lvars e ⊆ dom (relevant_env Σ (CTUnder b φ) e) ->
  X ⊆ lvars_fv (dom (relevant_env Σ (CTUnder b φ) e)) ->
  fiberwise_joinable_on X (ty_denote_gas gas Σ (CTUnder b φ) e).
Proof.
  intros HΣclosed Hlce HeD HXD.
  destruct gas as [|gas].
  - cbn [ty_denote_gas].
    apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_ty_guard_formula.
    + apply fiberwise_joinable_on_true.
  - cbn [ty_denote_gas].
    apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_ty_guard_formula.
    + apply fiberwise_joinable_on_forall.
      exists (X ∪ fv_tm e ∪ qual_dom φ ∪
        lvars_fv (dom (relevant_env Σ (CTUnder b φ) e))).
      intros r Hr.
      rewrite formula_open_impl.
      apply fiberwise_joinable_on_impl.
      * rewrite formula_open_expr_result_formula_at_shift0.
        2:{ apply lvars_shift_from_lc. apply relevant_env_closed. exact HΣclosed. }
        2:{ rewrite lvars_shift_from_fv. clear -Hr. set_solver. }
        2:{ exact Hlce. }
        2:{ clear -Hr. set_solver. }
        rewrite (lvars_shift_from_lc_eq 0
          (dom (relevant_env Σ (CTUnder b φ) e)))
          by (apply relevant_env_closed; exact HΣclosed).
        intros m σ mfib Hproj Hres.
        eapply expr_result_formula_at_fiber_stable.
        -- exact HXD.
        -- exact HeD.
        -- intros HrD.
           assert (HrDfv : r ∈
             lvars_fv (dom (relevant_env Σ (CTUnder b φ) e))).
           { apply lvars_fv_elem. exact HrD. }
           apply Hr. clear -HrDfv. set_solver.
        -- exact Hproj.
        -- exact Hres.
      * rewrite formula_open_under_self_body_normalize.
        -- apply fiberwise_joinable_on_under_open_body.
           clear -Hr. set_solver.
        -- intros Hrvars.
           assert (Hrφ : r ∈ qual_dom φ).
           { unfold qual_dom. apply lvars_fv_elem. exact Hrvars. }
           apply Hr. clear -Hrφ. set_solver.
Qed.

Lemma tm_lvars_tapp_ret_fvar_fvar_relevant_env_dom
    (Σ : lty_env) τ f y Tf Ty :
  Σ !! LVFree f = Some Tf ->
  Σ !! LVFree y = Some Ty ->
  tm_lvars (tapp_tm (tret (vfvar f)) (vfvar y)) ⊆
  dom (relevant_env Σ τ (tapp_tm (tret (vfvar f)) (vfvar y))).
Proof.
  intros Hf Hy v Hv.
  unfold relevant_env, lty_env_restrict_lvars.
  rewrite storeA_restrict_dom.
  apply elem_of_intersection. split.
  - rewrite tm_lvars_tapp_tm_fvar in Hv.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hv.
    apply elem_of_union in Hv as [Hv|Hv];
      apply elem_of_singleton in Hv; subst v;
      eapply elem_of_dom_2; eauto.
  - unfold relevant_lvars. apply elem_of_union_r. exact Hv.
Qed.

Lemma singleton_lvar_subset_tapp_ret_fvar_fvar_relevant_env_dom
    (Σ : lty_env) τ f y Tf Ty :
  Σ !! LVFree f = Some Tf ->
  Σ !! LVFree y = Some Ty ->
  {[y]} ⊆
  lvars_fv (dom (relevant_env Σ τ (tapp_tm (tret (vfvar f)) (vfvar y)))).
Proof.
  intros Hf Hy a Ha.
  apply elem_of_singleton in Ha. subst a.
  apply lvars_fv_elem.
  apply (tm_lvars_tapp_ret_fvar_fvar_relevant_env_dom
    Σ τ f y Tf Ty Hf Hy).
  rewrite tm_lvars_tapp_tm_fvar.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
  set_solver.
Qed.

Lemma ty_denote_gas_over_result_body_elim
    gas (Σ : lty_env) b φ e r
    (m mr : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm e ->
  r ∉ world_dom (m : WorldT) ->
  r ∉ fv_tm e ->
  r ∉ lvars_fv (dom (relevant_env Σ (CTOver b φ) e)) ->
  r ∉ qual_dom φ ->
  world_dom (mr : WorldT) = world_dom (m : WorldT) ∪ {[r]} ->
  res_restrict mr (world_dom (m : WorldT)) = m ->
  mr ⊨ expr_result_formula_at
        (dom (relevant_env Σ (CTOver b φ) e)) e (LVFree r) ->
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) e ->
  mr ⊨ over_open_body φ r.
Proof.
  intros HΣclosed Hlce Hrm Hre HrΣ Hrφ Hdom Hbase Hres Hden.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hforall].
  pose proof (res_models_forall_open_named_fresh
    m mr r _ Hforall Hrm Hdom Hbase) as Himpl.
  cbn [formula_open] in Himpl.
  denotation_result_first_open_norm_in Himpl.
  pose proof (res_models_impl_elim _ _ _ Himpl Hres) as Helim.
  exact Helim.
Qed.

Lemma ty_denote_gas_under_result_body_elim
    gas (Σ : lty_env) b φ e r
    (m mr : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm e ->
  r ∉ world_dom (m : WorldT) ->
  r ∉ fv_tm e ->
  r ∉ lvars_fv (dom (relevant_env Σ (CTUnder b φ) e)) ->
  r ∉ qual_dom φ ->
  world_dom (mr : WorldT) = world_dom (m : WorldT) ∪ {[r]} ->
  res_restrict mr (world_dom (m : WorldT)) = m ->
  mr ⊨ expr_result_formula_at
        (dom (relevant_env Σ (CTUnder b φ) e)) e (LVFree r) ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) e ->
  mr ⊨ under_open_body φ r.
Proof.
  intros HΣclosed Hlce Hrm Hre HrΣ Hrφ Hdom Hbase Hres Hden.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hforall].
  pose proof (res_models_forall_open_named_fresh
    m mr r _ Hforall Hrm Hdom Hbase) as Himpl.
  cbn [formula_open] in Himpl.
  denotation_result_first_open_norm_in Himpl.
  pose proof (res_models_impl_elim _ _ _ Himpl Hres) as Helim.
  exact Helim.
Qed.

Lemma arrow_value_persist_over_arg_apply_singleton
    gas (Σ : lty_env) bx φx τr ef y σ
    (m my : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm ef ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  y ∉ world_dom (m : WorldT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ qual_dom φx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm ef ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  dom (σ : StoreT) = fv_cty (CTOver bx φx) ∪ {[y]} ->
  res_restrict my (fv_cty (CTOver bx φx) ∪ {[y]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas (S gas) Σ
    (CTPersist (CTOver bx φx)) τr ef ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := TBase bx]> Σ)
    (CTOver bx φx) (tret (vfvar y)) ->
	  my ⊨ ty_denote_gas (S gas)
	    (<[LVFree y := TBase bx]> Σ)
	    (cty_open 0 y τr)
	    (tapp_tm ef (vfvar y)).
Proof.
  intros HΣclosed Hlc_ef Hlc_over Hlcτr Hym HyΣ Hyφ Hyτr Hyef
    Hdom Hrestrict Hdomσ Hsingle Hvalue Harg_over.
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros HyD. apply HyΣ. apply lvars_fv_elem. exact HyD.
  }
  assert (Harg_persist_norm :
      my ⊨ ty_denote_gas (S gas)
        (<[LVFree y := TBase bx]> Σ)
        (CTPersist (CTOver bx φx)) (tret (vfvar y))).
  {
    eapply ty_denote_gas_persist_over_ret_fvar_intro_singleton.
    - apply lty_env_closed_insert_free. exact HΣclosed.
    - exact Hyφ.
    - exact Hdomσ.
    - exact Hsingle.
    - exact Harg_over.
  }
  pose proof (res_models_forall_open_named_fresh
    m my y
    (FImpl
      (ty_denote_gas (S gas)
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        (cty_shift 0 (CTPersist (CTOver bx φx)))
        (tret (vbvar 0)))
      (ty_denote_gas (S gas)
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        τr
        (tapp_tm (tm_shift 0 ef) (vbvar 0))))
    Hvalue Hym Hdom Hrestrict) as Hopened.
  cbn [formula_open] in Hopened.
  assert (Harg_persist_open :
      my ⊨ formula_open 0 y
        (ty_denote_gas (S gas)
          (typed_lty_env_bind Σ
            (erase_ty (CTPersist (CTOver bx φx))))
          (cty_shift 0 (CTPersist (CTOver bx φx)))
          (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{
      cbn [fv_tm fv_value]. intros Hin.
      rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at].
      intros Hbad. apply Hyφ.
      unfold qual_dom.
      rewrite lvars_fv_lvars_at_depth in Hbad.
      exact Hbad.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
    2:{
      unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at].
      intros Hbad. apply Hyφ.
      unfold qual_dom.
      rewrite lvars_fv_lvars_at_depth in Hbad.
      exact Hbad.
    }
    rewrite typed_lty_env_bind_open_current.
    2:{ exact HyΣlv. }
    2:{ exact HΣclosed. }
    change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx).
    exact Harg_persist_norm.
  }
  pose proof (res_models_impl_elim _ _ _ Hopened Harg_persist_open)
    as Hres_open.
	  rewrite formula_open_ty_denote_gas_singleton in Hres_open.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
	  2:{ exact Hyτr. }
  rewrite open_tapp_tm_shift_bvar0_lc in Hres_open by exact Hlc_ef.
	  rewrite typed_lty_env_bind_open_current in Hres_open.
  2:{ exact HyΣlv. }
  2:{ exact HΣclosed. }
  change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx) in Hres_open.
  exact Hres_open.
Qed.

Lemma wand_value_over_arg_to_persist_over_arg_plain
    gas_src gas_tgt (Σ : lty_env) bx φx τr ef (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm ef ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world m
    (wand_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (CTPersist (CTOver bx φx)) τr ef) ->
  m ⊨ wand_value_denote_gas_with ty_denote_gas gas_src Σ
    (CTOver bx φx) τr ef ->
  m ⊨ wand_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (CTPersist (CTOver bx φx)) τr ef.
Proof.
  intros HΣclosed Hlc_ef Hlc_over Hlcτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue.
  cbn [wand_value_denote_gas_with] in Hvalue |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  destruct gas_tgt' as [|gas_tgt'']; [lia|].
  eapply res_models_fbwand_intro.
  { exact Hscope_tgt. }
  destruct (res_models_fbwand_rev _ _ _ _ Hvalue) as [Lsrc Hsrc].
  exists (Lsrc ∪ lvars_fv (dom Σ) ∪ qual_dom φx ∪
    fv_cty τr ∪ fv_tm ef).
  intros η n Hc Hbind Hηfresh Hdom Harg_persist.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
	  rewrite formula_open_env_singleton in Harg_persist |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by
    persist_eta_fresh_from Hηfresh.
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyφ : y ∉ qual_dom φx) by
    persist_eta_fresh_from Hηfresh.
  assert (Hyτr : y ∉ fv_cty τr) by
    persist_eta_fresh_from Hηfresh.
  assert (Hyef : y ∉ fv_tm ef) by
    persist_eta_fresh_from Hηfresh.
  assert (Harg_over :
      n ⊨ formula_open 0 y
        (ty_denote_gas (S gas_src')
          (typed_lty_env_bind Σ (erase_ty (CTOver bx φx)))
          (cty_shift 0 (CTOver bx φx)) (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{ cbn [fv_tm fv_value]. apply not_elem_of_empty. }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2: exact Hlc_over.
    2:{
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    replace (lvar_store_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
      with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
    2:{
      symmetry.
      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
    }
    assert (Harg_over_base :
        n ⊨ ty_denote_gas (S gas_tgt'')
          (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
          (CTOver bx φx) (tret (vfvar y))).
    {
      rewrite formula_open_ty_denote_gas_singleton in Harg_persist.
      2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
      2:{ cbn [fv_tm fv_value]. apply not_elem_of_empty. }
      2:{
        rewrite cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφ.
      }
      replace (lvar_store_open_one 0 y
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx)))))
        with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
        in Harg_persist.
      2:{
        symmetry.
        apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
      }
      replace (cty_open 0 y
        (cty_shift 0 (CTPersist (CTOver bx φx))))
        with (CTPersist (CTOver bx φx)) in Harg_persist.
      2:{
        symmetry. apply cty_open_shift_from_lc_fresh.
        - cbn [lc_context_ty cty_lc_at]. exact Hlc_over.
        - unfold fv_cty, qual_dom in *.
          cbn [context_ty_lvars context_ty_lvars_at] in *.
          rewrite lvars_fv_lvars_at_depth.
          exact Hyφ.
      }
      cbn [open_tm open_value] in Harg_persist.
      eapply (ty_denote_gas_persist_over_ret_fvar_elim
        (S gas_tgt'')
        (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
        bx φx y).
      - apply lty_env_closed_insert_free. exact HΣclosed.
      - exact Hyφ.
      - exact Harg_persist.
    }
    rewrite (ty_denote_gas_saturate (S gas_src')
      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
      (CTOver bx φx) (tret (vfvar y)))
      by (cbn [cty_depth]; lia).
    rewrite (ty_denote_gas_saturate (S gas_tgt'')
      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
      (CTOver bx φx) (tret (vfvar y))) in Harg_over_base
      by (cbn [cty_depth]; lia).
    exact Harg_over_base.
  }
  assert (Hηfresh_src : open_env_atoms (<[0 := y]> (∅ : gmap nat atom)) ## Lsrc).
  {
    rewrite open_env_atoms_insert by apply lookup_empty.
    rewrite open_env_atoms_empty.
    clear -Hηfresh. set_solver.
  }
  pose proof (Hsrc (<[0 := y]> (∅ : gmap nat atom))
    n Hc Hbind Hηfresh_src Hdom Harg_over) as Hres.
  rewrite formula_open_env_singleton in Hres.
	  rewrite formula_open_ty_denote_gas_singleton in Hres.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
	  2:{ exact Hyτr. }
  rewrite open_tapp_tm_shift_bvar0_lc in Hres by exact Hlc_ef.
	  rewrite formula_open_ty_denote_gas_singleton.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
	  2:{ exact Hyτr. }
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc_ef.
	  replace (lvar_store_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ) in Hres.
  2:{
    symmetry.
    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
  }
  replace (lvar_store_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx)))))
    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
  2:{
    symmetry.
    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
  }
	  rewrite (ty_denote_gas_saturate (S gas_src')
	    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	    (cty_open 0 y τr)
	    (tapp_tm ef (vfvar y))) in Hres
	    by (rewrite cty_open_preserves_depth; lia).
	  rewrite (ty_denote_gas_saturate (S (S gas_tgt''))
	    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	    (cty_open 0 y τr)
	    (tapp_tm ef (vfvar y)))
	    by (rewrite cty_open_preserves_depth; lia).
 	  exact Hres.
Qed.

Lemma wand_result_first_open_value_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr Tf f (mf : WfWorldT) :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  f ∉ qual_dom φx ->
  f ∉ fv_cty τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world mf
    (wand_value_denote_gas_with ty_denote_gas gas_tgt
      (<[LVFree f := Tf]> Σ)
      (CTPersist (CTOver bx φx)) τr (tret (vfvar f))) ->
  mf ⊨ wand_value_denote_gas_with ty_denote_gas gas_src
    (<[LVFree f := Tf]> Σ)
    (CTOver bx φx) τr (tret (vfvar f)) ->
  mf ⊨ wand_value_denote_gas_with ty_denote_gas gas_tgt
    (<[LVFree f := Tf]> Σ)
    (CTPersist (CTOver bx φx)) τr (tret (vfvar f)).
Proof.
  intros HΣclosed HfΣ Hlc_over Hlcτr Hfφ Hfτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue_src.
  eapply wand_value_over_arg_to_persist_over_arg_plain.
  - apply lty_env_closed_insert_free; assumption.
  - constructor. constructor.
  - exact Hlc_over.
  - exact Hlcτr.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - exact Hscope_tgt.
  - exact Hvalue_src.
Qed.

Lemma ty_denote_gas_wand_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr e (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  m ⊨ ty_denote_gas (S gas_src) Σ
    (CTWand (CTOver bx φx) τr) e ->
  m ⊨ ty_denote_gas (S gas_tgt) Σ
    (CTWand (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros HΣclosed Hlc_over Hlcτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hden.
  pose proof (ty_denote_gas_guard (S gas_src) Σ
    (CTWand (CTOver bx φx) τr) e m Hden) as Hguard_src.
  change (m ⊨ ty_guard_formula
    (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
    (CTWand (CTOver bx φx) τr) e) in Hguard_src.
  assert (Hbody_src :
      m ⊨ FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ (CTWand (CTOver bx φx) τr) e)))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
              (erase_ty (CTWand (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0))))).
  {
    change (m ⊨ FAnd
      (ty_guard_formula
        (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
        (CTWand (CTOver bx φx) τr) e)
      (FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ (CTWand (CTOver bx φx) τr) e)))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
              (erase_ty (CTWand (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0)))))) in Hden.
    eapply res_models_and_elim_r. exact Hden.
  }
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
        (CTWand (CTPersist (CTOver bx φx)) τr) e).
  { apply ty_guard_wand_over_arg_to_persist_over_arg. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas_tgt) Σ
          (CTWand (CTPersist (CTOver bx φx)) τr) e)).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  destruct (res_models_forall_rev _ _ Hbody_src) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (Σg := relevant_env Σ (CTWand (CTOver bx φx) τr) e).
  exists (Lsrc ∪ lvars_fv (dom Σg) ∪ qual_dom φx ∪
    fv_cty τr ∪ fv_tm e).
  intros f Hf mf Hdom Hrestrict.
  assert (Hscope_open :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ
                  (CTWand (CTPersist (CTOver bx φx)) τr) e)))
              (tm_shift 0 e) (LVBound 0))
            (wand_value_denote_gas_with ty_denote_gas gas_tgt
              (typed_lty_env_bind
                (relevant_env Σ
                  (CTWand (CTPersist (CTOver bx φx)) τr) e)
                (erase_ty (CTWand (CTPersist (CTOver bx φx)) τr)))
              (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
              (tret (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  cbn [formula_open].
  eapply res_models_impl_intro.
  { cbn [formula_open] in Hscope_open. exact Hscope_open. }
  intros Hresult_tgt.
  assert (HfΣg : LVFree f ∉ dom (Σg : lty_env)).
  { persist_lvar_fresh_from Hf. }
  assert (Hfφ : f ∉ qual_dom φx).
  { persist_outer_fresh_from Hf. }
  assert (Hfτr : f ∉ fv_cty τr).
  { persist_outer_fresh_from Hf. }
  assert (Hopened_src :
      mf ⊨ formula_open 0 f
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0 (dom Σg))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind Σg
              (erase_ty (CTWand (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0))))).
  {
    subst Σg.
    apply Hsrc.
    - persist_outer_fresh_from Hf.
    - exact Hdom.
    - exact Hrestrict.
  }
  cbn [formula_open] in Hopened_src.
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_src Σg (CTOver bx φx) τr
    (erase_ty (CTWand (CTOver bx φx) τr)) f) in Hopened_src.
  2:{ subst Σg. apply relevant_env_closed. exact HΣclosed. }
  2:{ exact HfΣg. }
  2:{ exact Hlc_over. }
  2:{ exact Hlcτr. }
  2:{
    unfold fv_cty, context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2:{ exact Hfτr. }
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hresult_tgt)
    as Hvalue_src.
  assert (Hvalue_tgt_scope :
      formula_scoped_in_world mf
        (wand_value_denote_gas_with ty_denote_gas gas_tgt
          (<[LVFree f := erase_ty (CTWand (CTOver bx φx) τr)]> Σg)
          (CTPersist (CTOver bx φx)) τr (tret (vfvar f)))).
  {
    cbn [formula_open] in Hscope_open.
    pose proof (formula_scoped_impl_r _ _ _ Hscope_open) as Hscope_value.
    rewrite (formula_open_result_first_wand_value_ret_bvar0
      gas_tgt
      (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
      (CTPersist (CTOver bx φx)) τr
      (erase_ty (CTWand (CTPersist (CTOver bx φx)) τr)) f)
      in Hscope_value.
    2:{ apply relevant_env_closed. exact HΣclosed. }
    2:{
      subst Σg.
      change (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
        with (relevant_env Σ (CTWand (CTOver bx φx) τr) e).
      exact HfΣg.
    }
    2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
    2:{ exact Hlcτr. }
    2:{
      unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth.
      exact Hfφ.
    }
    2:{ exact Hfτr. }
    subst Σg.
    change (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
      with (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
      in Hscope_value.
    change (erase_ty (CTWand (CTPersist (CTOver bx φx)) τr))
      with (erase_ty (CTWand (CTOver bx φx) τr))
      in Hscope_value.
    exact Hscope_value.
  }
  change (mf ⊨
    (wand_value_denote_gas_with ty_denote_gas gas_tgt
      (typed_lty_env_bind
        (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
        (erase_ty (CTWand (CTPersist (CTOver bx φx)) τr)))
      (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
      (tret (vbvar 0)) ^^ f)%formula).
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_tgt
    (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
    (CTPersist (CTOver bx φx)) τr
    (erase_ty (CTWand (CTPersist (CTOver bx φx)) τr)) f).
  2:{ apply relevant_env_closed. exact HΣclosed. }
  2:{
    subst Σg.
    change (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
      with (relevant_env Σ (CTWand (CTOver bx φx) τr) e).
    exact HfΣg.
  }
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2:{ exact Hlcτr. }
  2:{
    unfold fv_cty, context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2:{ exact Hfτr. }
  subst Σg.
  change (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) τr) e).
  change (erase_ty (CTWand (CTPersist (CTOver bx φx)) τr))
    with (erase_ty (CTWand (CTOver bx φx) τr)).
  eapply wand_result_first_open_value_over_arg_to_persist_over_arg.
  - apply relevant_env_closed. exact HΣclosed.
  - exact HfΣg.
  - exact Hlc_over.
  - exact Hlcτr.
  - exact Hfφ.
  - exact Hfτr.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - exact Hvalue_tgt_scope.
  - exact Hvalue_src.
Qed.

Lemma ty_denote_wand_over_arg_to_persist_over_arg
    Δ bx φx τr e (m : WfWorldT) :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  m ⊨ ty_denote Δ (CTWand (CTOver bx φx) τr) e ->
  m ⊨ ty_denote Δ (CTWand (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros HΔclosed Hlc_over Hlcτr Hden.
  unfold ty_denote in *.
  cbn [cty_depth].
  eapply ty_denote_gas_wand_over_arg_to_persist_over_arg.
  - exact HΔclosed.
  - exact Hlc_over.
  - exact Hlcτr.
  - apply Nat.le_max_r.
  - apply Nat.le_max_r.
  - apply Nat.le_max_l.
  - apply Nat.le_max_l.
  - exact Hden.
Qed.

End TypePersist.
