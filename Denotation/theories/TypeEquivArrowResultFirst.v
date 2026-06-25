(** * Denotation.TypeEquivArrowResultFirst
    Result-first Arrow transport helpers. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivFiberTransport
  TypeEquivBody
  TypeEquivArrow.

Section TypeDenote.
Lemma arrow_result_first_arg_to_regular_open
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  lty_env_closed (relevant_env Σ (CTArrow τx τr) e) ->
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  lc_context_ty τx ->
  f ∉ fv_cty τx ->
  y ∉ fv_cty τx ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e)
            (erase_ty (CTArrow τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτx Hfτx Hyτx Harg.
  rewrite (formula_open_result_first_fun_arg_two gas
    (relevant_env Σ (CTArrow τx τr) e) τx
    (erase_ty (CTArrow τx τr)) f y) in Harg.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτx.
  2: exact Hfτx.
  2: exact Hyτx.
  rewrite lvar_store_insert_free_commute in Harg by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) f (erase_ty (CTArrow τx τr))) in Harg.
  2:{
    rewrite dom_insert_L.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. congruence.
    - exact (HfΣ Hbad).
  }
  2:{
    intros Hbad. apply Hfτx.
    rewrite <- context_ty_lvars_fv.
    apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  exact Harg.
Qed.

Lemma arrow_result_first_regular_to_arg_open
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  lty_env_closed (relevant_env Σ (CTArrow τx τr) e) ->
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  lc_context_ty τx ->
  f ∉ fv_cty τx ->
  y ∉ fv_cty τx ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e)
            (erase_ty (CTArrow τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτx Hfτx Hyτx Harg.
  rewrite (formula_open_result_first_fun_arg_two gas
    (relevant_env Σ (CTArrow τx τr) e) τx
    (erase_ty (CTArrow τx τr)) f y).
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτx.
  2: exact Hfτx.
  2: exact Hyτx.
  rewrite lvar_store_insert_free_commute by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) f (erase_ty (CTArrow τx τr))).
  2:{
    rewrite dom_insert_L.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. congruence.
    - exact (HfΣ Hbad).
  }
  2:{
    intros Hbad. apply Hfτx.
    rewrite <- context_ty_lvars_fv.
    apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  exact Harg.
Qed.

Lemma arrow_result_first_result_to_regular_open
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  lty_env_closed (relevant_env Σ (CTArrow τx τr) e) ->
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e)
            (erase_ty (CTArrow τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τr)
        (tapp_tm (tret (vbvar 1)) (vbvar 0)))) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτr Hffresh Hyfresh Hres.
  rewrite (formula_open_result_first_fun_result_two gas
    (relevant_env Σ (CTArrow τx τr) e) τx τr
    (erase_ty (CTArrow τx τr)) f y) in Hres.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτr.
  2: exact Hffresh.
  2: exact Hyfresh.
  exact Hres.
Qed.

Lemma arrow_result_first_regular_to_result_open
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  lty_env_closed (relevant_env Σ (CTArrow τx τr) e) ->
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e)
            (erase_ty (CTArrow τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τr)
        (tapp_tm (tret (vbvar 1)) (vbvar 0)))).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτr Hffresh Hyfresh Hres.
  rewrite (formula_open_result_first_fun_result_two gas
    (relevant_env Σ (CTArrow τx τr) e) τx τr
    (erase_ty (CTArrow τx τr)) f y).
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτr.
  2: exact Hffresh.
  2: exact Hyfresh.
  exact Hres.
Qed.

Local Lemma arrow_result_body_relevant_subset τx τr e f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  relevant_lvars (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ∖ {[LVFree y]} ∖ {[LVFree f]} ⊆
  relevant_lvars (CTArrow τx τr) e.
Proof.
  intros Hlcτr Hffresh Hyfresh.
  eapply result_first_result_body_relevant_subset; [exact Hlcτr| |].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - intros Hy. apply Hyfresh. apply elem_of_union_r. exact Hy.
Qed.

Lemma arrow_result_first_result_env_agree
    gas (Σ : lty_env) τx τr e1 e2
    (my : WfWorldT) f y :
  cty_lc_at 1 τr ->
  lc_tm (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  f <> y ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e1)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e2)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)).
Proof.
  intros Hlcτr Hlcapp Hfy Hffresh Hyfresh Hres.
  set (τbody := cty_open 0 y τr).
  set (ebody := tapp_tm (tret (vfvar f)) (vfvar y)).
  change (my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e1))) τbody ebody) in Hres.
  change (my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e2))) τbody ebody).
  pose proof (ty_denote_gas_env_agree_on gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e1)))
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e2)))
    τbody ebody (relevant_lvars τbody ebody)
    ltac:(reflexivity)) as Hagree.
  rewrite Hagree in Hres; [exact Hres|].
  unfold lty_env_restrict_lvars, relevant_env.
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars τbody ebody)) as [HvX|HvX];
    [|reflexivity].
  destruct (decide (v = LVFree y)) as [->|Hvy].
  { rewrite !lookup_insert. repeat case_decide; try congruence; reflexivity. }
  rewrite !lookup_insert_ne by congruence.
  destruct (decide (v = LVFree f)) as [->|Hvf].
  {
    rewrite !lookup_insert. repeat case_decide; try congruence; reflexivity.
  }
  rewrite !lookup_insert_ne by congruence.
  assert (Hvrel : v ∈ relevant_lvars (CTArrow τx τr) e1 /\
                  v ∈ relevant_lvars (CTArrow τx τr) e2).
  {
    assert (Hvsmall :
        v ∈ relevant_lvars τbody ebody ∖ {[LVFree y]} ∖ {[LVFree f]}).
    { set_solver. }
    unfold τbody, ebody in Hvsmall.
    split.
    - eapply arrow_result_body_relevant_subset.
      + exact Hlcτr.
      + exact Hffresh.
      + exact Hyfresh.
      + exact Hvsmall.
    - eapply arrow_result_body_relevant_subset.
      + exact Hlcτr.
      + exact Hffresh.
      + exact Hyfresh.
      + exact Hvsmall.
  }
  destruct Hvrel as [Hvrel1 Hvrel2].
  unfold relevant_lvars in Hvrel1, Hvrel2.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e1))
    as [_|Hbad];
    [|exfalso; exact (Hbad Hvrel1)].
  destruct (decide (v ∈ context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e2))
    as [_|Hbad];
    [|exfalso; exact (Hbad Hvrel2)].
  reflexivity.
Qed.

Local Lemma arrow_lc_lvars_shift_from k D :
  lc_lvars D ->
  lc_lvars (lvars_shift_from k D).
Proof.
  apply result_first_lc_lvars_shift_from.
Qed.

Local Lemma arrow_lvars_shift_from_lc_eq k D :
  lc_lvars D ->
  lvars_shift_from k D = D.
Proof.
  apply result_first_lvars_shift_from_lc_eq.
Qed.

Local Ltac arrow_expr_result_shift0_side :=
  first
    [ assumption
    | apply arrow_lc_lvars_shift_from; assumption
    | rewrite lvars_shift_from_fv; assumption ].


Lemma ty_denote_gas_tm_equiv_arrow_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e1)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e2)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
	        (tret (vbvar 0)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_equiv_source_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_src.
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e1 m Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hguard_tgt.
  repeat rewrite res_models_and_iff in Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_tgt.
  destruct Hguard_src as [Hwf_src [Hworld_src _]].
  destruct Hguard_tgt as [_ [Hworld_tgt _]].
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_arrow_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTArrow τx τr) e1)) _
    HlcΣ_wf_src Hbasic_arrow_src) as Hlc_arrow.
  cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
  destruct Hlc_arrow as [Hlcτx Hlcτr].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas)
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  assert (Hfib :
      tm_fiber_equiv_on m (lvars_fv (context_ty_lvars (CTArrow τx τr)))
        e1 e2).
  {
    apply tm_equiv_on_to_fiber_equiv.
    eapply typed_total_equiv_tm_equiv. exact Hequiv.
  }
  pose proof (tm_fiber_equiv_to_projected_on
    Σ (CTArrow τx τr) m (context_ty_lvars (CTArrow τx τr))
    e1 e2 Hfib Hzero_src Hzero_tgt) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e2)) ∪
    lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪
    fv_cty τx ∪ fv_cty τr).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTArrow τx τr))).
  { clear -Hf. set_solver. }
  assert (Hf_src : f ∉ Lsrc).
  { clear -Hf. set_solver. }
  assert (Hfτx : f ∉ fv_cty τx).
  { clear -Hf. set_solver. }
  assert (Hfτr : f ∉ fv_cty τr).
  { clear -Hf. set_solver. }
  assert (Hfe : f ∉ fv_tm e1 ∪ fv_tm e2).
  { clear -Hf. set_solver. }
  assert (HfΣ1 :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))).
  {
    clear -Hf.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    set_solver.
  }
  assert (HfΣ2 :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
  {
    clear -Hf.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    set_solver.
  }
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTArrow τx τr) e2)))
              (tm_shift 0 e2) (LVBound 0))
            (arrow_value_denote_gas_with ty_denote_gas gas
              (typed_lty_env_bind
                (relevant_env Σ (CTArrow τx τr) e2)
                (erase_ty (CTArrow τx τr)))
              (cty_shift 0 τx) (cty_shift 1 τr)
              (tret (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. clear. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (first
      [ exact Hlc2
      | apply arrow_lc_lvars_shift_from; exact HlcΣ_tgt
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hfe; set_solver ]).
  rewrite (arrow_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt) in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTArrow τx τr) e2 m Hzero_tgt) in Hres_tgt.
  destruct (H21 f mf Hf_proj Hdom Hrestrict Hres_tgt)
    as [mf_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev f Hf_src mf_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (first
      [ exact Hlc1
      | apply arrow_lc_lvars_shift_from; exact HlcΣ_src
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hfe; set_solver ]).
  rewrite (arrow_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTArrow τx τr) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hequiv_src :
      typed_total_equiv_on Σ (CTArrow τx τr) mf_src e1 e2).
  {
    split.
    - eapply tm_equiv_full_world_extend_fresh.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + eapply typed_total_equiv_term_scope. exact Hequiv.
      + exact Hfe.
      + exact Hdom_src.
      + exact Hrestrict_src.
    - split.
      + eapply tm_total_equiv_full_world_extend_fresh.
        * eapply typed_total_equiv_total_equiv. exact Hequiv.
        * exact Hlc1.
        * exact Hlc2.
        * eapply typed_total_equiv_term_scope. exact Hequiv.
        * exact Hfe.
        * exact Hdom_src.
        * exact Hrestrict_src.
	      + split.
        * eapply (res_models_kripke m mf_src).
          -- change (m ⊑ mf_src).
             rewrite <- Hrestrict_src. apply res_restrict_le.
          -- exact Hzero_src.
        * eapply (res_models_kripke m mf_src).
          -- change (m ⊑ mf_src).
             rewrite <- Hrestrict_src. apply res_restrict_le.
          -- exact Hzero_tgt.
  }
  assert (Hvalue_tgt_src :
      mf_src ⊨ formula_open 0 f
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e2)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
  {
    assert (Hvalue_tgt_scope_src :
        formula_scoped_in_world mf_src
          (formula_open 0 f
	      (arrow_value_denote_gas_with ty_denote_gas gas
		(typed_lty_env_bind
		  (relevant_env Σ (CTArrow τx τr) e2)
		  (erase_ty (CTArrow τx τr)))
		(cty_shift 0 τx) (cty_shift 1 τr)
		(tret (vbvar 0))))).
    {
      eapply formula_scoped_open_arrow_value_body_obs.
      pose proof (ty_denote_gas_zero_type_fv_world
        Σ (CTArrow τx τr) e1 m Hzero_src) as Hτworld.
      rewrite Hdom_src.
      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - apply elem_of_union_l. exact (Hτworld a Ha).
      - apply elem_of_union_r. exact Ha.
    }
    cbn [formula_open arrow_value_denote_gas_with] in Hvalue_src |- *.
    cbn [formula_open arrow_value_denote_gas_with] in Hvalue_tgt_scope_src.
	    eapply res_models_forall_full_world_map;
	      [exact Hvalue_tgt_scope_src| |exact Hvalue_src].
	    exists (world_dom (mf_src : WorldT) ∪ world_dom (mf : WorldT) ∪
	        fv_cty τx ∪ fv_cty τr ∪ fv_tm e1 ∪ fv_tm e2 ∪
	        lvars_fv (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ∪
	        lvars_fv (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
      intros y Hy my Hdom_y Hrestrict_y Hopened_arg.
      cbn [formula_open] in Hopened_arg |- *.
      pose proof (formula_scoped_forall_open_res_le mf_src my y
        _ Hvalue_tgt_scope_src
        ltac:(rewrite <- Hrestrict_y; apply res_restrict_le)
        ltac:(rewrite Hdom_y; clear; set_solver)) as Htarget_impl_scope.
      cbn [formula_open] in Htarget_impl_scope.
      eapply res_models_impl_intro.
      { exact Htarget_impl_scope. }
      intros Harg_tgt.
      assert (Hyτx : y ∉ fv_cty τx).
      { clear -Hy. set_solver. }
      assert (Hyτr : y ∉ fv_cty τr).
      { clear -Hy. set_solver. }
      assert (Hye : y ∉ fv_tm e1 ∪ fv_tm e2).
      { clear -Hy. set_solver. }
      assert (HyΣ1 : y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))).
      { clear -Hy. set_solver. }
      assert (HyΣ2 : y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
      { clear -Hy. set_solver. }
      assert (Harg_tgt_open :
          my ⊨ ty_denote_gas gas
            (<[LVFree y := erase_ty τx]>
              (relevant_env Σ (CTArrow τx τr) e2))
            τx (tret (vfvar y))).
      {
        assert (Hf_rel2 :
            LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
	{
	  intros Hbad. apply HfΣ2.
	  apply lvars_fv_elem.
	  rewrite typed_lty_env_bind_dom.
	  rewrite (arrow_lvars_shift_from_lc_eq 0
	    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
	  apply elem_of_union_l. exact Hbad.
	}
	assert (Hy_rel2 :
	    LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
	{
	  intros Hbad. apply HyΣ2.
	  apply lvars_fv_elem.
	  rewrite typed_lty_env_bind_dom.
	  rewrite (arrow_lvars_shift_from_lc_eq 0
	    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
	  apply elem_of_union_l. exact Hbad.
	}
	assert (Hfy : f <> y).
	{
	  intros ->. apply Hy.
	  clear -Hdom.
	  rewrite Hdom. set_solver.
	}
        eapply arrow_result_first_arg_to_regular_open.
        - exact HlcΣ_tgt.
        - exact Hf_rel2.
        - exact Hy_rel2.
        - clear -Hfy. congruence.
        - exact Hlcτx.
        - exact Hfτx.
        - exact Hyτx.
        - exact Harg_tgt.
      }
		      pose proof (ty_denote_gas_tm_equiv_arrow_open_arg
		        gas Σ τx τr e1 e2 my y Harg_tgt_open) as Harg_src.
	      assert (Harg_src_formula :
	          my ⊨ formula_open 0 y
		    (formula_open 1 f
		      (ty_denote_gas gas
			(typed_lty_env_bind
			  (typed_lty_env_bind
			    (relevant_env Σ (CTArrow τx τr) e1)
			    (erase_ty (CTArrow τx τr)))
			  (erase_ty (cty_shift 0 τx)))
			(cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))))).
	      {
		eapply arrow_result_first_regular_to_arg_open.
		- exact HlcΣ_src.
		- assert (Hf_rel1 :
		      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
		  {
		    intros Hbad. apply HfΣ1.
		    apply lvars_fv_elem.
		    rewrite typed_lty_env_bind_dom.
		    rewrite (arrow_lvars_shift_from_lc_eq 0
		      (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
		    apply elem_of_union_l. exact Hbad.
		  }
		  exact Hf_rel1.
		- assert (Hy_rel1 :
		      LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
		  {
		    intros Hbad. apply HyΣ1.
		    apply lvars_fv_elem.
		    rewrite typed_lty_env_bind_dom.
		    rewrite (arrow_lvars_shift_from_lc_eq 0
		      (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
		    apply elem_of_union_l. exact Hbad.
			  }
			  exact Hy_rel1.
			- intros ->. apply Hy.
			  clear -Hdom.
			  rewrite Hdom. set_solver.
		- exact Hlcτx.
		- exact Hfτx.
		- exact Hyτx.
		- exact Harg_src.
	      }
	      change (my ⊨
			FImpl
			  (formula_open 0 y
			    (formula_open 1 f
			      (ty_denote_gas gas
				(typed_lty_env_bind
				  (typed_lty_env_bind
				    (relevant_env Σ (CTArrow τx τr) e1)
				    (erase_ty (CTArrow τx τr)))
				  (erase_ty (cty_shift 0 τx)))
				(cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))))
			  (formula_open 0 y
			    (formula_open 1 f
			      (ty_denote_gas gas
				(typed_lty_env_bind
				  (typed_lty_env_bind
				    (relevant_env Σ (CTArrow τx τr) e1)
				    (erase_ty (CTArrow τx τr)))
				  (erase_ty (cty_shift 0 τx)))
				(cty_shift 1 τr)
				(tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0)))))) in Hopened_arg.
	      pose proof (res_models_impl_elim _ _ _ Hopened_arg Harg_src_formula)
	        as Hres_src_inner.
	      assert (Hres_src_regular :
		  my ⊨ ty_denote_gas gas
		    (<[LVFree y := erase_ty τx]>
		      (<[LVFree f := erase_ty (CTArrow τx τr)]>
			(relevant_env Σ (CTArrow τx τr) e1)))
		    (cty_open 0 y τr)
		    (tapp_tm (tret (vfvar f)) (vfvar y))).
	      {
		eapply arrow_result_first_result_to_regular_open.
		- exact HlcΣ_src.
		- assert (Hf_rel1 :
		      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
		  {
		    intros Hbad. apply HfΣ1.
		    apply lvars_fv_elem.
		    rewrite typed_lty_env_bind_dom.
		    rewrite (arrow_lvars_shift_from_lc_eq 0
		      (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
		    apply elem_of_union_l. exact Hbad.
		  }
		  exact Hf_rel1.
		- assert (Hy_rel1 :
		      LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
		  {
		    intros Hbad. apply HyΣ1.
		    apply lvars_fv_elem.
		    rewrite typed_lty_env_bind_dom.
		    rewrite (arrow_lvars_shift_from_lc_eq 0
		      (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
		    apply elem_of_union_l. exact Hbad.
		  }
		  exact Hy_rel1.
		- intros ->. apply Hy.
		  clear -Hdom.
		  rewrite Hdom. set_solver.
			- exact Hlcτr.
			- intros Hin.
			  apply elem_of_union in Hin as [Hin|Hin].
			  + exact (Hfτx Hin).
			  + exact (Hfτr Hin).
			- intros Hin.
			  apply elem_of_union in Hin as [Hin|Hin].
			  + exact (Hyτx Hin).
			  + exact (Hyτr Hin).
			- exact Hres_src_inner.
	      }
	      assert (Hres_tgt_regular :
		  my ⊨ ty_denote_gas gas
		    (<[LVFree y := erase_ty τx]>
		      (<[LVFree f := erase_ty (CTArrow τx τr)]>
			(relevant_env Σ (CTArrow τx τr) e2)))
		    (cty_open 0 y τr)
		    (tapp_tm (tret (vfvar f)) (vfvar y))).
	      {
		eapply arrow_result_first_result_env_agree.
		- exact Hlcτr.
		- apply lc_tapp_tm; constructor; constructor.
			- intros ->. apply Hy.
			  clear -Hdom.
			  rewrite Hdom. set_solver.
			- intros Hin.
			  apply elem_of_union in Hin as [Hin|Hin].
			  + exact (Hfτx Hin).
			  + exact (Hfτr Hin).
			- intros Hin.
			  apply elem_of_union in Hin as [Hin|Hin].
			  + exact (Hyτx Hin).
			  + exact (Hyτr Hin).
			- exact Hres_src_regular.
	      }
	      eapply arrow_result_first_regular_to_result_open.
	      - exact HlcΣ_tgt.
	      - assert (Hf_rel2 :
		    LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
		{
		  intros Hbad. apply HfΣ2.
		  apply lvars_fv_elem.
		  rewrite typed_lty_env_bind_dom.
		  rewrite (arrow_lvars_shift_from_lc_eq 0
		    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
		  apply elem_of_union_l. exact Hbad.
		}
		exact Hf_rel2.
	      - assert (Hy_rel2 :
		    LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
		{
		  intros Hbad. apply HyΣ2.
		  apply lvars_fv_elem.
		  rewrite typed_lty_env_bind_dom.
		  rewrite (arrow_lvars_shift_from_lc_eq 0
		    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
		  apply elem_of_union_l. exact Hbad.
		}
		exact Hy_rel2.
	      - intros ->. apply Hy.
		clear -Hdom.
			rewrite Hdom. set_solver.
		      - exact Hlcτr.
		      - intros Hin.
			apply elem_of_union in Hin as [Hin|Hin].
			+ exact (Hfτx Hin).
			+ exact (Hfτr Hin).
		      - intros Hin.
			apply elem_of_union in Hin as [Hin|Hin].
			+ exact (Hyτx Hin).
			+ exact (Hyτr Hin).
		      - exact Hres_tgt_regular.
		  }
	  eapply res_models_projection; [|exact Hvalue_tgt_src].
	  eapply res_restrict_eq_subset; [|exact Hproj_obs].
	  etransitivity; [apply formula_open_fv_subset|].
	  unfold formula_fv, formula_lvars, arrow_value_denote_gas_with.
	  cbn [formula_lvars_at].
	  rewrite lvars_fv_union.
	  pose proof (ty_denote_gas_lvars_subset gas 1
	    (typed_lty_env_bind
	      (typed_lty_env_bind
	        (relevant_env Σ (CTArrow τx τr) e2)
	        (erase_ty (CTArrow τx τr)))
	      (erase_ty (cty_shift 0 τx)))
	    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg_fv.
	  pose proof (ty_denote_gas_lvars_subset gas 1
	    (typed_lty_env_bind
	      (typed_lty_env_bind
	        (relevant_env Σ (CTArrow τx τr) e2)
	        (erase_ty (CTArrow τx τr)))
	      (erase_ty (cty_shift 0 τx)))
	    (cty_shift 1 τr)
	    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))) as Hres_fv.
	  apply lvars_fv_mono in Harg_fv.
	  apply lvars_fv_mono in Hres_fv.
	  rewrite !lvars_fv_union in Harg_fv, Hres_fv.
	  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg_fv, Hres_fv.
	  rewrite !cty_shift_fv in Harg_fv, Hres_fv.
	  rewrite fv_tapp_tm, tm_shift_fv in Hres_fv.
	  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at]
	    in Harg_fv, Hres_fv |- *.
	  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
	  intros a Ha.
	  repeat rewrite elem_of_union in Ha.
	  repeat rewrite elem_of_union.
	  destruct Ha as [[Ha_arg | Ha_res] | Ha_f].
	  - specialize (Harg_fv a Ha_arg). rewrite cty_shift_fv in Harg_fv.
	    clear -Harg_fv. set_solver.
	  - specialize (Hres_fv a Ha_res). try rewrite cty_shift_fv in Hres_fv.
	    clear -Hres_fv. set_solver.
	  - clear -Ha_f. set_solver.
Qed.

End TypeDenote.
