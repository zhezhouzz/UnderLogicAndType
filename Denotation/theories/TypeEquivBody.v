(** * Denotation.TypeEquivBody

    Fiber-body and ordinary term-result-equivalence body lemmas. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen DenotationSetMapFacts TypeDenoteRegular.
From Denotation Require Import TypeEquivCore TypeEquivTermBase TypeEquivTermResult.
From Denotation Require Import TypeEquivFiberBaseCore TypeEquivFiberBaseProjected.
From Denotation Require TypeEquivFiberBaseCore.

Section TypeDenote.

Local Ltac expr_result_shift0_side :=
  first
    [ assumption
    | apply result_first_lc_lvars_shift_from; assumption
    | rewrite lvars_shift_from_fv; assumption ].

Local Ltac sum_open_side :=
  first
    [ assumption
    | rewrite typed_lty_env_bind_lvars_fv_dom; assumption
    | rewrite lvars_shift_from_fv; assumption
    | rewrite cty_shift_fv; assumption
    | cbn [fv_tm fv_value]; set_solver ].

Local Lemma formula_open_shifted_ret_bound0_ty_denote_gas
    gas (Σ : lty_env) τ y :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_cty τ ->
  formula_open 0 y
    (ty_denote_gas gas Σ (cty_shift 0 τ) (tret (vbvar 0))) =
  ty_denote_gas gas (lty_env_open_one 0 y Σ)
    (cty_open 0 y (cty_shift 0 τ)) (tret (vfvar y)).
Proof.
  intros HΣ Hτ.
  rewrite formula_open_ty_denote_gas_singleton.
  - reflexivity.
  - exact HΣ.
  - cbn [fv_tm fv_value]. set_solver.
  - rewrite cty_shift_fv. exact Hτ.
Qed.

Lemma formula_fv_open_over_body_obs b φ y :
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (over_result_body b φ))) ⊆
  lvars_fv (context_ty_lvars (CTOver b φ)) ∪ {[y]}.
Proof.
  etransitivity.
  - apply formula_fv_open_fibvars_qual_body_obs.
    unfold over_result_body.
    rewrite formula_fv_over, formula_fv_and, formula_fv_atom.
    rewrite formula_fv_result_basic_typing_formula.
    set_solver.
  - rewrite context_ty_lvars_over_fv. set_solver.
Qed.

Lemma formula_fv_open_under_body_obs b φ y :
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (under_result_body b φ))) ⊆
  lvars_fv (context_ty_lvars (CTUnder b φ)) ∪ {[y]}.
Proof.
  etransitivity.
  - apply formula_fv_open_fibvars_qual_body_obs.
    unfold under_result_body.
    rewrite formula_fv_under, formula_fv_and, formula_fv_atom.
    rewrite formula_fv_result_basic_typing_formula.
    set_solver.
  - rewrite context_ty_lvars_under_fv. set_solver.
Qed.

Lemma formula_fv_open_sum_body_obs gas Σ τ1 τ2 y :
  formula_fv
    (formula_open 0 y
      (FPlus
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
          (cty_shift 0 τ1) (tret (vbvar 0)))
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
          (cty_shift 0 τ2) (tret (vbvar 0))))) ⊆
  lvars_fv (dom Σ) ∪
    lvars_fv (context_ty_lvars (CTSum τ1 τ2)) ∪ {[y]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
  rewrite formula_fv_plus.
  intros a Ha.
  apply elem_of_union in Ha as [Hab|Ha].
  - apply elem_of_union in Hab as [Ha|Ha].
    + pose proof (ty_denote_gas_fv_subset gas
        (typed_lty_env_bind Σ (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0)) a Ha) as HaΣ.
      rewrite cty_shift_fv in HaΣ.
      cbn [fv_tm fv_value] in HaΣ.
      cbn [context_ty_lvars context_ty_lvars_at].
      rewrite lvars_fv_union.
      change (lvars_fv (context_ty_lvars_at 0 τ1)) with (fv_cty τ1).
      change (lvars_fv (context_ty_lvars_at 0 τ2)) with (fv_cty τ2).
      set_solver.
    + pose proof (ty_denote_gas_fv_subset gas
        (typed_lty_env_bind Σ (erase_ty τ1))
        (cty_shift 0 τ2) (tret (vbvar 0)) a Ha) as HaΣ.
      rewrite cty_shift_fv in HaΣ.
      cbn [fv_tm fv_value] in HaΣ.
      cbn [context_ty_lvars context_ty_lvars_at].
      rewrite lvars_fv_union.
      change (lvars_fv (context_ty_lvars_at 0 τ1)) with (fv_cty τ1).
      change (lvars_fv (context_ty_lvars_at 0 τ2)) with (fv_cty τ2).
      set_solver.
  - apply elem_of_union_r. exact Ha.
Qed.

Lemma formula_fv_sum_body_obs_relevant gas Σ τ1 τ2 y :
  formula_fv
    (FPlus
      (ty_denote_gas gas (<[LVFree y := erase_ty τ1]> Σ)
        τ1 (tret (vfvar y)))
      (ty_denote_gas gas (<[LVFree y := erase_ty τ1]> Σ)
        τ2 (tret (vfvar y)))) ⊆
  lvars_fv (context_ty_lvars (CTSum τ1 τ2)) ∪ {[y]}.
Proof.
  rewrite formula_fv_plus.
  intros a Ha.
  apply elem_of_union in Ha as [Ha_left|Ha_right].
  - pose proof (ty_denote_gas_fv_subset gas
      (<[LVFree y := erase_ty τ1]> Σ)
      τ1 (tret (vfvar y)) a Ha_left) as HaΣ.
    cbn [fv_tm fv_value] in HaΣ.
    cbn [context_ty_lvars context_ty_lvars_at].
    rewrite lvars_fv_union.
    change (lvars_fv (context_ty_lvars_at 0 τ1)) with (fv_cty τ1).
    change (lvars_fv (context_ty_lvars_at 0 τ2)) with (fv_cty τ2).
    set_solver.
  - pose proof (ty_denote_gas_fv_subset gas
      (<[LVFree y := erase_ty τ1]> Σ)
      τ2 (tret (vfvar y)) a Ha_right) as HaΣ.
    cbn [fv_tm fv_value] in HaΣ.
    cbn [context_ty_lvars context_ty_lvars_at].
    rewrite lvars_fv_union.
    change (lvars_fv (context_ty_lvars_at 0 τ1)) with (fv_cty τ1).
    change (lvars_fv (context_ty_lvars_at 0 τ2)) with (fv_cty τ2).
    set_solver.
Qed.

Local Lemma sum_branch_relevant_env_agree_inserted_core
    (Σsrc : lty_env) Ty y τbranch τsum e_src :
  context_ty_lvars τbranch ⊆ context_ty_lvars τsum ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]> (relevant_env Σsrc τsum e_src))
    (relevant_lvars τbranch (tret (vfvar y))) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (relevant_lvars τbranch (tret (vfvar y))).
Proof.
  intros Hτsub.
  apply lty_restrict_insert_relevant_eq.
  unfold relevant_lvars.
  cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
  intros v Hv.
  set_solver.
Qed.

Local Lemma sum_open_body_env_transport
    gas (Σ : lty_env) τ1 τ2 e_src e_tgt (m : WfWorldT) y :
  context_ty_lvars τ1 ⊆ context_ty_lvars (CTSum τ1 τ2) ->
  context_ty_lvars τ2 ⊆ context_ty_lvars (CTSum τ1 τ2) ->
  m ⊨ FPlus
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_src))
        τ1 (tret (vfvar y)))
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_src))
        τ2 (tret (vfvar y))) ->
  m ⊨ FPlus
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_tgt))
        τ1 (tret (vfvar y)))
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_tgt))
        τ2 (tret (vfvar y))).
Proof.
  intros Hτ1sub Hτ2sub Hbody.
  replace (FPlus
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_tgt))
        τ1 (tret (vfvar y)))
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_tgt))
        τ2 (tret (vfvar y))))
    with (FPlus
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_src))
        τ1 (tret (vfvar y)))
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e_src))
        τ2 (tret (vfvar y)))).
  - exact Hbody.
  - f_equal.
    + eapply ty_denote_gas_env_agree_on.
      * reflexivity.
      * transitivity (lty_env_restrict_lvars
          (<[LVFree y := erase_ty τ1]> Σ)
          (relevant_lvars τ1 (tret (vfvar y)))).
        -- apply sum_branch_relevant_env_agree_inserted_core.
           exact Hτ1sub.
        -- symmetry. apply sum_branch_relevant_env_agree_inserted_core.
           exact Hτ1sub.
    + eapply ty_denote_gas_env_agree_on.
      * reflexivity.
      * transitivity (lty_env_restrict_lvars
          (<[LVFree y := erase_ty τ1]> Σ)
          (relevant_lvars τ2 (tret (vfvar y)))).
        -- apply sum_branch_relevant_env_agree_inserted_core.
           exact Hτ2sub.
        -- symmetry. apply sum_branch_relevant_env_agree_inserted_core.
           exact Hτ2sub.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_over_body
    (gas : nat) (Σ : lty_env) (b : base_ty) φ e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTOver b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b φ) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (over_result_body b φ))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b φ) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (over_result_body b φ))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ (CTOver b φ) e1 m Hzero_src)
    as Hguard_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src)
    as Hworld_src.
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  pose proof (ty_denote_gas_guard_of_zero Σ (CTOver b φ) e2 m Hzero_tgt)
    as Hguard_tgt.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_tgt)
    as Hworld_tgt.
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTOver b φ) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  pose proof (typed_fiber_equiv_result_projected
    Σ (CTOver b φ) m e1 e2 Hequiv) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTOver b φ) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTOver b φ) e2)) ∪
    lvars_fv (context_ty_lvars (CTOver b φ))).
  intros y Hy my Hdom Hrestrict.
  assert (Hy_m : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
  assert (Hy_dom1 :
      y ∉ lvars_fv (dom (relevant_env Σ (CTOver b φ) e1)))
    by (clear -Hy; set_solver).
  assert (Hy_dom2 :
      y ∉ lvars_fv (dom (relevant_env Σ (CTOver b φ) e2)))
    by (clear -Hy; set_solver).
  assert (Hy_e1 : y ∉ fv_tm e1) by (clear -Hy; set_solver).
  assert (Hy_e2 : y ∉ fv_tm e2) by (clear -Hy; set_solver).
  assert (Hy_proj :
      y ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTOver b φ)))
    by (clear -Hy; set_solver).
  assert (Hy_src : y ∉ Lsrc) by (clear -Hy; set_solver).
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTOver b φ) e2)))
              (tm_shift 0 e2) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (over_result_body b φ))))).
	  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - exact (opened_world_dom_contains_slot m my y Hdom).
	  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by expr_result_shift0_side.
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTOver b φ) e2)) HlcΣ_tgt) in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTOver b φ) e2 m Hzero_tgt) in Hres_tgt.
  destruct (H21 y my Hy_proj Hdom Hrestrict Hres_tgt)
    as [my_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev y Hy_src my_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by expr_result_shift0_side.
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTOver b φ) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTOver b φ) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hbody_src.
  eapply res_models_projection; [|exact Hbody_src].
  eapply (res_restrict_eq_subset my_src my
    (lvars_fv (context_ty_lvars (CTOver b φ)) ∪ {[y]})).
  - etransitivity; [apply formula_fv_open_over_body_obs|].
    intros a Ha. exact Ha.
  - eapply res_restrict_eq_subset; [|exact Hproj_obs].
    intros a Ha. exact Ha.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_under_body
    (gas : nat) (Σ : lty_env) (b : base_ty) φ e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTUnder b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b φ) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (under_result_body b φ))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b φ) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (under_result_body b φ))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ (CTUnder b φ) e1 m Hzero_src)
    as Hguard_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src)
    as Hworld_src.
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  pose proof (ty_denote_gas_guard_of_zero Σ (CTUnder b φ) e2 m Hzero_tgt)
    as Hguard_tgt.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_tgt)
    as Hworld_tgt.
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTUnder b φ) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  pose proof (typed_fiber_equiv_result_projected
    Σ (CTUnder b φ) m e1 e2 Hequiv) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTUnder b φ) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTUnder b φ) e2)) ∪
    lvars_fv (context_ty_lvars (CTUnder b φ))).
  intros y Hy my Hdom Hrestrict.
  assert (Hy_m : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
  assert (Hy_dom1 :
      y ∉ lvars_fv (dom (relevant_env Σ (CTUnder b φ) e1)))
    by (clear -Hy; set_solver).
  assert (Hy_dom2 :
      y ∉ lvars_fv (dom (relevant_env Σ (CTUnder b φ) e2)))
    by (clear -Hy; set_solver).
  assert (Hy_e1 : y ∉ fv_tm e1) by (clear -Hy; set_solver).
  assert (Hy_e2 : y ∉ fv_tm e2) by (clear -Hy; set_solver).
  assert (Hy_proj :
      y ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTUnder b φ)))
    by (clear -Hy; set_solver).
  assert (Hy_src : y ∉ Lsrc) by (clear -Hy; set_solver).
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTUnder b φ) e2)))
              (tm_shift 0 e2) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (under_result_body b φ))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - exact (opened_world_dom_contains_slot m my y Hdom).
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by expr_result_shift0_side.
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTUnder b φ) e2)) HlcΣ_tgt) in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTUnder b φ) e2 m Hzero_tgt) in Hres_tgt.
  destruct (H21 y my Hy_proj Hdom Hrestrict Hres_tgt)
    as [my_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev y Hy_src my_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by expr_result_shift0_side.
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTUnder b φ) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTUnder b φ) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hbody_src.
  eapply res_models_projection; [|exact Hbody_src].
  eapply (res_restrict_eq_subset my_src my
    (lvars_fv (context_ty_lvars (CTUnder b φ)) ∪ {[y]})).
  - etransitivity; [apply formula_fv_open_under_body_obs|].
    intros a Ha. exact Ha.
  - eapply res_restrict_eq_subset; [|exact Hproj_obs].
    intros a Ha. exact Ha.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_sum_body
    (gas : nat)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTSum τ1 τ2) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e1)
              (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e1)
              (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTSum τ1 τ2) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
              (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
              (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ (CTSum τ1 τ2) e1 m Hzero_src)
    as Hguard_src.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_src) as Hwf_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src)
    as Hworld_src.
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  pose proof (ty_denote_gas_guard_of_zero Σ (CTSum τ1 τ2) e2 m Hzero_tgt)
    as Hguard_tgt.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_tgt)
    as Hworld_tgt.
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (context_ty_wf_formula_models_iff
    (relevant_env Σ (CTSum τ1 τ2) e1) (CTSum τ1 τ2) m) as Hwf_src_iff.
  apply Hwf_src_iff in Hwf_src as [_ [_ Hbasic_sum_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTSum τ1 τ2) e1))
    (CTSum τ1 τ2) HlcΣ_src Hbasic_sum_src) as Hlc_sum.
  cbn [lc_context_ty cty_lc_at] in Hlc_sum.
  destruct Hlc_sum as [Hlcτ1 Hlcτ2].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTSum τ1 τ2) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  pose proof (typed_fiber_equiv_result_projected
    Σ (CTSum τ1 τ2) m e1 e2 Hequiv) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e2)) ∪
    lvars_fv (context_ty_lvars (CTSum τ1 τ2))).
  intros y Hy my Hdom Hrestrict.
  assert (Hy_m : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
  assert (Hy_dom1 :
      y ∉ lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e1)))
    by (clear -Hy; set_solver).
  assert (Hy_dom2 :
      y ∉ lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e2)))
    by (clear -Hy; set_solver).
  assert (Hy_e1 : y ∉ fv_tm e1) by (clear -Hy; set_solver).
  assert (Hy_e2 : y ∉ fv_tm e2) by (clear -Hy; set_solver).
  assert (Hyτ1 : y ∉ fv_cty τ1).
  {
    intros Hyτ.
    apply Hy.
    repeat apply elem_of_union_r.
    apply lvars_fv_elem.
    cbn [context_ty_lvars context_ty_lvars_at].
    apply elem_of_union_l.
    apply lvars_fv_elem.
    rewrite context_ty_lvars_fv. exact Hyτ.
  }
  assert (Hyτ2 : y ∉ fv_cty τ2).
  {
    intros Hyτ.
    apply Hy.
    repeat apply elem_of_union_r.
    apply lvars_fv_elem.
    cbn [context_ty_lvars context_ty_lvars_at].
    apply elem_of_union_r.
    apply lvars_fv_elem.
    rewrite context_ty_lvars_fv. exact Hyτ.
  }
  assert (Hy_proj :
      y ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTSum τ1 τ2)))
    by (clear -Hy; set_solver).
  assert (Hy_src : y ∉ Lsrc) by (clear -Hy; set_solver).
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTSum τ1 τ2) e2)))
              (tm_shift 0 e2) (LVBound 0))
            (FPlus
              (ty_denote_gas gas
                (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
                  (erase_ty τ1))
                (cty_shift 0 τ1) (tret (vbvar 0)))
              (ty_denote_gas gas
                (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
                  (erase_ty τ1))
                (cty_shift 0 τ2) (tret (vbvar 0))))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - exact (opened_world_dom_contains_slot m my y Hdom).
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by expr_result_shift0_side.
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTSum τ1 τ2) e2)) HlcΣ_tgt) in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTSum τ1 τ2) e2 m Hzero_tgt) in Hres_tgt.
  destruct (H21 y my Hy_proj Hdom Hrestrict Hres_tgt)
    as [my_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev y Hy_src my_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by expr_result_shift0_side.
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTSum τ1 τ2) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTSum τ1 τ2) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hbody_src.
  rewrite formula_open_plus in Hbody_src.
  rewrite !formula_open_shifted_ret_bound0_ty_denote_gas in Hbody_src
    by (first [rewrite typed_lty_env_bind_lvars_fv_dom; assumption
              |sum_open_side]).
  rewrite (cty_open_shift_from_lc_fresh 0 y τ1 Hlcτ1 Hyτ1) in Hbody_src.
  rewrite (cty_open_shift_from_lc_fresh 0 y τ2 Hlcτ2 Hyτ2) in Hbody_src.
  rewrite (typed_lty_env_bind_open_current y
    (relevant_env Σ (CTSum τ1 τ2) e1) (erase_ty τ1)) in Hbody_src.
  2:{
    intros Hbad. apply Hy_dom1. apply lvars_fv_elem. exact Hbad.
  }
  2:{ exact HlcΣ_src. }
  assert (Hbody_src_tgt :
      my_src ⊨ FPlus
        (ty_denote_gas gas
          (<[LVFree y := erase_ty τ1]>
            (relevant_env Σ (CTSum τ1 τ2) e2))
          τ1 (tret (vfvar y)))
        (ty_denote_gas gas
          (<[LVFree y := erase_ty τ1]>
            (relevant_env Σ (CTSum τ1 τ2) e2))
          τ2 (tret (vfvar y)))).
  {
    eapply sum_open_body_env_transport.
	    - cbn [context_ty_lvars context_ty_lvars_at].
	      intros v Hv. apply elem_of_union_l. exact Hv.
	    - cbn [context_ty_lvars context_ty_lvars_at].
	      intros v Hv. apply elem_of_union_r. exact Hv.
	    - exact Hbody_src.
	  }
  replace (formula_open 0 y
      (FPlus
        (ty_denote_gas gas
          (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
            (erase_ty τ1))
          (cty_shift 0 τ1) (tret (vbvar 0)))
        (ty_denote_gas gas
          (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
            (erase_ty τ1))
          (cty_shift 0 τ2) (tret (vbvar 0)))))
    with (FPlus
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e2))
        τ1 (tret (vfvar y)))
      (ty_denote_gas gas
        (<[LVFree y := erase_ty τ1]>
          (relevant_env Σ (CTSum τ1 τ2) e2))
        τ2 (tret (vfvar y)))).
  2:{
    rewrite formula_open_plus.
    rewrite !formula_open_shifted_ret_bound0_ty_denote_gas
      by (first [rewrite typed_lty_env_bind_lvars_fv_dom; assumption
                |sum_open_side]).
    rewrite (cty_open_shift_from_lc_fresh 0 y τ1 Hlcτ1 Hyτ1).
    rewrite (cty_open_shift_from_lc_fresh 0 y τ2 Hlcτ2 Hyτ2).
    rewrite (typed_lty_env_bind_open_current y
      (relevant_env Σ (CTSum τ1 τ2) e2) (erase_ty τ1)).
    - reflexivity.
    - intros Hbad. apply Hy_dom2. apply lvars_fv_elem. exact Hbad.
    - exact HlcΣ_tgt.
  }
  eapply res_models_projection; [|exact Hbody_src_tgt].
  eapply (res_restrict_eq_subset my_src my
    (lvars_fv (context_ty_lvars (CTSum τ1 τ2)) ∪ {[y]})).
  - apply formula_fv_sum_body_obs_relevant.
  - eapply res_restrict_eq_subset; [|exact Hproj_obs].
    intros a Ha. exact Ha.
Qed.

End TypeDenote.

Section TypeDenote.

Lemma ty_denote_gas_tm_equiv_over_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTOver b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b φ) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (over_result_body b φ))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b φ) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (over_result_body b φ))).
Proof.
  intros Hequiv Hsrc.
  eapply (ty_denote_gas_tm_fiber_equiv_over_body
    gas Σ b φ e1 e2 m); [|exact Hsrc].
  apply typed_fiber_equiv_of_tm_equiv.
  - eapply typed_total_equiv_tm_equiv. exact Hequiv.
  - eapply typed_total_equiv_source_zero. exact Hequiv.
  - eapply typed_total_equiv_target_zero. exact Hequiv.
Qed.

Lemma ty_denote_gas_tm_equiv_under_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTUnder b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b φ) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (under_result_body b φ))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b φ) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (under_result_body b φ))).
Proof.
  intros Hequiv Hsrc.
  eapply (ty_denote_gas_tm_fiber_equiv_under_body
    gas Σ b φ e1 e2 m); [|exact Hsrc].
  apply typed_fiber_equiv_of_tm_equiv.
  - eapply typed_total_equiv_tm_equiv. exact Hequiv.
  - eapply typed_total_equiv_source_zero. exact Hequiv.
  - eapply typed_total_equiv_target_zero. exact Hequiv.
Qed.

Lemma ty_denote_gas_zero_project_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  erase_ty τsmall = erase_ty τbig ->
  context_ty_shape_ok τsmall ->
  m ⊨ ty_denote_gas 0 Σ τbig e ->
  m ⊨ ty_denote_gas 0 Σ τsmall e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_project_context.
Qed.

Lemma ty_denote_gas_zero_inter_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_inter_l.
Qed.

Lemma ty_denote_gas_zero_inter_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_inter_r.
Qed.

Lemma typed_total_equiv_project_context
    (Σ : lty_env) τsmall τbig m e1 e2 :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  erase_ty τsmall = erase_ty τbig ->
  context_ty_shape_ok τsmall ->
  typed_total_equiv_on Σ τbig m e1 e2 ->
  typed_total_equiv_on Σ τsmall m e1 e2.
Proof.
  intros Hlv Herase Hshape Hequiv.
  split; [eapply typed_total_equiv_tm_equiv; exact Hequiv|].
  split; [eapply typed_total_equiv_total_equiv; exact Hequiv|].
  split.
  - eapply ty_denote_gas_zero_project_context; eauto.
    eapply typed_total_equiv_source_zero. exact Hequiv.
  - eapply ty_denote_gas_zero_project_context; eauto.
    eapply typed_total_equiv_target_zero. exact Hequiv.
Qed.

Lemma typed_total_equiv_shape_ok
    (Σ : lty_env) τ m e1 e2 :
  typed_total_equiv_on Σ τ m e1 e2 ->
  context_ty_shape_ok τ.
Proof.
  intros Hequiv.
  pose proof (typed_total_equiv_source_zero _ _ _ _ _ Hequiv) as Hzero.
  apply ty_denote_gas_guard_of_zero in Hzero.
  repeat rewrite res_models_and_iff in Hzero.
  destruct Hzero as [Hwf _].
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
  exact Hshape.
Qed.

Lemma typed_total_equiv_inter_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ1 m e1 e2.
Proof.
  intros Hequiv.
  eapply (typed_total_equiv_project_context
    Σ τ1 (CTInter τ1 τ2) m e1 e2);
    [|reflexivity| |exact Hequiv].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - pose proof (typed_total_equiv_shape_ok
      Σ (CTInter τ1 τ2) m e1 e2 Hequiv) as Hshape.
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma typed_total_equiv_inter_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ2 m e1 e2.
Proof.
  intros Hequiv.
  assert (Hshape_big : context_ty_shape_ok (CTInter τ1 τ2)).
  {
    eapply typed_total_equiv_shape_ok. exact Hequiv.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (typed_total_equiv_project_context
    Σ τ2 (CTInter τ1 τ2) m e1 e2);
    [| |exact Hshape2|exact Hequiv].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma ty_denote_gas_tm_equiv_inter_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ1 e1 /\
  m ⊨ ty_denote_gas gas Σ τ2 e1 ->
  m ⊨ ty_denote_gas gas Σ τ1 e2 /\
  m ⊨ ty_denote_gas gas Σ τ2 e2.
Proof.
  intros Hequiv [H1 H2].
  split.
  - eapply IH; [|exact H1].
    eapply typed_total_equiv_inter_l; exact Hequiv.
  - eapply IH; [|exact H2].
    eapply typed_total_equiv_inter_r; exact Hequiv.
Qed.

Lemma ty_denote_gas_zero_union_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_union_l.
Qed.

Lemma ty_denote_gas_zero_union_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_union_r.
Qed.

Lemma typed_total_equiv_union_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ1 m e1 e2.
Proof.
  intros Hequiv.
  eapply (typed_total_equiv_project_context
    Σ τ1 (CTUnion τ1 τ2) m e1 e2);
    [|reflexivity| |exact Hequiv].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - pose proof (typed_total_equiv_shape_ok
      Σ (CTUnion τ1 τ2) m e1 e2 Hequiv) as Hshape.
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma typed_total_equiv_union_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ2 m e1 e2.
Proof.
  intros Hequiv.
  assert (Hshape_big : context_ty_shape_ok (CTUnion τ1 τ2)).
  {
    eapply typed_total_equiv_shape_ok. exact Hequiv.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (typed_total_equiv_project_context
    Σ τ2 (CTUnion τ1 τ2) m e1 e2);
    [| |exact Hshape2|exact Hequiv].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma ty_denote_gas_scope_from_zero_any
    gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  formula_scoped_in_world m (ty_denote_gas gas Σ τ e).
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_scope_from_zero_any.
Qed.

Lemma ty_denote_gas_tm_equiv_union_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  m ⊨
    FOr
      (ty_denote_gas gas Σ τ1 e1)
      (ty_denote_gas gas Σ τ2 e1) ->
  m ⊨
    FOr
	      (ty_denote_gas gas Σ τ1 e2)
	      (ty_denote_gas gas Σ τ2 e2).
Proof.
  intros Hequiv Hbody.
  pose proof (typed_total_equiv_union_l
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv1.
  pose proof (typed_total_equiv_union_r
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv2.
  pose proof (res_models_scoped _ _ Hbody) as Hscope_body.
  apply (proj1 (res_models_or_iff m _ _ Hscope_body)) in Hbody.
  destruct Hbody as [H1|H2].
  - eapply res_models_or_intro_l_from_model.
    + eapply IH; [exact Hequiv1|exact H1].
    + eapply ty_denote_gas_scope_from_zero_any.
      exact (typed_total_equiv_target_zero
        Σ τ2 m e1 e2 Hequiv2).
  - eapply res_models_or_intro_r_from_model.
    + eapply ty_denote_gas_scope_from_zero_any.
      exact (typed_total_equiv_target_zero
        Σ τ1 m e1 e2 Hequiv1).
    + eapply IH; [exact Hequiv2|exact H2].
Qed.

Lemma ty_denote_gas_zero_res_subset
    (Σ : lty_env) τ e (m n : WfWorldT) :
  res_subset n m ->
  m ⊨ ty_denote_gas 0 Σ τ e ->
  n ⊨ ty_denote_gas 0 Σ τ e.
Proof.
  intros Hsub Hzero.
  apply ty_denote_gas_zero_of_guard.
  apply ty_denote_gas_guard_of_zero in Hzero.
  repeat rewrite res_models_and_iff in Hzero |- *.
  destruct Hzero as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof Hsub as [Hdom _].
  split.
  - apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hscope Hbasic_ty]].
    apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [set_solver|exact Hbasic_ty].
  - split.
    + eapply basic_world_formula_res_subset; eauto.
    + split.
      * apply expr_basic_typing_formula_models_iff in Hbasic
          as [Hlc [Hscope Hty]].
        apply expr_basic_typing_formula_models_iff.
        split; [exact Hlc|]. split; [set_solver|exact Hty].
      * eapply expr_total_formula_res_subset; eauto.
Qed.

Lemma ty_denote_gas_zero_sum_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_sum_l.
Qed.

Lemma ty_denote_gas_zero_sum_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  apply TypeEquivFiberBaseCore.ty_denote_gas_zero_sum_r.
Qed.

Lemma typed_total_equiv_sum_l_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m1 : WfWorldT) :
  res_subset m1 m ->
  typed_total_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m1 ⊨ ty_denote_gas gas Σ τ1 e1 ->
  typed_total_equiv_on Σ τ1 m1 e1 e2.
Proof.
  intros Hsub Hequiv Hsrc.
  split.
  - eapply tm_equiv_res_store_subset.
    + exact Hsub.
    + eapply typed_total_equiv_tm_equiv. exact Hequiv.
  - split.
    + eapply tm_total_equiv_res_store_subset.
      * exact Hsub.
      * eapply typed_total_equiv_total_equiv. exact Hequiv.
    + split.
      * apply ty_denote_gas_zero_of_guard.
      eapply ty_denote_gas_guard. exact Hsrc.
      * apply ty_denote_gas_zero_sum_l with (τ2 := τ2).
        eapply ty_denote_gas_zero_res_subset; eauto.
        eapply typed_total_equiv_target_zero. exact Hequiv.
Qed.

Lemma typed_total_equiv_sum_r_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m2 : WfWorldT) :
  res_subset m2 m ->
  typed_total_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m2 ⊨ ty_denote_gas gas Σ τ2 e1 ->
  typed_total_equiv_on Σ τ2 m2 e1 e2.
Proof.
  intros Hsub Hequiv Hsrc.
  split.
  - eapply tm_equiv_res_store_subset.
    + exact Hsub.
    + eapply typed_total_equiv_tm_equiv. exact Hequiv.
  - split.
    + eapply tm_total_equiv_res_store_subset.
      * exact Hsub.
      * eapply typed_total_equiv_total_equiv. exact Hequiv.
    + split.
      * apply ty_denote_gas_zero_of_guard.
      eapply ty_denote_gas_guard. exact Hsrc.
      * apply ty_denote_gas_zero_sum_r with (τ1 := τ1).
        eapply ty_denote_gas_zero_res_subset; eauto.
        eapply typed_total_equiv_target_zero. exact Hequiv.
Qed.

Lemma ty_denote_gas_tm_equiv_sum_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTSum τ1 τ2) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e1)
              (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e1)
              (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTSum τ1 τ2) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
              (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e2)
              (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))).
Proof.
  intros Hequiv Hbody.
  eapply (ty_denote_gas_tm_fiber_equiv_sum_body
    gas Σ τ1 τ2 e1 e2 m); [|exact Hbody].
  apply typed_fiber_equiv_of_tm_equiv.
  - eapply typed_total_equiv_tm_equiv. exact Hequiv.
  - eapply typed_total_equiv_source_zero. exact Hequiv.
  - eapply typed_total_equiv_target_zero. exact Hequiv.
Qed.

End TypeDenote.
