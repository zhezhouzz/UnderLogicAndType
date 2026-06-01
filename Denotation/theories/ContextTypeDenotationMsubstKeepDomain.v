(** * Denotation.ContextTypeDenotationMsubstKeepDomain

    Split from ContextTypeDenotationMsubst for incremental compilation. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationLvars
  ContextTypeDenotationMsubstCore
  ContextTypeDenotationMsubstGuard.

Section ContextTypeDenotationMsubst.

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

Lemma qual_msubst_store_open_fibvars_domain σ φ k y :
  y ∉ dom (σ : gmap atom value) ->
  set_swap (LVBound k) (LVFree y) (qual_vars φ ∖ {[LVBound k]})
    ∖ dom (lstore_lift_free σ : LStoreT) =
  set_swap (LVBound k) (LVFree y)
    (qual_vars (qual_msubst_store σ φ) ∖ {[LVBound k]}).
Proof.
  intros Hy.
  rewrite qual_msubst_store_vars, dom_lstore_lift_free.
  set (R := lvars_of_atoms (dom (σ : gmap atom value))).
  assert (Hbound : LVBound k ∉ R).
  { subst R. unfold lvars_of_atoms. rewrite elem_of_map.
    intros (z & Hz & _). discriminate. }
  assert (Hfree : LVFree y ∉ R).
  { subst R. unfold lvars_of_atoms. rewrite elem_of_map.
    intros (z & Hz & Hzσ). inversion Hz. subst. exact (Hy Hzσ). }
  rewrite <- set_swap_difference_fresh by assumption.
  f_equal. set_solver.
Qed.

Lemma store_without_lvars_open_type_qualifier_fresh σ φ y :
  y ∉ dom (σ : gmap atom value) ->
  dom (store_without_lvars σ
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars φ ∖ {[LVBound 0]})) : StoreT) ##
  formula_fv (type_qualifier_formula (φ ^q^ y)).
Proof.
  intros Hy.
  unfold store_without_lvars.
  change (dom (storeA_restrict σ
    (dom (σ : StoreT) ∖
      lvars_fv
        (set_swap (LVBound 0) (LVFree y)
          (qual_vars φ ∖ {[LVBound 0]}))) : gmap atom value) ##
    formula_fv (type_qualifier_formula (φ ^q^ y))).
  rewrite storeA_restrict_dom.
  rewrite formula_fv_type_qualifier_formula.
  rewrite lvars_open_qual_vars_difference_bound0.
  rewrite lvars_fv_qual_vars_difference_free.
  intros x Hxleft Hxopen.
  apply elem_of_intersection in Hxleft as [Hxσ Hxnot].
  apply elem_of_difference in Hxnot as [_ Hxnot].
  destruct (decide (x = y)) as [->|Hxy].
  - set_solver.
  - apply Hxnot. set_solver.
Qed.

Ltac keep_domain_fv_norm :=
  formula_fv_syntax_norm;
  rewrite ?formula_lvars_fv_basic_world_formula;
  rewrite ?formula_lvars_fv_expr_result_formula;
  rewrite ?formula_lvars_fv_type_qualifier_formula;
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  type_syntax_norm;
  rewrite ?tm_shift_fv;
  cbn [formula_fv formula_lvars fv_tm fv_value];
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free,
    ?lvars_fv_difference_singleton_free;
  rewrite ?tm_lvars_fv, ?context_ty_lvars_fv.

Ltac keep_domain_fv_norm_in H :=
  formula_fv_syntax_norm_in H;
  rewrite ?formula_lvars_fv_basic_world_formula in H;
  rewrite ?formula_lvars_fv_expr_result_formula in H;
  rewrite ?formula_lvars_fv_type_qualifier_formula in H;
  rewrite ?formula_fv_basic_world_formula in H;
  rewrite ?formula_fv_expr_result_formula in H;
  rewrite ?formula_fv_type_qualifier_formula in H;
  type_syntax_norm_in H;
  rewrite ?tm_shift_fv in H;
  cbn [formula_fv formula_lvars fv_tm fv_value] in H;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free,
    ?lvars_fv_difference_singleton_free in H;
  rewrite ?tm_lvars_fv, ?context_ty_lvars_fv in H.

Lemma fv_tm_lstore_instantiate_lift_free_closed_subset σ e :
  store_closed σ ->
  fv_tm (lstore_instantiate_tm (lstore_lift_free σ) e) ⊆ fv_tm e.
Proof.
  intros Hclosed.
  rewrite lstore_instantiate_tm_no_bvars.
  - change (lstore_to_store (lstore_lift_free σ))
      with (lstore_free_part (lstore_lift_free σ)).
    rewrite lstore_free_part_lift_free.
    pose proof (msubst_fv_delete_tm σ e (proj1 Hclosed)).
    set_solver.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma formula_fv_over_keep_domain_target_subset
    σ b φ e :
  store_closed σ ->
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ))))) ⊆
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ))))).
Proof.
  intros Hclosed a Ha.
  pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset σ e Hclosed)
    as Hfvinst.
  keep_domain_fv_norm_in Ha.
  keep_domain_fv_norm.
  rewrite tm_shift_fv in Ha.
  rewrite tm_shift_fv.
  better_set_solver.
Qed.

Lemma formula_fv_under_keep_domain_target_subset
    σ b φ e :
  store_closed σ ->
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula φ))))) ⊆
  formula_fv
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula φ))))).
Proof.
  intros Hclosed a Ha.
  pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset σ e Hclosed)
    as Hfvinst.
  keep_domain_fv_norm_in Ha.
  keep_domain_fv_norm.
  rewrite tm_shift_fv in Ha.
  rewrite tm_shift_fv.
  better_set_solver.
Qed.

Lemma formula_scoped_over_keep_domain_target
    σ b φ e (m : WfWorldT) :
  store_closed σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (FForall
      (formula_msubst_store σ
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (type_qualifier_formula φ))))))) ->
  formula_scoped_in_world m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))).
Proof.
  intros Hclosed Hproj Hscope.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hσdom.
  unfold formula_scoped_in_world in Hscope |- *.
  rewrite !formula_fv_forall in Hscope |- *.
  intros a Ha.
  pose proof (formula_fv_over_keep_domain_target_subset σ b φ e
    Hclosed a Ha) as Ha_src.
  pose proof (formula_msubst_store_fv_restore σ
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ)))))
    a Ha_src) as Ha_restore.
  rewrite elem_of_union in Ha_restore.
  destruct Ha_restore as [Ha_msubst|Haσ].
  - exact (Hscope _ Ha_msubst).
  - exact (Hσdom _ Haσ).
Qed.

Lemma formula_scoped_under_keep_domain_target
    σ b φ e (m : WfWorldT) :
  store_closed σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (FForall
      (formula_msubst_store σ
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ))))))) ->
  formula_scoped_in_world m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ)))))).
Proof.
  intros Hclosed Hproj Hscope.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hσdom.
  unfold formula_scoped_in_world in Hscope |- *.
  rewrite !formula_fv_forall in Hscope |- *.
  intros a Ha.
  pose proof (formula_fv_under_keep_domain_target_subset σ b φ e
    Hclosed a Ha) as Ha_src.
  pose proof (formula_msubst_store_fv_restore σ
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula φ)))))
    a Ha_src) as Ha_restore.
  rewrite elem_of_union in Ha_restore.
  destruct Ha_restore as [Ha_msubst|Haσ].
  - exact (Hscope _ Ha_msubst).
  - exact (Hσdom _ Haσ).
Qed.

Lemma over_open_keep_domain_consequent
    σ φ y (my : WfWorldT) :
  y ∉ dom (σ : gmap atom value) ->
  y ∉ qual_dom φ ->
  store_singleton_projection σ my ->
  formula_scoped_in_world my
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FOver (type_qualifier_formula φ)))) ->
  my ⊨ formula_msubst_store σ
    (FFibVars
      (set_swap (LVBound 0) (LVFree y)
        (qual_vars φ ∖ {[LVBound 0]}))
      (FOver (type_qualifier_formula (φ ^q^ y)))) ->
  my ⊨ formula_open 0 y
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FOver (type_qualifier_formula φ))).
Proof.
  intros Hyσ Hyφ Hproj Hscope Hfib.
  formula_open_syntax_norm_in Hscope.
  formula_open_syntax_norm.
  rewrite formula_open_over in Hscope |- *.
  rewrite type_qualifier_formula_open in Hscope |- * by exact Hyφ.
  eapply res_models_msubst_store_fibvars_keep_domain_elim_from_model.
  - exact Hproj.
  - apply store_without_lvars_open_type_qualifier_fresh. exact Hyσ.
  - exact Hscope.
  - exact Hfib.
Qed.

Lemma over_open_keep_domain_consequent_norm
    σ φ y (my : WfWorldT) :
  y ∉ dom (σ : gmap atom value) ->
  y ∉ qual_dom φ ->
  store_singleton_projection σ my ->
  formula_scoped_in_world my
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FOver (type_qualifier_formula φ)))) ->
  my ⊨ formula_open 0 y
    (FFibVars
      ((qual_vars φ ∖ {[LVBound 0]}) ∖
        lvars_of_atoms (dom (σ : gmap atom value)))
      (FOver (formula_msubst_store σ (type_qualifier_formula φ)))) ->
  my ⊨ formula_open 0 y
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FOver (type_qualifier_formula φ))).
Proof.
  intros Hyσ Hyφ Hproj Hscope Hfib.
  rewrite formula_open_fibvars in Hfib.
  rewrite formula_open_over in Hfib.
  rewrite formula_open_msubst_store_fresh in Hfib by exact Hyσ.
  rewrite type_qualifier_formula_open in Hfib by exact Hyφ.
  rewrite set_swap_difference_fresh in Hfib.
  2:{ unfold lvars_of_atoms. rewrite elem_of_map.
      intros (z & Hz & _). discriminate. }
  2:{ unfold lvars_of_atoms. rewrite elem_of_map.
      intros (z & Hz & Hzσ). inversion Hz. subst. exact (Hyσ Hzσ). }
  rewrite <- (formula_msubst_store_fibvars σ
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars φ ∖ {[LVBound 0]}))
    (FOver (type_qualifier_formula (φ ^q^ y)))) in Hfib.
  eapply over_open_keep_domain_consequent; eauto.
Qed.

Lemma over_open_keep_domain_consequent_norm_intro
    σ φ y (my : WfWorldT) :
  y ∉ dom (σ : gmap atom value) ->
  y ∉ qual_dom φ ->
  store_singleton_projection σ my ->
  formula_scoped_in_world my
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FOver (type_qualifier_formula φ)))) ->
  my ⊨ formula_open 0 y
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FOver (type_qualifier_formula φ))) ->
  my ⊨ formula_open 0 y
    (FFibVars
      ((qual_vars φ ∖ {[LVBound 0]}) ∖
        lvars_of_atoms (dom (σ : gmap atom value)))
      (FOver (formula_msubst_store σ (type_qualifier_formula φ)))).
Proof.
  intros Hyσ Hyφ Hproj Hscope Hfib.
  formula_open_syntax_norm_in Hscope.
  rewrite formula_open_over in Hscope.
  rewrite type_qualifier_formula_open in Hscope by exact Hyφ.
  formula_open_syntax_norm_in Hfib.
  rewrite formula_open_over in Hfib.
  rewrite type_qualifier_formula_open in Hfib by exact Hyφ.
  pose proof (res_models_msubst_store_fibvars_keep_domain_intro_from_model
    my σ
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars φ ∖ {[LVBound 0]}))
    (FOver (type_qualifier_formula (φ ^q^ y)))
    Hproj
    (store_without_lvars_open_type_qualifier_fresh σ φ y Hyσ)
    Hscope Hfib) as Hmsubst.
  formula_msubst_syntax_norm_in Hmsubst.
  try rewrite dom_lstore_lift_free in Hmsubst.
  rewrite <- set_swap_difference_fresh in Hmsubst.
  2:{ unfold lvars_of_atoms. intros Hbad.
      apply elem_of_map in Hbad as (z & Hz & _). discriminate. }
  2:{ unfold lvars_of_atoms. intros Hbad.
      apply elem_of_map in Hbad as (z & Hz & Hzσ).
      inversion Hz. subst. exact (Hyσ Hzσ). }
  formula_open_syntax_norm.
  change (my ⊨ FFibVars
    (set_swap (LVBound 0) (LVFree y)
      ((qual_vars φ ∖ {[LVBound 0]}) ∖
        lvars_of_atoms (dom (σ : gmap atom value))))
    (FOver (formula_open 0 y
      (formula_msubst_store σ (type_qualifier_formula φ))))).
  rewrite formula_open_msubst_store_fresh by exact Hyσ.
  rewrite type_qualifier_formula_open by exact Hyφ.
  exact Hmsubst.
Qed.

Lemma under_open_keep_domain_consequent
    σ φ y (my : WfWorldT) :
  y ∉ dom (σ : gmap atom value) ->
  y ∉ qual_dom φ ->
  store_singleton_projection σ my ->
  formula_scoped_in_world my
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FUnder (type_qualifier_formula φ)))) ->
  my ⊨ formula_msubst_store σ
    (FFibVars
      (set_swap (LVBound 0) (LVFree y)
        (qual_vars φ ∖ {[LVBound 0]}))
      (FUnder (type_qualifier_formula (φ ^q^ y)))) ->
  my ⊨ formula_open 0 y
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FUnder (type_qualifier_formula φ))).
Proof.
  intros Hyσ Hyφ Hproj Hscope Hfib.
  formula_open_syntax_norm_in Hscope.
  formula_open_syntax_norm.
  rewrite formula_open_under in Hscope |- *.
  rewrite type_qualifier_formula_open in Hscope |- * by exact Hyφ.
  eapply res_models_msubst_store_fibvars_keep_domain_elim_from_model.
  - exact Hproj.
  - apply store_without_lvars_open_type_qualifier_fresh. exact Hyσ.
  - exact Hscope.
  - exact Hfib.
Qed.

Lemma under_open_keep_domain_consequent_norm
    σ φ y (my : WfWorldT) :
  y ∉ dom (σ : gmap atom value) ->
  y ∉ qual_dom φ ->
  store_singleton_projection σ my ->
  formula_scoped_in_world my
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FUnder (type_qualifier_formula φ)))) ->
  my ⊨ formula_open 0 y
    (FFibVars
      ((qual_vars φ ∖ {[LVBound 0]}) ∖
        lvars_of_atoms (dom (σ : gmap atom value)))
      (FUnder (formula_msubst_store σ (type_qualifier_formula φ)))) ->
  my ⊨ formula_open 0 y
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FUnder (type_qualifier_formula φ))).
Proof.
  intros Hyσ Hyφ Hproj Hscope Hfib.
  rewrite formula_open_fibvars in Hfib.
  rewrite formula_open_under in Hfib.
  rewrite formula_open_msubst_store_fresh in Hfib by exact Hyσ.
  rewrite type_qualifier_formula_open in Hfib by exact Hyφ.
  rewrite set_swap_difference_fresh in Hfib.
  2:{ unfold lvars_of_atoms. rewrite elem_of_map.
      intros (z & Hz & _). discriminate. }
  2:{ unfold lvars_of_atoms. rewrite elem_of_map.
      intros (z & Hz & Hzσ). inversion Hz. subst. exact (Hyσ Hzσ). }
  rewrite <- (formula_msubst_store_fibvars σ
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars φ ∖ {[LVBound 0]}))
    (FUnder (type_qualifier_formula (φ ^q^ y)))) in Hfib.
  eapply under_open_keep_domain_consequent; eauto.
Qed.

Lemma under_open_keep_domain_consequent_norm_intro
    σ φ y (my : WfWorldT) :
  y ∉ dom (σ : gmap atom value) ->
  y ∉ qual_dom φ ->
  store_singleton_projection σ my ->
  formula_scoped_in_world my
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FUnder (type_qualifier_formula φ)))) ->
  my ⊨ formula_open 0 y
    (FFibVars (qual_vars φ ∖ {[LVBound 0]})
      (FUnder (type_qualifier_formula φ))) ->
  my ⊨ formula_open 0 y
    (FFibVars
      ((qual_vars φ ∖ {[LVBound 0]}) ∖
        lvars_of_atoms (dom (σ : gmap atom value)))
      (FUnder (formula_msubst_store σ (type_qualifier_formula φ)))).
Proof.
  intros Hyσ Hyφ Hproj Hscope Hfib.
  formula_open_syntax_norm_in Hscope.
  rewrite formula_open_under in Hscope.
  rewrite type_qualifier_formula_open in Hscope by exact Hyφ.
  formula_open_syntax_norm_in Hfib.
  rewrite formula_open_under in Hfib.
  rewrite type_qualifier_formula_open in Hfib by exact Hyφ.
  pose proof (res_models_msubst_store_fibvars_keep_domain_intro_from_model
    my σ
    (set_swap (LVBound 0) (LVFree y)
      (qual_vars φ ∖ {[LVBound 0]}))
    (FUnder (type_qualifier_formula (φ ^q^ y)))
    Hproj
    (store_without_lvars_open_type_qualifier_fresh σ φ y Hyσ)
    Hscope Hfib) as Hmsubst.
  formula_msubst_syntax_norm_in Hmsubst.
  try rewrite dom_lstore_lift_free in Hmsubst.
  rewrite <- set_swap_difference_fresh in Hmsubst.
  2:{ unfold lvars_of_atoms. intros Hbad.
      apply elem_of_map in Hbad as (z & Hz & _). discriminate. }
  2:{ unfold lvars_of_atoms. intros Hbad.
      apply elem_of_map in Hbad as (z & Hz & Hzσ).
      inversion Hz. subst. exact (Hyσ Hzσ). }
  formula_open_syntax_norm.
  change (my ⊨ FFibVars
    (set_swap (LVBound 0) (LVFree y)
      ((qual_vars φ ∖ {[LVBound 0]}) ∖
        lvars_of_atoms (dom (σ : gmap atom value))))
    (FUnder (formula_open 0 y
      (formula_msubst_store σ (type_qualifier_formula φ))))).
  rewrite formula_open_msubst_store_fresh by exact Hyσ.
  rewrite type_qualifier_formula_open by exact Hyφ.
  exact Hmsubst.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_over_body_keep_domain
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
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
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))).
Proof.
  intros Hσty Hproj Hsrc.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (src :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ))))).
  set (dst :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ))))).
  pose proof (formula_scoped_over_keep_domain_target σ b φ e m
    Hclosed Hproj (res_models_scoped _ _ Hsrc)) as Hdstscope.
  change (m ⊨ FForall (formula_msubst_store σ src)) in Hsrc.
  formula_msubst_syntax_norm_in Hsrc.
  eapply (res_models_forall_full_world_impl2_map m); [exact Hdstscope | | exact Hsrc].
  exists (dom (σ : gmap atom value) ∪ fv_tm e ∪ qual_dom φ).
  intros y Hy my Hdom Hrestrict.
  assert (Hyσ : y ∉ dom (σ : gmap atom value)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (Hproj_my : store_singleton_projection σ my).
  { eapply store_singleton_projection_of_restrict_base; eauto. }
  split.
  - intros Hworld.
    formula_open_syntax_norm_in Hworld.
    change (my ⊨ formula_open 0 y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))).
    rewrite formula_open_msubst_store_fresh by exact Hyσ.
    formula_open_syntax_norm.
    change (my ⊨ FAtom (lqual_msubst_store σ
      (lqual_open 0 y
        (basic_world_lqual (<[LVBound 0 := TBase b]> ∅))))).
    rewrite lqual_msubst_store_fresh by
      (unfold lqual_fv, lqual_open, basic_world_lqual;
       cbn [lqual_dom];
       eapply elem_of_disjoint; intros z Hzσ Hzopen;
       pose proof (lvars_fv_open_subset 0 y
         (dom (<[LVBound 0 := TBase b]> ∅ : lty_env)) z Hzopen)
         as Hzopen';
       rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
         lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
       set_solver).
    exact Hworld.
  - split.
    + intros Hresult.
      change (my ⊨ formula_open 0 y
        (formula_msubst_store σ
          (expr_result_formula (tm_shift 0 e) (LVBound 0)))).
      rewrite formula_open_msubst_store_fresh by exact Hyσ.
      eapply expr_result_formula_msubst_store_open_shift_models_back;
        [exact Hclosed|set_solver|exact Hresult].
	    + intros Hfib.
	      eapply over_open_keep_domain_consequent_norm; eauto.
	      * pose proof (formula_scoped_open_from_forall_world_dom
	          m my dst y Hdstscope Hdom) as Hopen_dst_scope.
	        formula_open_syntax_norm_in Hopen_dst_scope.
	        eapply formula_scoped_impl_r.
	        eapply formula_scoped_impl_r.
	        exact Hopen_dst_scope.
	      * rewrite dom_lstore_lift_free in Hfib.
	        change (my ⊨ formula_open 0 y
	          (FFibVars
	            ((qual_vars φ ∖ {[LVBound 0]}) ∖
	              lvars_of_atoms (dom (σ : gmap atom value)))
	            (FOver (formula_msubst_store σ
	              (type_qualifier_formula φ))))) in Hfib.
	        exact Hfib.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_under_body_keep_domain
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
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
	          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
	            (FUnder (type_qualifier_formula φ)))))).
Proof.
  intros Hσty Hproj Hsrc.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  set (src :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula φ))))).
  set (dst :=
    FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula φ))))).
  pose proof (formula_scoped_under_keep_domain_target σ b φ e m
    Hclosed Hproj (res_models_scoped _ _ Hsrc)) as Hdstscope.
  change (m ⊨ FForall (formula_msubst_store σ src)) in Hsrc.
  formula_msubst_syntax_norm_in Hsrc.
  eapply (res_models_forall_full_world_impl2_map m); [exact Hdstscope | | exact Hsrc].
  exists (dom (σ : gmap atom value) ∪ fv_tm e ∪ qual_dom φ).
  intros y Hy my Hdom Hrestrict.
  assert (Hyσ : y ∉ dom (σ : gmap atom value)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (Hproj_my : store_singleton_projection σ my).
  { eapply store_singleton_projection_of_restrict_base; eauto. }
  split.
  - intros Hworld.
    formula_open_syntax_norm_in Hworld.
    change (my ⊨ formula_open 0 y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))).
    rewrite formula_open_msubst_store_fresh by exact Hyσ.
    formula_open_syntax_norm.
    change (my ⊨ FAtom (lqual_msubst_store σ
      (lqual_open 0 y
        (basic_world_lqual (<[LVBound 0 := TBase b]> ∅))))).
    rewrite lqual_msubst_store_fresh by
      (unfold lqual_fv, lqual_open, basic_world_lqual;
       cbn [lqual_dom];
       eapply elem_of_disjoint; intros z Hzσ Hzopen;
       pose proof (lvars_fv_open_subset 0 y
         (dom (<[LVBound 0 := TBase b]> ∅ : lty_env)) z Hzopen)
         as Hzopen';
       rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
         lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
       set_solver).
    exact Hworld.
  - split.
    + intros Hresult.
      change (my ⊨ formula_open 0 y
        (formula_msubst_store σ
          (expr_result_formula (tm_shift 0 e) (LVBound 0)))).
      rewrite formula_open_msubst_store_fresh by exact Hyσ.
      eapply expr_result_formula_msubst_store_open_shift_models_back;
        [exact Hclosed|set_solver|exact Hresult].
    + intros Hfib.
      eapply under_open_keep_domain_consequent_norm; eauto.
      * pose proof (formula_scoped_open_from_forall_world_dom
          m my dst y Hdstscope Hdom) as Hopen_dst_scope.
        formula_open_syntax_norm_in Hopen_dst_scope.
        eapply formula_scoped_impl_r.
        eapply formula_scoped_impl_r.
        exact Hopen_dst_scope.
      * rewrite dom_lstore_lift_free in Hfib.
        change (my ⊨ formula_open 0 y
          (FFibVars
            ((qual_vars φ ∖ {[LVBound 0]}) ∖
              lvars_of_atoms (dom (σ : gmap atom value)))
            (FUnder (formula_msubst_store σ
              (type_qualifier_formula φ))))) in Hfib.
        exact Hfib.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_over_body_keep_domain_back
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (type_qualifier_formula φ))))))) ->
  formula_scoped_in_world m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))) ->
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))) ->
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (type_qualifier_formula φ))))))).
Proof.
  intros Hσty Hproj Hsrc_scope Htgt_scope Htgt.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  eapply res_models_forall_full_world_impl2_map; [exact Hsrc_scope | | exact Htgt].
  exists (dom (σ : gmap atom value) ∪ fv_tm e ∪ qual_dom φ).
  intros y Hy my Hdom Hrestrict.
  assert (Hyσ : y ∉ dom (σ : gmap atom value)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (Hproj_my : store_singleton_projection σ my).
  { eapply store_singleton_projection_of_restrict_base; eauto. }
  split.
  - intros Hworld.
    formula_open_syntax_norm_in Hworld.
    change (my ⊨ formula_open 0 y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))) in Hworld.
    rewrite formula_open_msubst_store_fresh in Hworld by exact Hyσ.
    formula_open_syntax_norm_in Hworld.
    change (my ⊨ FAtom (lqual_msubst_store σ
      (lqual_open 0 y
        (basic_world_lqual (<[LVBound 0 := TBase b]> ∅))))) in Hworld.
    rewrite lqual_msubst_store_fresh in Hworld by
      (unfold lqual_fv, lqual_open, basic_world_lqual;
       cbn [lqual_dom];
       eapply elem_of_disjoint; intros z Hzσ Hzopen;
       pose proof (lvars_fv_open_subset 0 y
         (dom (<[LVBound 0 := TBase b]> ∅ : lty_env)) z Hzopen)
         as Hzopen';
       rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
         lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
       set_solver).
    exact Hworld.
  - split.
    + intros Hresult.
      rewrite formula_open_msubst_store_fresh in Hresult by exact Hyσ.
      eapply expr_result_formula_msubst_store_open_shift_models;
        [exact Hclosed|set_solver|exact Hresult].
    + intros Hfib.
      eapply over_open_keep_domain_consequent_norm_intro;
        [exact Hyσ|exact Hyφ|exact Hproj_my| | exact Hfib].
      * pose proof (formula_scoped_open_from_forall_world_dom
          m my
          (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
            (FImpl
              (expr_result_formula
                (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
                (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FOver (type_qualifier_formula φ)))))
          y Htgt_scope Hdom) as Hopen_tgt_scope.
        formula_open_syntax_norm_in Hopen_tgt_scope.
        eapply formula_scoped_impl_r.
        eapply formula_scoped_impl_r.
        exact Hopen_tgt_scope.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_under_body_keep_domain_back
    σ Σ b φ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ))))))) ->
  formula_scoped_in_world m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ)))))) ->
  res_models m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula
            (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
            (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ)))))) ->
  res_models m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula (tm_shift 0 e) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ))))))).
Proof.
  intros Hσty Hproj Hsrc_scope Htgt_scope Htgt.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  eapply res_models_forall_full_world_impl2_map; [exact Hsrc_scope | | exact Htgt].
  exists (dom (σ : gmap atom value) ∪ fv_tm e ∪ qual_dom φ).
  intros y Hy my Hdom Hrestrict.
  assert (Hyσ : y ∉ dom (σ : gmap atom value)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (Hproj_my : store_singleton_projection σ my).
  { eapply store_singleton_projection_of_restrict_base; eauto. }
  split.
  - intros Hworld.
    formula_open_syntax_norm_in Hworld.
    change (my ⊨ formula_open 0 y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := TBase b]> ∅)))) in Hworld.
    rewrite formula_open_msubst_store_fresh in Hworld by exact Hyσ.
    formula_open_syntax_norm_in Hworld.
    change (my ⊨ FAtom (lqual_msubst_store σ
      (lqual_open 0 y
        (basic_world_lqual (<[LVBound 0 := TBase b]> ∅))))) in Hworld.
    rewrite lqual_msubst_store_fresh in Hworld by
      (unfold lqual_fv, lqual_open, basic_world_lqual;
       cbn [lqual_dom];
       eapply elem_of_disjoint; intros z Hzσ Hzopen;
       pose proof (lvars_fv_open_subset 0 y
         (dom (<[LVBound 0 := TBase b]> ∅ : lty_env)) z Hzopen)
         as Hzopen';
       rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
         lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
       set_solver).
    exact Hworld.
  - split.
    + intros Hresult.
      rewrite formula_open_msubst_store_fresh in Hresult by exact Hyσ.
      eapply expr_result_formula_msubst_store_open_shift_models;
        [exact Hclosed|set_solver|exact Hresult].
    + intros Hfib.
      eapply under_open_keep_domain_consequent_norm_intro;
        [exact Hyσ|exact Hyφ|exact Hproj_my| | exact Hfib].
      pose proof (formula_scoped_open_from_forall_world_dom
        m my
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ)))))
        y Htgt_scope Hdom) as Hopen_tgt_scope.
      formula_open_syntax_norm_in Hopen_tgt_scope.
      eapply formula_scoped_impl_r.
      eapply formula_scoped_impl_r.
      exact Hopen_tgt_scope.
Qed.


End ContextTypeDenotationMsubst.
