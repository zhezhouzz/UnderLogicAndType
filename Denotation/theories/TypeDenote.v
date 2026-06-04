(** * Denotation.TypeDenote *)

From Denotation Require Import Notation.

Section TypeDenote.

Definition ty_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))).

Definition ty_static_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (expr_basic_typing_formula Σ e (erase_ty τ))).

Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := relevant_env Σ τ e in
  FAnd
    (ty_guard_formula Σg τ e)
    (match gas with
    | 0 => FTrue
    | S gas' =>
      match τ with
      | CTOver b φ =>
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
              (FImpl
                (expr_result_formula (tm_shift 0 e) (LVBound 0))
                (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                  (FOver (type_qualifier_formula φ)))))
      | CTUnder b φ =>
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
              (FImpl
                (expr_result_formula (tm_shift 0 e) (LVBound 0))
                (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                  (FUnder (type_qualifier_formula φ)))))
      | CTInter τ1 τ2 =>
          FAnd
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          FPlus
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTArrow τx τr =>
          let Σx := typed_lty_env_bind Σg (erase_ty τx) in
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := (erase_ty τx)]> ∅))
              (FImpl
                (ty_denote_gas gas' Σx
                  (cty_shift 0 τx) (tret (vbvar 0)))
                (ty_denote_gas gas' Σx τr
                  (tapp_tm (tm_shift 0 e) (vbvar 0)))))
      | CTWand τx τr =>
          let Σx := typed_lty_env_bind Σg (erase_ty τx) in
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := (erase_ty τx)]> ∅))
              (FWand
                (ty_denote_gas gas' Σx
                  (cty_shift 0 τx) (tret (vbvar 0)))
                (ty_denote_gas gas' Σx τr
                  (tapp_tm (tm_shift 0 e) (vbvar 0)))))
    end
    end).

Lemma open_env_lift_fresh_for_bound0_bind_dom η T :
  open_env_fresh_for_lvars
    (kmap S η)
    (dom (<[LVBound 0 := T]> (∅ : gmap logic_var ty))).
Proof.
  replace (dom (<[LVBound 0 := T]> (∅ : gmap logic_var ty)))
    with ({[LVBound 0]} : lvset)
    by (rewrite dom_insert_L, dom_empty_L; set_solver).
  apply open_env_lift_fresh_for_bound0_singleton.
Qed.

Lemma formula_open_env_denot_guard η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η
    (ty_guard_formula (relevant_env Σ τ e) τ e) =
  ty_guard_formula
    (relevant_env (lty_env_open_lvars η Σ)
      (open_cty_env η τ) (open_tm_env η e))
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  intros Hfresh Hinj.
  unfold ty_guard_formula.
  rewrite !formula_open_env_and.
  rewrite formula_open_env_context_ty_wf_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (relevant_env_dom_subset_direct Σ τ e).
    unfold relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_basic_world_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (relevant_env_dom_subset_direct Σ τ e).
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_expr_basic_typing_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (relevant_env_dom_subset_direct Σ τ e).
    unfold relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_expr_total_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    unfold relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite relevant_env_open_env by exact Hfresh || exact Hinj.
  rewrite open_cty_env_preserves_erasure.
  reflexivity.
Qed.

Lemma formula_open_env_ty_denote_gas_zero η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (ty_denote_gas 0 Σ τ e) =
  ty_denote_gas 0
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  intros Hfresh Hinj.
  cbn [ty_denote_gas].
  rewrite formula_open_env_and.
  rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
  rewrite formula_open_env_true.
  reflexivity.
Qed.

Ltac denot_open_env_child_fresh Hfresh :=
  eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
  unfold relevant_lvars;
  intros v Hv; cbn [context_ty_lvars context_ty_lvars_at] in *;
  set_solver.

Ltac denot_open_env_qual_case η Hfresh Hinj φ e :=
  let Hfreshφ := fresh "Hfreshφ" in
  let Hfreshe := fresh "Hfreshe" in
  assert (Hfreshφ :
      open_env_fresh_for_lvars ((kmap S η)) (qual_vars φ));
  [ apply open_env_lift_fresh_for_lvars_at_depth1;
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
    unfold relevant_lvars;
    cbn [context_ty_lvars context_ty_lvars_at];
    set_solver
  | assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e));
    [ eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
      unfold relevant_lvars; set_solver
    | cbn [ty_denote_gas];
      rewrite formula_open_env_and;
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj);
      first [rewrite open_cty_env_over by exact Hinj
            |rewrite open_cty_env_under by exact Hinj];
      cbn [ty_denote_gas];
      rewrite formula_open_env_forall by exact Hinj;
      rewrite !formula_open_env_impl;
      rewrite formula_open_env_basic_world_formula;
      [|apply open_env_lift_fresh_for_bound0_bind_dom
       |apply open_env_values_inj_lift; exact Hinj];
      rewrite lty_env_open_lvars_lift_bound0_singleton by exact Hinj;
      rewrite open_env_lift_expr_result_shift0_core
        by (exact Hfreshe || exact Hinj);
      rewrite formula_open_env_fibvars;
      [|eapply open_env_fresh_for_lvars_mono; [|exact Hfreshφ]; set_solver];
      rewrite open_env_lift_qual_diff_bound0
        by exact Hfreshφ;
      first [rewrite formula_open_env_over
            |rewrite formula_open_env_under];
      rewrite type_qualifier_formula_open_env;
      [reflexivity
      |exact Hfreshφ
      |apply open_env_values_inj_lift; exact Hinj] ] ].

Ltac denot_open_env_binary_case IH Hfresh Hinj :=
  cbn [ty_denote_gas];
  rewrite formula_open_env_and;
  rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj);
  first [rewrite open_cty_env_inter
        |rewrite open_cty_env_union
        |rewrite open_cty_env_sum];
  cbn [ty_denote_gas];
  first [rewrite formula_open_env_and
        |rewrite formula_open_env_or
        |rewrite formula_open_env_plus];
  rewrite (IH _ _ _ _);
  [|denot_open_env_child_fresh Hfresh|exact Hinj];
  rewrite (IH _ _ _ _);
  [reflexivity|denot_open_env_child_fresh Hfresh|exact Hinj].

Lemma formula_open_env_ty_denote_gas η gas Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (ty_denote_gas gas Σ τ e) =
  ty_denote_gas gas
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  (* Multi-open commutes with type denotation.  The local tactics below cover
     the qualifier and binary connective branches; Arrow/Wand recurse under
     [formula_open_env_forall] with [(kmap S η)]. *)
  revert Σ τ e η.
  induction gas as [|gas IH]; intros Σ τ e η Hfresh Hinj.
  - apply formula_open_env_ty_denote_gas_zero; assumption.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr].
    + denot_open_env_qual_case η Hfresh Hinj φ e.
    + denot_open_env_qual_case η Hfresh Hinj φ e.
    + denot_open_env_binary_case IH Hfresh Hinj.
    + denot_open_env_binary_case IH Hfresh Hinj.
    + denot_open_env_binary_case IH Hfresh Hinj.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (relevant_env Σ (CTArrow τx τr) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (relevant_env_dom_subset_direct Σ (CTArrow τx τr) e).
        set_solver.
      }
      assert (Hfresh_arg :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
           relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_arrow_arg_lift_support_subset.
      }
      assert (Hfresh_body :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
           relevant_lvars τr
             (tapp_tm (tm_shift 0 e) (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply arrow_body_lvars_lift_support_subset.
      }
      cbn [ty_denote_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      cbn [ty_denote_gas].
      rewrite formula_open_env_forall by exact Hinj.
      rewrite !formula_open_env_impl.
      rewrite formula_open_env_basic_world_formula.
      2:{
        apply open_env_lift_fresh_for_bound0_bind_dom.
      }
      2: apply open_env_values_inj_lift; exact Hinj.
      rewrite lty_env_open_lvars_lift_bound0_singleton by exact Hinj.
      rewrite (IH
        (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_arg.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e) (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_body.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift by exact HfreshΣg.
      rewrite relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      rewrite open_cty_env_preserves_erasure.
      rewrite open_cty_env_lift_shift0_exact by exact Hinj.
      rewrite open_tm_env_lift_tret_bound0.
      rewrite open_tm_env_lift_tapp_shift_bvar0.
      reflexivity.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (relevant_env Σ (CTWand τx τr) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (relevant_env_dom_subset_direct Σ (CTWand τx τr) e).
        set_solver.
      }
      assert (Hfresh_arg :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
           relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_wand_arg_lift_support_subset.
      }
      assert (Hfresh_body :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
           relevant_lvars τr
             (tapp_tm (tm_shift 0 e) (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_wand_body_lift_support_subset.
      }
      cbn [ty_denote_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      cbn [ty_denote_gas].
      rewrite formula_open_env_forall by exact Hinj.
      rewrite formula_open_env_impl.
      rewrite formula_open_env_wand.
      rewrite formula_open_env_basic_world_formula.
      2:{
        apply open_env_lift_fresh_for_bound0_bind_dom.
      }
      2: apply open_env_values_inj_lift; exact Hinj.
      rewrite lty_env_open_lvars_lift_bound0_singleton by exact Hinj.
      rewrite (IH
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_arg.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e) (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_body.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift by exact HfreshΣg.
      rewrite relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      rewrite open_cty_env_preserves_erasure.
      rewrite open_cty_env_lift_shift0_exact by exact Hinj.
      rewrite open_tm_env_lift_tret_bound0.
      rewrite open_tm_env_lift_tapp_shift_bvar0.
      reflexivity.
Qed.

Lemma ty_denote_gas_env_agree_on gas Σ1 Σ2 τ e X :
  relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  ty_denote_gas gas Σ1 τ e =
  ty_denote_gas gas Σ2 τ e.
Proof.
  induction gas as [|gas IH] in Σ1, Σ2, τ, e, X |- *; intros Hsub Heq.
  - cbn [ty_denote_gas].
    unfold relevant_env, lty_env_restrict_lvars.
    erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
    reflexivity.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2];
      cbn [ty_denote_gas].
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
Qed.

Lemma res_models_ty_denote_gas_env_agree_on
    gas Σ1 Σ2 τ e X (m : WfWorldT) :
  relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  m ⊨ ty_denote_gas gas Σ1 τ e ->
  m ⊨ ty_denote_gas gas Σ2 τ e.
Proof.
  intros Hsub Heq Hmodels.
  rewrite <- (ty_denote_gas_env_agree_on gas Σ1 Σ2 τ e X Hsub Heq).
  exact Hmodels.
Qed.

End TypeDenote.

(** ** Free-variable support for denotation formulas *)

Section TypeDenoteSupport.

Ltac rewrite_tm_support :=
  repeat match goal with
  | |- context [lvars_at_depth ?d (tm_lvars ?e)] =>
      rewrite (tm_lvars_depth e d)
  | H : context [lvars_at_depth ?d (tm_lvars ?e)] |- _ =>
      rewrite (tm_lvars_depth e d) in H
  end.

Ltac unfold_formula_lvars_atoms :=
  unfold ty_guard_formula;
  cbn [formula_lvars_at context_ty_wf_formula basic_world_formula
    expr_basic_typing_formula expr_total_formula expr_result_formula
    type_qualifier_formula];
  unfold lqual_lvars, context_ty_wf_lqual, basic_world_lqual,
    expr_basic_typing_lqual, expr_total_lqual, expr_result_lqual,
    type_qualifier_lqual;
  cbn [lqual_dom].

Ltac normalize_denot_formula_lvars :=
  unfold_formula_lvars_atoms;
  repeat rewrite ?lvars_at_depth_union;
  rewrite_tm_support;
  rewrite ?context_ty_lvars_depth;
  rewrite ?tm_lvars_at_shift_under by lia;
  rewrite ?context_ty_lvars_at_shift_under by lia;
  rewrite ?value_lvars_at_bound0_under;
  rewrite ?tm_lvars_at_tret_bound0_under;
  rewrite ?lvars_at_depth_dom_singleton_bound0_succ;
  rewrite ?lvars_at_depth_singleton_bound0_succ;
  rewrite ?lvars_at_depth_empty;
  cbn [context_ty_lvars_at tm_lvars_at value_lvars_at].

Lemma ty_denote_gas_lvars_subset gas d Σ τ e :
  formula_lvars_at d (ty_denote_gas gas Σ τ e) ⊆
  tm_lvars_at d e ∪ context_ty_lvars_at d τ.
Proof.
  induction gas as [|gas IH] in d, Σ, τ, e |- *.
  - cbn [ty_denote_gas formula_lvars_at].
    normalize_denot_formula_lvars.
    pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ τ e).
    intros v Hv.
    set_unfold in H.
    set_unfold in Hv.
    set_unfold.
    destruct Hv as [[Hv|[Hv|[Hv|Hv]]]|Hv].
    + specialize (H v Hv). tauto.
    + specialize (H v Hv). tauto.
    + specialize (H v Hv). tauto.
    + tauto.
    + tauto.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2];
      cbn [ty_denote_gas formula_lvars_at].
    + normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ (CTOver b φ) e).
      pose proof (lvars_at_depth_mono (S d)
        (qual_vars φ ∖ {[LVBound 0]}) (qual_vars φ)
        ltac:(set_solver)).
      cbn [context_ty_lvars_at].
      set_solver.
    + normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ (CTUnder b φ) e).
      pose proof (lvars_at_depth_mono (S d)
        (qual_vars φ ∖ {[LVBound 0]}) (qual_vars φ)
        ltac:(set_solver)).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ (CTInter τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ (CTUnion τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ (CTSum τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      rewrite ?lvars_at_depth_dom_singleton_bound0_succ.
      rewrite ?lvars_at_depth_singleton_bound0_succ.
      rewrite ?lvars_at_depth_empty.
      rewrite ?tm_lvars_at_tret_bound0_under.
      rewrite ?context_ty_lvars_at_shift_under by lia.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        d Σ (CTArrow τ1 τ2) e) as Hrel.
      pose proof (IH (S d)
        (typed_lty_env_bind (relevant_env Σ (CTArrow τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0))) as Harg.
      rewrite tm_lvars_at_tret_bound0_under in Harg.
      rewrite context_ty_lvars_at_shift_under in Harg by lia.
      pose proof (IH (S d)
        (typed_lty_env_bind (relevant_env Σ (CTArrow τ1 τ2) e)
          (erase_ty τ1))
        τ2 (tapp_tm (tm_shift 0 e) (vbvar 0))) as Hres.
      pose proof (tm_lvars_at_tapp_shift0_bound0 e d) as Htapp.
      cbn [context_ty_lvars_at].
      cbn [context_ty_lvars_at] in Hrel.
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      rewrite ?lvars_at_depth_dom_singleton_bound0_succ.
      rewrite ?lvars_at_depth_singleton_bound0_succ.
      rewrite ?lvars_at_depth_empty.
      rewrite ?tm_lvars_at_tret_bound0_under.
      rewrite ?context_ty_lvars_at_shift_under by lia.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        d Σ (CTWand τ1 τ2) e) as Hrel.
      pose proof (IH (S d)
        (typed_lty_env_bind (relevant_env Σ (CTWand τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0))) as Harg.
      rewrite tm_lvars_at_tret_bound0_under in Harg.
      rewrite context_ty_lvars_at_shift_under in Harg by lia.
      pose proof (IH (S d)
        (typed_lty_env_bind (relevant_env Σ (CTWand τ1 τ2) e)
          (erase_ty τ1))
        τ2 (tapp_tm (tm_shift 0 e) (vbvar 0))) as Hres.
      pose proof (tm_lvars_at_tapp_shift0_bound0 e d) as Htapp.
      cbn [context_ty_lvars_at].
      cbn [context_ty_lvars_at] in Hrel.
      set_solver.
Qed.

Lemma ty_denote_gas_fv_subset gas Σ τ e :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  rewrite <- (formula_lvars_at_fv 0).
  transitivity (lvars_fv (relevant_lvars τ e)).
  - apply lvars_fv_mono.
    unfold relevant_lvars.
    transitivity (tm_lvars_at 0 e ∪ context_ty_lvars_at 0 τ).
    + apply ty_denote_gas_lvars_subset.
    + change (tm_lvars_at 0 e) with (tm_lvars e).
      change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ).
      set_solver.
  - rewrite relevant_lvars_fv. set_solver.
Qed.

Lemma ty_denote_gas_scope_of_guard
    gas Σ τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τbig e) τbig)
    (FAnd (basic_world_formula (relevant_env Σ τbig e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τbig e) e
          (erase_ty τbig))
        (expr_total_formula e))) ->
  formula_fv (ty_denote_gas gas Σ τsmall e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hτ Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal_e]]].
  transitivity (fv_tm e ∪ fv_cty τsmall).
  - apply ty_denote_gas_fv_subset.
  - pose proof (res_models_fuel_scoped _ _ _ Htotal_e) as Hscope_e.
    unfold formula_scoped_in_world in Hscope_e.
    rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_e.
    pose proof (context_ty_wf_formula_fv_cty_subset
      (relevant_env Σ τbig e) τbig m Hwf) as Hτbig_fv.
    pose proof (proj1 (basic_world_formula_models_iff
      (relevant_env Σ τbig e) m) Hworld)
      as [_ [Hworld_dom _]].
    assert (Hτsmall_fv : fv_cty τsmall ⊆ fv_cty τbig).
    {
      rewrite <- !context_ty_lvars_fv.
      apply lvars_fv_mono. exact Hτ.
    }
    set_solver.
Qed.

End TypeDenoteSupport.
