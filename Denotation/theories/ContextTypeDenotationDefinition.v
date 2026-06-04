(** * Denotation.ContextTypeDenotationDefinition

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation.

Section ContextTypeDenotation.

Fixpoint denot_ty_lvar_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := denot_relevant_env Σ τ e in
  FAnd
    (FAnd (context_ty_wf_formula Σg τ)
      (FAnd (basic_world_formula Σg)
        (FAnd (expr_basic_typing_formula Σg e (erase_ty τ))
              (expr_total_formula e))))
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
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          FPlus
            (denot_ty_lvar_gas gas' Σ τ1 e)
            (denot_ty_lvar_gas gas' Σ τ2 e)
      | CTArrow τx τr =>
          let Σx := typed_lty_env_bind Σg (erase_ty τx) in
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := (erase_ty τx)]> ∅))
              (FImpl
                (denot_ty_lvar_gas gas' Σx
                  (cty_shift 0 τx) (tret (vbvar 0)))
                (denot_ty_lvar_gas gas' Σx τr
                  (tapp_tm (tm_shift 0 e) (vbvar 0)))))
      | CTWand τx τr =>
          let Σx := typed_lty_env_bind Σg (erase_ty τx) in
          FForall
            (FImpl (basic_world_formula (<[LVBound 0 := (erase_ty τx)]> ∅))
              (FWand
                (denot_ty_lvar_gas gas' Σx
                  (cty_shift 0 τx) (tret (vbvar 0)))
                (denot_ty_lvar_gas gas' Σx τr
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
  open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η
    (FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
      (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
        (FAnd
          (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
            (erase_ty τ))
          (expr_total_formula e)))) =
  FAnd
    (context_ty_wf_formula
      (denot_relevant_env (lty_env_open_lvars η Σ)
        (open_cty_env η τ) (open_tm_env η e))
      (open_cty_env η τ))
    (FAnd
      (basic_world_formula
        (denot_relevant_env (lty_env_open_lvars η Σ)
          (open_cty_env η τ) (open_tm_env η e)))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env (lty_env_open_lvars η Σ)
            (open_cty_env η τ) (open_tm_env η e))
          (open_tm_env η e) (erase_ty (open_cty_env η τ)))
        (expr_total_formula (open_tm_env η e)))).
Proof.
  intros Hfresh Hinj.
  rewrite !formula_open_env_and.
  rewrite formula_open_env_context_ty_wf_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (denot_relevant_env_dom_subset_direct Σ τ e).
    unfold denot_relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_basic_world_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (denot_relevant_env_dom_subset_direct Σ τ e).
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_expr_basic_typing_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (denot_relevant_env_dom_subset_direct Σ τ e).
    unfold denot_relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_expr_total_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    unfold denot_relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite denot_relevant_env_open_env by exact Hfresh || exact Hinj.
  rewrite open_cty_env_preserves_erasure.
  reflexivity.
Qed.

Lemma formula_open_env_denot_ty_lvar_gas_zero η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (denot_ty_lvar_gas 0 Σ τ e) =
  denot_ty_lvar_gas 0
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  intros Hfresh Hinj.
  cbn [denot_ty_lvar_gas].
  rewrite formula_open_env_and.
  rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
  rewrite formula_open_env_true.
  reflexivity.
Qed.

Lemma formula_open_env_denot_ty_lvar_gas η gas Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (denot_ty_lvar_gas gas Σ τ e) =
  denot_ty_lvar_gas gas
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  (* Main mopen theorem.  The intended proof is by induction on [gas].
     The guard part is handled by [formula_open_env_denot_guard].  Recursive
     branches use the IH directly; Arrow/Wand recurse under
     [formula_open_env_forall] with [(kmap S η)]. *)
  revert Σ τ e η.
  induction gas as [|gas IH]; intros Σ τ e η Hfresh Hinj.
  - apply formula_open_env_denot_ty_lvar_gas_zero; assumption.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr].
    + assert (Hfreshφ :
        open_env_fresh_for_lvars ((kmap S η)) (qual_vars φ)).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        cbn [context_ty_lvars context_ty_lvars_at].
        set_solver.
      }
      assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e)).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars. set_solver.
      }
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_over by exact Hinj.
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_forall by exact Hinj.
      rewrite !formula_open_env_impl.
      rewrite formula_open_env_basic_world_formula.
      2:{
        apply open_env_lift_fresh_for_bound0_bind_dom.
      }
      2: apply open_env_values_inj_lift; exact Hinj.
      rewrite lty_env_open_lvars_lift_bound0_singleton by exact Hinj.
      rewrite formula_open_env_lift_expr_result_formula_shift0_core
        by (exact Hfreshe || exact Hinj).
      rewrite formula_open_env_fibvars.
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfreshφ].
        set_solver.
      }
      rewrite lvars_open_env_lift_qual_vars_difference_bound0
        by exact Hfreshφ.
      rewrite formula_open_env_over.
      rewrite type_qualifier_formula_open_env.
      2: exact Hfreshφ.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      reflexivity.
    + assert (Hfreshφ :
        open_env_fresh_for_lvars ((kmap S η)) (qual_vars φ)).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        cbn [context_ty_lvars context_ty_lvars_at].
        set_solver.
      }
      assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e)).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars. set_solver.
      }
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_under by exact Hinj.
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_forall by exact Hinj.
      rewrite !formula_open_env_impl.
      rewrite formula_open_env_basic_world_formula.
      2:{
        apply open_env_lift_fresh_for_bound0_bind_dom.
      }
      2: apply open_env_values_inj_lift; exact Hinj.
      rewrite lty_env_open_lvars_lift_bound0_singleton by exact Hinj.
      rewrite formula_open_env_lift_expr_result_formula_shift0_core
        by (exact Hfreshe || exact Hinj).
      rewrite formula_open_env_fibvars.
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfreshφ].
        set_solver.
      }
      rewrite lvars_open_env_lift_qual_vars_difference_bound0
        by exact Hfreshφ.
      rewrite formula_open_env_under.
      rewrite type_qualifier_formula_open_env.
      2: exact Hfreshφ.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      reflexivity.
    + cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_inter.
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite (IH Σ τ1 e η).
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        intros v Hv. cbn [context_ty_lvars context_ty_lvars_at] in *.
        set_solver.
      }
      2: exact Hinj.
      rewrite (IH Σ τ2 e η).
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        intros v Hv. cbn [context_ty_lvars context_ty_lvars_at] in *.
        set_solver.
      }
      2: exact Hinj.
      reflexivity.
    + cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_union.
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_or.
      rewrite (IH Σ τ1 e η).
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        intros v Hv. cbn [context_ty_lvars context_ty_lvars_at] in *.
        set_solver.
      }
      2: exact Hinj.
      rewrite (IH Σ τ2 e η).
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        intros v Hv. cbn [context_ty_lvars context_ty_lvars_at] in *.
        set_solver.
      }
      2: exact Hinj.
      reflexivity.
    + cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_sum.
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_plus.
      rewrite (IH Σ τ1 e η).
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        intros v Hv. cbn [context_ty_lvars context_ty_lvars_at] in *.
        set_solver.
      }
      2: exact Hinj.
      rewrite (IH Σ τ2 e η).
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold denot_relevant_lvars.
        intros v Hv. cbn [context_ty_lvars context_ty_lvars_at] in *.
        set_solver.
      }
      2: exact Hinj.
      reflexivity.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (denot_relevant_env Σ (CTArrow τx τr) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (denot_relevant_env_dom_subset_direct Σ (CTArrow τx τr) e).
        set_solver.
      }
      assert (Hfresh_arg :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
           denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_arrow_arg_lift_support_subset.
      }
      assert (Hfresh_body :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
           denot_relevant_lvars τr
             (tapp_tm (tm_shift 0 e) (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_arrow_body_lift_support_subset.
      }
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      cbn [denot_ty_lvar_gas].
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
          (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_arg.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e) (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_body.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift by exact HfreshΣg.
      rewrite denot_relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      rewrite open_cty_env_preserves_erasure.
      rewrite open_cty_env_lift_shift0_exact by exact Hinj.
      rewrite open_tm_env_lift_tret_bound0.
      rewrite open_tm_env_lift_tapp_shift_bvar0.
      reflexivity.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (denot_relevant_env Σ (CTWand τx τr) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (denot_relevant_env_dom_subset_direct Σ (CTWand τx τr) e).
        set_solver.
      }
      assert (Hfresh_arg :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
           denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_wand_arg_lift_support_subset.
      }
      assert (Hfresh_body :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
           denot_relevant_lvars τr
             (tapp_tm (tm_shift 0 e) (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply lvars_at_depth_wand_body_lift_support_subset.
      }
      cbn [denot_ty_lvar_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      cbn [denot_ty_lvar_gas].
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
          (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_arg.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e) (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_body.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift by exact HfreshΣg.
      rewrite denot_relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      rewrite open_cty_env_preserves_erasure.
      rewrite open_cty_env_lift_shift0_exact by exact Hinj.
      rewrite open_tm_env_lift_tret_bound0.
      rewrite open_tm_env_lift_tapp_shift_bvar0.
      reflexivity.
Qed.

Lemma res_models_open_env_denot_ty_lvar_gas_iff
    η gas Σ τ e (m : WfWorldT) :
  open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e) ->
  open_env_values_inj η ->
  m ⊨ formula_open_env η (denot_ty_lvar_gas gas Σ τ e) <->
  m ⊨ denot_ty_lvar_gas gas
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  intros Hfresh Hinj.
  rewrite (formula_open_env_denot_ty_lvar_gas η gas Σ τ e Hfresh Hinj).
  reflexivity.
Qed.

Lemma denot_ty_lvar_gas_env_agree_on gas Σ1 Σ2 τ e X :
  denot_relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  denot_ty_lvar_gas gas Σ1 τ e =
  denot_ty_lvar_gas gas Σ2 τ e.
Proof.
  induction gas as [|gas IH] in Σ1, Σ2, τ, e, X |- *; intros Hsub Heq.
  - cbn [denot_ty_lvar_gas].
    unfold denot_relevant_env, lty_env_restrict_lvars.
    erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
    reflexivity.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2];
      cbn [denot_ty_lvar_gas].
    + unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold denot_relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold denot_relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold denot_relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold denot_relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold denot_relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold denot_relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold denot_relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
Qed.

Lemma res_models_denot_ty_lvar_gas_env_agree_on
    gas Σ1 Σ2 τ e X (m : WfWorldT) :
  denot_relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  m ⊨ denot_ty_lvar_gas gas Σ1 τ e ->
  m ⊨ denot_ty_lvar_gas gas Σ2 τ e.
Proof.
  intros Hsub Heq Hmodels.
  rewrite <- (denot_ty_lvar_gas_env_agree_on gas Σ1 Σ2 τ e X Hsub Heq).
  exact Hmodels.
Qed.

End ContextTypeDenotation.
