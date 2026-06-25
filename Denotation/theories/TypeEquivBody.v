(** * Denotation.TypeEquivBody

    Body cases for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import TypeEquivCore TypeEquivTerm TypeEquivFiberBody.
From Denotation Require TypeEquivFiberBaseCore.

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
          (FOver (FAtom φ)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTOver b φ) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FAtom φ)))).
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
          (FUnder (FAtom φ)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0 (dom (relevant_env Σ (CTUnder b φ) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FAtom φ)))).
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
