(** * Denotation.ContextTypeDenotationSaturateBody

    Split out from [ContextTypeDenotationSaturate.v] to keep individual proof files small. *)

From Denotation Require Import Notation ContextTypeDenotationMsubstCore.
From Denotation Require Export ContextTypeDenotationTactics.
From Denotation Require Import ContextTypeDenotationSaturateCore.

Section ContextTypeDenotation.

Lemma denot_ty_lvar_gas_tm_result_equiv_over_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTOver b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e1) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e2) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_tm_result_equiv_on_term_lc_lvars
    Σ (CTOver b φ) m e1 e2 Hequiv) as [Hlc_e1 Hlc_e2].
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ (CTOver b φ) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ (CTOver b φ) e2 m Hzero_tgt) as Hguard_tgt.
  assert (Hscope_tgt :
      formula_scoped_in_world m
        (denot_ty_lvar_gas (S gas) Σ (CTOver b φ) e2)).
  {
    unfold formula_scoped_in_world.
    eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
      [reflexivity|exact Hguard_tgt].
  }
  cbn [denot_ty_lvar_gas] in Hscope_tgt.
  pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hbody_scope.
  eapply res_models_forall_full_world_impl2_map;
    [exact Hbody_scope| |exact Hsrc].
  exists (fv_tm e1 ∪ fv_tm e2).
  intros y Hy my Hdom Hrestrict.
  split.
  - intros Hworld. exact Hworld.
  - split.
    + intros Hresult.
      eapply expr_result_formula_shift0_transport_of_tm_result_equiv_open;
        [ exact (proj1 Hequiv)
        | exact Hlc_e1
        | exact Hlc_e2
        | | set_solver
        | exact Hdom
        | exact Hrestrict
        | exact Hresult ].
      eapply typed_total_tm_result_equiv_on_term_scope. exact Hequiv.
    + intros Hfib. exact Hfib.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_under_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTUnder b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e1) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ))))) ->
  m ⊨
    FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl
          (expr_result_formula (tm_shift 0 e2) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ))))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_tm_result_equiv_on_term_lc_lvars
    Σ (CTUnder b φ) m e1 e2 Hequiv) as [Hlc_e1 Hlc_e2].
  pose proof (typed_total_tm_result_equiv_on_target_zero
    Σ (CTUnder b φ) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ (CTUnder b φ) e2 m Hzero_tgt) as Hguard_tgt.
  assert (Hscope_tgt :
      formula_scoped_in_world m
        (denot_ty_lvar_gas (S gas) Σ (CTUnder b φ) e2)).
  {
    unfold formula_scoped_in_world.
    eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
      [reflexivity|exact Hguard_tgt].
  }
  cbn [denot_ty_lvar_gas] in Hscope_tgt.
  pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hbody_scope.
  eapply res_models_forall_full_world_impl2_map;
    [exact Hbody_scope| |exact Hsrc].
  exists (fv_tm e1 ∪ fv_tm e2).
  intros y Hy my Hdom Hrestrict.
  split.
  - intros Hworld. exact Hworld.
  - split.
    + intros Hresult.
      eapply expr_result_formula_shift0_transport_of_tm_result_equiv_open;
        [ exact (proj1 Hequiv)
        | exact Hlc_e1
        | exact Hlc_e2
        | | set_solver
        | exact Hdom
        | exact Hrestrict
        | exact Hresult ].
      eapply typed_total_tm_result_equiv_on_term_scope. exact Hequiv.
    + intros Hfib. exact Hfib.
Qed.

Lemma denot_ty_lvar_gas_zero_project_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  erase_ty τsmall = erase_ty τbig ->
  context_ty_shape_ok τsmall ->
  m ⊨ denot_ty_lvar_gas 0 Σ τbig e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τsmall e.
Proof.
  intros Hτ Herase Hshape_small Hzero.
  apply denot_ty_lvar_gas_zero_of_guard.
  apply denot_ty_lvar_gas_guard_of_zero in Hzero.
  repeat rewrite res_models_and_iff in Hzero |- *.
  destruct Hzero as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (denot_relevant_env_dom_mono_context
    Σ τsmall τbig e Hτ) as Hdom_small_big.
  assert (Hrel_small_big :
      denot_relevant_lvars τsmall e ⊆ denot_relevant_lvars τbig e).
  { unfold denot_relevant_lvars. set_solver. }
  split.
  - apply context_ty_wf_formula_models_iff in Hwf
      as [Hlc_big [Hscope_big Hbasic_big]].
    apply context_ty_wf_formula_models_iff.
    assert (HbasicΣ_small :
        basic_context_ty_lvars (dom Σ) τsmall).
    {
      destruct Hbasic_big as [Hvars_big _].
      split; [|exact Hshape_small].
      intros v Hv.
      eapply denot_relevant_env_dom_subset_direct.
      apply Hvars_big. exact (Hτ _ Hv).
    }
    split.
    + intros v Hv. apply Hlc_big. exact (Hdom_small_big _ Hv).
    + split.
      * intros a Ha.
        apply Hscope_big.
        apply lvars_fv_elem in Ha.
        apply lvars_fv_elem. exact (Hdom_small_big _ Ha).
      * apply basic_context_ty_lvars_denot_relevant_env.
        exact HbasicΣ_small.
  - split.
    + eapply basic_world_formula_denot_relevant_mono_context; eauto.
    + split.
      * apply expr_basic_typing_formula_models_iff in Hbasic
          as [Hlc_big [Hscope_big Hty_big]].
        apply expr_basic_typing_formula_models_iff.
        split.
        -- intros v Hv. apply Hlc_big. exact (Hdom_small_big _ Hv).
        -- split.
           ++ intros a Ha.
              apply Hscope_big.
              apply lvars_fv_elem in Ha.
              apply lvars_fv_elem. exact (Hdom_small_big _ Ha).
           ++ rewrite Herase.
              replace (denot_relevant_env Σ τsmall e) with
                (storeA_restrict
                  (denot_relevant_env Σ τbig e)
                  (denot_relevant_lvars τsmall e)).
              2:{
                unfold denot_relevant_env.
                rewrite <- (denot_relevant_env_restrict_subset
                  Σ τbig e (denot_relevant_lvars τsmall e) Hrel_small_big).
                reflexivity.
              }
              eapply basic_tm_has_ltype_restrict_lvars_lc.
              ** exact Hty_big.
              ** eapply basic_tm_has_ltype_lc; eauto.
              ** unfold denot_relevant_lvars. set_solver.
      * exact Htotal.
Qed.

Lemma denot_ty_lvar_gas_zero_inter_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ1 (CTInter τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply denot_ty_lvar_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma denot_ty_lvar_gas_zero_inter_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTInter τ1 τ2)).
  {
    apply denot_ty_lvar_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ2 (CTInter τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_tm_result_equiv_on_inter_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ1 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_inter_l; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_inter_l; exact Hzero_tgt.
Qed.

Lemma typed_total_tm_result_equiv_on_inter_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ2 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_inter_r; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_inter_r; exact Hzero_tgt.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_inter_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  m ⊨ denot_ty_lvar_gas gas Σ τ1 e1 /\
  m ⊨ denot_ty_lvar_gas gas Σ τ2 e1 ->
  m ⊨ denot_ty_lvar_gas gas Σ τ1 e2 /\
  m ⊨ denot_ty_lvar_gas gas Σ τ2 e2.
Proof.
  intros Hequiv [H1 H2].
  split.
  - eapply IH; [|exact H1].
    eapply typed_total_tm_result_equiv_on_inter_l; exact Hequiv.
  - eapply IH; [|exact H2].
    eapply typed_total_tm_result_equiv_on_inter_r; exact Hequiv.
Qed.

Lemma denot_ty_lvar_gas_zero_union_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ1 (CTUnion τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply denot_ty_lvar_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma denot_ty_lvar_gas_zero_union_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTUnion τ1 τ2)).
  {
    apply denot_ty_lvar_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ2 (CTUnion τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_tm_result_equiv_on_union_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ1 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_union_l; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_union_l; exact Hzero_tgt.
Qed.

Lemma typed_total_tm_result_equiv_on_union_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_tm_result_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_tm_result_equiv_on Σ τ2 m e1 e2.
Proof.
  intros [Heq [Hzero_src Hzero_tgt]].
  split; [exact Heq|].
  split.
  - eapply denot_ty_lvar_gas_zero_union_r; exact Hzero_src.
  - eapply denot_ty_lvar_gas_zero_union_r; exact Hzero_tgt.
Qed.

Lemma denot_ty_lvar_gas_scope_from_zero_any
    gas Σ τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  formula_scoped_in_world m (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hzero.
  eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open.
  - reflexivity.
  - apply denot_ty_lvar_gas_guard_of_zero. exact Hzero.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_union_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  m ⊨
    FOr
      (denot_ty_lvar_gas gas Σ τ1 e1)
      (denot_ty_lvar_gas gas Σ τ2 e1) ->
  m ⊨
    FOr
	      (denot_ty_lvar_gas gas Σ τ1 e2)
	      (denot_ty_lvar_gas gas Σ τ2 e2).
Proof.
  intros Hequiv Hbody.
  pose proof (typed_total_tm_result_equiv_on_union_l
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv1.
  pose proof (typed_total_tm_result_equiv_on_union_r
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv2.
  pose proof (res_models_scoped _ _ Hbody) as Hscope_body.
  apply (proj1 (res_models_or_iff m _ _ Hscope_body)) in Hbody.
  destruct Hbody as [H1|H2].
  - eapply res_models_or_intro_l_from_model.
    + eapply IH; [exact Hequiv1|exact H1].
    + eapply denot_ty_lvar_gas_scope_from_zero_any.
      exact (typed_total_tm_result_equiv_on_target_zero
        Σ τ2 m e1 e2 Hequiv2).
  - eapply res_models_or_intro_r_from_model.
    + eapply denot_ty_lvar_gas_scope_from_zero_any.
      exact (typed_total_tm_result_equiv_on_target_zero
        Σ τ1 m e1 e2 Hequiv1).
    + eapply IH; [exact Hequiv2|exact H2].
Qed.

Lemma denot_ty_lvar_gas_zero_res_subset
    (Σ : lty_env) τ e (m n : WfWorldT) :
  res_subset n m ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ e ->
  n ⊨ denot_ty_lvar_gas 0 Σ τ e.
Proof.
  intros Hsub Hzero.
  apply denot_ty_lvar_gas_zero_of_guard.
  apply denot_ty_lvar_gas_guard_of_zero in Hzero.
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

Lemma denot_ty_lvar_gas_zero_sum_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ1 (CTSum τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply denot_ty_lvar_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma denot_ty_lvar_gas_zero_sum_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTSum τ1 τ2)).
  {
    apply denot_ty_lvar_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (denot_ty_lvar_gas_zero_project_context
    Σ τ2 (CTSum τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_l_target_zero
    (Σ : lty_env) τ1 τ2 (e1 e2 : tm) (m m1 : WfWorldT) :
  res_subset m1 m ->
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e2 ->
  m1 ⊨ denot_ty_lvar_gas 0 Σ τ1 e2.
Proof.
  intros Hsub Hzero.
  apply denot_ty_lvar_gas_zero_sum_l with (τ2 := τ2).
  eapply denot_ty_lvar_gas_zero_res_subset; eauto.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_r_target_zero
    (Σ : lty_env) τ1 τ2 (e1 e2 : tm) (m m2 : WfWorldT) :
  res_subset m2 m ->
  m ⊨ denot_ty_lvar_gas 0 Σ (CTSum τ1 τ2) e2 ->
  m2 ⊨ denot_ty_lvar_gas 0 Σ τ2 e2.
Proof.
  intros Hsub Hzero.
  apply denot_ty_lvar_gas_zero_sum_r with (τ1 := τ1).
  eapply denot_ty_lvar_gas_zero_res_subset; eauto.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_l_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m1 : WfWorldT) :
  res_subset m1 m ->
  typed_total_tm_result_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m1 ⊨ denot_ty_lvar_gas gas Σ τ1 e1 ->
  typed_total_tm_result_equiv_on Σ τ1 m1 e1 e2.
Proof.
  intros Hsub [Heq [_ Hzero_tgt]] Hsrc.
  split.
  - eapply tm_result_equiv_on_res_store_subset; eauto.
  - split.
    + apply denot_ty_lvar_gas_zero_of_guard.
      eapply denot_ty_lvar_gas_guard. exact Hsrc.
    + eapply typed_total_tm_result_equiv_on_sum_l_target_zero;
        eauto.
Qed.

Lemma typed_total_tm_result_equiv_on_sum_r_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m2 : WfWorldT) :
  res_subset m2 m ->
  typed_total_tm_result_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m2 ⊨ denot_ty_lvar_gas gas Σ τ2 e1 ->
  typed_total_tm_result_equiv_on Σ τ2 m2 e1 e2.
Proof.
  intros Hsub [Heq [_ Hzero_tgt]] Hsrc.
  split.
  - eapply tm_result_equiv_on_res_store_subset; eauto.
  - split.
    + apply denot_ty_lvar_gas_zero_of_guard.
      eapply denot_ty_lvar_gas_guard. exact Hsrc.
    + eapply typed_total_tm_result_equiv_on_sum_r_target_zero;
        eauto.
Qed.

Lemma denot_ty_lvar_gas_tm_result_equiv_sum_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_tm_result_equiv_on Σ τ m e1 e2 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e1 ->
      m ⊨ denot_ty_lvar_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_tm_result_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m ⊨
    FPlus
      (denot_ty_lvar_gas gas Σ τ1 e1)
      (denot_ty_lvar_gas gas Σ τ2 e1) ->
  m ⊨
    FPlus
	      (denot_ty_lvar_gas gas Σ τ1 e2)
	      (denot_ty_lvar_gas gas Σ τ2 e2).
Proof.
  intros Hequiv Hbody.
  apply res_models_plus_iff in Hbody as
    [n1 [n2 [Hdef [Hle [Hτ1 Hτ2]]]]].
  destruct (res_sum_pullback_subset_projection_full m n1 n2 Hdef Hle)
    as [Hsub1 [Hsub2 [Hdef_full Hle_full]]].
  set (m1 := res_pullback_subset_projection m n1 Hsub1).
  set (m2 := res_pullback_subset_projection m n2 Hsub2).
  assert (Hτ1_full : m1 ⊨ denot_ty_lvar_gas gas Σ τ1 e1).
  {
    subst m1.
    eapply res_models_pullback_subset_projection. exact Hτ1.
  }
  assert (Hτ2_full : m2 ⊨ denot_ty_lvar_gas gas Σ τ2 e1).
  {
    subst m2.
    eapply res_models_pullback_subset_projection. exact Hτ2.
  }
	  eapply res_models_plus_intro; [exact Hle_full| |].
	  - eapply IH; [|exact Hτ1_full].
	    refine (typed_total_tm_result_equiv_on_sum_l_pullback
	      gas Σ τ1 τ2 e1 e2 m m1 _ Hequiv Hτ1_full).
	    subst m1. apply res_pullback_subset_projection_subset.
	  - eapply IH; [|exact Hτ2_full].
	    refine (typed_total_tm_result_equiv_on_sum_r_pullback
	      gas Σ τ1 τ2 e1 e2 m m2 _ Hequiv Hτ2_full).
	    subst m2. apply res_pullback_subset_projection_subset.
	Qed.

End ContextTypeDenotation.
