(** * Denotation.ContextTypeDenotationOpen *)

From Denotation Require Import Notation.
From Denotation Require Export ContextTypeDenotationTactics.

Section ContextTypeDenotation.

Definition denot_ty
    (Δ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty_lvar_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

Lemma formula_open_denot_ty_lvar_gas_singleton
    k y gas Σ τ e :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  formula_open k y (denot_ty_lvar_gas gas Σ τ e) =
  denot_ty_lvar_gas gas
    (lty_env_open_one k y Σ)
    (cty_open k y τ)
    (open_tm k (vfvar y) e).
Proof.
  intros HΣ He Hτ.
  assert (HΣfree : LVFree y ∉ dom Σ).
  {
    intros Hbad. apply HΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hfresh :
    open_env_fresh_for_lvars (<[k := y]> ∅)
      (dom Σ ∪ denot_relevant_lvars τ e)).
  { denot_open_set. }
  pose proof (formula_open_env_denot_ty_lvar_gas
    (<[k := y]> ∅) gas Σ τ e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  exact Heq.
Qed.

Lemma res_models_open_denot_ty_lvar_guard_to_open
    k y Σ τ e (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ->
  m ⊨ formula_open k y
    (FAnd (context_ty_wf_formula Σ τ)
      (FAnd (basic_world_formula Σ)
        (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
              (expr_total_formula e)))) ->
  m ⊨
    FAnd (context_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ))
      (FAnd (basic_world_formula (lty_env_open_one k y Σ))
        (FAnd
          (expr_basic_typing_formula (lty_env_open_one k y Σ)
            (open_tm k (vfvar y) e) (erase_ty (cty_open k y τ)))
          (expr_total_formula (open_tm k (vfvar y) e)))).
Proof.
  intros Hy Hmodels.
  rewrite !formula_open_and in Hmodels.
  repeat rewrite res_models_and_iff in Hmodels |- *.
  destruct Hmodels as [Hwf [Hworld [Hbasic Htotal]]].
  split.
  - rewrite formula_open_context_ty_wf_formula in Hwf.
    exact Hwf.
  - split.
    + rewrite formula_open_basic_world_formula in Hworld.
      exact Hworld.
    + split.
      * rewrite cty_open_preserves_erasure.
        eapply res_models_open_expr_basic_typing_to_open.
        -- set_solver.
        -- exact Hbasic.
      * rewrite formula_open_expr_total_formula in Htotal by set_solver.
        exact Htotal.
Qed.

Lemma res_models_open_denot_ty_lvar_guard_iff
    k y Σ τ e (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ∪ fv_cty τ ->
  m ⊨ formula_open k y
    (FAnd (context_ty_wf_formula Σ τ)
      (FAnd (basic_world_formula Σ)
        (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
              (expr_total_formula e)))) <->
  m ⊨
    FAnd (context_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ))
      (FAnd (basic_world_formula (lty_env_open_one k y Σ))
        (FAnd
          (expr_basic_typing_formula (lty_env_open_one k y Σ)
            (open_tm k (vfvar y) e) (erase_ty (cty_open k y τ)))
          (expr_total_formula (open_tm k (vfvar y) e)))).
Proof.
  intros Hy. split.
  - apply res_models_open_denot_ty_lvar_guard_to_open. exact Hy.
  - intros Hmodels.
    rewrite !formula_open_and.
    repeat rewrite res_models_and_iff in Hmodels |- *.
    destruct Hmodels as [Hwf [Hworld [Hbasic Htotal]]].
    split.
    + rewrite formula_open_context_ty_wf_formula.
      exact Hwf.
    + split.
      * rewrite formula_open_basic_world_formula.
        exact Hworld.
      * split.
        -- rewrite cty_open_preserves_erasure in Hbasic.
           apply (proj2 (res_models_open_expr_basic_typing_iff
             k y Σ e (erase_ty τ) m ltac:(set_solver))).
           exact Hbasic.
        -- rewrite formula_open_expr_total_formula by set_solver.
           exact Htotal.
Qed.

Lemma formula_open_over_body k y b φ e :
  y ∉ fv_tm e ->
  y ∉ qual_dom φ ->
  formula_open k y
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FOver (type_qualifier_formula φ)))))) =
  FForall
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 (open_tm k (vfvar y) e)) (LVBound 0))
        (FFibVars
          (qual_vars (qual_open_atom (S k) y φ) ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula (qual_open_atom (S k) y φ)))))).
Proof.
  intros Hy Hφ.
  rewrite formula_open_forall.
  rewrite !formula_open_impl.
  rewrite formula_open_basic_world_formula.
  rewrite lvar_store_open_one_succ_bound0_singleton.
  rewrite formula_open_expr_result_formula_shift0_under_core by exact Hy.
  rewrite formula_open_fibvars.
  rewrite lvars_open_qual_vars_difference_bound0_under.
  rewrite formula_open_over.
  rewrite type_qualifier_formula_open by exact Hφ.
  reflexivity.
Qed.

Lemma formula_open_under_body k y b φ e :
  y ∉ fv_tm e ->
  y ∉ qual_dom φ ->
  formula_open k y
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
        (FImpl (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
            (FUnder (type_qualifier_formula φ)))))) =
  FForall
    (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
      (FImpl
        (expr_result_formula (tm_shift 0 (open_tm k (vfvar y) e)) (LVBound 0))
        (FFibVars
          (qual_vars (qual_open_atom (S k) y φ) ∖ {[LVBound 0]})
          (FUnder (type_qualifier_formula (qual_open_atom (S k) y φ)))))).
Proof.
  intros Hy Hφ.
  rewrite formula_open_forall.
  rewrite !formula_open_impl.
  rewrite formula_open_basic_world_formula.
  rewrite lvar_store_open_one_succ_bound0_singleton.
  rewrite formula_open_expr_result_formula_shift0_under_core by exact Hy.
  rewrite formula_open_fibvars.
  rewrite lvars_open_qual_vars_difference_bound0_under.
  rewrite formula_open_under.
  rewrite type_qualifier_formula_open by exact Hφ.
  reflexivity.
Qed.

(** Proof plan for the Arrow/Wand open-body transports below.

    These obligations should stay aligned with Logic syntax, not with a
    special-purpose "Arrow denotation FV" lemma.  Most of the needed
    connective principles already exist:

    - use [res_models_forall_map_subset_fv] or [res_models_forall_transport]
      one direction at a time for the outer [FForall]; avoid introducing a new
      iff lemma unless both directions really share the same proof term.
    - use [res_models_impl_map_future] for nested [FImpl] bodies.
    - use [res_models_wand_map] for the [FWand] case.
    - after the forall witness is opened, normalize the two opens with
      [formula_open_commute_fresh], then apply the recursive IH to the two
      [denot_ty_lvar_gas] subformulas.

    Scope/FV side conditions should not be discharged by an Arrow-specific
    source-covers-target lemma.  The TLet Over case shows the intended shape:
    first fold the expanded branch back through the enclosing
    [denot_ty_lvar_gas] guard/scope facts, then project the branch scope with
    the Logic syntax lemmas.  If the standalone helper shape below lacks the
    enclosing guard needed for that argument, inline the proof into the
    [CTArrow]/[CTWand] branches of [res_models_open_denot_ty_lvar_gas_iff]
    rather than adding a denotation-specific FV transport lemma. *)
Lemma res_models_open_arrow_body_iff
    k y gas Σ τx τr e (m : WfWorldT) :
  (forall k Σ τ e (m : WfWorldT),
    y ∉ lvars_fv (dom Σ) ->
    y ∉ fv_tm e ->
    y ∉ fv_cty τ ->
    m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e) <->
      m ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one k y Σ)
        (cty_open k y τ)
        (open_tm k (vfvar y) e)) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty (CTArrow τx τr) ->
  m ⊨ formula_open k y
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e) (vbvar 0)))))) <->
  m ⊨
    FForall
      (FImpl
        (basic_world_formula
          (<[LVBound 0 := erase_ty (cty_open k y τx)]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env (lty_env_open_one k y Σ)
                (CTArrow (cty_open k y τx) (cty_open (S k) y τr))
                (open_tm k (vfvar y) e))
              (erase_ty (cty_open k y τx)))
            (cty_shift 0 (cty_open k y τx)) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env (lty_env_open_one k y Σ)
                (CTArrow (cty_open k y τx) (cty_open (S k) y τr))
                (open_tm k (vfvar y) e))
              (erase_ty (cty_open k y τx)))
            (cty_open (S k) y τr)
            (tapp_tm (tm_shift 0 (open_tm k (vfvar y) e)) (vbvar 0))))).
Proof.
  intros _ HΣ Hy Hτ.
  assert (HΣfree : LVFree y ∉ dom Σ).
  {
    intros Hbad. apply HΣ. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hfresh :
    open_env_fresh_for_lvars (<[k := y]> ∅)
      (dom Σ ∪ denot_relevant_lvars (CTArrow τx τr) e)).
  { denot_open_set. }
  pose proof (formula_open_env_denot_ty_lvar_gas
    (<[k := y]> ∅) (S gas) Σ (CTArrow τx τr) e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  cbn [denot_ty_lvar_gas] in Heq.
  rewrite formula_open_and in Heq.
  inversion Heq; subst.
  rewrite formula_open_forall.
  rewrite !formula_open_impl.
  rewrite formula_open_basic_world_formula.
  rewrite lvar_store_open_one_succ_bound0_singleton.
  match goal with
  | H : formula_open (S k) y
          (denot_ty_lvar_gas gas _ (cty_shift 0 τx) (tret (vbvar 0))) = _
      |- _ => rewrite H
  end.
  match goal with
  | H : formula_open (S k) y
          (denot_ty_lvar_gas gas _ τr
            (tapp_tm (tm_shift 0 e) (vbvar 0))) = _
      |- _ => rewrite H
  end.
  rewrite cty_open_preserves_erasure.
  reflexivity.
Qed.

Lemma res_models_open_wand_body_iff
    k y gas Σ τx τr e (m : WfWorldT) :
  (forall k Σ τ e (m : WfWorldT),
    y ∉ lvars_fv (dom Σ) ->
    y ∉ fv_tm e ->
    y ∉ fv_cty τ ->
    m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e) <->
      m ⊨ denot_ty_lvar_gas gas
        (lty_env_open_one k y Σ)
        (cty_open k y τ)
        (open_tm k (vfvar y) e)) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty (CTWand τx τr) ->
  m ⊨ formula_open k y
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx))
            τr (tapp_tm (tm_shift 0 e) (vbvar 0)))))) <->
  m ⊨
    FForall
      (FImpl
        (basic_world_formula
          (<[LVBound 0 := erase_ty (cty_open k y τx)]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env (lty_env_open_one k y Σ)
                (CTWand (cty_open k y τx) (cty_open (S k) y τr))
                (open_tm k (vfvar y) e))
              (erase_ty (cty_open k y τx)))
            (cty_shift 0 (cty_open k y τx)) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env (lty_env_open_one k y Σ)
                (CTWand (cty_open k y τx) (cty_open (S k) y τr))
                (open_tm k (vfvar y) e))
              (erase_ty (cty_open k y τx)))
            (cty_open (S k) y τr)
            (tapp_tm (tm_shift 0 (open_tm k (vfvar y) e)) (vbvar 0))))).
Proof.
  intros _ HΣ Hy Hτ.
  assert (HΣfree : LVFree y ∉ dom Σ).
  {
    intros Hbad. apply HΣ. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hfresh :
    open_env_fresh_for_lvars (<[k := y]> ∅)
      (dom Σ ∪ denot_relevant_lvars (CTWand τx τr) e)).
  { denot_open_set. }
  pose proof (formula_open_env_denot_ty_lvar_gas
    (<[k := y]> ∅) (S gas) Σ (CTWand τx τr) e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  cbn [denot_ty_lvar_gas] in Heq.
  rewrite formula_open_and in Heq.
  inversion Heq; subst.
  rewrite formula_open_forall.
  rewrite formula_open_impl.
  rewrite formula_open_wand.
  rewrite formula_open_basic_world_formula.
  rewrite lvar_store_open_one_succ_bound0_singleton.
  match goal with
  | H : formula_open (S k) y
          (denot_ty_lvar_gas gas _ (cty_shift 0 τx) (tret (vbvar 0))) = _
      |- _ => rewrite H
  end.
  match goal with
  | H : formula_open (S k) y
          (denot_ty_lvar_gas gas _ τr
            (tapp_tm (tm_shift 0 e) (vbvar 0))) = _
      |- _ => rewrite H
  end.
  rewrite cty_open_preserves_erasure.
  reflexivity.
Qed.

Lemma res_models_open_denot_ty_lvar_gas_iff
    k y gas Σ τ e (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  m ⊨ formula_open k y (denot_ty_lvar_gas gas Σ τ e) <->
    m ⊨ denot_ty_lvar_gas gas
      (lty_env_open_one k y Σ)
      (cty_open k y τ)
      (open_tm k (vfvar y) e).
Proof.
  intros HΣ Hy Hτ.
  rewrite formula_open_denot_ty_lvar_gas_singleton by assumption.
  reflexivity.
Qed.

End ContextTypeDenotation.
