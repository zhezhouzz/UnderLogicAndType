(** * Denotation.ContextTypeDenotationOpen

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation.
From Denotation Require Export ContextTypeDenotationLvars.

Section ContextTypeDenotation.

Definition denot_ty
    (Δ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  denot_ty_lvar_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

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

Lemma formula_open_expr_result_formula_shift0_under k y e :
  y ∉ fv_tm e ->
  formula_open (S k) y (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula (tm_shift 0 (open_tm k (vfvar y) e)) (LVBound 0).
Proof.
  apply formula_open_expr_result_formula_shift0_under_core.
Qed.

Lemma formula_open_env_lift_expr_result_formula_shift0 η e :
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env ((kmap S η))
    (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula (tm_shift 0 (open_tm_env η e)) (LVBound 0).
Proof.
  apply formula_open_env_lift_expr_result_formula_shift0_core.
Qed.

Lemma lvars_open_qual_vars_difference_bound0_under k y q :
  lvars_open (S k) y (qual_vars q ∖ {[LVBound 0]}) =
  qual_vars (qual_open_atom (S k) y q) ∖ {[LVBound 0]}.
Proof.
  rewrite qual_open_atom_vars.
  apply set_eq. intros v.
  rewrite set_swap_elem.
  rewrite elem_of_difference, elem_of_difference.
  split.
  - intros [Hv Hnot]. split.
    + rewrite set_swap_elem. exact Hv.
    + intros Hbad. apply Hnot.
      rewrite elem_of_singleton in Hbad |- *.
      subst v.
      unfold swap. repeat destruct decide; try lia; try congruence.
  - intros [Hv Hnot]. split.
    + rewrite set_swap_elem in Hv. exact Hv.
    + intros Hbad. apply Hnot.
      rewrite elem_of_singleton in Hbad |- *.
      destruct v as [n|a]; cbn in Hbad;
        unfold swap in Hbad;
        repeat destruct decide; try lia; try congruence.
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
  rewrite formula_open_expr_result_formula_shift0_under by exact Hy.
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
  rewrite formula_open_expr_result_formula_shift0_under by exact Hy.
  rewrite formula_open_fibvars.
  rewrite lvars_open_qual_vars_difference_bound0_under.
  rewrite formula_open_under.
  rewrite type_qualifier_formula_open by exact Hφ.
  reflexivity.
Qed.

Lemma open_tret_bvar0_under k y :
  open_tm (S k) (vfvar y) (tret (vbvar 0)) = tret (vbvar 0).
Proof.
  cbn [open_tm open_value].
  destruct decide; [lia|reflexivity].
Qed.

Lemma open_tapp_tm_shift_bvar0_under k y e :
  open_tm (S k) (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0)) =
  tapp_tm (tm_shift 0 (open_tm k (vfvar y) e)) (vbvar 0).
Proof.
  unfold tapp_tm.
  cbn [open_tm open_value value_shift].
  rewrite tm_shift_open_tm_fvar by lia.
  repeat (destruct decide; try lia); reflexivity.
Qed.

Lemma lty_env_open_one_denot_relevant_bind_under k y Σ τ e T :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  lty_env_open_one (S k) y
    (typed_lty_env_bind (denot_relevant_env Σ τ e) T) =
  typed_lty_env_bind
    (denot_relevant_env (lty_env_open_one k y Σ)
      (cty_open k y τ) (open_tm k (vfvar y) e))
    T.
Proof.
  intros HΣ Hy.
  rewrite typed_lty_env_bind_open_under.
  - rewrite denot_relevant_env_open_one by exact Hy.
    reflexivity.
  - intros Hbad.
    apply HΣ.
    eapply lty_env_restrict_lvars_fv_dom_subset.
    apply lvars_fv_elem. exact Hbad.
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
  {
    apply open_env_fresh_for_lvars_singleton.
    rewrite lvars_fv_union.
    unfold denot_relevant_lvars.
    rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
  }
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
  {
    apply open_env_fresh_for_lvars_singleton.
    rewrite lvars_fv_union.
    unfold denot_relevant_lvars.
    rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
  }
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
  induction gas as [|gas IH] in k, Σ, τ, e, m, HΣ, Hy, Hτ |- *.
  - cbn [denot_ty_lvar_gas].
    rewrite formula_open_and.
    repeat rewrite res_models_and_iff.
    rewrite (res_models_open_denot_ty_lvar_guard_iff
      k y (denot_relevant_env Σ τ e) τ e m).
    + rewrite denot_relevant_env_open_one by exact Hy.
      rewrite formula_open_true.
      repeat rewrite res_models_and_iff.
      reflexivity.
    + unfold denot_relevant_env, denot_relevant_lvars.
      pose proof (lty_env_restrict_lvars_fv_subset
        Σ (context_ty_lvars τ ∪ tm_lvars e)) as Hsubfv.
      rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
      set_solver.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas].
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTOver b φ) e)
        (CTOver b φ) e m).
      * rewrite denot_relevant_env_open_one by exact Hy.
        repeat rewrite res_models_and_iff.
        split; intros [Hguard Hbody]; split; [exact Hguard| | exact Hguard|].
        -- rewrite formula_open_over_body in Hbody.
           exact Hbody.
           ++ exact Hy.
           ++ unfold fv_cty, context_ty_lvars in Hτ.
              cbn [context_ty_lvars_at] in Hτ.
              rewrite lvars_fv_lvars_at_depth in Hτ. exact Hτ.
        -- rewrite formula_open_over_body.
           exact Hbody.
           ++ exact Hy.
           ++ unfold fv_cty, context_ty_lvars in Hτ.
              cbn [context_ty_lvars_at] in Hτ.
              rewrite lvars_fv_lvars_at_depth in Hτ. exact Hτ.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTOver b φ) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTUnder b φ) e)
        (CTUnder b φ) e m).
      * rewrite denot_relevant_env_open_one by exact Hy.
        repeat rewrite res_models_and_iff.
        split; intros [Hguard Hbody]; split; [exact Hguard| | exact Hguard|].
        -- rewrite formula_open_under_body in Hbody.
           exact Hbody.
           ++ exact Hy.
           ++ unfold fv_cty, context_ty_lvars in Hτ.
              cbn [context_ty_lvars_at] in Hτ.
              rewrite lvars_fv_lvars_at_depth in Hτ. exact Hτ.
        -- rewrite formula_open_under_body.
           exact Hbody.
           ++ exact Hy.
           ++ unfold fv_cty, context_ty_lvars in Hτ.
              cbn [context_ty_lvars_at] in Hτ.
              rewrite lvars_fv_lvars_at_depth in Hτ. exact Hτ.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTUnder b φ) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTInter τ1 τ2) e)
        (CTInter τ1 τ2) e m).
      * rewrite denot_relevant_env_open_one by exact Hy.
        repeat rewrite res_models_and_iff.
        split; intros [Hguard Hbody]; split; [exact Hguard| | exact Hguard|].
        -- rewrite formula_open_and in Hbody.
           apply res_models_and_iff in Hbody as [Hbody1 Hbody2].
           apply res_models_and_iff. split.
           ++ apply (proj1 (IH k Σ τ1 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hbody1.
           ++ apply (proj1 (IH k Σ τ2 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hbody2.
        -- apply res_models_and_iff in Hbody as [Hbody1 Hbody2].
           rewrite formula_open_and.
           apply res_models_and_iff. split.
           ++ apply (proj2 (IH k Σ τ1 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hbody1.
           ++ apply (proj2 (IH k Σ τ2 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hbody2.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTInter τ1 τ2) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTUnion τ1 τ2) e)
        (CTUnion τ1 τ2) e m).
      * rewrite denot_relevant_env_open_one by exact Hy.
        repeat rewrite res_models_and_iff.
        split; intros [Hguard Hbody]; split; [exact Hguard| | exact Hguard|].
        -- rewrite formula_open_or in Hbody.
           assert (HguardF :
             m ⊨ FAnd
               (context_ty_wf_formula
                 (denot_relevant_env (lty_env_open_one k y Σ)
                   (cty_open k y (CTUnion τ1 τ2))
                   (open_tm k (vfvar y) e))
                 (cty_open k y (CTUnion τ1 τ2)))
               (FAnd
                 (basic_world_formula
                   (denot_relevant_env (lty_env_open_one k y Σ)
                     (cty_open k y (CTUnion τ1 τ2))
                     (open_tm k (vfvar y) e)))
                 (FAnd
                   (expr_basic_typing_formula
                     (denot_relevant_env (lty_env_open_one k y Σ)
                       (cty_open k y (CTUnion τ1 τ2))
                       (open_tm k (vfvar y) e))
                     (open_tm k (vfvar y) e)
                     (erase_ty (cty_open k y (CTUnion τ1 τ2))))
                   (expr_total_formula (open_tm k (vfvar y) e))))).
           { repeat rewrite res_models_and_iff. exact Hguard. }
           eapply res_models_or_transport_between_worlds;
             [| | | | exact Hbody].
           ++ eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
                [| exact HguardF].
              unfold context_ty_lvars. cbn [context_ty_lvars_at]. set_solver.
           ++ eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
                [| exact HguardF].
              unfold context_ty_lvars. cbn [context_ty_lvars_at]. set_solver.
           ++ intros Hτ1.
              apply (proj1 (IH k Σ τ1 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ1.
           ++ intros Hτ2.
              apply (proj1 (IH k Σ τ2 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ2.
        -- assert (HguardF :
             m ⊨ FAnd
               (context_ty_wf_formula
                 (denot_relevant_env (lty_env_open_one k y Σ)
                   (cty_open k y (CTUnion τ1 τ2))
                   (open_tm k (vfvar y) e))
                 (cty_open k y (CTUnion τ1 τ2)))
               (FAnd
                 (basic_world_formula
                   (denot_relevant_env (lty_env_open_one k y Σ)
                     (cty_open k y (CTUnion τ1 τ2))
                     (open_tm k (vfvar y) e)))
                 (FAnd
                   (expr_basic_typing_formula
                     (denot_relevant_env (lty_env_open_one k y Σ)
                       (cty_open k y (CTUnion τ1 τ2))
                       (open_tm k (vfvar y) e))
                     (open_tm k (vfvar y) e)
                     (erase_ty (cty_open k y (CTUnion τ1 τ2))))
                   (expr_total_formula (open_tm k (vfvar y) e))))).
           { repeat rewrite res_models_and_iff. exact Hguard. }
           eapply res_models_or_transport_between_worlds;
             [| | | | exact Hbody].
           ++ transitivity
                (fv_tm (open_tm k (vfvar y) e) ∪
                 fv_cty (cty_open k y τ1)).
              ** apply formula_fv_open_denot_ty_lvar_gas_subset_relevant.
                 --- exact Hy.
                 --- unfold fv_cty, context_ty_lvars in Hτ |- *.
                     cbn [context_ty_lvars_at] in Hτ.
                     rewrite lvars_fv_union in Hτ. set_solver.
              ** pose proof (denot_guard_term_type_fv_scope
                   (lty_env_open_one k y Σ)
                   (cty_open k y (CTUnion τ1 τ2))
                   (open_tm k (vfvar y) e) m HguardF) as Hscope.
                 intros a Ha. apply Hscope.
                 apply elem_of_union in Ha as [Ha|Ha].
                 --- apply elem_of_union_l. exact Ha.
                 --- apply elem_of_union_r.
                     unfold fv_cty, context_ty_lvars in Ha |- *.
                     cbn [cty_open context_ty_lvars_at].
                     rewrite lvars_fv_union. apply elem_of_union_l. exact Ha.
           ++ transitivity
                (fv_tm (open_tm k (vfvar y) e) ∪
                 fv_cty (cty_open k y τ2)).
              ** apply formula_fv_open_denot_ty_lvar_gas_subset_relevant.
                 --- exact Hy.
                 --- unfold fv_cty, context_ty_lvars in Hτ |- *.
                     cbn [context_ty_lvars_at] in Hτ.
                     rewrite lvars_fv_union in Hτ. set_solver.
              ** pose proof (denot_guard_term_type_fv_scope
                   (lty_env_open_one k y Σ)
                   (cty_open k y (CTUnion τ1 τ2))
                   (open_tm k (vfvar y) e) m HguardF) as Hscope.
                 intros a Ha. apply Hscope.
                 apply elem_of_union in Ha as [Ha|Ha].
                 --- apply elem_of_union_l. exact Ha.
                 --- apply elem_of_union_r.
                     unfold fv_cty, context_ty_lvars in Ha |- *.
                     cbn [cty_open context_ty_lvars_at].
                     rewrite lvars_fv_union. apply elem_of_union_r. exact Ha.
           ++ intros Hτ1.
              apply (proj2 (IH k Σ τ1 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ1.
           ++ intros Hτ2.
              apply (proj2 (IH k Σ τ2 e m HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ2.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTUnion τ1 τ2) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTSum τ1 τ2) e)
        (CTSum τ1 τ2) e m).
      * rewrite denot_relevant_env_open_one by exact Hy.
        repeat rewrite res_models_and_iff.
        split; intros [Hguard Hbody]; split; [exact Hguard| | exact Hguard|].
        -- rewrite formula_open_plus in Hbody.
           assert (HguardF :
             m ⊨ FAnd
               (context_ty_wf_formula
                 (denot_relevant_env (lty_env_open_one k y Σ)
                   (cty_open k y (CTSum τ1 τ2))
                   (open_tm k (vfvar y) e))
                 (cty_open k y (CTSum τ1 τ2)))
               (FAnd
                 (basic_world_formula
                   (denot_relevant_env (lty_env_open_one k y Σ)
                     (cty_open k y (CTSum τ1 τ2))
                     (open_tm k (vfvar y) e)))
                 (FAnd
                   (expr_basic_typing_formula
                     (denot_relevant_env (lty_env_open_one k y Σ)
                       (cty_open k y (CTSum τ1 τ2))
                       (open_tm k (vfvar y) e))
                     (open_tm k (vfvar y) e)
                     (erase_ty (cty_open k y (CTSum τ1 τ2))))
                   (expr_total_formula (open_tm k (vfvar y) e))))).
           { repeat rewrite res_models_and_iff. exact Hguard. }
           eapply res_models_plus_map; [| | | exact Hbody].
           ++ apply formula_scoped_in_world_from_formula_fv.
              rewrite formula_fv_plus.
              assert (Hscope1 :
                formula_fv
                  (denot_ty_lvar_gas gas (lty_env_open_one k y Σ)
                    (cty_open k y τ1) (open_tm k (vfvar y) e)) ⊆
                world_dom (m : WorldT)).
              {
                eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
                  [| exact HguardF].
                unfold context_ty_lvars. cbn [context_ty_lvars_at]. set_solver.
              }
              assert (Hscope2 :
                formula_fv
                  (denot_ty_lvar_gas gas (lty_env_open_one k y Σ)
                    (cty_open k y τ2) (open_tm k (vfvar y) e)) ⊆
                world_dom (m : WorldT)).
              {
                eapply formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open;
                  [| exact HguardF].
                unfold context_ty_lvars. cbn [context_ty_lvars_at]. set_solver.
              }
              set_solver.
           ++ intros m' Hτ1.
              apply (proj1 (IH k Σ τ1 e m' HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ1.
           ++ intros m' Hτ2.
              apply (proj1 (IH k Σ τ2 e m' HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ2.
        -- assert (HguardF :
             m ⊨ FAnd
               (context_ty_wf_formula
                 (denot_relevant_env (lty_env_open_one k y Σ)
                   (cty_open k y (CTSum τ1 τ2))
                   (open_tm k (vfvar y) e))
                 (cty_open k y (CTSum τ1 τ2)))
               (FAnd
                 (basic_world_formula
                   (denot_relevant_env (lty_env_open_one k y Σ)
                     (cty_open k y (CTSum τ1 τ2))
                     (open_tm k (vfvar y) e)))
                 (FAnd
                   (expr_basic_typing_formula
                     (denot_relevant_env (lty_env_open_one k y Σ)
                       (cty_open k y (CTSum τ1 τ2))
                       (open_tm k (vfvar y) e))
                     (open_tm k (vfvar y) e)
                     (erase_ty (cty_open k y (CTSum τ1 τ2))))
                   (expr_total_formula (open_tm k (vfvar y) e))))).
           { repeat rewrite res_models_and_iff. exact Hguard. }
           eapply res_models_plus_map; [| | | exact Hbody].
           ++ apply formula_scoped_in_world_from_formula_fv.
              rewrite formula_fv_plus.
              assert (Hscope :
                fv_tm (open_tm k (vfvar y) e) ∪
                fv_cty (cty_open k y (CTSum τ1 τ2)) ⊆
                world_dom (m : WorldT)).
              {
                apply (denot_guard_term_type_fv_scope
                  (lty_env_open_one k y Σ)
                  (cty_open k y (CTSum τ1 τ2))
                  (open_tm k (vfvar y) e) m HguardF).
              }
              assert (Hscope1 :
                formula_fv
                  (formula_open k y
                    (denot_ty_lvar_gas gas Σ τ1 e)) ⊆
                world_dom (m : WorldT)).
              {
                transitivity
                  (fv_tm (open_tm k (vfvar y) e) ∪
                   fv_cty (cty_open k y τ1)).
                - apply formula_fv_open_denot_ty_lvar_gas_subset_relevant.
                  + exact Hy.
                  + unfold fv_cty, context_ty_lvars in Hτ |- *.
                    cbn [context_ty_lvars_at] in Hτ.
                    rewrite lvars_fv_union in Hτ. set_solver.
                - intros a Ha. apply Hscope.
                  apply elem_of_union in Ha as [Ha|Ha].
                  + apply elem_of_union_l. exact Ha.
                  + apply elem_of_union_r.
                    unfold fv_cty, context_ty_lvars in Ha |- *.
                    cbn [cty_open context_ty_lvars_at].
                    rewrite lvars_fv_union. apply elem_of_union_l. exact Ha.
              }
              assert (Hscope2 :
                formula_fv
                  (formula_open k y
                    (denot_ty_lvar_gas gas Σ τ2 e)) ⊆
                world_dom (m : WorldT)).
              {
                transitivity
                  (fv_tm (open_tm k (vfvar y) e) ∪
                   fv_cty (cty_open k y τ2)).
                - apply formula_fv_open_denot_ty_lvar_gas_subset_relevant.
                  + exact Hy.
                  + unfold fv_cty, context_ty_lvars in Hτ |- *.
                    cbn [context_ty_lvars_at] in Hτ.
                    rewrite lvars_fv_union in Hτ. set_solver.
                - intros a Ha. apply Hscope.
                  apply elem_of_union in Ha as [Ha|Ha].
                  + apply elem_of_union_l. exact Ha.
                  + apply elem_of_union_r.
                    unfold fv_cty, context_ty_lvars in Ha |- *.
                    cbn [cty_open context_ty_lvars_at].
                    rewrite lvars_fv_union. apply elem_of_union_r. exact Ha.
              }
              set_solver.
           ++ intros m' Hτ1.
              apply (proj2 (IH k Σ τ1 e m' HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ1.
           ++ intros m' Hτ2.
              apply (proj2 (IH k Σ τ2 e m' HΣ Hy
                ltac:(unfold fv_cty, context_ty_lvars in Hτ;
                  cbn [context_ty_lvars_at] in Hτ;
                  rewrite lvars_fv_union in Hτ; set_solver))). exact Hτ2.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTSum τ1 τ2) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTArrow τx τr) e)
        (CTArrow τx τr) e m).
	    * rewrite denot_relevant_env_open_one by exact Hy.
	      repeat rewrite res_models_and_iff.
	      split.
	      -- intros [Hguard Hbody]. split; [exact Hguard|].
	         pose proof (res_models_open_arrow_body_iff
	          k y gas Σ τx τr e m IH HΣ Hy Hτ) as Hiff.
	         apply (proj1 Hiff). exact Hbody.
	      -- intros [Hguard Hbody]. split; [exact Hguard|].
	         pose proof (res_models_open_arrow_body_iff
	          k y gas Σ τx τr e m IH HΣ Hy Hτ) as Hiff.
	         apply (proj2 Hiff). exact Hbody.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
    + rewrite formula_open_and.
      repeat rewrite res_models_and_iff.
      rewrite (res_models_open_denot_ty_lvar_guard_iff
        k y (denot_relevant_env Σ (CTWand τx τr) e)
        (CTWand τx τr) e m).
	    * rewrite denot_relevant_env_open_one by exact Hy.
	      repeat rewrite res_models_and_iff.
	      split.
	      -- intros [Hguard Hbody]. split; [exact Hguard|].
	         pose proof (res_models_open_wand_body_iff
	          k y gas Σ τx τr e m IH HΣ Hy Hτ) as Hiff.
	         apply (proj1 Hiff). exact Hbody.
	      -- intros [Hguard Hbody]. split; [exact Hguard|].
	         pose proof (res_models_open_wand_body_iff
	          k y gas Σ τx τr e m IH HΣ Hy Hτ) as Hiff.
	         apply (proj2 Hiff). exact Hbody.
      * unfold denot_relevant_env, denot_relevant_lvars.
        pose proof (lty_env_restrict_lvars_fv_subset
          Σ (context_ty_lvars (CTWand τx τr) ∪ tm_lvars e)) as Hsubfv.
        rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv in Hsubfv.
        set_solver.
Qed.

End ContextTypeDenotation.
