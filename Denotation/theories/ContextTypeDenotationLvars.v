(** * Denotation.ContextTypeDenotationLvars

    Split out from [ContextTypeDenotation.v] to keep individual proof files small. *)

From Denotation Require Import Notation.
From Denotation Require Export ContextTypeDenotationDefinition.

Section ContextTypeDenotation.

Fixpoint formula_lvars_at (d : nat) (φ : FormulaT) : lvset :=
  match φ with
  | FTrue | FFalse => ∅
  | FAtom q => lvars_at_depth d (lqual_lvars q)
  | FAnd p q | FOr p q | FImpl p q
  | FStar p q | FWand p q | FPlus p q =>
      formula_lvars_at d p ∪ formula_lvars_at d q
  | FForall p => formula_lvars_at (S d) p
  | FOver p | FUnder p => formula_lvars_at d p
  | FFibVars D p => lvars_at_depth d D ∪ formula_lvars_at d p
  end.

Lemma formula_lvars_at_fv d (φ : FormulaT) :
  lvars_fv (formula_lvars_at d φ) = formula_fv φ.
Proof.
  induction φ in d |- *; cbn [formula_lvars_at];
    rewrite ?lvars_fv_lvars_at_depth, ?lvars_fv_union,
      ?IHφ1, ?IHφ2, ?IHφ;
    rewrite ?formula_fv_true, ?formula_fv_false, ?formula_fv_atom,
      ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl,
      ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus,
      ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under,
      ?formula_fv_fibvars;
    rewrite ?lvars_fv_lvars_at_depth;
    reflexivity.
Qed.

Lemma formula_lvars_at_open d k y (φ : FormulaT) :
  formula_lvars_at d (formula_open (d + k) y φ) =
  lvars_open k y (formula_lvars_at d φ).
Proof.
  induction φ in d, k |- *; cbn [formula_open formula_lvars_at].
  - set_solver.
  - set_solver.
  - match goal with
    | |- context [lqual_open _ _ ?q] => destruct q as [D P]
    end.
    cbn [lqual_open lqual_lvars lqual_dom].
    apply lvars_at_depth_open.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - rewrite IHφ1, IHφ2.
    symmetry. rewrite lvars_open_union. reflexivity.
  - replace (S (d + k)) with (S d + k) by lia.
    apply IHφ.
  - apply IHφ.
  - apply IHφ.
  - rewrite lvars_at_depth_open.
    rewrite IHφ.
    symmetry. rewrite lvars_open_union. reflexivity.
Qed.

Ltac rewrite_tm_support :=
  repeat match goal with
  | |- context [lvars_at_depth ?d (tm_lvars ?e)] =>
      rewrite (tm_lvars_depth e d)
  | H : context [lvars_at_depth ?d (tm_lvars ?e)] |- _ =>
      rewrite (tm_lvars_depth e d) in H
  end.

Ltac unfold_formula_lvars_atoms :=
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

Lemma formula_lvars_at_denot_ty_lvar_gas_subset_relevant gas d Σ τ e :
  formula_lvars_at d (denot_ty_lvar_gas gas Σ τ e) ⊆
  tm_lvars_at d e ∪ context_ty_lvars_at d τ.
Proof.
  induction gas as [|gas IH] in d, Σ, τ, e |- *.
  - cbn [denot_ty_lvar_gas formula_lvars_at].
    normalize_denot_formula_lvars.
    pose proof (lvars_at_depth_denot_relevant_env_subset_relevant d Σ τ e).
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
      cbn [denot_ty_lvar_gas formula_lvars_at].
    + normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant d Σ (CTOver b φ) e).
      pose proof (lvars_at_depth_mono (S d)
        (qual_vars φ ∖ {[LVBound 0]}) (qual_vars φ)
        ltac:(set_solver)).
      cbn [context_ty_lvars_at].
      try solve [set_solver].
    + normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant d Σ (CTUnder b φ) e).
      pose proof (lvars_at_depth_mono (S d)
        (qual_vars φ ∖ {[LVBound 0]}) (qual_vars φ)
        ltac:(set_solver)).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant d Σ (CTInter τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant d Σ (CTUnion τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant d Σ (CTSum τ1 τ2) e).
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
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
        d Σ (CTArrow τ1 τ2) e) as Hrel.
      pose proof (IH (S d)
        (typed_lty_env_bind (denot_relevant_env Σ (CTArrow τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0))) as Harg.
      rewrite tm_lvars_at_tret_bound0_under in Harg.
      rewrite context_ty_lvars_at_shift_under in Harg by lia.
      pose proof (IH (S d)
        (typed_lty_env_bind (denot_relevant_env Σ (CTArrow τ1 τ2) e)
          (erase_ty τ1))
        τ2 (tapp_tm (tm_shift 0 e) (vbvar 0))) as Hres.
      pose proof (tm_lvars_at_tapp_shift0_bound0 e d) as Htapp.
      cbn [context_ty_lvars_at].
      cbn [context_ty_lvars_at] in Hrel.
      intros v Hv.
      repeat (apply elem_of_union in Hv as [Hv|Hv]).
      all: try solve [apply Hrel in Hv; fast_set_solver].
      all: try solve [apply Harg in Hv; fast_set_solver].
      all: try solve [apply Hres in Hv; fast_set_solver].
      all: fast_set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      rewrite ?lvars_at_depth_dom_singleton_bound0_succ.
      rewrite ?lvars_at_depth_singleton_bound0_succ.
      rewrite ?lvars_at_depth_empty.
      rewrite ?tm_lvars_at_tret_bound0_under.
      rewrite ?context_ty_lvars_at_shift_under by lia.
      pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
        d Σ (CTWand τ1 τ2) e) as Hrel.
      pose proof (IH (S d)
        (typed_lty_env_bind (denot_relevant_env Σ (CTWand τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0))) as Harg.
      rewrite tm_lvars_at_tret_bound0_under in Harg.
      rewrite context_ty_lvars_at_shift_under in Harg by lia.
      pose proof (IH (S d)
        (typed_lty_env_bind (denot_relevant_env Σ (CTWand τ1 τ2) e)
          (erase_ty τ1))
        τ2 (tapp_tm (tm_shift 0 e) (vbvar 0))) as Hres.
      pose proof (tm_lvars_at_tapp_shift0_bound0 e d) as Htapp.
      cbn [context_ty_lvars_at].
      cbn [context_ty_lvars_at] in Hrel.
      intros v Hv.
      repeat (apply elem_of_union in Hv as [Hv|Hv]).
      all: try solve [apply Hrel in Hv; fast_set_solver].
      all: try solve [apply Harg in Hv; fast_set_solver].
      all: try solve [apply Hres in Hv; fast_set_solver].
      all: fast_set_solver.
Qed.

Lemma formula_lvars_at_denot_ty_lvar_gas_subset gas d Σ τ e :
  formula_lvars_at d (denot_ty_lvar_gas gas Σ τ e) ⊆
  lvars_at_depth d (dom Σ) ∪ tm_lvars_at d e ∪ context_ty_lvars_at d τ.
Proof.
  intros v Hv.
  apply formula_lvars_at_denot_ty_lvar_gas_subset_relevant in Hv.
  set_solver.
Qed.

Lemma formula_fv_open_denot_ty_lvar_gas_subset_relevant
    gas k y Σ τ e :
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  formula_fv (formula_open k y (denot_ty_lvar_gas gas Σ τ e)) ⊆
  fv_tm (open_tm k (vfvar y) e) ∪ fv_cty (cty_open k y τ).
Proof.
  intros Hy Hτ.
  rewrite <- (formula_lvars_at_fv 0
    (formula_open k y (denot_ty_lvar_gas gas Σ τ e))).
  change k with (0 + k) at 1.
  rewrite formula_lvars_at_open.
  rewrite <- (tm_lvars_at_fv (open_tm k (vfvar y) e) 0).
  rewrite <- (context_ty_lvars_fv_at 0 (cty_open k y τ)).
  replace (open_tm k (vfvar y) e) with
    (open_tm (0 + k) (vfvar y) e) by
      (replace (0 + k) with k by lia; reflexivity).
  replace (cty_open k y τ) with (cty_open (0 + k) y τ) by
    (replace (0 + k) with k by lia; reflexivity).
  rewrite (tm_lvars_at_open e 0 k y) by
    (rewrite tm_lvars_at_fv; exact Hy).
  change (cty_open (0 + k) y τ) with ({0 + k ~> y} τ).
  rewrite (context_ty_lvars_at_open 0 k y τ).
  rewrite <- lvars_fv_union.
  apply lvars_fv_mono.
  rewrite <- lvars_open_union.
  apply lvars_open_mono.
  apply formula_lvars_at_denot_ty_lvar_gas_subset_relevant.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open gas Σ τ e :
  formula_fv (denot_ty_lvar_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  rewrite <- (formula_lvars_at_fv 0).
  transitivity (lvars_fv (tm_lvars_at 0 e ∪ context_ty_lvars_at 0 τ)).
  - apply lvars_fv_mono.
    apply formula_lvars_at_denot_ty_lvar_gas_subset_relevant.
  - rewrite lvars_fv_union.
    change (tm_lvars_at 0 e) with (tm_lvars e).
    change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ).
    rewrite tm_lvars_fv, context_ty_lvars_fv.
    reflexivity.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_scope_from_guard_pre_open
    gas Σ τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τbig e) τbig)
    (FAnd (basic_world_formula (denot_relevant_env Σ τbig e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τbig e) e
          (erase_ty τbig))
        (expr_total_formula e))) ->
  formula_fv (denot_ty_lvar_gas gas Σ τsmall e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hτ Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal_e]]].
  transitivity (fv_tm e ∪ fv_cty τsmall).
  - apply formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open.
  - pose proof (res_models_fuel_scoped _ _ _ Htotal_e) as Hscope_e.
    unfold formula_scoped_in_world in Hscope_e.
    rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_e.
    pose proof (context_ty_wf_formula_fv_cty_subset
      (denot_relevant_env Σ τbig e) τbig m Hwf) as Hτbig_fv.
    pose proof (proj1 (basic_world_formula_models_iff
      (denot_relevant_env Σ τbig e) m) Hworld)
      as [_ [Hworld_dom _]].
    assert (Hτsmall_fv : fv_cty τsmall ⊆ fv_cty τbig).
    {
      rewrite <- !context_ty_lvars_fv.
      apply lvars_fv_mono. exact Hτ.
    }
    set_solver.
Qed.

Lemma denot_guard_term_type_fv_scope
    Σ τ e (m : WfWorldT) :
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  fv_tm e ∪ fv_cty τ ⊆ world_dom (m : WorldT).
Proof.
  intros Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal]]].
  pose proof (res_models_fuel_scoped _ _ _ Htotal) as He.
  unfold formula_scoped_in_world in He.
  rewrite formula_fv_expr_total_formula, tm_lvars_fv in He.
  pose proof (context_ty_wf_formula_fv_cty_subset
    (denot_relevant_env Σ τ e) τ m Hwf) as Hτ.
  pose proof (proj1 (basic_world_formula_models_iff
    (denot_relevant_env Σ τ e) m) Hworld)
    as [_ [Hworld_dom _]].
  set_solver.
Qed.

End ContextTypeDenotation.
