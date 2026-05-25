(** * Denotation.TLet

    The key [tlet] introduction shape for the new denotation route.

    The statement is deliberately phrased almost entirely at the Logic level:
    regularity side conditions needed by [denot_ty_lvar_gas] are expected to be
    recovered from the component formulas carried by the denotation itself.
    The explicit operational inputs are only the result extension for [e1],
    totality of [e1], and basic typing of [e1]. *)

From LocallyNameless Require Import Classes Tactics.
From CoreLang Require Import BasicTyping BasicTypingProps LocallyNamelessProps Syntax Sugar.
From ChoiceAlgebra Require Import Resource ResourceExtensionCore.
From ChoiceLogic Require Import Formula FormulaTactics FormulaDerived FormulaForall FormulaWorldExtension.
From ChoiceTypeLanguage Require Import Interface.
From ChoiceBasicDenotation Require Import Interface.
From Denotation Require Import TypeDenotation.

Section TLetDenotation.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Local Notation FiberExtensionT := (fiber_extension (V := value)) (only parsing).
Local Notation FormulaT := (Formula (V := value)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

#[local] Instance stale_lty_env_tlet : Stale lty_env := lty_env_atom_dom.

Ltac normalize_formula_fv :=
  repeat first
    [ rewrite formula_fv_true | rewrite formula_fv_false
    | rewrite formula_fv_and | rewrite formula_fv_or
    | rewrite formula_fv_impl | rewrite formula_fv_star
    | rewrite formula_fv_wand | rewrite formula_fv_plus
    | rewrite formula_fv_forall | rewrite formula_fv_over
    | rewrite formula_fv_under | rewrite formula_fv_fibvars ];
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_choice_ty_wf_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  cbn [formula_fv formula_lvars];
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms, ?lvars_fv_singleton_free;
  repeat first
    [ rewrite formula_fv_true | rewrite formula_fv_false
    | rewrite formula_fv_and | rewrite formula_fv_or
    | rewrite formula_fv_impl | rewrite formula_fv_star
    | rewrite formula_fv_wand | rewrite formula_fv_plus
    | rewrite formula_fv_forall | rewrite formula_fv_over
    | rewrite formula_fv_under | rewrite formula_fv_fibvars ];
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_choice_ty_wf_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms, ?lvars_fv_singleton_free.

Lemma fiber_extension_singleton_out_fresh_in
    (F : FiberExtensionT) y :
  ext_out F = {[y]} ->
  y ∉ ext_in F.
Proof.
  intros Hout.
  pose proof (extA_disjoint F) as Hdisj.
  unfold ext_out, ext_in in *.
  rewrite Hout in Hdisj. set_solver.
Qed.

Lemma tlet_forall_fresh_from_input
    (F : FiberExtensionT) y X :
  ext_in F = X ->
  ext_out F = {[y]} ->
  y ∉ X.
Proof.
  intros HFin HFout.
  rewrite <- HFin. eapply fiber_extension_singleton_out_fresh_in; eauto.
Qed.

Lemma tlet_fresh_tm_from_forall_input
    (F : FiberExtensionT) y X e :
  ext_in F = X ->
  ext_out F = {[y]} ->
  fv_tm e ⊆ X ->
  y ∉ fv_tm e.
Proof.
  intros HFin HFout Hsub.
  pose proof (tlet_forall_fresh_from_input F y X HFin HFout).
  set_solver.
Qed.

Lemma tlet_fresh_lty_env_from_forall_input
    (F : FiberExtensionT) y X (Σ : lty_env) :
  ext_in F = X ->
  ext_out F = {[y]} ->
  lvars_fv (dom Σ) ⊆ X ->
  LVFree y ∉ dom Σ.
Proof.
  intros HFin HFout Hsub Hy.
  pose proof (tlet_forall_fresh_from_input F y X HFin HFout) as HyX.
  apply HyX, Hsub. apply lvars_fv_elem. exact Hy.
Qed.

Lemma tlet_atom_notin_lvars_fv_iff_free_notin y (D : lvset) :
  y ∉ lvars_fv D ↔ LVFree y ∉ D.
Proof.
  rewrite lvars_fv_elem. tauto.
Qed.

Lemma tlet_lvars_fv_empty :
  lvars_fv (∅ : lvset) = ∅.
Proof.
  apply set_eq. intros x. rewrite lvars_fv_elem. set_solver.
Qed.

Lemma tlet_lvars_fv_dom_insert_free (Σ : lty_env) x T :
  lvars_fv (dom (<[LVFree x := T]> Σ)) =
  {[x]} ∪ lvars_fv (dom Σ).
Proof.
  change (lvars_fv (dom ((<[LVFree x := T]> (Σ : gmap logic_var ty)) :
    gmap logic_var ty)) = {[x]} ∪ lvars_fv (dom (Σ : gmap logic_var ty))).
  rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free.
  set_solver.
Qed.

Lemma tlet_lvars_fv_subset_insert_free_drop
    (D : lvset) (Σ : lty_env) x T :
  LVFree x ∉ D ->
  D ⊆ dom (<[LVFree x := T]> Σ) ->
  lvars_fv D ⊆ lvars_fv (dom Σ).
Proof.
  intros Hfresh Hsub y Hy.
  rewrite lvars_fv_elem in Hy |- *.
  specialize (Hsub (LVFree y) Hy).
  change (LVFree y ∈ dom
    ((<[LVFree x := T]> (Σ : gmap logic_var ty)) :
      gmap logic_var ty)) in Hsub.
  rewrite dom_insert_L in Hsub.
  destruct (decide (y = x)) as [-> | Hneq].
  - exfalso. exact (Hfresh Hy).
  - set_solver.
Qed.

Lemma tlet_choice_ty_lvars_insert_free_fv_drop
    (Σ : lty_env) τ x T :
  LVFree x ∉ choice_ty_lvars τ ->
  basic_choice_ty_lvars (dom (<[LVFree x := T]> Σ)) τ ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hfresh [Hsub _].
  rewrite <- choice_ty_lvars_fv.
  eapply tlet_lvars_fv_subset_insert_free_drop; eauto.
Qed.

Lemma tlet_fresh_qualifier_from_forall_input
    (F : FiberExtensionT) y X (φ : type_qualifier) :
  ext_in F = X ->
  ext_out F = {[y]} ->
  qual_dom φ ⊆ X ->
  y ∉ qual_dom φ.
Proof.
  intros HFin HFout Hsub.
  pose proof (tlet_forall_fresh_from_input F y X HFin HFout).
  set_solver.
Qed.

Ltac tlet_normalize_freshness :=
  repeat match goal with
  | H : LVFree ?y ∉ ?D |- _ =>
      rewrite <- (tlet_atom_notin_lvars_fv_iff_free_notin y D) in H
  | |- LVFree ?y ∉ ?D =>
      rewrite <- (tlet_atom_notin_lvars_fv_iff_free_notin y D)
  | H : context[stale ?x] |- _ =>
      lazymatch type of x with
      | atom => change (stale x) with ({[x]} : aset) in H
      end
  | |- context[stale ?x] =>
      lazymatch type of x with
      | atom => change (stale x) with ({[x]} : aset)
      end
  end;
  cbn [stale stale_lty_env_tlet lty_env_atom_dom stale_tm_inst
       stale_qualifier stale_cty_inst stale_logic_var Stale_atom] in *;
  rewrite ?tlet_lvars_fv_dom_insert_free in *;
  rewrite ?lvars_fv_union, ?lvars_fv_singleton_free in *.

Ltac tlet_support_solver :=
  tlet_normalize_freshness;
  match goal with
  | |- ?y ∉ fv_tm (?e ^^ ?x) =>
      intros Hbad;
      pose proof (open_fv_tm e (vfvar x) 0) as Hopen;
      apply Hopen in Hbad; simpl in Hbad;
      tlet_normalize_freshness;
      first [fast_set_solver!! | set_solver]
  | |- _ ∉ _ =>
      first [fast_set_solver!! | set_solver]
  | |- _ ⊆ _ =>
      first [fast_set_solver!! | set_solver]
  | |- _ ## _ =>
      first [fast_set_solver!! | set_solver]
  | |- _ <> _ =>
      first [fast_set_solver!! | set_solver]
  end.

Ltac solve_formula_fv_subset :=
  repeat match goal with
  | H : lty_env_to_atom_env ?Σ ⊢ₑ ?e ⋮ ?T |- _ =>
      lazymatch goal with
      | Hfv : fv_tm e ⊆ lvars_fv (dom Σ) |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_lty" in
          pose proof (basic_typing_lty_env_to_atom_env_fv_subset Σ e T H) as Hfv
      end
  | H : ?Γ ⊢ₑ ?e ⋮ ?T |- _ =>
      lazymatch goal with
      | Hfv : fv_tm e ⊆ dom Γ |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_basic" in
          pose proof (basic_typing_contains_fv_tm Γ e T H) as Hfv
      end
  | |- context[fv_tm (open_tm ?k ?u ?e)] =>
      lazymatch goal with
      | Hfv : fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_open" in
          pose proof (open_fv_tm e u k) as Hfv
      end
  | H : context[fv_tm (open_tm ?k ?u ?e)] |- _ =>
      lazymatch goal with
      | Hfv : fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_open" in
          pose proof (open_fv_tm e u k) as Hfv
      end
  end;
  normalize_formula_fv;
  cbn [fv_tm fv_value] in *;
  tlet_normalize_freshness;
  set_solver.

Ltac harvest_tlet_models :=
  repeat match goal with
  | H : ?m ⊨ choice_ty_wf_formula ?Σ ?τ |- _ =>
      lazymatch goal with
      | Hscope : lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) |- _ => fail
      | _ =>
          let Hscope := fresh "Hchoice_scope" in
          pose proof (choice_ty_wf_formula_scope_dom Σ τ m H) as Hscope
      end
  | H : ?m ⊨ choice_ty_wf_formula ?Σ ?τ |- _ =>
      lazymatch goal with
      | Hbasic : basic_choice_ty_lvars (dom Σ) τ |- _ => fail
      | _ =>
          let Hbasic := fresh "Hchoice_lvars" in
          pose proof (choice_ty_wf_formula_basic_lvars Σ τ m H) as Hbasic
      end
  | H : ?m ⊨ expr_basic_typing_formula ?Σ ?e ?T |- _ =>
      lazymatch goal with
      | Hscope : lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) |- _ => fail
      | _ =>
          let Hscope := fresh "Hexpr_basic_scope" in
          pose proof (expr_basic_typing_formula_scope_dom Σ e T m H) as Hscope
      end
  | H : ?m ⊨ expr_basic_typing_formula ?Σ ?e ?T |- _ =>
      lazymatch goal with
      | Hbasic : basic_tm_has_ltype Σ e T |- _ => fail
      | _ =>
          let Hbasic := fresh "Hexpr_basic_ltype" in
          pose proof (expr_basic_typing_formula_basic_ltype Σ e T m H) as Hbasic
      end
  | H : lty_env_to_atom_env ?Σ ⊢ₑ ?e ⋮ ?T |- _ =>
      lazymatch goal with
      | Hfv : fv_tm e ⊆ lvars_fv (dom Σ) |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_lty" in
          pose proof (basic_typing_lty_env_to_atom_env_fv_subset Σ e T H) as Hfv
      end
  | H : ?Γ ⊢ₑ ?e ⋮ ?T |- _ =>
      lazymatch goal with
      | Hfv : fv_tm e ⊆ dom Γ |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_basic" in
          pose proof (basic_typing_contains_fv_tm Γ e T H) as Hfv
      end
  | Hfresh : LVFree ?x ∉ choice_ty_lvars ?τ,
    Hbasic : basic_choice_ty_lvars (dom (<[LVFree ?x := ?T]> ?Σ)) ?τ |- _ =>
      lazymatch goal with
      | Hfv : fv_cty τ ⊆ lvars_fv (dom Σ) |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_cty_drop" in
          pose proof (tlet_choice_ty_lvars_insert_free_fv_drop
            Σ τ x T Hfresh Hbasic) as Hfv
      end
  end;
  repeat match goal with
  | H : basic_choice_ty_lvars _ _ |- _ =>
      let Hsub := fresh "Hchoice_lvars_sub" in
      let Hshape := fresh "Hchoice_shape" in
      destruct H as [Hsub Hshape]
  end.

Ltac solve_formula_scoped :=
  solve
  [ eapply res_models_scoped; eassumption
  | unfold formula_scoped_in_world;
    harvest_tlet_models;
    normalize_formula_fv;
    rewrite ?choice_ty_lvars_fv in *;
    rewrite ?lvars_fv_lvars_at_depth in *;
    cbn [fv_tm fv_value] in *;
    tlet_normalize_freshness;
    fast_set_solver!!
  ].

Lemma formula_lvars_fv_basic_world_formula Σ :
  lvars_fv (formula_lvars (basic_world_formula Σ)) = lvars_fv (dom Σ).
Proof.
  change (lvars_fv (formula_lvars (basic_world_formula Σ)))
    with (formula_fv (basic_world_formula Σ)).
  apply formula_fv_basic_world_formula.
Qed.

Lemma formula_lvars_fv_expr_result_formula e x :
  lvars_fv (formula_lvars (expr_result_formula e x)) =
  lvars_fv (tm_lvars e ∪ {[x]}).
Proof.
  change (lvars_fv (formula_lvars (expr_result_formula e x)))
    with (formula_fv (expr_result_formula e x)).
  apply formula_fv_expr_result_formula.
Qed.

Lemma formula_lvars_fv_type_qualifier_formula φ :
  lvars_fv (formula_lvars (type_qualifier_formula φ)) = qual_dom φ.
Proof.
  change (lvars_fv (formula_lvars (type_qualifier_formula φ)))
    with (formula_fv (type_qualifier_formula φ)).
  apply formula_fv_type_qualifier_formula.
Qed.

Ltac normalize_tlet_forall_fv :=
  rewrite ?formula_fv_true, ?formula_fv_false;
  rewrite ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl;
  rewrite ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus;
  rewrite ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under,
    ?formula_fv_fibvars;
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_choice_ty_wf_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  cbn [formula_lvars basic_world_formula basic_world_lqual
    expr_result_formula expr_result_lqual type_qualifier_formula
    type_qualifier_lqual choice_ty_wf_formula choice_ty_wf_lqual
    expr_basic_typing_formula expr_basic_typing_lqual
    expr_total_formula expr_total_lqual
    lqual_fvars lqual_lvars lqual_dom];
  repeat match goal with
  | |- context[lvars_fv (formula_lvars (denot_ty_lvar_gas ?gas ?Σ ?τ ?e))] =>
      change (lvars_fv (formula_lvars (denot_ty_lvar_gas gas Σ τ e)))
        with (formula_fv (denot_ty_lvar_gas gas Σ τ e))
  | H : context[lvars_fv (formula_lvars (denot_ty_lvar_gas ?gas ?Σ ?τ ?e))] |- _ =>
      change (lvars_fv (formula_lvars (denot_ty_lvar_gas gas Σ τ e)))
        with (formula_fv (denot_ty_lvar_gas gas Σ τ e)) in H
  end;
  rewrite ?typed_lty_env_bind_lvars_fv_dom;
  rewrite ?tlet_lvars_fv_dom_insert_free;
  rewrite ?choice_ty_lvars_over_fv, ?choice_ty_lvars_under_fv;
  rewrite ?tm_shift_fv, ?cty_shift_fv;
  rewrite ?tm_lvars_fv;
  rewrite ?lvars_fv_lvars_at_depth;
  rewrite ?lvars_fv_qual_vars_difference_free, ?lvars_fv_qual_vars;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?lvars_fv_difference_singleton_free,
    ?tlet_lvars_fv_empty;
  rewrite ?tm_lvars_fv;
  cbn [fv_tm fv_value].

Lemma tlet_over_fib_formula_fresh_x x y b φ :
  LVFree x ∉ choice_ty_lvars (CTOver b φ) ->
  x <> y ->
  x ∉ formula_fv
    (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
      (FOver (type_qualifier_formula (φ ^q^ y)))).
Proof.
  intros Hfresh Hxy.
  normalize_tlet_forall_fv.
  pose proof (choice_ty_over_fresh_open_qual_dom x y b φ Hfresh Hxy).
  set_solver.
Qed.

Lemma tlet_under_fib_formula_fresh_x x y b φ :
  LVFree x ∉ choice_ty_lvars (CTUnder b φ) ->
  x <> y ->
  x ∉ formula_fv
    (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
      (FUnder (type_qualifier_formula (φ ^q^ y)))).
Proof.
  intros Hfresh Hxy.
  normalize_tlet_forall_fv.
  pose proof (choice_ty_under_fresh_open_qual_dom x y b φ Hfresh Hxy).
  set_solver.
Qed.

Lemma tlet_arrow_result_env_term_subset Σ T1 x e1 e2 τx τr :
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τr) ->
  lvars_fv (dom (typed_lty_env_bind Σ (erase_ty τx))) ∪
    fv_tm (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)) ⊆
  lvars_fv (dom (typed_lty_env_bind (<[LVFree x := T1]> Σ) (erase_ty τx))) ∪
    fv_tm (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)).
Proof.
  intros Hlet.
  pose proof (basic_typing_lty_env_to_atom_env_fv_subset _ _ _ Hlet) as Hfv_let.
  transitivity (lvars_fv (dom (typed_lty_env_bind Σ (erase_ty τx))) ∪
    fv_tm (tlete e1 e2)).
  - rewrite (fv_tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)).
    rewrite (tm_shift_fv 0 (tlete e1 e2)).
    cbn [fv_value].
    set_solver.
  - rewrite ?typed_lty_env_bind_lvars_fv_dom, ?tlet_lvars_fv_dom_insert_free.
    fast_set_solver!!.
Qed.

Lemma tlet_over_forall_fv_subset Σ T1 x b e1 e2 φ :
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTOver b φ) ->
  formula_fv
    (FImpl
      (basic_world_formula
        (denot_relevant_env (typed_lty_env_bind Σ b)
          (CTOver b φ) (tm_shift 0 (tlete e1 e2))))
      (FImpl
        (expr_result_formula (tm_shift 0 (tlete e1 e2)) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (type_qualifier_formula φ))))) ⊆
  formula_fv
    (FImpl
      (basic_world_formula
        (denot_relevant_env
          (typed_lty_env_bind (<[LVFree x := T1]> Σ) b)
          (CTOver b φ) (tm_shift 0 (e2 ^^ x))))
      (FImpl
        (expr_result_formula (tm_shift 0 (e2 ^^ x)) (LVBound 0))
		      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
		        (FOver (type_qualifier_formula φ))))).
Admitted.

Lemma tlet_over_forall_scope Σ b e1 e2 φ (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTOver b φ) ->
  m ⊨ choice_ty_wf_formula Σ (CTOver b φ) ->
  formula_scoped_in_world m
    (FForall
      (FImpl
        (basic_world_formula
          (denot_relevant_env (typed_lty_env_bind Σ b)
            (CTOver b φ) (tm_shift 0 (tlete e1 e2))))
        (FImpl
          (expr_result_formula (tm_shift 0 (tlete e1 e2)) (LVBound 0))
		          (FFibVars (qual_vars φ ∖ {[LVBound 0]})
		            (FOver (type_qualifier_formula φ)))))).
Admitted.

Lemma tlet_arrow_forall_fv_subset gas Σ T1 x e1 e2 τx τr :
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τr) ->
  formula_fv
    (FImpl
      (basic_world_formula
        (lty_env_restrict_lvars (typed_lty_env_bind Σ (erase_ty τx))
          (denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)) ∪
           denot_relevant_lvars τr
             (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)))))
      (FImpl
        (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))
        (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τx))
          τr (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0))))) ⊆
  formula_fv
    (FImpl
      (basic_world_formula
        (lty_env_restrict_lvars
          (typed_lty_env_bind (<[LVFree x := T1]> Σ) (erase_ty τx))
          (denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)) ∪
           denot_relevant_lvars τr
             (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)))))
      (FImpl
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind (<[LVFree x := T1]> Σ) (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))
	        (denot_ty_lvar_gas gas
	          (typed_lty_env_bind (<[LVFree x := T1]> Σ) (erase_ty τx))
		          τr (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0))))).
Admitted.

Lemma tlet_arrow_forall_scope gas Σ e1 e2 τx τr (m : WfWorldT) :
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τr) ->
  m ⊨ choice_ty_wf_formula Σ (CTArrow τx τr) ->
  formula_scoped_in_world m
    (FForall
      (FImpl
        (basic_world_formula
          (lty_env_restrict_lvars (typed_lty_env_bind Σ (erase_ty τx))
            (denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0)) ∪
             denot_relevant_lvars τr
               (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)))))
        (FImpl
          (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas (typed_lty_env_bind Σ (erase_ty τx))
            τr (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)))))).
Admitted.

Lemma tlet_lc_open_body_from_lc e1 e2 x :
  lc_tm (tlete e1 e2) ->
  lc_tm (e2 ^^ x).
Proof.
  intros Hlc.
  apply lc_lete_iff_body in Hlc as [_ Hbody].
  apply body_open_tm; [exact Hbody | constructor].
Qed.

Lemma tlet_lc_open_body_from_basic Γ e1 e2 T x :
  Γ ⊢ₑ tlete e1 e2 ⋮ T ->
  lc_tm (e2 ^^ x).
Proof.
  intros Htyped.
  eapply tlet_lc_open_body_from_lc.
  eapply basic_typing_regular_tm. exact Htyped.
Qed.

Lemma tlet_lc_tapp_open_body_from_basic Γ e1 e2 T x y :
  Γ ⊢ₑ tlete e1 e2 ⋮ T ->
  lc_tm (tapp_tm (e2 ^^ x) (vfvar y)).
Proof.
  intros Htyped.
  apply lc_tapp_tm; [eapply tlet_lc_open_body_from_basic; eauto | constructor].
Qed.

Ltac tlet_lc_solver :=
  solve
  [ constructor
  | eapply basic_typing_regular_tm; eassumption
  | eapply tlet_lc_open_body_from_basic; eassumption
  | eapply tlet_lc_tapp_open_body_from_basic; eassumption
  | apply lc_tapp_tm; [tlet_lc_solver | constructor]
  ].

Ltac solve_tlet_sidecond :=
  first
  [ assumption
  | match goal with
    | H : expr_result_extension_witness _ ?x ?F |- ext_out ?F = {[?x]} =>
        exact (proj2 (expr_result_extension_witness_shape _ _ _ H))
    end
  | tlet_lc_solver
  | tlet_support_solver
  | eauto using
	      lty_env_closed_insert_free,
	      tlet_forall_fresh_from_input,
	      tlet_fresh_tm_from_forall_input,
	      tlet_fresh_lty_env_from_forall_input,
	      tlet_fresh_qualifier_from_forall_input
  ].

Ltac solve_tlet_impl_scope :=
  first
  [ eassumption
  | match goal with
    | Hscope : formula_scoped_in_world ?m (FImpl ?p0 (FImpl ?p ?q))
      |- formula_scoped_in_world ?m (FImpl ?p ?q) =>
        let Hparts := fresh "Himpl_scope_parts" in
        pose proof (proj1 (formula_scoped_impl_iff m p0 (FImpl p q)) Hscope) as Hparts;
        exact (proj2 Hparts)
    | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
      |- formula_scoped_in_world ?m ?p =>
        let Hparts := fresh "Himpl_scope_parts" in
        pose proof (proj1 (formula_scoped_impl_iff m p q) Hscope) as Hparts;
        exact (proj1 Hparts)
    | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
      |- formula_scoped_in_world ?m ?q =>
        let Hparts := fresh "Himpl_scope_parts" in
        pose proof (proj1 (formula_scoped_impl_iff m p q) Hscope) as Hparts;
        exact (proj2 Hparts)
    end
  | solve_formula_scoped
  ].

Ltac intro_models_impl H :=
  match goal with
  | |- ?m ⊨ FImpl ?p ?q =>
      eapply res_models_impl_intro;
      [solve_tlet_impl_scope
      | intro H]
  end.

Ltac use_models_impl H Hout :=
  match type of H with
  | ?m ⊨ FImpl ?p ?q =>
      let Harg := fresh "Harg" in
      assert (Harg : m ⊨ p);
      [ | pose proof (res_models_impl_elim m p q H Harg) as Hout;
          clear Harg ]
  end.

Ltac normalize_models_ands_in H :=
  repeat rewrite res_models_and_iff in H.

Ltac normalize_models_ands_goal :=
  repeat rewrite res_models_and_iff.

Ltac normalize_models_ands :=
  normalize_models_ands_goal.

Lemma open_tapp_tm_fvar_lc_arg e x y :
  open_tm 0 (vfvar x) (tapp_tm e (vfvar y)) =
  tapp_tm (open_tm 0 (vfvar x) e) (vfvar y).
Proof.
  apply open_tapp_tm_lc_arg. constructor.
Qed.

Lemma denot_ty_lvar_gas_insert_commute_tapp_open
    gas (Σ : lty_env) x y T1 Ty τ e2 (m : WfWorldT) :
  x <> y ->
  m ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := Ty]> (<[LVFree x := T1]> Σ))
      τ (tapp_tm (e2 ^^ x) (vfvar y)) ->
  m ⊨ denot_ty_lvar_gas gas
      (<[LVFree x := T1]> (<[LVFree y := Ty]> Σ))
      τ ((tapp_tm e2 (vfvar y)) ^^ x).
Proof.
  intros Hxy Hm.
  rewrite lty_env_insert_free_commute by exact Hxy.
  change (((tapp_tm e2 (vfvar y)) ^^ x)) with
    (open_tm 0 (vfvar x) (tapp_tm e2 (vfvar y))).
  rewrite open_tapp_tm_fvar_lc_arg.
  exact Hm.
Qed.

Ltac open_formula_syntax_step :=
  rewrite ?formula_open_impl;
  rewrite ?formula_open_fibvars;
  rewrite ?formula_open_over;
  rewrite ?formula_open_choice_ty_wf_formula;
  rewrite ?formula_open_expr_total_formula by solve_tlet_sidecond;
  rewrite ?formula_open_basic_world_typed_bind_current by solve_tlet_sidecond;
  rewrite ?formula_open_basic_world_formula;
  rewrite ?formula_open_expr_result_formula_shift0 by solve_tlet_sidecond;
  rewrite ?formula_open_expr_result_formula by solve_tlet_sidecond;
  rewrite ?lvars_open_qual_vars_difference_bound0;
  rewrite ?type_qualifier_formula_open by solve_tlet_sidecond;
  rewrite ?open_tapp_tm_fvar_lc_arg.

Ltac normalize_open_denot_goal :=
  rewrite ?formula_open_denot_ty_lvar_gas_arrow_arg_current by solve_tlet_sidecond;
  rewrite ?formula_open_denot_ty_lvar_gas_arrow_conseq_current by solve_tlet_sidecond;
  rewrite ?formula_open_denot_ty_lvar_gas_typed_bind_current by solve_tlet_sidecond;
  rewrite ?open_tapp_tm_fvar_lc_arg.

Ltac normalize_open_denot_in H :=
  rewrite ?formula_open_denot_ty_lvar_gas_arrow_arg_current in H by solve_tlet_sidecond;
  rewrite ?formula_open_denot_ty_lvar_gas_arrow_conseq_current in H by solve_tlet_sidecond;
  rewrite ?formula_open_denot_ty_lvar_gas_typed_bind_current in H by solve_tlet_sidecond;
  rewrite ?open_tapp_tm_fvar_lc_arg in H.

Ltac normalize_formula_open_syntax :=
  rewrite ?formula_open_impl in *;
  rewrite ?formula_open_fibvars in *;
  rewrite ?formula_open_over in *;
  rewrite ?formula_open_basic_world_formula in *;
  rewrite ?typed_lty_env_bind_open_current_base in * by solve_tlet_sidecond;
  rewrite ?typed_lty_env_bind_open_current in * by solve_tlet_sidecond;
  rewrite ?formula_open_basic_world_typed_bind_current in * by solve_tlet_sidecond;
  rewrite ?formula_open_expr_result_formula_shift0 in * by solve_tlet_sidecond;
  rewrite ?lvars_open_qual_vars_difference_bound0 in *;
  rewrite ?type_qualifier_formula_open in * by solve_tlet_sidecond.

Lemma tlet_extensions_commute_obligation
    (m mx my mxy : WfWorldT) (Fx Fy : FiberExtensionT) :
  res_extend_by m Fx mx ->
  res_extend_by m Fy my ->
  res_extend_by mx Fy mxy ->
  res_extend_by my Fx mxy.
Proof.
  intros Hmx Hmy Hmxy.
  apply (proj1 (res_extend_by_commute_input_widen
    m mx Fx Fy Fy my mxy Hmx Hmy
    (fiber_extension_input_widen_to_refl Fy)
    ltac:(eapply res_extend_by_input_dom; exact Hmxy))).
  exact Hmxy.
Qed.

Lemma tlet_extensions_commute_widened_obligation
    (m mx my mxy : WfWorldT) (Fx Fy : FiberExtensionT) X :
  res_extend_by m Fx mx ->
  res_extend_by m Fy my ->
  res_extend_by_input_widened_to mx Fy X mxy ->
  res_extend_by my Fx mxy.
Proof.
  intros Hmx Hmy [Fywide [Hwid [_ Hmxy]]].
  apply (proj1 (res_extend_by_commute_input_widen
    m mx Fx Fy Fywide my mxy Hmx Hmy Hwid
    ltac:(eapply res_extend_by_input_dom; exact Hmxy))).
  exact Hmxy.
Qed.

Lemma tlet_arrow_arg_extend_obligation
    gas (Σ : lty_env) x y T1 Ty τx
    (my mxy : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  x <> y ->
  LVFree x ∉ choice_ty_lvars τx ->
  extension_has_ltype (<[LVFree x := T1]> ∅)
    (res_restrict my (ext_in Fx)) Fx ->
  res_extend_by my Fx mxy ->
  my ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := Ty]> Σ)
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)) ->
  mxy ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := Ty]> (<[LVFree x := T1]> Σ))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)).
Proof.
  intros HxΣ Hxy Hxτx HFx_ty Hext Hmy.
  rewrite <- lty_env_insert_free_commute by exact Hxy.
  assert (HxΣy : LVFree x ∉
    dom ((<[LVFree y := Ty]> (Σ : gmap logic_var ty))
      : gmap logic_var ty)).
  { rewrite dom_insert_L. set_solver. }
  assert (Hxτopen :
    LVFree x ∉ choice_ty_lvars (cty_open 0 y (cty_shift 0 τx))).
  { apply choice_ty_lvars_open_shift_fresh; assumption. }
  assert (Hmxy_old : mxy ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := Ty]> Σ)
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y))).
  {
    eapply res_models_extend_mono; [exact Hext | exact Hmy].
  }
  eapply denot_ty_lvar_gas_insert_fresh_lty_env; eauto.
  cbn [fv_tm fv_value]. set_solver.
Qed.

Ltac solve_tlet_guard :=
  match goal with
  | |- _ ⊨ choice_ty_wf_formula _ _ =>
      eapply choice_ty_wf_formula_drop_fresh_lvar; eauto; solve_tlet_sidecond
  | |- _ ⊨ basic_world_formula _ =>
      eapply basic_world_formula_drop_result_extension; eauto; solve_tlet_sidecond
  | |- _ ⊨ expr_basic_typing_formula _ (tlete _ _) _ =>
      eapply expr_basic_typing_formula_tlete_intro; eauto;
      eapply basic_world_formula_drop_result_extension; eauto; solve_tlet_sidecond
  | |- _ ⊨ expr_total_formula (tlete _ _) =>
      eapply expr_total_formula_tlete_intro_from_result_extension; eauto;
      first
        [ eapply basic_world_formula_drop_result_extension; eauto;
          solve_tlet_sidecond
        | solve_tlet_sidecond ]
  | |- formula_scoped_in_world _ _ =>
      solve_formula_scoped
  end.

Lemma tlet_intro_denotation_gas_zero
    (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
    (τ : choice_ty) :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ (tlete e1 e2) ⋮ erase_ty τ ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ (tlete e1 e2)) ->
  LVFree x ∉ dom Σ ->
  LVFree x ∉ choice_ty_lvars τ ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_lvar_gas 0
    (<[LVFree x := T1]> Σ) τ (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ (tlete e1 e2).
Proof.
  intros HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx.
  cbn [denot_ty_lvar_gas] in Hmx |- *.
  repeat rewrite res_models_and_iff in Hmx |- *.
  destruct Hmx as [[Hmx_wf [Hmx_world [Hmx_basic Hmx_total]]] _].
  split.
  - split.
    + apply choice_ty_wf_formula_models_iff.
    apply basic_world_formula_models_iff in Hbase_world
      as [Hlc_base [Hscope_base _]].
    apply choice_ty_wf_formula_models_iff in Hmx_wf
      as [_ [_ [Hvars_mx Hshape]]].
    split; [exact Hlc_base|].
    split; [exact Hscope_base|].
    split; [|exact Hshape].
    intros v Hv.
    assert (Hv_mx : v ∈ dom (denot_relevant_env
      (<[LVFree x := T1]> Σ) τ (e2 ^^ x))).
    { exact (Hvars_mx v Hv). }
    unfold denot_relevant_env, lty_env_restrict_lvars in Hv_mx |- *.
    change (v ∈ dom (storeA_restrict
      ((<[LVFree x := T1]> (Σ : gmap logic_var ty)) : lty_env)
      (denot_relevant_lvars τ (e2 ^^ x)))) in Hv_mx.
    rewrite storeA_restrict_dom in Hv_mx.
    apply elem_of_intersection in Hv_mx as [Hv_insert _].
	    change (v ∈ dom (storeA_restrict (Σ : gmap logic_var ty)
	      (denot_relevant_lvars τ (tlete e1 e2)))).
	    rewrite storeA_restrict_dom.
	    apply elem_of_intersection. split.
	    { change (v ∈ dom ((<[LVFree x := T1]> (Σ : gmap logic_var ty))
	        : gmap logic_var ty)) in Hv_insert.
	      rewrite dom_insert_L in Hv_insert.
	      apply elem_of_union in Hv_insert as [Hvx|HvΣ].
	      - rewrite elem_of_singleton in Hvx. subst v. contradiction.
	      - exact HvΣ. }
	    { unfold denot_relevant_lvars. set_solver. }
    + split.
	      * exact Hbase_world.
	      * split.
	        -- eapply expr_basic_typing_formula_tlete_intro; [exact Hbase_world|].
	           apply basic_typing_lty_env_to_atom_env_denot_relevant_env.
	           exact Hlet.
	        -- eapply expr_total_formula_tlete_intro_from_result_extension
	             with (Σ := denot_relevant_env Σ τ (tlete e1 e2)); eauto.
	           ++ unfold denot_relevant_env, lty_env_restrict_lvars.
	              change (LVFree x ∉ dom
	                (storeA_restrict (Σ : gmap logic_var ty)
	                   (denot_relevant_lvars τ (tlete e1 e2)))).
	              rewrite storeA_restrict_dom. set_solver.
	           ++ apply basic_typing_lty_env_to_atom_env_denot_relevant_env.
	              exact Hlet.
  - cbn [res_models res_models_fuel formula_measure].
    split; [apply formula_scoped_true_iff; exact I | exact I].
Qed.

Lemma tlet_arrow_result_from_body_denotation
    gas (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx my mxy : WfWorldT) (Fx : FiberExtensionT)
    (x y : atom) τx τr :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ (tlete e1 e2) ⋮ erase_ty (CTArrow τx τr) ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  LVFree x ∉ dom Σ ->
  res_extend_by m Fx mx ->
  res_extend_by my Fx mxy ->
  mxy ⊨ denot_ty_lvar_gas gas
    (<[LVFree x := T1]> (<[LVFree y := erase_ty τx]> Σ))
    (cty_open 0 y τr)
    ((tapp_tm e2 (vfvar y)) ^^ x) ->
	  my ⊨ denot_ty_lvar_gas gas
	    (<[LVFree y := erase_ty τx]> Σ)
	    (cty_open 0 y τr)
	    (tapp_tm (tlete e1 e2) (vfvar y)).
Admitted.

(** [tlet_intro_ih_sigma] is the reusable induction-hypothesis shape that the
    structural cases, especially [CTArrow], should consume.  It says: if [e1]
    is total and well-typed in the base lvar context, and evaluating [e1]
    produces a fresh result extension [Fx] from [m] to [mx], then denotation of
    the opened body in the extended context implies denotation of the whole
    [tlete] in the original context. *)
Lemma tlet_intro_denotation
    (gas : nat) (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
    (τ : choice_ty) :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
	  lty_env_to_atom_env Σ ⊢ₑ (tlete e1 e2) ⋮ erase_ty τ ->
		  expr_result_extension_witness e1 x Fx ->
		  m ⊨ expr_total_formula e1 ->
		  m ⊨ basic_world_formula (denot_relevant_env Σ τ (tlete e1 e2)) ->
		  LVFree x ∉ dom Σ ∪ choice_ty_lvars τ ->
		  res_extend_by m Fx mx ->
	  mx ⊨ denot_ty_lvar_gas gas
	    (<[LVFree x := T1]> Σ) τ (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ (tlete e1 e2).
Proof.
	  revert Σ T1 e1 e2 m mx Fx x τ.
	  induction gas as [|gas IH];
	    intros Σ T1 e1 e2 m mx Fx x τ
	      HΣ He1 Hlet HFx Htotal Hbase_world Hfresh Hext Hmx.
	  - cbn [denot_ty_lvar_gas] in Hmx |- *.
		    (* gas = 0: only the inlined guard remains.  This should follow from
		       [He1], [Htotal], [HΣ], [Hfresh], and the guard already present in
		       [Hmx]. *)
				    assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
				    assert (Hxτ : LVFree x ∉ choice_ty_lvars τ) by tlet_support_solver.
				    eapply tlet_intro_denotation_gas_zero; eauto.
  - destruct τ as [b φ | b φ | τ1 τ2 | τ1 τ2 | τ1 τ2 | τx τr | τx τr];
      cbn [denot_ty_lvar_gas] in Hmx |- *.
    + clear IH.
      normalize_models_ands_in Hmx; normalize_models_ands_goal.
	      destruct Hmx as [Hmx_guard Hmx_over_body].
	      split.
	      * admit.
	      * eapply res_models_forall_ext_transport in Hmx_over_body; eauto.
	        -- admit.
	        -- exists (lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
	           qual_dom φ ∪ {[x]}).
	           intros y Hy my myx Hle Hdom_my HmyFx Hmyx_body.
	           normalize_formula_open_syntax.
	           eapply res_models_impl_intro.
	           { admit. }
	           intro Hmy_world.
	           use_models_impl Hmyx_body Hbody_after_outer.
	           {
	             eapply res_models_extend_mono; [exact HmyFx | exact Hmy_world].
	           }
	           eapply res_models_impl_intro.
	           { admit. }
	           intro Hmy_result.
	           use_models_impl Hbody_after_outer Hbody_after_inner.
	           {
	             eapply expr_result_formula_tlete_elim_body_from_result_extension in Hmy_result; eauto.
	             - eapply typing_tm_lc; eauto.
	             - tlet_support_solver.
	             - assert (Hfv_tlet :
	                 fv_tm (tlete e1 e2) ⊆ lvars_fv (dom Σ)).
	               { eapply basic_typing_lty_env_to_atom_env_fv_subset; eauto. }
		               intros Hxe2. apply Hfresh. apply elem_of_union_l.
	               apply lvars_fv_elem. apply Hfv_tlet.
	               cbn [fv_tm]. set_solver.
	             - assert (Hmy_base_world :
	                 my ⊨ basic_world_formula
	                   (denot_relevant_env Σ (CTOver b φ) (tlete e1 e2))).
	               {
	                 eapply res_models_kripke; [exact Hle | exact Hbase_world].
	               }
	               eapply (basic_world_formula_wfworld_closed_on_atoms
	                 (denot_relevant_env Σ (CTOver b φ) (tlete e1 e2))).
	               + unfold denot_relevant_env, lty_env_restrict_lvars,
	                   denot_relevant_lvars.
	                 change (lvars_of_atoms (fv_tm (tlete e1 e2)) ⊆
	                   dom (storeA_restrict (Σ : gmap logic_var ty)
	                     (choice_ty_lvars (CTOver b φ) ∪
	                      tm_lvars (tlete e1 e2)))).
	                 rewrite storeA_restrict_dom.
	                 intros v Hv.
	                 unfold lvars_of_atoms in Hv.
	                 apply elem_of_map in Hv as [a [-> Ha]].
	                 apply elem_of_intersection. split.
	                 * apply lvars_fv_elem.
	                   pose proof (basic_typing_lty_env_to_atom_env_fv_subset
	                     Σ (tlete e1 e2) (erase_ty (CTOver b φ)) Hlet) as Hfv_tlet.
	                   apply Hfv_tlet. exact Ha.
		                 * apply elem_of_union_r.
		                   apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
	               + exact Hmy_base_world.
	           }
	           eapply res_models_fuel_projection with (m := myx); eauto.
	           { symmetry. eapply res_restrict_le_eq.
	             - eapply res_extend_by_le; eauto.
	             - destruct HFx as [_ [_ HoutFx] _].
	               eapply formula_fv_in_base_dom_of_extend_scoped;
	                 [exact HmyFx | exact HoutFx | exact Hbody_after_inner |].
	               eapply tlet_over_fib_formula_fresh_x.
	               + intros Hbad. apply Hfresh. apply elem_of_union_r. exact Hbad.
	               + tlet_support_solver. }
	    + admit.
    + admit.
    + admit.
    + admit.
    + normalize_models_ands_in Hmx; normalize_models_ands_goal.
      destruct Hmx as [Hmx_guard Hmx_arrow_body].
      split.
      * admit.
      * eapply res_models_forall_ext_transport.
        -- admit.
        -- exact Hext.
        -- exists (lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
             fv_cty τx ∪ fv_cty τr ∪ {[x]}).
           intros y Hy my myx Hle Hdom_my HmyFx Hmyx_body.
           admit.
        -- exact Hmx_arrow_body.
    + admit.
(*
    + cbn [denot_ty_lvar_gas] in Hmx |- *.
	      (* CTOver: peel the shared guard, then transport the inlined
	         expression-continuation forall through [Fx]. *)
	      normalize_models_ands.
	      destruct Hmx as
	        [[Hmx_ty_wf [Hmx_world [Hmx_basic_typing Hmx_total]]]
	         Hmx_over_body].
		      split.
			      ++ admit.
			      ++ eapply res_models_forall_ext_transport in Hmx_over_body; eauto.
		         -- eapply tlet_over_forall_fv_subset; eauto.
			         -- eapply tlet_over_forall_scope; [exact Hlet | solve_tlet_guard].
				         -- auto_exists_L.
				            intros y HySupport Fy mxy my HFin HFout Hwide Hmy Hbody.
				            pose proof (formula_scoped_open_of_extend
				              m Fy my _ y HFin HFout Hmy) as Htarget_scope.
				            normalize_formula_open_syntax.
				            intro_models_impl Hmy_world.
					            normalize_formula_open_syntax.
					            assert (HyΣ : LVFree y ∉ dom Σ) by tlet_support_solver.
						            try rewrite (typed_lty_env_bind_open_current_base y Σ b HyΣ)
						              in Hmy_world.
					            intro_models_impl Hmy_result.
					            normalize_formula_open_syntax.
						            assert (HyΣx : LVFree y ∉ dom (<[LVFree x := T1]> Σ))
						              by tlet_support_solver.
					            try rewrite (typed_lty_env_bind_open_current_base
					              y (<[LVFree x := T1]> Σ) b HyΣx) in Hbody.
	            assert (HmyFx : res_extend_by my Fx mxy)
	              by (eapply tlet_extensions_commute_widened_obligation; eauto).
	            use_models_impl Hbody Hbody_after_outer.
	            {
	              assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
	              assert (Hxy : x <> y) by tlet_support_solver.
			              assert (HFx_ty_m : extension_has_ltype
			                (<[LVFree x := T1]> ∅) (res_restrict m (ext_in Fx)) Fx).
			              {
			                eapply result_extension_has_ltype_from_basic_world;
			                  [exact HxΣ | exact HFx | exact Hext | exact Hmx_world].
			              }
			              assert (HFx_ty : extension_has_ltype
			                (<[LVFree x := T1]> ∅) (res_restrict my (ext_in Fx)) Fx).
			              {
			                eapply extension_has_ltype_input_resource_eq.
			                - symmetry. eapply res_extend_by_restrict_subdom_base.
			                  + eapply res_extend_by_input_dom; exact Hext.
			                  + exact Hmy.
			                - exact HFx_ty_m.
			              }
		              assert (Hdisj :
		                dom (<[LVFree y := TBase b]> Σ) ##
		                dom (<[LVFree x := T1]> (∅ : lty_env))).
		              {
		                change (dom ((<[LVFree y := TBase b]>
		                  (Σ : gmap logic_var ty)) : gmap logic_var ty) ##
		                dom ((<[LVFree x := T1]>
		                  (∅ : gmap logic_var ty)) : gmap logic_var ty)).
		                rewrite !dom_insert_L, dom_empty_L. set_solver.
		              }
		              pose proof (basic_world_formula_extend_by_typed_extension
		                (<[LVFree y := TBase b]> Σ) (<[LVFree x := T1]> (∅ : lty_env))
		                my mxy Fx Hdisj Hmy_world HFx_ty HmyFx) as Hcombined.
		              rewrite <- (lty_env_union_insert_free_singleton
		                Σ x y T1 (TBase b) Hxy HxΣ).
		              exact Hcombined.
	            }
		            use_models_impl Hbody_after_outer Hbody_after_inner.
		            {
		              eapply expr_result_formula_tlete_elim_body_from_result_extension.
		              - eapply typing_tm_lc; eauto.
		              - intros Heq. subst y.
		                apply HyΣx.
		                change (LVFree x ∈ dom
		                  ((<[LVFree x := T1]> (Σ : gmap logic_var ty)) :
		                    gmap logic_var ty)).
		                rewrite dom_insert_L. set_solver.
		              - assert (HxΣ_result : LVFree x ∉ dom Σ) by set_solver.
		                assert (Hfv_tlet :
		                  fv_tm (tlete e1 e2) ⊆ lvars_fv (dom Σ)).
		                { eapply basic_typing_lty_env_to_atom_env_fv_subset; eauto. }
		                intros Hxe2.
		                apply HxΣ_result. apply lvars_fv_elem.
		                apply Hfv_tlet. cbn [fv_tm]. set_solver.
		              - eapply (basic_world_formula_wfworld_closed_on_atoms
		                (<[LVFree y := TBase b]> Σ)).
		                + unfold lvars_of_atoms. intros z Hz.
		                  apply elem_of_map in Hz as [a [-> Ha]].
		                  change (LVFree a ∈ dom
		                    ((<[LVFree y := TBase b]> (Σ : gmap logic_var ty)) :
		                      gmap logic_var ty)).
		                  rewrite dom_insert_L. apply elem_of_union_r.
		                  apply lvars_fv_elem.
		                  pose proof (basic_typing_lty_env_to_atom_env_fv_subset
		                    Σ (tlete e1 e2) (erase_ty (CTOver b φ)) Hlet) as Hfv_tlet.
		                  apply Hfv_tlet. exact Ha.
		                + exact Hmy_world.
		              - exact HFx.
		              - exact HmyFx.
		              - exact Hmy_result.
		            }
			            assert (Hfv_fib :
			              formula_fv
			                (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
			                  (FOver (type_qualifier_formula (φ ^q^ y)))) ⊆
			              world_dom (my : WorldT)).
			            {
			              pose proof (proj1 (formula_scoped_impl_iff my _ _)
			                Htarget_scope) as [_ Hinner_scope].
			              pose proof (proj1 (formula_scoped_impl_iff my _ _)
			                Hinner_scope) as [_ Hfib_scope].
			              exact Hfib_scope.
			            }
		            pose proof (proj1 (res_models_extend_base_iff
		              my Fx mxy _ HmyFx Hfv_fib) Hbody_after_inner) as Hfib.
		            exact Hfib.
		    + (* CTUnder: same outer shape as Over, but with [FUnder]. *)
		      admit.
		    + (* CTInter: peel conjunction and use IH on both branches. *)
		      admit.
		    + (* CTUnion: transport the selected branch using IH. *)
		      admit.
		    + (* CTSum: use extension/sum pullback, then IH on each summand. *)
		      admit.
    + cbn [denot_ty_lvar_gas] in Hmx |- *.
      (* CTArrow: open the source forall with a fresh atom [y].  The source
         gives the consequent in the world [mx #> Fy].  Commute [Fx] and [Fy],
         then apply [IH] to the opened result type. *)
      normalize_models_ands.
      destruct Hmx as
        [[Hmx_ty_wf [Hmx_world [Hmx_basic_typing Hmx_total]]]
         Hmx_arrow_body].
      split.
      ++ admit.
		      ++ eapply res_models_forall_ext_transport in Hmx_arrow_body; eauto.
		         -- eapply tlet_arrow_forall_fv_subset; eauto.
			         -- eapply tlet_arrow_forall_scope; [exact Hlet | solve_tlet_guard].
				         -- auto_exists_L.
				            intros y HySupport Fy mxy my HFin HFout Hwide Hmy Hbody.
				            pose proof (formula_scoped_open_of_extend
				              m Fy my _ y HFin HFout Hmy) as Htarget_scope.
			            normalize_formula_open_syntax.
		            normalize_open_denot_in Hbody.
			            normalize_open_denot_goal.
		            normalize_open_denot_in Htarget_scope.
				            intro_models_impl Hmy_world.
			            normalize_formula_open_syntax.
			            assert (HyΣ : LVFree y ∉ dom Σ) by tlet_support_solver.
				            try rewrite (typed_lty_env_bind_open_current y Σ
				              (erase_ty τx) HyΣ) in Hmy_world.
			            assert (HyΣx : LVFree y ∉ dom (<[LVFree x := T1]> Σ))
			              by tlet_support_solver.
				            try rewrite (typed_lty_env_bind_open_current
				              y (<[LVFree x := T1]> Σ) (erase_ty τx) HyΣx) in Hbody.
			            normalize_open_denot_in Hbody.
		            assert (HmyFx : res_extend_by my Fx mxy)
	              by (eapply tlet_extensions_commute_widened_obligation; eauto).
	            use_models_impl Hbody Hbody_after_outer.
	            {
	              assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
	              assert (Hxy : x <> y) by tlet_support_solver.
		              assert (HFx_ty_m : extension_has_ltype
		                (<[LVFree x := T1]> ∅) (res_restrict m (ext_in Fx)) Fx).
		              {
		                eapply result_extension_has_ltype_from_basic_world;
		                  [exact HxΣ | exact HFx | exact Hext | exact Hmx_world].
		              }
		              assert (HFx_ty : extension_has_ltype
		                (<[LVFree x := T1]> ∅) (res_restrict my (ext_in Fx)) Fx).
		              {
		                eapply extension_has_ltype_input_resource_eq.
		                - symmetry. eapply res_extend_by_restrict_subdom_base.
		                  + eapply res_extend_by_input_dom; exact Hext.
		                  + exact Hmy.
		                - exact HFx_ty_m.
		              }
	              assert (Hdisj :
	                dom (<[LVFree y := erase_ty τx]> Σ) ##
	                dom (<[LVFree x := T1]> (∅ : lty_env))).
	              {
	                change (dom ((<[LVFree y := erase_ty τx]>
	                  (Σ : gmap logic_var ty)) : gmap logic_var ty) ##
	                dom ((<[LVFree x := T1]>
	                  (∅ : gmap logic_var ty)) : gmap logic_var ty)).
	                rewrite !dom_insert_L, dom_empty_L. set_solver.
	              }
	              pose proof (basic_world_formula_extend_by_typed_extension
	                (<[LVFree y := erase_ty τx]> Σ) (<[LVFree x := T1]> (∅ : lty_env))
	                my mxy Fx Hdisj Hmy_world HFx_ty HmyFx) as Hcombined.
	              rewrite <- (lty_env_union_insert_free_singleton
	                Σ x y T1 (erase_ty τx) Hxy HxΣ).
	              exact Hcombined.
	            }
			            intro_models_impl Hmy_arg.
			            normalize_formula_open_syntax.
			            normalize_open_denot_in Hbody_after_outer.
			            normalize_open_denot_in Hmy_arg.
	            use_models_impl Hbody_after_outer Hbody_after_inner.
            {
              assert (HxΣ0 : LVFree x ∉ dom Σ) by tlet_support_solver.
              assert (Hxy0 : x <> y) by tlet_support_solver.
              assert (Hxτx : LVFree x ∉ choice_ty_lvars τx).
              {
                cbn [choice_ty_lvars choice_ty_lvars_at] in Hfresh.
                set_solver.
              }
              assert (HFx_ty_m : extension_has_ltype
                (<[LVFree x := T1]> ∅) (res_restrict m (ext_in Fx)) Fx).
              {
                eapply result_extension_has_ltype_from_basic_world;
                  [exact HxΣ0 | exact HFx | exact Hext | exact Hmx_world].
              }
              assert (HFx_ty : extension_has_ltype
                (<[LVFree x := T1]> ∅) (res_restrict my (ext_in Fx)) Fx).
              {
                eapply extension_has_ltype_input_resource_eq.
                - symmetry. eapply res_extend_by_restrict_subdom_base.
                  + eapply res_extend_by_input_dom; exact Hext.
                  + exact Hmy.
                - exact HFx_ty_m.
              }
              eapply (tlet_arrow_arg_extend_obligation
                gas Σ x y T1 (erase_ty τx) τx my mxy Fx);
                [ exact HxΣ0
                | exact Hxy0
                | exact Hxτx
                | exact HFx_ty
                | exact HmyFx
                | exact Hmy_arg ].
            }
            assert (Hret_body_open :
                mxy ⊨ denot_ty_lvar_gas gas
                  (<[LVFree x := T1]>
                    (<[LVFree y := erase_ty τx]> Σ))
                  (cty_open 0 y τr)
                  ((tapp_tm e2 (vfvar y)) ^^ x)).
            {
              (* Normalize the opened source consequent and commute the two
                 lvar inserts, turning the source arrow body into the IH
                 premise for the opened result type. *)
			              eapply denot_ty_lvar_gas_insert_commute_tapp_open.
			              - tlet_support_solver.
			              - exact Hbody_after_inner.
		            }
				            normalize_open_denot_goal.
				            assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
				            eapply tlet_arrow_result_from_body_denotation; eauto.
			    + (* CTWand: structurally parallel to Arrow, with wand transport. *)
			      admit.
*)
Admitted.

End TLetDenotation.
