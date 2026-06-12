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
  FAnd
    (ty_guard_formula Σ τ e)
    (match gas with
    | 0 => FTrue
    | S gas' =>
      match τ with
      | CTOver b φ =>
          FForall
            (FImpl
              (expr_result_formula_at (dom Σ)
                (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FOver (FAtom φ))))
      | CTUnder b φ =>
          FForall
            (FImpl
              (expr_result_formula_at (dom Σ)
                (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FUnder (FAtom φ))))
      | CTInter τ1 τ2 =>
          FAnd
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          let Σr := typed_lty_env_bind Σ (erase_ty τ1) in
          FForall
            (FImpl
              (expr_result_formula_at (dom Σ)
                (tm_shift 0 e) (LVBound 0))
              (FPlus
                (ty_denote_gas gas' Σr
                  (cty_shift 0 τ1) (tret (vbvar 0)))
                (ty_denote_gas gas' Σr
                  (cty_shift 0 τ2) (tret (vbvar 0)))))
      | CTArrow τx τr =>
          let Σx := typed_lty_env_bind Σ (erase_ty τx) in
          FForall
            (FImpl
              (ty_denote_gas gas' Σx
                (cty_shift 0 τx) (tret (vbvar 0)))
              (ty_denote_gas gas' Σx τr
                (tapp_tm (tm_shift 0 e) (vbvar 0))))
      | CTWand τx τr =>
          let Σx := typed_lty_env_bind Σ (erase_ty τx) in
          FBWand 1
            (ty_denote_gas gas' Σx
              (cty_shift 0 τx) (tret (vbvar 0)))
            (ty_denote_gas gas' Σx τr
              (tapp_tm (tm_shift 0 e) (vbvar 0)))
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
    (ty_guard_formula Σ τ e) =
  ty_guard_formula
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
Admitted.

Lemma formula_open_env_ty_denote_gas_zero η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (ty_denote_gas 0 Σ τ e) =
  ty_denote_gas 0
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
Admitted.

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
	      rewrite formula_open_env_fibvars;
	      [|eapply open_env_fresh_for_lvars_mono; [|exact Hfreshφ]; set_solver];
	      rewrite open_env_lift_qual_diff_bound0
	        by exact Hfreshφ;
	      rewrite !formula_open_env_impl;
	      rewrite open_env_lift_expr_result_shift0_core
	        by (exact Hfreshe || exact Hinj);
	      first [rewrite formula_open_env_over
	            |rewrite formula_open_env_under];
	      rewrite formula_open_env_atom;
	      reflexivity ] ].

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

Lemma sum_result_lift_support_subset Σ τsum τ e T :
  context_ty_lvars τ ⊆ context_ty_lvars τsum ->
  lvars_at_depth 1
    (dom (typed_lty_env_bind (relevant_env Σ τsum e) T) ∪
     relevant_lvars (cty_shift 0 τ) (tret (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars τsum e.
Proof.
  intros Hτsub.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  rewrite elem_of_subseteq. intros u Hu.
  rewrite elem_of_union in Hu.
  destruct Hu as [Hu|Hu].
  - pose proof (lvars_at_depth_relevant_env_subset_relevant
      0 Σ τsum e u Hu) as Hrel.
    set_solver.
  - rewrite lvars_at_depth_union in Hu.
    rewrite context_ty_lvars_depth in Hu.
    rewrite tm_lvars_depth in Hu.
    rewrite tm_lvars_at_tret_bound0_under in Hu.
    rewrite context_ty_lvars_at_shift_under in Hu by lia.
    change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ) in Hu.
    set_solver.
Qed.

Lemma expr_result_shift0_bound0_lvars_subset e d :
  formula_lvars_at (S d)
    (expr_result_formula (tm_shift 0 e) (LVBound 0)) ⊆
  tm_lvars_at d e.
Proof.
  unfold expr_result_formula, expr_result_formula_at, expr_result_qual.
  cbn [formula_lvars_at qual_vars qual_lvars].
  rewrite lvars_at_depth_union.
  rewrite tm_lvars_depth.
  rewrite tm_lvars_at_shift_under by lia.
  rewrite lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma expr_result_atom_shift0_bound0_lvars_subset e d :
  formula_lvars_at (S d)
    (expr_result_atom_formula (tm_shift 0 e) (LVBound 0)) ⊆
  tm_lvars_at d e.
Proof.
  unfold expr_result_atom_formula, expr_result_qual.
  cbn [formula_lvars_at qual_vars qual_lvars].
  rewrite lvars_at_depth_union.
  rewrite tm_lvars_depth.
  rewrite tm_lvars_at_shift_under by lia.
  rewrite lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma formula_open_env_ty_denote_gas η gas Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (ty_denote_gas gas Σ τ e) =
  ty_denote_gas gas
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
Admitted.

Definition ty_denote
    (Δ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

Lemma formula_open_ty_denote_gas_singleton
    k y gas Σ τ e :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  formula_open k y (ty_denote_gas gas Σ τ e) =
  ty_denote_gas gas
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
      (dom Σ ∪ relevant_lvars τ e)).
  {
    apply open_env_fresh_for_lvars_singleton.
    relevant_lvars_norm. better_set_solver.
  }
  pose proof (formula_open_env_ty_denote_gas
    (<[k := y]> ∅) gas Σ τ e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  exact Heq.
Qed.

Lemma ty_denote_gas_env_agree_on gas Σ1 Σ2 τ e X :
  relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  ty_denote_gas gas Σ1 τ e =
  ty_denote_gas gas Σ2 τ e.
Proof.
Admitted.

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

Notation "'⟦ty' τ '⟧[' Σ ',' gas ']'" :=
  (ty_denote_gas gas Σ τ)
  (at level 20, τ at level 200, Σ at level 200, gas at level 9,
   only parsing).

Notation "'⟦ty' τ '⟧[' Σ ',' gas ']' e" :=
  (ty_denote_gas gas Σ τ e)
  (at level 20, τ at level 200, Σ at level 200,
   gas at level 9, e at level 20,
   only parsing).

Notation "'⟦ty' τ '⟧[' Δ ']'" :=
  (ty_denote Δ τ)
  (at level 20, τ at level 200, Δ at level 200,
   only parsing).

Notation "'⟦ty' τ '⟧[' Δ ']' e" :=
  (ty_denote Δ τ e)
  (at level 20, τ at level 200, Δ at level 200, e at level 20,
   only parsing).

Notation "'⟦ty⟧[' Σ ',' gas ']' τ" :=
  (ty_denote_gas gas Σ τ)
  (at level 20, Σ at level 200, gas at level 9, τ at level 200,
   format "⟦ty⟧[ Σ ,  gas ]  τ").

Notation "'⟦ty⟧[' Σ ',' gas ']' τ e" :=
  (ty_denote_gas gas Σ τ e)
  (at level 20, Σ at level 200, gas at level 9,
   τ at level 200, e at level 20,
   format "⟦ty⟧[ Σ ,  gas ]  τ  e").

Notation "'⟦ty⟧[' Δ ']' τ" :=
  (ty_denote Δ τ)
  (at level 20, Δ at level 200, τ at level 200,
   format "⟦ty⟧[ Δ ]  τ").

Notation "'⟦ty⟧[' Δ ']' τ e" :=
  (ty_denote Δ τ e)
  (at level 20, Δ at level 200, τ at level 200, e at level 20,
   format "⟦ty⟧[ Δ ]  τ  e").

Notation "'guard[' Σ ']' τ" :=
  (ty_guard_formula Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "guard[ Σ ]  τ").

Notation "'guard[' Σ ']' τ e" :=
  (ty_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "guard[ Σ ]  τ  e").

Notation "'static_guard[' Σ ']' τ" :=
  (ty_static_guard_formula Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "static_guard[ Σ ]  τ").

Notation "'static_guard[' Σ ']' τ e" :=
  (ty_static_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "static_guard[ Σ ]  τ  e").

Ltac ty_denote_open_one_side :=
  first
    [ assumption
    | relevant_lvars_norm; better_set_solver
    | type_open_env_syntax_norm;
      cbn [fv_tm fv_value value_lvars value_lvars_at];
      rewrite ?fv_tapp_tm, ?tm_shift_fv, ?cty_shift_fv;
      better_set_solver ].

Ltac ty_denote_open_one_norm :=
  repeat match goal with
  | |- context [formula_open 0 ?y
      (ty_denote_gas ?gas ?Σ ?τ ?e)] =>
      rewrite (formula_open_ty_denote_gas_singleton 0 y gas Σ τ e)
        by ty_denote_open_one_side
  end;
  repeat match goal with
  | |- context [open_tm 0 (vfvar ?y) (tret (vbvar 0))] =>
      change (open_tm 0 (vfvar y) (tret (vbvar 0)))
        with (tret (vfvar y))
  end;
  try rewrite ?open_tapp_tm_shift_bvar0_lc by assumption;
  type_open_env_syntax_norm.

Ltac ty_denote_open_one_norm_in H :=
  repeat match type of H with
  | context [formula_open 0 ?y
      (ty_denote_gas ?gas ?Σ ?τ ?e)] =>
      rewrite (formula_open_ty_denote_gas_singleton 0 y gas Σ τ e) in H
        by ty_denote_open_one_side
  end;
  repeat match type of H with
  | context [open_tm 0 (vfvar ?y) (tret (vbvar 0))] =>
      change (open_tm 0 (vfvar y) (tret (vbvar 0)))
        with (tret (vfvar y)) in H
  end;
  try rewrite ?open_tapp_tm_shift_bvar0_lc in H by assumption;
  type_open_env_syntax_norm_in H.

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
  unfold ty_guard_formula, context_ty_wf_formula, basic_world_formula,
    expr_basic_typing_formula, expr_total_formula, expr_result_formula,
    expr_result_atom_formula, FFiberAtom;
  cbn [formula_lvars_at];
	  unfold context_ty_wf_qual, basic_world_qual,
	    expr_basic_typing_qual, expr_total_qual, expr_result_qual;
	  cbn [qual_dom qual_vars qual_lvars].

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
  lvars_at_depth d (dom Σ).
Proof.
Admitted.

Lemma ty_denote_gas_fv_subset gas Σ τ e :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆
  lvars_fv (dom Σ).
Proof.
Admitted.

Lemma fv_tm_ty_denote_gas_subset_formula gas Σ τ e :
  fv_tm e ⊆ formula_fv (ty_denote_gas gas Σ τ e).
Proof.
  destruct gas; cbn [ty_denote_gas]; unfold ty_guard_formula.
  all: rewrite !formula_fv_and, formula_fv_expr_total_formula, tm_lvars_fv;
    set_solver.
Qed.

Lemma relevant_env_fv_ty_denote_gas_subset_formula gas Σ τ e :
  lvars_fv (dom (relevant_env Σ τ e)) ⊆
  formula_fv (ty_denote_gas gas Σ τ e).
Proof.
Admitted.

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
Admitted.

End TypeDenoteSupport.
