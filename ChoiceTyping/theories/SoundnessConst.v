(** * ChoiceTyping.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From ChoiceTyping Require Export SoundnessHelpers.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Definition const_eq_qual (c : constant) (ν : atom) : type_qualifier :=
  qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)).

Definition const_over_consequent (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FAnd
    (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
    (FFibVars (qual_vars (const_eq_qual c ν))
      (FOver (FTypeQualifier (const_eq_qual c ν)))).

Definition const_under_consequent (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FAnd
    (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
    (FFibVars (qual_vars (const_eq_qual c ν))
      (FUnder (FTypeQualifier (const_eq_qual c ν)))).

Definition const_over_consequent_on (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FAnd
    (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
      ({[ν]} ∪ qual_dom (const_eq_qual c ν)))
    (FFibVars (qual_vars (const_eq_qual c ν))
      (FOver (FTypeQualifier (const_eq_qual c ν)))).

Definition const_under_consequent_on (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FAnd
    (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
      ({[ν]} ∪ qual_dom (const_eq_qual c ν)))
    (FFibVars (qual_vars (const_eq_qual c ν))
      (FUnder (FTypeQualifier (const_eq_qual c ν)))).

Lemma basic_const_world_from_lookup c ν Σ m :
  (∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some (vconst c)) →
  m ⊨ basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]}.
Proof.
  (* Transitional const/basic-store bridge during lqual-domain LN refactor. *)
Admitted.

Lemma basic_const_world_from_expr_atom c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨ basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]}.
Proof.
  intros Hexpr.
  apply basic_const_world_from_lookup.
  apply expr_logic_qual_ret_const_lookup. exact Hexpr.
Qed.

Lemma lifted_const_qualifier_from_projection c ν m σ
    (Hproj : res_restrict m {[ν]} σ) :
  σ !! ν = Some (vconst c) →
  res_models_with_store σ
    (res_fiber_from_projection m {[ν]} σ Hproj)
    (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))).
Proof.
Admitted.

Local Ltac solve_const_refinement_scope Hbasic :=
  pose proof (res_models_with_store_fuel_scoped _ ∅ _ _ Hbasic);
  unfold formula_scoped_in_world in *; simpl in *;
  unfold stale, stale_logic_qualifier in *;
  repeat rewrite formula_fv_FTypeQualifier in *;
  unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *;
  repeat (rewrite decide_True in * by set_solver);
  simpl in *; set_solver.

Lemma const_over_consequent_from_expr c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨ const_over_consequent Σ c ν.
Proof.
  (* Transitional const bridge during primitive fiber/LN refactor. *)
Admitted.

Lemma const_under_consequent_from_expr c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨ const_under_consequent Σ c ν.
Proof.
  (* Transitional const bridge during primitive fiber/LN refactor. *)
Admitted.

Lemma const_over_consequent_from_expr_on c ν Σ m :
  m ⊨ FExprResultAt (dom Σ) (tret (vconst c)) ν →
  m ⊨ const_over_consequent_on Σ c ν.
Proof.
  (* Transitional const bridge during primitive fiber/LN refactor. *)
Admitted.

Lemma const_under_consequent_from_expr_on c ν Σ m :
  m ⊨ FExprResultAt (dom Σ) (tret (vconst c)) ν →
  m ⊨ const_under_consequent_on Σ c ν.
Proof.
  (* Transitional const bridge during primitive fiber/LN refactor. *)
Admitted.

Lemma const_over_consequent_from_renamed_expr c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FAtom (expr_logic_qual (tret (vconst c)) ν)) →
  m ⊨ formula_rename_atom ν y (const_over_consequent Σ c ν).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply const_over_consequent_from_expr.
  apply res_models_swap.
  exact Hexpr.
Qed.

Lemma const_under_consequent_from_renamed_expr c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FAtom (expr_logic_qual (tret (vconst c)) ν)) →
  m ⊨ formula_rename_atom ν y (const_under_consequent Σ c ν).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply const_under_consequent_from_expr.
  apply res_models_swap.
  exact Hexpr.
Qed.

Lemma const_over_consequent_from_renamed_expr_on c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FExprResultAt (dom Σ) (tret (vconst c)) ν) →
  m ⊨ formula_rename_atom ν y (const_over_consequent_on Σ c ν).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply (const_over_consequent_from_expr_on c ν Σ).
  apply res_models_swap.
  exact Hexpr.
Qed.

Lemma const_under_consequent_from_renamed_expr_on c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FExprResultAt (dom Σ) (tret (vconst c)) ν) →
  m ⊨ formula_rename_atom ν y (const_under_consequent_on Σ c ν).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply (const_under_consequent_from_expr_on c ν Σ).
  apply res_models_swap.
  exact Hexpr.
Qed.

Definition const_over_body (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FAtom (expr_logic_qual (tret (vconst c)) ν))
    (const_over_consequent Σ c ν).

Definition const_under_body (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FAtom (expr_logic_qual (tret (vconst c)) ν))
    (const_under_consequent Σ c ν).

Definition const_over_body_on
    (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FExprResultAt (dom Σ) (tret (vconst c)) ν)
    (const_over_consequent_on Σ c ν).

Definition const_under_body_on
    (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FExprResultAt (dom Σ) (tret (vconst c)) ν)
    (const_under_consequent_on Σ c ν).

Lemma const_over_body_fv_subset Σ c ν :
  formula_fv (const_over_body Σ c ν) ⊆ {[ν]}.
Proof.
  (* Transitional fv accounting during primitive fiber/LN refactor. *)
Admitted.

Lemma const_under_body_fv_subset Σ c ν :
  formula_fv (const_under_body Σ c ν) ⊆ {[ν]}.
Proof.
  (* Transitional fv accounting during primitive fiber/LN refactor. *)
Admitted.

Lemma const_over_body_on_fv_subset Σ c ν :
  formula_fv (const_over_body_on Σ c ν) ⊆ dom Σ ∪ {[ν]}.
Proof.
Admitted.

Lemma const_under_body_on_fv_subset Σ c ν :
  formula_fv (const_under_body_on Σ c ν) ⊆ dom Σ ∪ {[ν]}.
Proof.
Admitted.

Lemma const_over_body_rename_scoped Σ c ν y (m : WfWorld) :
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m (formula_rename_atom ν y (const_over_body Σ c ν)).
Proof.
  intros Hym.
  unfold formula_scoped_in_world. intros z Hz.
  rewrite dom_empty_L in Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  rewrite formula_fv_rename_atom in Hz.
  rewrite elem_of_aset_swap in Hz.
  pose proof (const_over_body_fv_subset Σ c ν _ Hz) as Hν.
  apply elem_of_singleton in Hν.
  unfold atom_swap in Hν.
  repeat destruct decide; subst; try congruence; exact Hym.
Qed.

Lemma const_under_body_rename_scoped Σ c ν y (m : WfWorld) :
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m (formula_rename_atom ν y (const_under_body Σ c ν)).
Proof.
  intros Hym.
  unfold formula_scoped_in_world. intros z Hz.
  rewrite dom_empty_L in Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  rewrite formula_fv_rename_atom in Hz.
  rewrite elem_of_aset_swap in Hz.
  pose proof (const_under_body_fv_subset Σ c ν _ Hz) as Hν.
  apply elem_of_singleton in Hν.
  unfold atom_swap in Hν.
  repeat destruct decide; subst; try congruence; exact Hym.
Qed.

Lemma const_over_body_on_rename_scoped Σ c ν y (m : WfWorld) :
  dom Σ ⊆ world_dom (m : World) →
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m
    (formula_rename_atom ν y (const_over_body_on Σ c ν)).
Proof.
Admitted.

Lemma const_under_body_on_rename_scoped Σ c ν y (m : WfWorld) :
  dom Σ ⊆ world_dom (m : World) →
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m
    (formula_rename_atom ν y (const_under_body_on Σ c ν)).
Proof.
Admitted.
