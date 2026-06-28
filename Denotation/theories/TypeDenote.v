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

Lemma fiberwise_joinable_on_ty_static_guard_formula X Σ τ e :
  fiberwise_joinable_on X (ty_static_guard_formula Σ τ e).
Proof.
  unfold ty_static_guard_formula.
  apply fiberwise_joinable_on_and.
  - apply fiberwise_joinable_on_context_ty_wf_formula.
  - apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_basic_world_formula.
    + apply fiberwise_joinable_on_expr_basic_typing_formula.
Qed.

Lemma fiberwise_joinable_on_ty_guard_formula X Σ τ e :
  fiberwise_joinable_on X (ty_guard_formula Σ τ e).
Proof.
  unfold ty_guard_formula.
  apply fiberwise_joinable_on_and.
  - apply fiberwise_joinable_on_context_ty_wf_formula.
  - apply fiberwise_joinable_on_and.
    + apply fiberwise_joinable_on_basic_world_formula.
    + apply fiberwise_joinable_on_and.
      * apply fiberwise_joinable_on_expr_basic_typing_formula.
      * apply fiberwise_joinable_on_expr_total_formula.
Qed.

Lemma fiberwise_joinable_ty_static_guard_formula Σ τ e :
  fiberwise_joinable (ty_static_guard_formula Σ τ e).
Proof. intros X. apply fiberwise_joinable_on_ty_static_guard_formula. Qed.

Lemma fiberwise_joinable_ty_guard_formula Σ τ e :
  fiberwise_joinable (ty_guard_formula Σ τ e).
Proof. intros X. apply fiberwise_joinable_on_ty_guard_formula. Qed.

Definition result_basic_typing_formula (b : base_ty) : FormulaT :=
  expr_basic_typing_formula
    (typed_lty_env_bind ∅ (TBase b))
    (tret (vbvar 0))
    (TBase b).

Definition over_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  FOver (FAnd (FAtom φ) (result_basic_typing_formula b)).

Definition under_result_body (b : base_ty) (φ : type_qualifier) : FormulaT :=
  FUnder (FAnd (FAtom φ) (result_basic_typing_formula b)).

Lemma formula_fv_result_basic_typing_formula b :
  formula_fv (result_basic_typing_formula b) = ∅.
Proof.
  unfold result_basic_typing_formula.
  rewrite formula_fv_expr_basic_typing_formula.
  rewrite typed_lty_env_bind_dom, dom_empty_L.
  rewrite lvars_fv_union, lvars_shift_from_fv,
    lvars_fv_empty, lvars_fv_singleton_bound.
  set_solver.
Qed.

Definition arrow_value_denote_gas_with
    (denote : nat -> lty_env -> context_ty -> tm -> FormulaT)
    (gas : nat) (Σ : lty_env) (τx τr : context_ty) (ef : tm) :
    FormulaT :=
  let Σx := typed_lty_env_bind Σ (erase_ty τx) in
  FForall
    (FImpl
      (denote gas Σx
        (cty_shift 0 τx) (tret (vbvar 0)))
      (denote gas Σx τr
        (tapp_tm (tm_shift 0 ef) (vbvar 0)))).

Definition wand_value_denote_gas_with
    (denote : nat -> lty_env -> context_ty -> tm -> FormulaT)
    (gas : nat) (Σ : lty_env) (τx τr : context_ty) (ef : tm) :
    FormulaT :=
  let Σx := typed_lty_env_bind Σ (erase_ty τx) in
  FBWand 1
    (denote gas Σx
      (cty_shift 0 τx) (tret (vbvar 0)))
    (denote gas Σx τr
      (tapp_tm (tm_shift 0 ef) (vbvar 0))).

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
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (over_result_body b φ)))
      | CTUnder b φ =>
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (under_result_body b φ)))
      | CTInter τ1 τ2 =>
          FAnd
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          let Σr := typed_lty_env_bind Σg (erase_ty τ1) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FPlus
                (ty_denote_gas gas' Σr
                  (cty_shift 0 τ1) (tret (vbvar 0)))
                (ty_denote_gas gas' Σr
                  (cty_shift 0 τ2) (tret (vbvar 0)))))
      | CTArrow τx τr =>
          let Σf := typed_lty_env_bind Σg (erase_ty (CTArrow τx τr)) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (arrow_value_denote_gas_with ty_denote_gas gas' Σf
                (cty_shift 0 τx) (cty_shift 1 τr)
                (tret (vbvar 0))))
      | CTWand τx τr =>
          let Σf := typed_lty_env_bind Σg (erase_ty (CTWand τx τr)) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (wand_value_denote_gas_with ty_denote_gas gas' Σf
                (cty_shift 0 τx) (cty_shift 1 τr)
                (tret (vbvar 0))))
      | CTPersist τ1=>
          let Σr := typed_lty_env_bind Σg (erase_ty (CTPersist τ1)) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FPersist (ty_denote_gas gas' Σr
                    (cty_shift 0 τ1) (tret (vbvar 0)))))
    end
    end).

Definition arrow_value_denote_gas :=
  arrow_value_denote_gas_with ty_denote_gas.

Definition wand_value_denote_gas :=
  wand_value_denote_gas_with ty_denote_gas.

Definition ty_denote
    (Δ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

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

End TypeDenote.
