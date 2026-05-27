(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    choice-type denotation. *)

From Denotation Require Export Notation.
From Denotation Require Import TypeDenotation.

Section ContextDenotation.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Fixpoint denot_ctx_under (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
  match Γ with
  | CtxEmpty =>
      FTrue
  | CtxBind x τ =>
      denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))
  | CtxComma Γ1 Γ2 =>
      FAnd
        (denot_ctx_under Σ Γ1)
        (denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2)
  | CtxStar Γ1 Γ2 =>
      FStar (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  | CtxSum Γ1 Γ2 =>
      FPlus (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  end.

Definition denot_ctx (Γ : ctx) : FormulaT :=
  denot_ctx_under (erase_ctx Γ) Γ.

Definition denot_ctx_in_env (Σ : gmap atom ty) (Γ : ctx) : FormulaT :=
  FAnd (basic_world_formula (atom_env_to_lty_env Σ))
    (FAnd
      (basic_world_formula (atom_env_to_lty_env (erase_ctx_under Σ Γ)))
      (denot_ctx_under Σ Γ)).

Definition denot_ty_under
    (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FormulaT :=
  denot_ty Σ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx Γ) τ e.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FormulaT :=
  denot_ty (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorldT) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  m ⊨ expr_total_formula e.

Definition entails_total (φ : FormulaT) (P : WfWorldT -> Prop) : Prop :=
  forall m, m ⊨ φ -> P m.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  forall x, x ∈ X -> Σ1 !! x = Σ2 !! x.

End ContextDenotation.

#[global] Instance denot_cty_inst :
    Denotation choice_ty (tm -> Formula (V := value)) :=
  fun τ e => denot_ty ∅ τ e.
#[global] Instance denot_ctx_inst :
    Denotation ctx (Formula (V := value)) := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.
