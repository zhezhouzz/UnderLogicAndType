(** * Denotation.Context

    Denotation of type contexts, expressed directly with the new recursive
    choice-type denotation. *)

From CoreLang Require Import Syntax.
From ChoiceLogic Require Import Formula FormulaDerived.
From ChoiceTypeLanguage Require Import Interface.
From Denotation Require Import TypeDenotation.

Section ContextDenotation.

Local Notation FormulaT := (Formula (V := value)) (only parsing).

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

End ContextDenotation.
