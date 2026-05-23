(** * ChoiceTypeLanguage.Notation

    Public syntax notation for the pure choice-type language layer. *)

From CoreLang Require Export SyntaxNotation.
From ChoiceTypeLanguage Require Export Env.

Declare Scope choice_scope.
Delimit Scope choice_scope with choice.
Bind Scope choice_scope with choice_ty.
Bind Scope choice_scope with ctx.
Bind Scope choice_scope with logic_var.
Bind Scope choice_scope with lty_env.

Class Erase A B := erase : A -> B.
Class Lift A B := lift : A -> B.

#[global] Instance erase_choice_ty : Erase choice_ty ty := erase_ty.
#[global] Instance erase_ctx_inst : Erase ctx (gmap atom ty) := erase_ctx.

#[global] Instance lift_ty_inst : Lift ty choice_ty := lift_ty.
#[global] Instance lift_ctx_inst : Lift (gmap atom ty) ctx := lift_ctx.

Notation "⌊ x ⌋" := (erase x)
  (at level 20, format "⌊ x ⌋").

Notation "⌈ x ⌉" := (lift x)
  (at level 20, format "⌈ x ⌉") : choice_scope.

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, format "#ₗ k") : choice_scope.

Notation "'$ₗ' x" := (LVFree x)
  (at level 5, format "$ₗ x") : choice_scope.

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, format "↑ₗ Σ") : choice_scope.

Module TypeLanguageNotationSmoke.
  Section Smoke.
    Variable τ : choice_ty.
    Variable Γ : ctx.
    Variable T : ty.
    Variable Δ : gmap atom ty.
    Variable η : gmap nat atom.
    Variable e : tm.
    Variable Σ : lty_env.
    Variable x : atom.

    Example erase_ty_notation :
      ⌊τ⌋ = erase_ty τ := eq_refl.

    Example erase_ctx_notation :
      ⌊Γ⌋ = erase_ctx Γ := eq_refl.

    Example lift_ty_notation :
      (⌈T⌉)%choice = lift_ty T := eq_refl.

    Example lift_ctx_notation :
      (⌈Δ⌉)%choice = lift_ctx Δ := eq_refl.

    Example mopen_ty_notation :
      (η ⊙ τ)%choice = open_cty_env η τ := eq_refl.

    Example mopen_lty_env_notation :
      (η ⊙ Σ)%choice = lty_env_open η Σ := eq_refl.

    Example lvar_notation :
      (#ₗ 0, $ₗ x)%choice = (LVBound 0, LVFree x) := eq_refl.

    Example atom_env_notation :
      (↑ₗ Δ)%choice = atom_env_to_lty_env Δ := eq_refl.
  End Smoke.
End TypeLanguageNotationSmoke.
