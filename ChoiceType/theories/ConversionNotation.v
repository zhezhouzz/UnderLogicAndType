(** * ChoiceType.ConversionNotation

    Uniform notation for the small structural conversions that otherwise make
    denotation goals noisy. *)

From CoreLang Require Export SyntaxNotation.
From ChoiceType Require Export DenotationType.

Declare Scope choice_scope.
Delimit Scope choice_scope with choice.
Bind Scope choice_scope with choice_ty.
Bind Scope choice_scope with ctx.
Bind Scope choice_scope with logic_var.
Bind Scope choice_scope with lty_env.

Class Erase A B := erase : A → B.
Class Lift A B := lift : A → B.
Class MOpen Env A B := mopen : Env → A → B.

#[global] Instance erase_choice_ty : Erase choice_ty ty := erase_ty.
#[global] Instance erase_ctx_inst : Erase ctx (gmap atom ty) := erase_ctx.

#[global] Instance lift_ty_inst : Lift ty choice_ty := lift_ty.
#[global] Instance lift_ctx_inst : Lift (gmap atom ty) ctx := lift_ctx.

#[global] Instance mopen_choice_ty :
  MOpen (gmap nat atom) choice_ty choice_ty := open_cty_env.
#[global] Instance mopen_tm :
  MOpen (gmap nat atom) tm tm := open_tm_env.
#[global] Instance mopen_lty_env :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lty_env_open.

Notation "⌊ x ⌋" := (erase_ty x)
  (at level 20, format "⌊ x ⌋", only printing) : choice_scope.
Notation "⌊ x ⌋" := (erase_ctx x)
  (at level 20, format "⌊ x ⌋", only printing) : choice_scope.
Notation "⌊ x ⌋" := (erase x)
  (at level 20, format "⌊ x ⌋") : choice_scope.

Notation "⌈ x ⌉" := (lift x)
  (at level 20, format "⌈ x ⌉") : choice_scope.

Notation "η ⊙ x" := (mopen η x)
  (at level 30, right associativity, format "η  ⊙  x") : choice_scope.

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, format "#ₗ k") : choice_scope.
Notation "'$ₗ' x" := (LVFree x)
  (at level 5, format "$ₗ x") : choice_scope.

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, format "↑ₗ Σ") : choice_scope.

Module ConversionNotationSmoke.
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
      (⌊τ⌋)%choice = erase_ty τ := eq_refl.

    Example erase_ctx_notation :
      (⌊Γ⌋)%choice = erase_ctx Γ := eq_refl.

    Example lift_ty_notation :
      (⌈T⌉)%choice = lift_ty T := eq_refl.

    Example lift_ctx_notation :
      (⌈Δ⌉)%choice = lift_ctx Δ := eq_refl.

    Example mopen_ty_notation :
      (η ⊙ τ)%choice = open_cty_env η τ := eq_refl.

    Example mopen_tm_notation :
      (η ⊙ e)%choice = open_tm_env η e := eq_refl.

    Example mopen_lty_env_notation :
      (η ⊙ Σ)%choice = lty_env_open η Σ := eq_refl.

    Example lvar_notation :
      (#ₗ 0, $ₗ x)%choice = (LVBound 0, LVFree x) := eq_refl.

    Example atom_env_notation :
      (↑ₗ Δ)%choice = atom_env_to_lty_env Δ := eq_refl.
  End Smoke.
End ConversionNotationSmoke.
