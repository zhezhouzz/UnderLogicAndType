(** * ChoiceType.DenotationNotation

    Formula custom-entry notation for the ChoiceType-specific atoms that appear
    in type denotations and tlet proofs. *)

From ChoiceLogic Require Export FormulaNotation.
From ChoiceType Require Export ConversionNotation.

Notation "'basic' '[' Σe ',' Στ ']' e '⋮' τ" :=
  (FBasicTypingIn Σe Στ τ e)
  (at level 10,
   Σe at level 9, Στ at level 9,
   e at level 9, τ at level 9) : formula_scope.

Notation "'closed' Σ" := (FClosedResourceIn Σ)
  (at level 10, Σ at level 9) : formula_scope.

Notation "'total' '[' Σ ']' e" := (FStrongTotalIn Σ e)
  (at level 10, Σ at level 9, e at level 9) : formula_scope.

Notation "'result-basic' '[' Σ ',' D ']' b" :=
  (FResultBasicWorld Σ b D)
  (at level 10,
   Σ at level 9, D at level 9, b at level 9) : formula_scope.

Notation "'tyq' q" := (FTypeQualifier q)
  (at level 10, q at level 9) : formula_scope.

Notation "e '⇓' '[' D ']'" := (FExprResultOn D e)
  (at level 20, D at level 9) : formula_scope.

Notation "e '⇓' '[' D ']' '@' ν" := (FExprResultAt D e ν)
  (at level 20,
   D at level 9, ν at level 9) : formula_scope.

Notation "'result' D e" := (FExprResultOn D e)
  (at level 20, D at level 9, e at level 9) : formula_scope.

Notation "'result' D e 'at' ν" := (FExprResultAt D e ν)
  (at level 20,
   D at level 9, e at level 9, ν at level 9) : formula_scope.

Notation "'cont' '[' Σ ']' e '=>' φ" := (FExprContIn Σ e φ)
  (at level 100,
   Σ at level 9, e at level 9,
   φ at level 200) : formula_scope.

Notation "'denot' '[' Σe ',' Στ ']' e '⋮' τ" :=
  (denot_ty_lvar Σe Στ τ e)
  (at level 10,
   Σe at level 9, Στ at level 9,
   e at level 9, τ at level 9) : formula_scope.

Notation "'denot-body' '[' Σe ',' Στ ']' e '⋮' τ" :=
  (denot_ty_body_lvar Σe Στ τ e)
  (at level 10,
   Σe at level 9, Στ at level 9,
   e at level 9, τ at level 9) : formula_scope.

Notation "'denot-on' '[' Σ ']' e '⋮' τ" :=
  (denot_ty_on Σ τ e)
  (at level 10, Σ at level 9, e at level 9, τ at level 9) : formula_scope.

Notation "'basic' '[' Σe ',' Στ ']' e ':' τ" :=
  (FBasicTypingIn Σe Στ τ e)
  (in custom form at level 10,
   Σe constr at level 9, Στ constr at level 9,
   e constr at level 9, τ constr at level 9, only parsing).

Notation "'closed' Σ" := (FClosedResourceIn Σ)
  (in custom form at level 10, Σ constr at level 9, only parsing).

Notation "'total' '[' Σ ']' e" := (FStrongTotalIn Σ e)
  (in custom form at level 10, Σ constr at level 9,
   e constr at level 9, only parsing).

Notation "'result-basic' '[' Σ ',' D ']' b" :=
  (FResultBasicWorld Σ b D)
  (in custom form at level 10,
   Σ constr at level 9, D constr at level 9,
   b constr at level 9, only parsing).

Notation "'tyq' q" := (FTypeQualifier q)
  (in custom form at level 10, q constr at level 9, only parsing).

Notation "e '⇓' '[' D ']'" := (FExprResultOn D e)
  (in custom form at level 20, e constr at level 9,
   D constr at level 9, only parsing).

Notation "e '⇓' '[' D ']' '@' ν" := (FExprResultAt D e ν)
  (in custom form at level 20,
   e constr at level 9, D constr at level 9,
   ν constr at level 9, only parsing).

Notation "'result' D e" := (FExprResultOn D e)
  (in custom form at level 20, D constr at level 9,
   e constr at level 9, only parsing).

Notation "'result' D e 'at' ν" := (FExprResultAt D e ν)
  (in custom form at level 20,
   D constr at level 9, e constr at level 9,
   ν constr at level 9, only parsing).

Notation "'cont' '[' Σ ']' e '=>' φ" := (FExprContIn Σ e φ)
  (in custom form at level 90,
   Σ constr at level 9, e constr at level 9,
   φ custom form at level 90, only parsing).

Module DenotationNotationSmoke.
  Section Smoke.
    Variables Σe Στ : lty_env.
    Variable Σ : gmap atom ty.
    Variables τ : choice_ty.
    Variable e : tm.
    Variable x : atom.
    Variable b : base_ty.
    Variable D : lvset.
    Variable q : type_qualifier.

    Example basic_notation :
      <{ basic[Σe, Στ] e : τ }> =
      FBasicTypingIn Σe Στ τ e := eq_refl.

    Example closed_total_notation :
      <{ closed Σe ∧ total[Σe] e }> =
      FAnd (FClosedResourceIn Σe) (FStrongTotalIn Σe e) := eq_refl.

    Example result_basic_fiber_notation :
      <{ result-basic[Στ, D] b ∧ fib D |> over tyq q }> =
      FAnd (FResultBasicWorld Στ b D)
        (FFibVars D (FOver (FTypeQualifier q))) := eq_refl.

    Example result_on_symbol_notation :
      <{ e ⇓[D] }> = FExprResultOn D e := eq_refl.

    Example result_at_notation :
      <{ result D e at x }> = FExprResultAt D e x := eq_refl.

    Example cont_notation :
      <{ cont[Σ] e => result-basic[Στ, D] b }> =
      FExprContIn Σ e (FResultBasicWorld Στ b D) := eq_refl.

    Example formula_scope_denot_notation :
      (∀. denot[Σe, Στ] e ⋮ τ → e ⇓[D])%formula =
      FForall (FImpl (denot_ty_lvar Σe Στ τ e) (FExprResultOn D e)) :=
      eq_refl.
  End Smoke.
End DenotationNotationSmoke.
