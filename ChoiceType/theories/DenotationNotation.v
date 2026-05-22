(** * ChoiceType.DenotationNotation

    Formula custom-entry notation for the ChoiceType-specific atoms that appear
    in type denotations and tlet proofs. *)

From ChoiceLogic Require Export FormulaNotation.
From ChoiceType Require Export ConversionNotation.

Notation "'obl' '[' Σ ']' e '⋮' τ" :=
  (FDenotObligationIn Σ τ e)
  (at level 10,
   Σ at level 9, e at level 9, τ at level 9) : formula_scope.

Notation "'closed' Σ" := (FClosedResourceIn Σ)
  (at level 10, Σ at level 9) : formula_scope.

Notation "'tyq' q" := (FTypeQualifier q)
  (at level 10, q at level 9) : formula_scope.

Notation "e '⇓ₗ' '[' D ']' '@' ν" := (FExprResultAtLvar D e ν)
  (at level 20,
   D at level 9, ν at level 9) : formula_scope.

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

Notation "'result-lvar' D e 'at' ν" := (FExprResultAtLvar D e ν)
  (at level 20,
   D at level 9, e at level 9, ν at level 9) : formula_scope.

Notation "'cont' '[' Σ ',' T ']' e '=>' φ" := (FExprContIn Σ T e (fun _ => φ))
  (at level 100,
   Σ at level 9, T at level 9, e at level 9,
   φ at level 200) : formula_scope.

Notation "'denot' '[' Σ ']' e '⋮' τ" :=
  (denot_ty_lvar Σ τ e)
  (at level 10,
   Σ at level 9,
   e at level 9, τ at level 9) : formula_scope.

Notation "'denot-on' '[' Σ ']' e '⋮' τ" :=
  (denot_ty_on Σ τ e)
  (at level 10, Σ at level 9, e at level 9, τ at level 9) : formula_scope.

Notation "'obl' '[' Σ ']' e ':' τ" :=
  (FDenotObligationIn Σ τ e)
  (in custom form at level 10,
   Σ constr at level 9,
   e constr at level 9, τ constr at level 9, only parsing).

Notation "'closed' Σ" := (FClosedResourceIn Σ)
  (in custom form at level 10, Σ constr at level 9, only parsing).

Notation "'tyq' q" := (FTypeQualifier q)
  (in custom form at level 10, q constr at level 9, only parsing).

Notation "e '⇓ₗ' '[' D ']' '@' ν" := (FExprResultAtLvar D e ν)
  (in custom form at level 20,
   e constr at level 9, D constr at level 9,
   ν constr at level 9, only parsing).

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

Notation "'result-lvar' D e 'at' ν" := (FExprResultAtLvar D e ν)
  (in custom form at level 20,
   D constr at level 9, e constr at level 9,
   ν constr at level 9, only parsing).

Notation "'cont' '[' Σ ',' T ']' e '=>' φ" := (FExprContIn Σ T e (fun _ => φ))
  (in custom form at level 90,
   Σ constr at level 9, T constr at level 9, e constr at level 9,
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
    Variable X : aset.
    Variable q : type_qualifier.

    Example obligation_notation :
      <{ obl[Σe] e : τ }> =
      FDenotObligationIn Σe τ e := eq_refl.

    Example closed_notation :
      <{ closed Σe }> = FClosedResourceIn Σe := eq_refl.

    Example result_on_symbol_notation :
      <{ e ⇓[D] }> = FExprResultOn D e := eq_refl.

    Example result_lvar_notation :
      (result-lvar D e at (LVBound 0))%formula =
      FExprResultAtLvar D e (LVBound 0) := eq_refl.

    Example result_at_notation :
      <{ result X e at x }> = FExprResultAt X e x := eq_refl.

    Example cont_notation :
      <{ cont[Σe, TBase b] e => fib D |> over tyq q }> =
      FExprContIn Σe (TBase b) e
        (fun _ => FFibVars D (FOver (FTypeQualifier q))) := eq_refl.

    Example formula_scope_denot_notation :
      (∀. denot[Σe] e ⋮ τ → e ⇓[D])%formula =
      FForall (FImpl (denot_ty_lvar Σe τ e) (FExprResultOn D e)) :=
      eq_refl.
  End Smoke.
End DenotationNotationSmoke.
