(** * ChoiceTyping.TLetExprCont

    Thin expression-continuation interface for the [tlet] soundness case.

    The previous implementation in this file targeted the old untyped
    [FExprContIn Σ e Q] API.  The refactored type-denotation layer uses
    [FExprContIn Σ T e Q], so keep only the review-facing statements needed by
    the current fundamental skeleton. *)

From CoreLang Require Import Instantiation BasicTypingProps.
From ChoiceTyping Require Export TLetTotal.
From ChoiceTyping Require Import ResultWorldExtension.
From ChoiceType Require Import BasicStore DenotationNotation.

Import Tactics.

Lemma expr_total_on_tlete_elim_body_ext
    X e1 e2 x (m mx : WfWorld) F :
  result_extends_on X e1 x m F mx ->
  X ⊆ world_dom (m : World) ->
  fv_tm (tlete e1 e2) ⊆ X ->
  x ∉ X ->
  x ∉ fv_tm e2 ->
  world_closed_on X m ->
  lc_tm (tlete e1 e2) ->
  expr_total_on (tlete e1 e2) m ->
  expr_total_on (e2 ^^ x) mx.
Proof.
  (* Operational tlet elimination under an abstract result extension. *)
Admitted.

Lemma FExprCont_tlet_reduction
    (Σ : gmap atom ty) (T1 T2 : ty)
    (m mx : WfWorld) Fx e1 e2 (x : atom) (Q : FormulaQ) :
  result_extends e1 x m Fx mx ->
  Σ ⊢ₑ e1 ⋮ T1 ->
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 ->
  x ∉ dom Σ ->
  world_dom (m : World) = dom Σ ->
  world_closed_on (dom Σ) m ->
  expr_total_on (tlete e1 e2) m ->
  formula_fv Q ⊆ dom Σ ->
  mx ⊨ FExprContIn (atom_env_to_lty_env (<[x := T1]> Σ)) T2
    (e2 ^^ x) (fun _ => Q) ->
  m ⊨ FExprContIn (atom_env_to_lty_env Σ) T2
    (tlete e1 e2) (fun _ => Q).
Proof.
  (* Typed expression-continuation transport for [tlet]. *)
Admitted.
