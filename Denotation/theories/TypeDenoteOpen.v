(** * Denotation.TypeDenoteOpen *)

From Denotation Require Import Notation.
From Denotation Require Import TypeDenoteTactics.
From Denotation Require Export TypeDenote.

Section TypeDenote.

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
  { denot_open_set. }
  pose proof (formula_open_env_ty_denote_gas
    (<[k := y]> ∅) gas Σ τ e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  exact Heq.
Qed.

End TypeDenote.
