(** * ContextLogic.FormulaTactics *)

From ContextLogic Require Import Formula.
From Stdlib Require Import Lia.

Ltac models_fuel_finish :=
  rewrite ?formula_open_preserves_measure;
  rewrite ?formula_mlsubst_preserves_measure;
  rewrite ?formula_msubst_store_preserves_measure;
  simpl; lia.

Tactic Notation "models_fuel_irrel" constr(H) :=
  eapply res_models_fuel_irrel; [| | exact H]; models_fuel_finish.

Ltac models_fuel_irrel_auto :=
  eapply res_models_fuel_irrel; [| | eassumption]; models_fuel_finish.

Ltac formula_open_syntax_norm :=
  rewrite ?formula_open_true, ?formula_open_false, ?formula_open_atom;
  rewrite ?formula_open_and, ?formula_open_or, ?formula_open_impl;
  rewrite ?formula_open_star, ?formula_open_wand, ?formula_open_plus;
  rewrite ?formula_open_forall;
  rewrite ?formula_open_over, ?formula_open_under, ?formula_open_fibvars.

Ltac formula_scope_syntax_norm :=
  rewrite ?formula_scoped_true_iff, ?formula_scoped_false_iff;
  rewrite ?formula_scoped_atom_iff;
  rewrite ?formula_scoped_and_iff, ?formula_scoped_or_iff;
  rewrite ?formula_scoped_impl_iff;
  rewrite ?formula_scoped_star_iff, ?formula_scoped_wand_iff;
  rewrite ?formula_scoped_plus_iff;
  rewrite ?formula_scoped_forall_iff;
  rewrite ?formula_scoped_over_iff, ?formula_scoped_under_iff;
  rewrite ?formula_scoped_fibvars_iff.

Ltac formula_syntax_norm :=
  formula_open_syntax_norm;
  formula_scope_syntax_norm.
