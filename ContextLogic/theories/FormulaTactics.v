(** * ContextLogic.FormulaTactics *)

From ContextLogic Require Import FormulaSemantics.
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

Ltac formula_scope_step :=
  match goal with
  | Hscope : formula_scoped_in_world ?m (FAnd ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_and_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FAnd ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_and_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FOr ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_or_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FOr ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_or_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_impl_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_impl_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FStar ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_star_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FStar ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_star_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FWand ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_wand_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FWand ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_wand_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FPlus ?p ?q)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_plus_l; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FPlus ?p ?q)
    |- formula_scoped_in_world ?m ?q =>
      eapply formula_scoped_plus_r; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FForall ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_forall_body; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FOver ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_over_body; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FUnder ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_under_body; exact Hscope
  | Hscope : formula_scoped_in_world ?m (FFibVars ?D ?p)
    |- formula_scoped_in_world ?m ?p =>
      eapply formula_scoped_fibvars_r; exact Hscope
  end.

Ltac formula_scope_solve :=
  solve [eassumption | formula_scope_step | formula_scope_syntax_norm; tauto].
