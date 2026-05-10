(** * ChoiceLogic.FormulaTactics

    Small proof automation for formula satisfaction.  Keep these tactics close
    to [Formula] so downstream denotation and typing proofs can reuse them
    without rebuilding fuel/measure bookkeeping. *)

From ChoiceLogic Require Import Formula.
From Stdlib Require Import Lia.

Ltac models_fuel_finish :=
  rewrite ?formula_rename_preserves_measure; simpl; lia.

Tactic Notation "models_fuel_irrel" constr(H) :=
  eapply res_models_with_store_fuel_irrel; [| | exact H]; models_fuel_finish.

Ltac models_fuel_irrel_auto :=
  eapply res_models_with_store_fuel_irrel; [| | eassumption]; models_fuel_finish.
