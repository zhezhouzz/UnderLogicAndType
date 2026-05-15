(** * ChoiceType.DenotationFibers

    Fiber modality helpers for ChoiceType denotations. *)

From LocallyNameless Require Import Tactics.
From ChoiceType Require Export Syntax.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

Definition FFibVars_obligation
    (X : aset) (p : FQ) (ρ : Store) (m : WfWorld) : Prop :=
  dom ρ ## X ∧
  ∀ σ (Hproj : res_restrict m X σ),
    res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m X σ Hproj) p.

Lemma FFibVars_formula_fv_subset D (p : FQ) :
  formula_fv (FFibVars D p) ⊆ lvars_fv D ∪ formula_fv p.
Proof.
  simpl. set_solver.
Qed.

Lemma FFibVars_formula_fv D (p : FQ) :
  formula_fv (FFibVars D p) = lvars_fv D ∪ formula_fv p.
Proof.
  simpl. reflexivity.
Qed.

Lemma FFibVars_models_elim D (p : FQ) ρ m :
  res_models_with_store ρ m (FFibVars D p) →
  FFibVars_obligation (lvars_fv D) p ρ m.
Proof.
  unfold FFibVars_obligation.
  unfold res_models_with_store. simpl.
  intros Hm. destruct Hm as [_ [Hdisj Hfib]].
  split; [exact Hdisj |].
  intros σ Hproj. models_fuel_irrel (Hfib σ Hproj).
Qed.

Lemma FFibVars_models_intro D (p : FQ) ρ m :
  formula_scoped_in_world ρ m (FFibVars D p) →
  FFibVars_obligation (lvars_fv D) p ρ m →
  res_models_with_store ρ m (FFibVars D p).
Proof.
  unfold FFibVars_obligation.
  intros Hscope [Hdisj Hfib].
  unfold res_models_with_store. simpl.
  split; [exact Hscope |].
  split; [exact Hdisj |].
  intros σ Hproj.
  specialize (Hfib σ Hproj).
  models_fuel_irrel Hfib.
Qed.
