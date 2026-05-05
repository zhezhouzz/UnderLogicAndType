(** * ChoiceType.LocallyNamelessProps

    Structural locally-nameless facts for choice types and tree-shaped
    contexts.  This file deliberately focuses on syntactic/fv/substitution
    facts; paper-level typing and well-formedness remain in [ChoiceTyping]. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Export Syntax QualifierProps.
From ChoiceType Require Import QualifierInstances.

(** ** Choice-type substitution *)

Lemma cty_subst_fresh x v (τ : choice_ty) :
  x # τ → {x := v} τ = τ.
Proof.
  intros Hfresh. induction τ; autounfold with class_simpl in *; simpl in *.
  - f_equal. exact (qual_subst_fresh x v φ ltac:(set_solver)).
  - f_equal. exact (qual_subst_fresh x v φ ltac:(set_solver)).
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
Qed.

Lemma cty_fv_of_subst x v (τ : choice_ty) :
  stale ({x := v} τ) ⊆ (stale τ ∖ {[x]}) ∪ stale v.
Proof.
  induction τ; simpl; try set_solver.
  - pose proof (fv_of_subst x v φ). simpl in H. set_solver.
  - pose proof (fv_of_subst x v φ). simpl in H. set_solver.
Qed.

Lemma cty_fv_of_subst_closed x v (τ : choice_ty) :
  stale v = ∅ →
  stale ({x := v} τ) = stale τ ∖ {[x]}.
Proof.
  intros Hclosed. induction τ; simpl; try set_solver.
  - pose proof (fv_of_subst_closed x v φ Hclosed). simpl in H. set_solver.
  - pose proof (fv_of_subst_closed x v φ Hclosed). simpl in H. set_solver.
Qed.
