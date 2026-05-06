(** * ChoiceType.LocallyNamelessInstances

    Locally-nameless theorem-class instances for choice types. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Import Syntax QualifierInstances LocallyNamelessProps.

#[global] Instance OpenFv_cty : OpenFv atom choice_ty.
Proof.
  intros τ. induction τ; intros x k; simpl; try set_solver.
  - pose proof (open_fv φ x (S k)). simpl in H. set_solver.
  - pose proof (open_fv φ x (S k)). simpl in H. set_solver.
Qed.

#[global] Instance OpenFvPrime_cty : OpenFvPrime atom choice_ty.
Proof.
  intros τ. induction τ; intros x k; simpl; try set_solver.
  - pose proof (open_fv' φ x (S k)). simpl in H. set_solver.
  - pose proof (open_fv' φ x (S k)). simpl in H. set_solver.
Qed.
