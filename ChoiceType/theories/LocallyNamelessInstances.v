(** * ChoiceType.LocallyNamelessInstances

    Locally-nameless theorem-class instances for choice types. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Import Syntax QualifierInstances QualifierProps.

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

#[global] Instance SubstFresh_cty : SubstFresh choice_ty.
Proof.
  intros τ x v Hfresh. induction τ; autounfold with class_simpl in *; simpl in *.
  - f_equal. exact (qual_subst_fresh x v φ ltac:(set_solver)).
  - f_equal. exact (qual_subst_fresh x v φ ltac:(set_solver)).
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
  - f_equal; [apply IHτ1 | apply IHτ2]; set_solver.
Qed.

#[global] Instance FvOfSubst_cty : FvOfSubst choice_ty.
Proof.
  intros x v τ. induction τ; simpl; try set_solver.
  - pose proof (fv_of_subst x v φ). simpl in H. set_solver.
  - pose proof (fv_of_subst x v φ). simpl in H. set_solver.
Qed.

#[global] Instance FvOfSubstClosed_cty : FvOfSubstClosed choice_ty.
Proof.
  intros x v τ Hclosed. induction τ; simpl; try set_solver.
  - pose proof (fv_of_subst_closed x v φ Hclosed). simpl in H. set_solver.
  - pose proof (fv_of_subst_closed x v φ Hclosed). simpl in H. set_solver.
Qed.
