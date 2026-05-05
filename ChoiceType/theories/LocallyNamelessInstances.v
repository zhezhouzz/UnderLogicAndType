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

#[global] Instance SubstFresh_cty : SubstFresh choice_ty.
Proof.
  intros τ x v Hfresh. exact (cty_subst_fresh x v τ Hfresh).
Qed.

#[global] Instance FvOfSubst_cty : FvOfSubst choice_ty.
Proof.
  intros x v τ. exact (cty_fv_of_subst x v τ).
Qed.

#[global] Instance FvOfSubstClosed_cty : FvOfSubstClosed choice_ty.
Proof.
  intros x v τ Hclosed. exact (cty_fv_of_subst_closed x v τ Hclosed).
Qed.

#[global] Instance SubstFresh_ctx : SubstFresh ctx.
Proof. intros Γ x v Hfresh. exact (ctx_subst_fresh x v Γ Hfresh). Qed.
