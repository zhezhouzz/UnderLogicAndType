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

(** ** Context substitution *)

Fixpoint ctx_subst_one (x : atom) (v : value) (Γ : ctx) : ctx :=
  match Γ with
  | CtxEmpty => CtxEmpty
  | CtxBind y τ => CtxBind y ({x := v} τ)
  | CtxComma Γ1 Γ2 => CtxComma (ctx_subst_one x v Γ1) (ctx_subst_one x v Γ2)
  | CtxStar Γ1 Γ2 => CtxStar (ctx_subst_one x v Γ1) (ctx_subst_one x v Γ2)
  | CtxSum Γ1 Γ2 => CtxSum (ctx_subst_one x v Γ1) (ctx_subst_one x v Γ2)
  end.

Fixpoint ctx_subst_map (σ : Store) (Γ : ctx) : ctx :=
  match Γ with
  | CtxEmpty => CtxEmpty
  | CtxBind y τ => CtxBind y (subst_map σ τ)
  | CtxComma Γ1 Γ2 => CtxComma (ctx_subst_map σ Γ1) (ctx_subst_map σ Γ2)
  | CtxStar Γ1 Γ2 => CtxStar (ctx_subst_map σ Γ1) (ctx_subst_map σ Γ2)
  | CtxSum Γ1 Γ2 => CtxSum (ctx_subst_map σ Γ1) (ctx_subst_map σ Γ2)
  end.

#[global] Instance subst_ctx_inst : SubstV value ctx := ctx_subst_one.
#[global] Instance substM_ctx_inst : SubstM Store ctx := ctx_subst_map.
Arguments subst_ctx_inst /.
Arguments substM_ctx_inst /.

Lemma ctx_dom_subst_one x v Γ :
  ctx_dom ({x := v} Γ) = ctx_dom Γ.
Proof. induction Γ; simpl; try set_solver. Qed.

Lemma ctx_dom_subst_map σ Γ :
  ctx_dom (subst_map σ Γ) = ctx_dom Γ.
Proof. induction Γ; simpl; try set_solver. Qed.

Lemma ctx_subst_fresh x v Γ :
  x # Γ → {x := v} Γ = Γ.
Proof.
  intros Hfresh. induction Γ; simpl in *; try reflexivity.
  - change (CtxBind x0 ({x := v} τ) = CtxBind x0 τ).
    f_equal. apply cty_subst_fresh. set_solver.
  - change (CtxComma ({x := v} Γ1) ({x := v} Γ2) = CtxComma Γ1 Γ2).
    f_equal; [apply IHΓ1 | apply IHΓ2]; set_solver.
  - change (CtxStar ({x := v} Γ1) ({x := v} Γ2) = CtxStar Γ1 Γ2).
    f_equal; [apply IHΓ1 | apply IHΓ2]; set_solver.
  - change (CtxSum ({x := v} Γ1) ({x := v} Γ2) = CtxSum Γ1 Γ2).
    f_equal; [apply IHΓ1 | apply IHΓ2]; set_solver.
Qed.

Lemma ctx_fv_subst_subset x v Γ :
  stale ({x := v} Γ) ⊆ stale Γ ∪ stale v.
Proof.
  induction Γ; simpl; try set_solver.
  change ({[x0]} ∪ stale ({x := v} τ) ⊆
    ({[x0]} ∪ stale τ) ∪ stale v).
  pose proof (cty_fv_of_subst x v τ). set_solver.
Qed.

Lemma ctx_fv_subst_closed_subset x v Γ :
  stale v = ∅ →
  stale ({x := v} Γ) ⊆ stale Γ.
Proof.
  intros Hclosed. induction Γ; simpl; try set_solver.
  change ({[x0]} ∪ stale ({x := v} τ) ⊆ {[x0]} ∪ stale τ).
  pose proof (cty_fv_of_subst_closed x v τ Hclosed). set_solver.
Qed.
