(** * ChoiceType.LocallyNamelessProps

    Structural locally-nameless facts for choice types and tree-shaped
    contexts.  This file deliberately focuses on atom-open syntactic facts;
    paper-level typing and well-formedness remain in [ChoiceTyping].

    Choice types intentionally do not provide variable-to-value substitution:
    type qualifiers open locally-nameless binders to atoms, and future
    transport lemmas should use atom rename/swap rather than value
    substitution. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Export Syntax QualifierProps.
From ChoiceType Require Import QualifierInstances.

(** ** Atom swap facts *)

Lemma cty_fv_swap x y τ :
  fv_cty (cty_swap_atom x y τ) = aset_swap x y (fv_cty τ).
Proof.
  induction τ; simpl; try rewrite ?qual_dom_swap;
    try rewrite ?IHτ1, ?IHτ2, <- ?aset_swap_union; reflexivity.
Qed.

Lemma cty_open_fv_subset k x τ :
  fv_cty ({k ~> x} τ) ⊆ fv_cty τ ∪ {[x]}.
Proof.
  induction τ in k |- *; simpl; try set_solver.
  - pose proof (qual_open_atom_dom_subset (S k) x φ). set_solver.
  - pose proof (qual_open_atom_dom_subset (S k) x φ). set_solver.
Qed.

Lemma ctx_fv_swap x y Γ :
  ctx_fv (ctx_swap_atom x y Γ) = aset_swap x y (ctx_fv Γ).
Proof.
  induction Γ; simpl.
  - symmetry. apply aset_swap_empty.
  - rewrite cty_fv_swap.
    rewrite <- aset_swap_singleton, <- aset_swap_union.
    reflexivity.
  - rewrite IHΓ1, IHΓ2, <- aset_swap_union. reflexivity.
  - rewrite IHΓ1, IHΓ2, <- aset_swap_union. reflexivity.
  - rewrite IHΓ1, IHΓ2, <- aset_swap_union. reflexivity.
Qed.

Lemma ctx_dom_swap x y Γ :
  ctx_dom (ctx_swap_atom x y Γ) = aset_swap x y (ctx_dom Γ).
Proof.
  induction Γ; simpl.
  - symmetry. apply aset_swap_empty.
  - rewrite <- aset_swap_singleton. reflexivity.
  - rewrite IHΓ1, IHΓ2, <- aset_swap_union. reflexivity.
  - rewrite IHΓ1, IHΓ2, <- aset_swap_union. reflexivity.
  - rewrite IHΓ1, IHΓ2, <- aset_swap_union. reflexivity.
Qed.

Lemma cty_swap_preserves_erasure x y τ :
  erase_ty (cty_swap_atom x y τ) = erase_ty τ.
Proof.
  induction τ; simpl; congruence.
Qed.
