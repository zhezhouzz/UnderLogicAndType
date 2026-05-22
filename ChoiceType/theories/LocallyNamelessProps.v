(** * ChoiceType.LocallyNamelessProps

    Structural locally-nameless facts for choice types and tree-shaped
    contexts.  This file deliberately focuses on atom-open syntactic facts;
    paper-level typing and well-formedness remain in [ChoiceTyping].

    Choice types intentionally do not provide variable-to-value substitution:
    type qualifiers open locally-nameless binders to atoms. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Export Syntax QualifierProps.

Lemma cty_open_fv_subset k x τ :
  fv_cty ({k ~> x} τ) ⊆ fv_cty τ ∪ {[x]}.
Proof.
  induction τ in k |- *; simpl; try set_solver.
  - pose proof (qual_open_atom_dom_subset (S k) x φ). set_solver.
  - pose proof (qual_open_atom_dom_subset (S k) x φ). set_solver.
Qed.

Lemma ctx_stale_eq_fv_dom Γ :
  ctx_stale Γ = ctx_fv Γ ∪ ctx_dom Γ.
Proof.
  induction Γ; simpl.
  - set_solver.
  - set_solver.
  - apply set_eq. intros z.
    rewrite IHΓ1, IHΓ2.
    rewrite !elem_of_union, elem_of_difference.
    split.
    + intros [[Hzfv1 | Hzdom1] | [Hzfv2 | Hzdom2]].
      * left. left. exact Hzfv1.
      * right. left. exact Hzdom1.
      * destruct (decide (z ∈ ctx_dom Γ1)) as [Hzdom1 | Hznotdom1].
        -- right. left. exact Hzdom1.
        -- left. right. split; [exact Hzfv2 | exact Hznotdom1].
      * right. right. exact Hzdom2.
    + intros [[Hzfv1 | [Hzfv2 Hznotdom1]] | [Hzdom1 | Hzdom2]].
      * left. left. exact Hzfv1.
      * right. left. exact Hzfv2.
      * left. right. exact Hzdom1.
      * right. right. exact Hzdom2.
  - rewrite IHΓ1, IHΓ2. set_solver.
  - rewrite IHΓ1, IHΓ2. set_solver.
Qed.

Lemma cty_open_preserves_erasure k x τ :
  erase_ty ({k ~> x} τ) = erase_ty τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

Lemma cty_open_preserves_depth k x τ :
  cty_depth ({k ~> x} τ) = cty_depth τ.
Proof.
  induction τ in k |- *; simpl; try rewrite ?IHτ1, ?IHτ2; reflexivity.
Qed.

(** ** Shared locally-nameless class instances

    These instances wrap the lemmas above, so keeping them here avoids a tiny
    instance-only file that reloads this layer just to register typeclasses.

    MIGRATION NOTE(TypeLanguage): these are legacy class instances for the old
    LN opening API.  The new TypeLanguage layer keeps explicit fv/open/shift
    lemmas instead of blindly re-exporting every class instance from this file.
    In particular, old [OpenIdemp]-style facts should not be migrated under
    the new swap-based opening discipline. *)

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

Lemma open_rec_body_qualifier_S φ k x :
  body_qualifier φ →
  {S k ~> x} φ = φ.
Proof.
  intros [L Hbody].
  pose (y := fresh_for L).
  assert (Hy : y ∉ L) by (subst y; apply fresh_for_not_in).
  pose proof (Hbody y Hy) as Hlc.
  eapply (@fact1 atom type_qualifier _ _ x y φ (S k) 0); [lia |].
  apply open_rec_lc. exact Hlc.
Qed.

#[global] Instance Fact1_cty : Fact1 atom choice_ty.
Proof.
  intros x y τ i j Hij Hopen.
  induction τ in i, j, Hij, Hopen |- *;
    cbn [open_one open_cty_atom_inst cty_open] in *.
  - f_equal.
    inversion Hopen; subst.
    eapply (@fact1 atom type_qualifier _ _ x y φ (S i) (S j));
      [lia | assumption].
  - f_equal.
    inversion Hopen; subst.
    eapply (@fact1 atom type_qualifier _ _ x y φ (S i) (S j));
      [lia | assumption].
  - inversion Hopen; subst. f_equal; eauto.
  - inversion Hopen; subst. f_equal; eauto.
  - inversion Hopen; subst. f_equal; eauto.
  - inversion Hopen; subst. f_equal; eauto with lia.
  - inversion Hopen; subst. f_equal; eauto with lia.
Qed.

Lemma cty_open_lc_core τ :
  lc_choice_ty τ →
  ∀ k x, {k ~> x} τ = τ.
Proof.
  intros Hlc.
  induction Hlc; intros k x; cbn [open_one open_cty_atom_inst cty_open].
  - rewrite open_rec_body_qualifier_S by exact H. reflexivity.
  - rewrite open_rec_body_qualifier_S by exact H. reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
 - rewrite IHHlc.
   f_equal.
   pose (y := fresh_for L).
    assert (Hy : y ∉ L) by (subst y; apply fresh_for_not_in).
    specialize (H0 y Hy).
    eapply (@fact1 atom choice_ty _ _ x y τ (S k) 0); [lia |].
    apply H0.
 - rewrite IHHlc.
   f_equal.
   pose (y := fresh_for L).
    assert (Hy : y ∉ L) by (subst y; apply fresh_for_not_in).
    specialize (H0 y Hy).
    eapply (@fact1 atom choice_ty _ _ x y τ (S k) 0); [lia |].
    apply H0.
Qed.

#[global] Instance OpenRecLc_cty : OpenRecLc atom choice_ty.
Proof.
  intros τ Hlc k x. apply cty_open_lc_core. exact Hlc.
Qed.
