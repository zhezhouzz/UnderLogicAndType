(** * CoreLang.OperationalResults

    Pure operational comparisons between open expressions.

    These relations live outside Choice Logic and Choice Type.  Logic
    entailment follows the Kripke/domain-restriction order on worlds; it is not
    a same-domain subset relation on result sets.  For open terms, the result
    set is a relation from an input store domain [X] to possible results, so
    operational comparison must name [X] explicitly. *)

From CoreLang Require Import Instantiation InstantiationProps SmallStep OperationalProps.

Definition expr_result_incl_on (X : aset) (e_to e_from : tm) : Prop :=
  fv_tm e_to ∪ fv_tm e_from ⊆ X ∧
  ∀ σ v,
    dom σ = X →
    closed_env σ →
    subst_map σ e_to →* tret v →
    subst_map σ e_from →* tret v.

Definition expr_result_equiv_on (X : aset) (e1 e2 : tm) : Prop :=
  expr_result_incl_on X e1 e2 ∧ expr_result_incl_on X e2 e1.

Lemma expr_result_incl_on_refl X e :
  fv_tm e ⊆ X →
  expr_result_incl_on X e e.
Proof.
  intros Hfv. split; [set_solver |].
  intros σ v _ _ Hsteps. exact Hsteps.
Qed.

Lemma expr_result_incl_on_trans X e3 e2 e1 :
  expr_result_incl_on X e3 e2 →
  expr_result_incl_on X e2 e1 →
  expr_result_incl_on X e3 e1.
Proof.
  intros [Hfv32 H32] [Hfv21 H21]. split; [set_solver |].
  intros σ v Hdom Hclosed Hsteps.
  pose proof (H32 σ v Hdom Hclosed Hsteps) as Hsteps2.
  exact (H21 σ v Hdom Hclosed Hsteps2).
Qed.

Lemma expr_result_equiv_on_refl X e :
  fv_tm e ⊆ X →
  expr_result_equiv_on X e e.
Proof.
  intros Hfv. split; apply expr_result_incl_on_refl; exact Hfv.
Qed.

Lemma expr_result_equiv_on_sym X e1 e2 :
  expr_result_equiv_on X e1 e2 →
  expr_result_equiv_on X e2 e1.
Proof. intros [H12 H21]. split; assumption. Qed.

Lemma expr_result_equiv_on_trans X e3 e2 e1 :
  expr_result_equiv_on X e3 e2 →
  expr_result_equiv_on X e2 e1 →
  expr_result_equiv_on X e3 e1.
Proof.
  intros [H32 H23] [H21 H12]. split.
  - eapply expr_result_incl_on_trans; eauto.
  - eapply expr_result_incl_on_trans; eauto.
Qed.
