From CoreLang Require Import BasicTyping LocallyNamelessProps.

(** * Basic typing facts for CoreLang

    These mirror the basic typing facts in HATs/UnderType, specialized to the
    direct-style CoreLang syntax. *)

Lemma basic_typing_contains_fv_value Γ v T :
  Γ ⊢ᵥ v ⋮ T → fv_value v ⊆ dom Γ
with basic_typing_contains_fv_tm Γ e T :
  Γ ⊢ₑ e ⋮ T → fv_tm e ⊆ dom Γ.
Proof. Admitted.

Lemma basic_typing_closed_value v T :
  ∅ ⊢ᵥ v ⋮ T → fv_value v = ∅.
Proof.
  intros Hty. apply basic_typing_contains_fv_value in Hty. set_solver.
Qed.

Lemma basic_typing_closed_tm e T :
  ∅ ⊢ₑ e ⋮ T → fv_tm e = ∅.
Proof.
  intros Hty. apply basic_typing_contains_fv_tm in Hty. set_solver.
Qed.

Lemma basic_typing_regular_value Γ v T :
  Γ ⊢ᵥ v ⋮ T → lc_value v.
Proof. apply typing_value_lc. Qed.

Lemma basic_typing_regular_tm Γ e T :
  Γ ⊢ₑ e ⋮ T → lc_tm e.
Proof. apply typing_tm_lc. Qed.

Lemma basic_typing_base_canonical_form v b :
  ∅ ⊢ᵥ v ⋮ TBase b →
  ∃ c, v = vconst c ∧ base_ty_of_const c = b.
Proof.
  intros Hty. inversion Hty; subst; eauto.
  all: try match goal with
  | Hlookup : ∅ !! _ = Some _ |- _ =>
      rewrite lookup_empty in Hlookup; discriminate
  end.
Qed.

Lemma basic_typing_bool_canonical_form v :
  ∅ ⊢ᵥ v ⋮ TBase TBool →
  v = vconst (cbool true) ∨ v = vconst (cbool false).
Proof.
  intros Hty.
  destruct (basic_typing_base_canonical_form v TBool Hty) as [[b|n] [-> Hbase]]; simpl in Hbase.
  - destruct b; auto.
  - discriminate.
Qed.

Lemma basic_typing_nat_canonical_form v :
  ∅ ⊢ᵥ v ⋮ TBase TNat →
  ∃ n, v = vconst (cnat n).
Proof.
  intros Hty.
  destruct (basic_typing_base_canonical_form v TNat Hty) as [[b|n] [-> Hbase]]; simpl in Hbase.
  - discriminate.
  - eauto.
Qed.

Lemma basic_typing_arrow_canonical_form v s T :
  ∅ ⊢ᵥ v ⋮ (s →ₜ T) →
  (∃ s' e, v = vlam s' e) ∨ (∃ Tf vf, v = vfix Tf vf).
Proof.
  intros Hty. inversion Hty; subst; eauto.
  all: try match goal with
  | Hlookup : ∅ !! _ = Some _ |- _ =>
      rewrite lookup_empty in Hlookup; discriminate
  end.
Qed.
