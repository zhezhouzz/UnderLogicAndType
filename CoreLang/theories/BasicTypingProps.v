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

(** ** Structural typing lemmas *)

Lemma basic_typing_weaken_value Γ Γ' v T :
  Γ ⊢ᵥ v ⋮ T → Γ ⊆ Γ' → Γ' ⊢ᵥ v ⋮ T.
Proof. apply weakening_value. Qed.

Lemma basic_typing_weaken_tm Γ Γ' e T :
  Γ ⊢ₑ e ⋮ T → Γ ⊆ Γ' → Γ' ⊢ₑ e ⋮ T.
Proof. apply weakening_tm. Qed.

Lemma basic_typing_weaken_insert_value Γ v T x U :
  x ∉ dom Γ →
  Γ ⊢ᵥ v ⋮ T →
  <[x := U]> Γ ⊢ᵥ v ⋮ T.
Proof.
  intros Hfresh Hty. eapply basic_typing_weaken_value; eauto.
  apply insert_subseteq. by apply not_elem_of_dom.
Qed.

Lemma basic_typing_weaken_insert_tm Γ e T x U :
  x ∉ dom Γ →
  Γ ⊢ₑ e ⋮ T →
  <[x := U]> Γ ⊢ₑ e ⋮ T.
Proof.
  intros Hfresh Hty. eapply basic_typing_weaken_tm; eauto.
  apply insert_subseteq. by apply not_elem_of_dom.
Qed.

Lemma basic_typing_subst_value Γ x s v T vx :
  Γ ⊢ᵥ v ⋮ T →
  ∅ ⊢ᵥ vx ⋮ s →
  Γ !! x = Some s →
  delete x Γ ⊢ᵥ ({x := vx} v) ⋮ T.
Proof. apply subst_typing_value. Qed.

Lemma basic_typing_subst_tm Γ x s e T vx :
  Γ ⊢ₑ e ⋮ T →
  ∅ ⊢ᵥ vx ⋮ s →
  Γ !! x = Some s →
  delete x Γ ⊢ₑ ({x := vx} e) ⋮ T.
Proof. apply subst_typing_tm. Qed.

Lemma basic_typing_unique_value Γ v T1 T2 :
  Γ ⊢ᵥ v ⋮ T1 → Γ ⊢ᵥ v ⋮ T2 → T1 = T2.
Proof. Admitted.

Lemma basic_typing_unique_tm Γ e T1 T2 :
  Γ ⊢ₑ e ⋮ T1 → Γ ⊢ₑ e ⋮ T2 → T1 = T2.
Proof. Admitted.

Lemma basic_typing_strengthen_value Γ x Tx v T :
  <[x := Tx]> Γ ⊢ᵥ v ⋮ T →
  x ∉ fv_value v →
  Γ ⊢ᵥ v ⋮ T.
Proof. Admitted.

Lemma basic_typing_strengthen_tm Γ x Tx e T :
  <[x := Tx]> Γ ⊢ₑ e ⋮ T →
  x ∉ fv_tm e →
  Γ ⊢ₑ e ⋮ T.
Proof. Admitted.
