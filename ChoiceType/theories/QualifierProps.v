(** * ChoiceType.QualifierProps

    Lemmas about shallow type qualifiers.  The definitions live in
    [Qualifier.v]; proof-oriented facts are kept here so the core syntax layer
    stays light. *)

From ChoiceType Require Export Qualifier.

(** ** Key substitution and interpretation lemmas *)

Lemma qual_subst_fresh x v (q : type_qualifier) :
  x # q → {x := v}q q = q.
Proof.
  destruct q as [B d p]. unfold stale, subst_one, qual_subst_value. simpl.
  intros Hfresh. rewrite decide_False by exact Hfresh. reflexivity.
Qed.

Lemma qual_interp_subst_compose (σ_X σ : gmap atom value) (q : type_qualifier) :
  store_compat σ_X σ →
  qual_interp σ (qual_subst_map σ_X q) ↔ qual_interp (σ_X ∪ σ) q.
Proof. Admitted.

Lemma qual_interp_and q1 q2 σ :
  qual_interp σ (q1 &q q2) ↔ qual_interp σ q1 ∧ qual_interp σ q2.
Proof. Admitted.
