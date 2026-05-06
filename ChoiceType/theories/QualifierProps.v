(** * ChoiceType.QualifierProps

    Lemmas about shallow type qualifiers.  The definitions live in
    [Qualifier.v]; proof-oriented facts are kept here so the core syntax layer
    stays light. *)

From ChoiceType Require Export Qualifier.

(** ** Key interpretation lemmas *)

Lemma qual_interp_and q1 q2 σ :
  qual_interp σ (q1 &q q2) ↔ qual_interp σ q1 ∧ qual_interp σ q2.
Proof.
  destruct q1 as [B1 d1 p1], q2 as [B2 d2 p2].
  unfold qual_interp, qual_interp_full, qual_and. simpl.
  rewrite !store_restrict_restrict, !map_filter_empty.
  replace ((d1 ∪ d2) ∩ d1) with d1 by set_solver.
  replace ((d1 ∪ d2) ∩ d2) with d2 by set_solver.
  tauto.
Qed.
