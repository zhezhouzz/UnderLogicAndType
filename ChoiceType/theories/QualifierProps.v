(** * ChoiceType.QualifierProps

    Lemmas about shallow type qualifiers.  The definitions live in
    [Qualifier.v]; proof-oriented facts are kept here so the core syntax layer
    stays light. *)

From ChoiceType Require Export Qualifier.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** ** Swap lemmas *)

Lemma qual_bvars_swap x y q :
  qual_bvars (qual_swap_atom x y q) = qual_bvars q.
Proof. destruct q; reflexivity. Qed.

Lemma qual_dom_swap x y q :
  qual_dom (qual_swap_atom x y q) = aset_swap x y (qual_dom q).
Proof. destruct q; reflexivity. Qed.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [B d p]. unfold qual_open_atom, qual_dom.
  destruct decide; simpl; set_solver.
Qed.

Lemma qual_open_atom_swap_fresh k x y q :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  qual_swap_atom x y (qual_open_atom k x q) = qual_open_atom k y q.
Proof.
  destruct q as [B d p]. simpl. intros Hk Hx Hy.
  unfold qual_open_atom, qual_swap_atom, qual_bvars, qual_dom in *; simpl in *.
  rewrite !decide_True by exact Hk.
  f_equal.
  - rewrite aset_swap_union, aset_swap_singleton.
    unfold atom_swap at 1.
    destruct (decide (x = x)) as [_|Hxx]; [|congruence].
    destruct (decide (x = y)) as [->|Hxy].
    + rewrite aset_swap_fresh by assumption. set_solver.
    + rewrite aset_swap_fresh by assumption. reflexivity.
  - apply functional_extensionality. intros β.
    apply functional_extensionality. intros σ.
    apply functional_extensionality. intros a.
    apply propositional_extensionality.
    rewrite map_restrict_store_swap_fresh by assumption.
    rewrite map_restrict_store_swap_fresh by assumption.
    rewrite store_swap_lookup_inv.
    replace (atom_swap x y x) with y.
    2:{ unfold atom_swap.
        destruct (decide (x = x)) as [_|Hxx]; [reflexivity | congruence]. }
    reflexivity.
Qed.

Lemma qual_lc_swap x y q :
  lc_qualifier q →
  lc_qualifier (qual_swap_atom x y q).
Proof.
  unfold lc_qualifier. rewrite qual_bvars_swap. exact id.
Qed.

Lemma qual_interp_full_swap x y q β σ ρ :
  qual_interp_full β σ ρ (qual_swap_atom x y q) ↔
  qual_interp_full β (store_swap x y σ) (store_swap x y ρ) q.
Proof.
  destruct q as [B d p].
  unfold qual_interp_full, qual_swap_atom. simpl.
  replace (store_swap x y (store_restrict σ (aset_swap x y d)))
    with (store_restrict (store_swap x y σ) d).
  2:{
    rewrite <- (store_restrict_swap x y σ (aset_swap x y d)).
    rewrite aset_swap_involutive. reflexivity.
  }
  replace (store_swap x y (store_restrict ρ (aset_swap x y d)))
    with (store_restrict (store_swap x y ρ) d).
  2:{
    rewrite <- (store_restrict_swap x y ρ (aset_swap x y d)).
    rewrite aset_swap_involutive. reflexivity.
  }
  reflexivity.
Qed.

Lemma qual_interp_swap x y q σ :
  qual_interp σ (qual_swap_atom x y q) ↔
  qual_interp (store_swap x y σ) q.
Proof.
  unfold qual_interp.
  rewrite qual_interp_full_swap.
  reflexivity.
Qed.

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

Lemma qual_interp_open_eq_const x c σ :
  qual_interp σ (qual_open_atom 0 x (mk_q_eq (vbvar 0) (vconst c))) ↔
  σ !! x = Some (vconst c).
Proof.
  unfold qual_interp, qual_interp_full, qual_open_atom, mk_q_eq.
  simpl.
  rewrite decide_True by set_solver.
  rewrite !map_filter_empty.
  split.
  - intros [v [Hlook Heq]].
    apply store_restrict_lookup_some in Hlook as [_ Hlook].
    simpl in Heq. rewrite lookup_insert in Heq.
    inversion Heq. subst v. exact Hlook.
  - intros Hlook.
    exists (vconst c). split.
    + apply store_restrict_lookup_some_2; [exact Hlook | set_solver].
    + reflexivity.
Qed.
