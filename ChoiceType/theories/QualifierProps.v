(** * ChoiceType.QualifierProps

    Lemmas about shallow type qualifiers.  The definitions live in
    [Qualifier.v]; proof-oriented facts are kept here so the core syntax layer
    stays light. *)

From ChoiceType Require Export Qualifier.
From LocallyNameless Require Import Classes.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** ** Swap lemmas *)

Lemma qual_bvars_swap x y q :
  qual_bvars (qual_swap_atom x y q) = qual_bvars q.
Proof. destruct q; simpl. apply lvars_bv_swap. Qed.

Lemma qual_dom_swap x y q :
  qual_dom (qual_swap_atom x y q) = aset_swap x y (qual_dom q).
Proof. destruct q; simpl. apply lvars_fv_swap. Qed.

Lemma qual_swap_atom_involutive x y q :
  qual_swap_atom x y (qual_swap_atom x y q) = q.
Proof.
  destruct q as [D p]. unfold qual_swap_atom. simpl.
  f_equal.
  - apply lvars_swap_involutive.
  - apply functional_extensionality. intros β.
    apply functional_extensionality. intros σ.
    apply functional_extensionality. intros a.
    apply propositional_extensionality.
    rewrite !store_swap_involutive. reflexivity.
Qed.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [D p]. unfold qual_open_atom, qual_dom, qual_bvars.
  destruct decide; simpl.
  - pose proof (lvars_fv_open_subset k x D). set_solver.
  - set_solver.
Qed.

Lemma qual_open_atom_swap_fresh k x y q :
  k ∈ qual_bvars q →
  x ∉ qual_dom q →
  y ∉ qual_dom q →
  qual_swap_atom x y (qual_open_atom k x q) = qual_open_atom k y q.
Proof.
Admitted.

Lemma qual_open_atom_swap k x y z q :
  qual_open_atom k z (qual_swap_atom x y q) =
  qual_swap_atom x y (qual_open_atom k (atom_swap x y z) q).
Proof.
Admitted.

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
Admitted.

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
Admitted.

Lemma qual_interp_open_eq_const x c σ :
  qual_interp σ (qual_open_atom 0 x (mk_q_eq (vbvar 0) (vconst c))) ↔
  σ !! x = Some (vconst c).
Proof.
Admitted.

(** ** Shared locally-nameless class instances

    Keep these next to the qualifier lemmas they wrap.  A separate tiny
    instances file forces downstream files to reload this whole layer just to
    register typeclasses. *)

#[global] Instance OpenFv_qualifier : OpenFv atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenFvPrime_qualifier : OpenFvPrime atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenRecLc_qualifier : OpenRecLc atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenLcRespect_qualifier : OpenLcRespect atom type_qualifier.
Proof.
Admitted.

#[global] Instance OpenIdemp_qualifier : OpenIdemp atom type_qualifier.
Proof.
Admitted.
