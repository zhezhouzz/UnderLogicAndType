(** * ChoiceType.QualifierProps

    Lemmas about shallow type qualifiers.  The definitions live in
    [Qualifier.v]; proof-oriented facts are kept here so the core syntax layer
    stays light. *)

From ChoiceType Require Export Qualifier.
From LocallyNameless Require Import Classes.

Lemma qual_open_atom_dom_subset k x q :
  qual_dom (qual_open_atom k x q) ⊆ qual_dom q ∪ {[x]}.
Proof.
  destruct q as [D p]. unfold qual_open_atom, qual_dom, qual_bvars.
  destruct decide; simpl.
  - pose proof (lvars_fv_open_subset k x D). set_solver.
  - set_solver.
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
