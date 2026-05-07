From ChoiceLogic Require Import Prelude.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).

Inductive logic_qualifier : Type :=
  | lqual (d : aset) (prop : StoreT → WfWorldT → Prop).

Definition lqual_dom (q : logic_qualifier) : aset :=
  match q with
  | lqual d _ => d
  end.

Definition lqual_prop (q : logic_qualifier) : StoreT → WfWorldT → Prop :=
  match q with
  | lqual _ p => p
  end.

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (σ : StoreT)
    (w : WfWorldT) : Prop :=
  match q with
  | lqual d p => p (store_restrict σ d) (res_restrict w d)
  end.

Definition lqual_rename_atom (x y : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual d p =>
      lqual (aset_rename x y d)
        (λ σ w, p (store_rename_atom y x σ) (res_rename_atom y x w))
  end.

Definition lqual_swap (x y : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual d p =>
      lqual (aset_swap x y d)
        (λ σ w, p (store_swap x y σ) (res_swap x y w))
  end.

Lemma logic_qualifier_denote_rename_atom x y q σ w :
  logic_qualifier_denote (lqual_rename_atom x y q) σ w ↔
  logic_qualifier_denote q (store_rename_atom y x σ) (res_rename_atom y x w).
Proof.
  destruct q as [d p]. simpl.
  rewrite store_restrict_rename_atom.
  rewrite res_restrict_rename_atom.
  reflexivity.
Qed.

Lemma logic_qualifier_denote_swap x y q σ w :
  logic_qualifier_denote (lqual_swap x y q) σ w ↔
  logic_qualifier_denote q (store_swap x y σ) (res_swap x y w).
Proof.
  destruct q as [d p]. simpl.
  rewrite <- (store_restrict_swap x y σ (aset_swap x y d)).
  rewrite <- (res_restrict_swap x y w (aset_swap x y d)).
  rewrite !aset_swap_involutive.
  reflexivity.
Qed.

Lemma logic_qualifier_denote_restrict q σ w X :
  lqual_dom q ⊆ X →
  logic_qualifier_denote q σ (res_restrict w X) ↔
  logic_qualifier_denote q σ w.
Proof.
  destruct q as [d p]. simpl. intros HdX.
  rewrite res_restrict_restrict_eq.
  replace (X ∩ d) with d by set_solver.
  reflexivity.
Qed.

Lemma lqual_swap_conjugate a b x y q :
  lqual_swap a b (lqual_swap x y q) =
  lqual_swap (atom_swap a b x) (atom_swap a b y) (lqual_swap a b q).
Proof.
  destruct q as [d p]. simpl.
  f_equal.
  - apply aset_swap_conjugate.
  - apply functional_extensionality. intros σ.
    apply functional_extensionality. intros w.
    apply propositional_extensionality.
    rewrite store_swap_conjugate_inv, res_swap_conjugate_inv.
    reflexivity.
Qed.

Definition lqual_and (q1 q2 : logic_qualifier) : logic_qualifier :=
  match q1, q2 with
  | lqual d1 p1, lqual d2 p2 =>
      lqual (d1 ∪ d2) (λ σ w, p1 σ w ∧ p2 σ w)
  end.

Definition lqual_or (q1 q2 : logic_qualifier) : logic_qualifier :=
  match q1, q2 with
  | lqual d1 p1, lqual d2 p2 =>
      lqual (d1 ∪ d2) (λ σ w, p1 σ w ∨ p2 σ w)
  end.

Definition lqual_top : logic_qualifier :=
  lqual ∅ (λ _ _, True).

Definition lqual_bot : logic_qualifier :=
  lqual ∅ (λ _ _, False).

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

End LogicQualifier.
