From ChoiceLogic Require Import Prelude.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    The predicate also receives a locally-nameless binder environment.  The
    environment maps bound logic-variable indices to the fresh atom chosen by
    [formula_open].  Store and world domains remain atom-based; bound variables
    are interpreted only before an atom is evaluated.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).

Inductive logic_qualifier : Type :=
  | lqual
      (D : lvset)
      (prop : gmap nat atom → StoreT → WfWorldT → Prop).

Definition lqual_vars (q : logic_qualifier) : lvset :=
  match q with
  | lqual D _ => D
  end.

Definition lqual_dom (q : logic_qualifier) : aset :=
  match q with
  | lqual D _ => lvars_fv D
  end.

Definition lqual_bvars (q : logic_qualifier) : gset nat :=
  match q with
  | lqual D _ => lvars_bv D
  end.

Definition lqual_prop (q : logic_qualifier) :
    gmap nat atom → StoreT → WfWorldT → Prop :=
  match q with
  | lqual _ p => p
  end.

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (σ : StoreT)
  (w : WfWorldT) : Prop :=
  match q with
  | lqual D p =>
      let d := lvars_fv D in
      p ∅ (store_restrict σ d) (res_restrict w d)
  end.

Definition lqual_fvars (d : aset) (prop : StoreT → WfWorldT → Prop) : logic_qualifier :=
  lqual (lvars_of_atoms d) (λ _ σ w, prop σ w).

Definition lqual_open (k : nat) (x : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual D p => lqual (lvars_open k x D) (λ η σ w, p (<[k := x]> η) σ w)
  end.

Lemma logic_qualifier_denote_restrict q σ w X :
  lqual_dom q ⊆ X →
  logic_qualifier_denote q σ (res_restrict w X) ↔
  logic_qualifier_denote q σ w.
Proof.
  destruct q as [D p]. simpl. intros HdX.
  resource_norm.
  reflexivity.
Qed.

Definition lqual_and (q1 q2 : logic_qualifier) : logic_qualifier :=
  match q1, q2 with
  | lqual d1 p1, lqual d2 p2 =>
      lqual (d1 ∪ d2) (λ η σ w, p1 η σ w ∧ p2 η σ w)
  end.

Definition lqual_or (q1 q2 : logic_qualifier) : logic_qualifier :=
  match q1, q2 with
  | lqual d1 p1, lqual d2 p2 =>
      lqual (d1 ∪ d2) (λ η σ w, p1 η σ w ∨ p2 η σ w)
  end.

Definition lqual_top : logic_qualifier :=
  lqual ∅ (λ _ _ _, True).

Definition lqual_bot : logic_qualifier :=
  lqual ∅ (λ _ _ _, False).

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

End LogicQualifier.
