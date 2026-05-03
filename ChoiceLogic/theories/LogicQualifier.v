From ChoiceLogic Require Import Prelude.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation bnamingT := (gmap nat atom) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).

Inductive logic_qualifier : Type :=
  | lqual (B : gset nat) (d : aset) (prop : bnamingT → StoreT → WfWorldT → Prop).

Definition lqual_dom (q : logic_qualifier) : aset :=
  match q with
  | lqual _ d _ => d
  end.

Definition lqual_bvars (q : logic_qualifier) : gset nat :=
  match q with
  | lqual B _ _ => B
  end.

Definition lqual_prop (q : logic_qualifier) : bnamingT → StoreT → WfWorldT → Prop :=
  match q with
  | lqual _ _ p => p
  end.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (σ : StoreT)
    (w : WfWorldT) : Prop :=
  match q with
  | lqual _ d p => p ∅ (store_restrict σ d) (res_restrict w d)
  end.

End LogicQualifier.
