From ChoiceLogic Require Import Prelude.
From ChoicePrelude Require Import Qualifier.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).

Definition logic_qualifier : Type := qualifier (V := V) (A := WfWorldT).

Definition lqual
    (B : gset nat) (d : aset)
    (prop : gmap nat V → gmap atom V → WfWorldT → Prop) : logic_qualifier :=
  qual B d prop.

Definition lqual_dom (q : logic_qualifier) : aset := qual_dom q.

Definition lqual_bvars (q : logic_qualifier) : gset nat := qual_bvars q.

Definition lqual_prop (q : logic_qualifier) :
    gmap nat V → gmap atom V → WfWorldT → Prop :=
  qual_prop q.

Definition lqual_open (k : nat) (x : atom) (q : logic_qualifier) : logic_qualifier :=
  qual_open_atom k x q.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (bmap : gmap nat V)
    (σ : gmap atom V)
    (w : WfWorldT) : Prop :=
  match q with
  | qual B d p => p (map_restrict V bmap B) (store_restrict σ d) (res_restrict w d)
  end.

End LogicQualifier.
