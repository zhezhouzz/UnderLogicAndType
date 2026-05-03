From ChoiceLogic Require Import Prelude.

(** * Logic qualifiers

    Logic qualifiers are resource-level atoms.  They carry:
    - a finite domain [d] of referenced variables;
    - a predicate over the domain-restricted explicit store and world.

    We do not require [dom store = d] or [world_dom w = d].  Denotation
    restricts both inputs to [d] before calling the predicate. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation BStoreT := (gmap nat V) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).

Inductive logic_qualifier : Type :=
  | lqual (B : gset nat) (d : aset) (prop : BStoreT → StoreT → WfWorldT → Prop).

Definition lqual_dom (q : logic_qualifier) : aset :=
  match q with
  | lqual _ d _ => d
  end.

Definition lqual_bvars (q : logic_qualifier) : gset nat :=
  match q with
  | lqual B _ _ => B
  end.

Definition lqual_prop (q : logic_qualifier) : BStoreT → StoreT → WfWorldT → Prop :=
  match q with
  | lqual _ _ p => p
  end.

Definition lqual_open (k : nat) (x : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual B d p =>
      if decide (k ∈ B) then
        lqual (B ∖ {[k]}) ({[x]} ∪ d)
          (λ β σ w, ∃ v, σ !! x = Some v ∧ p (<[k := v]> β) σ w)
      else q
  end.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_dom.
Arguments stale_logic_qualifier /.

Definition logic_qualifier_denote
    (q : logic_qualifier)
    (bmap : BStoreT)
    (σ : StoreT)
    (w : WfWorldT) : Prop :=
  match q with
  | lqual B d p => p (map_restrict V bmap B) (store_restrict σ d) (res_restrict w d)
  end.

End LogicQualifier.
