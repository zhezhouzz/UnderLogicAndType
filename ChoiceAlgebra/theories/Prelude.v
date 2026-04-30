From stdpp Require Export gmap sets fin_sets fin_map_dom.
From Corelib Require Export Program.Wf.
From Hammer Require Export Hammer.

(** ** Shared atom and freshness infrastructure *)

Definition atom : Type := positive.
#[global] Instance atom_eqdec     : EqDecision atom := _.
#[global] Instance atom_countable : Countable  atom := _.
#[global] Instance atom_infinite  : Infinite   atom := _.
Notation aset := (gset atom).

(** Free-variable/resource-domain collection. *)
Class Stale A := stale : A → aset.

Notation "x '#' s" := (x ∉ stale s) (at level 40).

Definition fresh_for (s : aset) : atom := fresh s.

Lemma fresh_for_not_in (s : aset) : fresh_for s ∉ s.
Proof. apply is_fresh. Qed.

Ltac pick_fresh x s :=
  let a := fresh x in
  set (a := fresh_for s);
  assert (a ∉ s) by apply fresh_for_not_in.

(** All files open a Section parameterizing over:
      [Var]   : countable type of program variables
      [Value] : type of runtime values (needs EqDecision for map lookups)
    These are introduced in each file's own Section. *)

#[global] Hint Unfold stale : class_simpl.
