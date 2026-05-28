(** * Shared atoms and freshness infrastructure *)

From ContextBase Require Export SetTactics MapTactics.
From stdpp Require Export gmap sets fin_sets fin_map_dom fin_maps countable.
From Corelib Require Export Program.Wf.
From Stdlib Require Export Lia.

Definition atom : Type := positive.
#[global] Instance atom_eqdec     : EqDecision atom := _.
#[global] Instance atom_countable : Countable  atom := _.
#[global] Instance atom_infinite  : Infinite   atom := _.
Notation aset := (gset atom).

(** Free-variable/resource-domain collection. *)
Class Stale A := stale : A → aset.

#[global] Instance stale_aset : Stale aset := id.

Notation "x '#' s" := (x ∉ stale s) (at level 40).

