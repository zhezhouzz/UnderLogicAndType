(** * Store examples

    Small sanity checks for the finite-map/store layer.  These examples are
    meant to make the intended behavior of restriction, compatibility, union,
    and atom renaming easy to inspect. *)

From ChoicePrelude Require Import Store.

(** Concrete atoms standing for paper variables x, y, z. *)
Definition x_atom : atom := 1%positive.
Definition y_atom : atom := 2%positive.
Definition z_atom : atom := 3%positive.

Local Notation "'x" := x_atom.
Local Notation "'y" := y_atom.
Local Notation "'z" := z_atom.

Local Instance nat_valuesig : ValueSig nat := {|
  valuesig_eqdec := _;
  valuesig_inhabited := populate 0;
|}.

Local Notation StoreN := (gmap atom nat).

Definition store_x1 : StoreN := <['x := 1%nat]> ∅.
Definition store_y2 : StoreN := <['y := 2%nat]> ∅.
Definition store_x1_y2 : StoreN := <['x := 1%nat]> (<['y := 2%nat]> ∅).
Definition store_x2 : StoreN := <['x := 2%nat]> ∅.

Example restrict_xy_to_x :
  store_restrict store_x1_y2 ({['x]}) = store_x1.
Proof. Admitted.

Example restrict_xy_to_y :
  store_restrict store_x1_y2 ({['y]}) = store_y2.
Proof. Admitted.

Example restrict_twice_intersection (s : StoreN) (X Y : aset) :
  store_restrict (store_restrict s X) Y = store_restrict s (X ∩ Y).
Proof. apply store_restrict_restrict. Qed.

Example compatible_disjoint_stores :
  store_compat store_x1 store_y2.
Proof. Admitted.

Example incompatible_overlapping_stores :
  ¬ store_compat store_x1 store_x2.
Proof. Admitted.

Example compatible_union_restrict_x :
  store_restrict (store_x1 ∪ store_y2) ({['x]}) = store_x1.
Proof. Admitted.

Example compatible_union_restrict_y :
  store_restrict (store_x1 ∪ store_y2) ({['y]}) = store_y2.
Proof. Admitted.

Example rename_moves_binding :
  store_rename_atom 'x 'z store_x1_y2 =
  <['z := 1%nat]> (<['y := 2%nat]> ∅).
Proof. Admitted.

Example rename_missing_deletes_target :
  store_rename_atom 'z 'y store_x1_y2 = <['x := 1%nat]> ∅.
Proof. Admitted.
