(** * Store examples

    Small sanity checks for the finite-map/store layer.  These examples are
    meant to make the intended behavior of restriction, compatibility, union,
    and atom renaming easy to inspect. *)

From ChoicePrelude Require Import Store.

Definition ex_x : atom := 1%positive.
Definition ex_y : atom := 2%positive.
Definition ex_z : atom := 3%positive.

Local Instance nat_valuesig : ValueSig nat := {|
  valuesig_eqdec := _;
  valuesig_inhabited := populate 0;
|}.

Local Notation StoreN := (gmap atom nat).

Definition store_x1 : StoreN := <[ex_x := 1%nat]> ∅.
Definition store_y2 : StoreN := <[ex_y := 2%nat]> ∅.
Definition store_x1_y2 : StoreN := <[ex_x := 1%nat]> (<[ex_y := 2%nat]> ∅).
Definition store_x2 : StoreN := <[ex_x := 2%nat]> ∅.

Example restrict_xy_to_x :
  store_restrict store_x1_y2 ({[ex_x]}) = store_x1.
Proof. Admitted.

Example restrict_xy_to_y :
  store_restrict store_x1_y2 ({[ex_y]}) = store_y2.
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
  store_restrict (store_x1 ∪ store_y2) ({[ex_x]}) = store_x1.
Proof. Admitted.

Example compatible_union_restrict_y :
  store_restrict (store_x1 ∪ store_y2) ({[ex_y]}) = store_y2.
Proof. Admitted.

Example rename_moves_binding :
  store_rename_atom ex_x ex_z store_x1_y2 =
  <[ex_z := 1%nat]> (<[ex_y := 2%nat]> ∅).
Proof. Admitted.

Example rename_missing_deletes_target :
  store_rename_atom ex_z ex_y store_x1_y2 = <[ex_x := 1%nat]> ∅.
Proof. Admitted.
