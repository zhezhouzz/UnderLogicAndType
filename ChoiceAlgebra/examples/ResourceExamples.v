(** * Resource examples

    Sanity checks for the concrete [World]/[WfWorld] resource definitions.
    The main example mirrors the paper's diagonal-vs-product discussion:
    product forms all independent compatible combinations, while the order [⊑]
    is domain restriction, not alternative inclusion. *)

From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import Resource.

Definition ex_x : atom := 1%positive.
Definition ex_y : atom := 2%positive.

Local Instance nat_valuesig : ValueSig nat := {|
  valuesig_eqdec := _;
  valuesig_inhabited := populate 0;
|}.

Local Notation StoreN := (gmap atom nat).
Local Notation WorldN := (World (V := nat)).
Local Notation WfWorldN := (WfWorld (V := nat)).

Definition sx1 : StoreN := <[ex_x := 1%nat]> ∅.
Definition sx2 : StoreN := <[ex_x := 2%nat]> ∅.
Definition sy3 : StoreN := <[ex_y := 3%nat]> ∅.
Definition sy4 : StoreN := <[ex_y := 4%nat]> ∅.

Definition s13 : StoreN := <[ex_x := 1%nat]> (<[ex_y := 3%nat]> ∅).
Definition s14 : StoreN := <[ex_x := 1%nat]> (<[ex_y := 4%nat]> ∅).
Definition s23 : StoreN := <[ex_x := 2%nat]> (<[ex_y := 3%nat]> ∅).
Definition s24 : StoreN := <[ex_x := 2%nat]> (<[ex_y := 4%nat]> ∅).

Definition mx : WorldN := {|
  world_dom := {[ex_x]};
  world_stores := fun s => s = sx1 ∨ s = sx2;
|}.

Definition my : WorldN := {|
  world_dom := {[ex_y]};
  world_stores := fun s => s = sy3 ∨ s = sy4;
|}.

Definition mxy_diag : WorldN := {|
  world_dom := {[ex_x; ex_y]};
  world_stores := fun s => s = s13 ∨ s = s24;
|}.

Definition mx_one : WorldN := {|
  world_dom := {[ex_x]};
  world_stores := fun s => s = sx1;
|}.

Definition mx_two : WorldN := {|
  world_dom := {[ex_x]};
  world_stores := fun s => s = sx2;
|}.

(** ** Product: independent choices produce all compatible combinations. *)

Example mx_my_compatible :
  world_compat mx my.
Proof. Admitted.

Example product_contains_all_four :
  raw_product mx my s13 ∧
  raw_product mx my s14 ∧
  raw_product mx my s23 ∧
  raw_product mx my s24.
Proof. Admitted.

Example diag_contains_only_two :
  mxy_diag s13 ∧ mxy_diag s24 ∧
  ¬ mxy_diag s14 ∧ ¬ mxy_diag s23.
Proof. Admitted.

Example product_has_cross_terms_not_in_diag :
  raw_product mx my s14 ∧ raw_product mx my s23 ∧
  ¬ mxy_diag s14 ∧ ¬ mxy_diag s23.
Proof. Admitted.

(** ** Restriction order: [⊑] compares projections, not cardinalities. *)

Example restrict_diag_to_x :
  raw_restrict mxy_diag ({[ex_x]}) = mx.
Proof. Admitted.

Example restrict_diag_to_y :
  raw_restrict mxy_diag ({[ex_y]}) = my.
Proof. Admitted.

Example restrict_product_to_x :
  raw_restrict (raw_product mx my) ({[ex_x]}) = mx.
Proof. Admitted.

Example restrict_product_to_y :
  raw_restrict (raw_product mx my) ({[ex_y]}) = my.
Proof. Admitted.

Example mx_raw_le_diag :
  raw_le mx mxy_diag.
Proof. Admitted.

Example my_raw_le_diag :
  raw_le my mxy_diag.
Proof. Admitted.

Example mx_raw_le_product :
  raw_le mx (raw_product mx my).
Proof. Admitted.

Example my_raw_le_product :
  raw_le my (raw_product mx my).
Proof. Admitted.

Example product_not_raw_le_diag :
  ¬ raw_le (raw_product mx my) mxy_diag.
Proof. Admitted.

Example diag_not_raw_le_product :
  ¬ raw_le mxy_diag (raw_product mx my).
Proof. Admitted.

(** ** Sum: choice union is defined only at the same domain. *)

Example sum_defined_same_domain :
  raw_sum_defined mx_one mx_two.
Proof. Admitted.

Example sum_contains_both_choices :
  raw_sum mx_one mx_two sx1 ∧ raw_sum mx_one mx_two sx2.
Proof. Admitted.

Example sum_not_defined_different_domains :
  ¬ raw_sum_defined mx my.
Proof. Admitted.

(** ** Fiber: fixing a projection selects the compatible slice. *)

Definition sigma_y3 : StoreN := <[ex_y := 3%nat]> ∅.

Example fiber_y3_keeps_13_and_23 :
  raw_fiber (raw_product mx my) sigma_y3 s13 ∧
  raw_fiber (raw_product mx my) sigma_y3 s23.
Proof. Admitted.

Example fiber_y3_removes_14_and_24 :
  ¬ raw_fiber (raw_product mx my) sigma_y3 s14 ∧
  ¬ raw_fiber (raw_product mx my) sigma_y3 s24.
Proof. Admitted.

(** ** Compatibility: overlapping domains must agree on shared atoms. *)

Example same_value_overlap_compatible :
  world_compat mx_one mx_one.
Proof. Admitted.

Example different_value_overlap_incompatible :
  ¬ world_compat mx_one mx_two.
Proof. Admitted.

Example disjoint_domains_compatible :
  world_compat mx my.
Proof. Admitted.
