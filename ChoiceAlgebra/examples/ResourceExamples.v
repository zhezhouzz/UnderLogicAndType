(** * Resource examples

    Sanity checks for the concrete [World]/[WfWorld] resource definitions.
    The main example mirrors the paper's diagonal-vs-product discussion:
    product forms all independent compatible combinations, while the order [⊑]
    is domain restriction, not alternative inclusion. *)

From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import Resource.

(** Concrete atoms standing for paper variables x and y. *)
Definition x_atom : atom := 1%positive.
Definition y_atom : atom := 2%positive.

Local Notation "'x" := x_atom.
Local Notation "'y" := y_atom.

Local Instance nat_valuesig : ValueSig nat := {|
  valuesig_eqdec := _;
  valuesig_inhabited := populate 0;
|}.

Local Notation StoreN := (gmap atom nat).
Local Notation WorldN := (World (V := nat)).
Local Notation WfWorldN := (WfWorld (V := nat)).

Ltac crush_store := vm_compute; try tauto; try congruence; try reflexivity.

Ltac split4 := repeat split.

Definition sx1 : StoreN := <['x := 1%nat]> ∅.
Definition sx2 : StoreN := <['x := 2%nat]> ∅.
Definition sy3 : StoreN := <['y := 3%nat]> ∅.
Definition sy4 : StoreN := <['y := 4%nat]> ∅.

Definition s13 : StoreN := <['x := 1%nat]> (<['y := 3%nat]> ∅).
Definition s14 : StoreN := <['x := 1%nat]> (<['y := 4%nat]> ∅).
Definition s23 : StoreN := <['x := 2%nat]> (<['y := 3%nat]> ∅).
Definition s24 : StoreN := <['x := 2%nat]> (<['y := 4%nat]> ∅).

Definition mx : WorldN := {|
  world_dom := {['x]};
  world_stores := fun s => s = sx1 ∨ s = sx2;
|}.

Definition my : WorldN := {|
  world_dom := {['y]};
  world_stores := fun s => s = sy3 ∨ s = sy4;
|}.

Definition mxy_diag : WorldN := {|
  world_dom := {['x; 'y]};
  world_stores := fun s => s = s13 ∨ s = s24;
|}.

Definition mx_one : WorldN := {|
  world_dom := {['x]};
  world_stores := fun s => s = sx1;
|}.

Definition mx_two : WorldN := {|
  world_dom := {['x]};
  world_stores := fun s => s = sx2;
|}.

(** ** Product: independent choices produce all compatible combinations. *)

Example mx_my_compatible :
  world_compat mx my.
Proof.
  unfold world_compat, mx, my. simpl.
  intros s1 s2 [-> | ->] [-> | ->];
    apply disj_dom_store_compat; crush_store.
Qed.

Example product_contains_all_four :
  raw_product mx my s13 ∧
  raw_product mx my s14 ∧
  raw_product mx my s23 ∧
  raw_product mx my s24.
Proof.
  unfold raw_product, mx, my. simpl.
  split4.
  - exists sx1, sy3. repeat split; try (left; reflexivity);
      try (apply disj_dom_store_compat; crush_store); crush_store.
  - exists sx1, sy4. repeat split; try (left; reflexivity);
      try (right; reflexivity); try (apply disj_dom_store_compat; crush_store);
      crush_store.
  - exists sx2, sy3. repeat split; try (right; reflexivity);
      try (left; reflexivity); try (apply disj_dom_store_compat; crush_store);
      crush_store.
  - exists sx2, sy4. repeat split; try (right; reflexivity);
      try (apply disj_dom_store_compat; crush_store); crush_store.
Qed.

Example diag_contains_only_two :
  mxy_diag s13 ∧ mxy_diag s24 ∧
  ¬ mxy_diag s14 ∧ ¬ mxy_diag s23.
Proof.
  unfold mxy_diag. simpl.
  repeat split; try (left; reflexivity); try (right; reflexivity).
  - intros [H | H]; vm_compute in H; discriminate H.
  - intros [H | H]; vm_compute in H; discriminate H.
Qed.

Example product_has_cross_terms_not_in_diag :
  raw_product mx my s14 ∧ raw_product mx my s23 ∧
  ¬ mxy_diag s14 ∧ ¬ mxy_diag s23.
Proof.
  pose proof product_contains_all_four as Hprod.
  pose proof diag_contains_only_two as Hdiag.
  tauto.
Qed.

(** ** Restriction order: [⊑] compares projections, not cardinalities. *)

Example restrict_diag_to_x :
  raw_restrict mxy_diag ({['x]}) = mx.
Proof.
  apply world_ext.
  - crush_store.
  - intros s. unfold raw_restrict, mxy_diag, mx. simpl.
    split.
    + intros [s' [Hdiag Hrestr]].
      destruct Hdiag as [-> | ->]; subst s; [left | right]; crush_store.
    + intros [-> | ->].
      * exists s13. split; [left; reflexivity | crush_store].
      * exists s24. split; [right; reflexivity | crush_store].
Qed.

Example restrict_diag_to_y :
  raw_restrict mxy_diag ({['y]}) = my.
Proof.
  apply world_ext.
  - crush_store.
  - intros s. unfold raw_restrict, mxy_diag, my. simpl.
    split.
    + intros [s' [Hdiag Hrestr]].
      destruct Hdiag as [-> | ->]; subst s; [left | right]; crush_store.
    + intros [-> | ->].
      * exists s13. split; [left; reflexivity | crush_store].
      * exists s24. split; [right; reflexivity | crush_store].
Qed.

Example restrict_product_to_x :
  raw_restrict (raw_product mx my) ({['x]}) = mx.
Proof.
  apply world_ext.
  - crush_store.
  - intros s. unfold raw_restrict, raw_product, mx, my. simpl.
    split.
    + intros [s' [Hprod Hrestr]].
      destruct Hprod as [s1 [s2 [[-> | ->] [[-> | ->] [_ Heq]]]]];
        subst s'; subst s;
        [left | left | right | right]; crush_store.
    + intros [-> | ->].
      * exists s13. split; [exists sx1, sy3 |]; repeat split; try (left; reflexivity);
          try (apply disj_dom_store_compat; crush_store); crush_store.
      * exists s23. split; [exists sx2, sy3 |]; repeat split; try (left; reflexivity);
          try (right; reflexivity); try (apply disj_dom_store_compat; crush_store);
          crush_store.
Qed.

Example restrict_product_to_y :
  raw_restrict (raw_product mx my) ({['y]}) = my.
Proof.
  apply world_ext.
  - crush_store.
  - intros s. unfold raw_restrict, raw_product, mx, my. simpl.
    split.
    + intros [s' [Hprod Hrestr]].
      destruct Hprod as [s1 [s2 [[-> | ->] [[-> | ->] [_ Heq]]]]];
        subst s'; subst s;
        [left | right | left | right]; crush_store.
    + intros [-> | ->].
      * exists s13. split; [exists sx1, sy3 |]; repeat split; try (left; reflexivity);
          try (apply disj_dom_store_compat; crush_store); crush_store.
      * exists s14. split; [exists sx1, sy4 |]; repeat split; try (left; reflexivity);
          try (right; reflexivity); try (apply disj_dom_store_compat; crush_store);
          crush_store.
Qed.

Example mx_raw_le_diag :
  raw_le mx mxy_diag.
Proof. unfold raw_le. symmetry. exact restrict_diag_to_x. Qed.

Example my_raw_le_diag :
  raw_le my mxy_diag.
Proof. unfold raw_le. symmetry. exact restrict_diag_to_y. Qed.

Example mx_raw_le_product :
  raw_le mx (raw_product mx my).
Proof. unfold raw_le. symmetry. exact restrict_product_to_x. Qed.

Example my_raw_le_product :
  raw_le my (raw_product mx my).
Proof. unfold raw_le. symmetry. exact restrict_product_to_y. Qed.

Example product_not_raw_le_diag :
  ¬ raw_le (raw_product mx my) mxy_diag.
Proof.
  unfold raw_le. intros Heq.
  assert (H : (raw_product mx my) s14).
  { pose proof product_contains_all_four as [_ [H _]]. exact H. }
  rewrite Heq in H. simpl in H.
  destruct H as [s' [[-> | ->] Hrestr]];
    vm_compute in Hrestr; discriminate Hrestr.
Qed.

Example diag_not_raw_le_product :
  ¬ raw_le mxy_diag (raw_product mx my).
Proof.
  unfold raw_le. intros Heq.
  assert (H : raw_restrict (raw_product mx my) (world_dom mxy_diag) s14).
  { simpl. exists s14. split.
    - pose proof product_contains_all_four as [_ [H _]]. exact H.
    - crush_store. }
  rewrite <- Heq in H. simpl in H.
  destruct H as [H | H]; vm_compute in H; discriminate H.
Qed.

(** ** Sum: choice union is defined only at the same domain. *)

Example sum_defined_same_domain :
  raw_sum_defined mx_one mx_two.
Proof. unfold raw_sum_defined, mx_one, mx_two. simpl. reflexivity. Qed.

Example sum_contains_both_choices :
  raw_sum mx_one mx_two sx1 ∧ raw_sum mx_one mx_two sx2.
Proof. unfold raw_sum, mx_one, mx_two. simpl. split; [left | right]; reflexivity. Qed.

Example sum_not_defined_different_domains :
  ¬ raw_sum_defined mx my.
Proof. unfold raw_sum_defined, mx, my. simpl. crush_store. Qed.

(** ** Fiber: fixing a projection selects the compatible slice. *)

Definition sigma_y3 : StoreN := <['y := 3%nat]> ∅.

Example fiber_y3_keeps_13_and_23 :
  raw_fiber (raw_product mx my) sigma_y3 s13 ∧
  raw_fiber (raw_product mx my) sigma_y3 s23.
Proof.
  unfold raw_fiber. simpl. split; split.
  - pose proof product_contains_all_four as [H _]. exact H.
  - crush_store.
  - pose proof product_contains_all_four as [_ [_ [H _]]]. exact H.
  - crush_store.
Qed.

Example fiber_y3_removes_14_and_24 :
  ¬ raw_fiber (raw_product mx my) sigma_y3 s14 ∧
  ¬ raw_fiber (raw_product mx my) sigma_y3 s24.
Proof.
  unfold raw_fiber. simpl. split; intros [_ Hrestrict];
    vm_compute in Hrestrict; discriminate Hrestrict.
Qed.

(** ** Compatibility: overlapping domains must agree on shared atoms. *)

Example same_value_overlap_compatible :
  world_compat mx_one mx_one.
Proof.
  unfold world_compat, mx_one. simpl.
  intros s1 s2 -> ->. apply store_compat_refl.
Qed.

Example different_value_overlap_incompatible :
  ¬ world_compat mx_one mx_two.
Proof.
  unfold not, world_compat, mx_one, mx_two. simpl.
  intros Hcompat.
  specialize (Hcompat sx1 sx2 eq_refl eq_refl).
  unfold store_compat, map_compat in Hcompat.
  specialize (Hcompat 'x 1%nat 2%nat).
  vm_compute in Hcompat. discriminate (Hcompat eq_refl eq_refl).
Qed.

Example disjoint_domains_compatible :
  world_compat mx my.
Proof. exact mx_my_compatible. Qed.
