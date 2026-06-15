(** * Denotation.DenotationSetMapFacts

    Small set/map/store facts shared by denotation and soundness proofs.

    This file is intentionally low-tech: it collects deterministic rewrites
    and side-condition helpers that used to be reproved locally in the larger
    transport proofs. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore.

Lemma lty_env_insert_free_commute
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  <[LVFree x := Tx]> (<[LVFree y := Ty]> Σ) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof.
  intros Hxy.
  apply map_eq. intros u.
  destruct (decide (u = LVFree x)) as [->|Hux].
  - rewrite lookup_insert_eq.
    rewrite lookup_insert_ne by congruence.
    rewrite lookup_insert_eq. reflexivity.
  - destruct (decide (u = LVFree y)) as [->|Huy].
    + rewrite lookup_insert_ne by congruence.
      rewrite !lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma store_restrict_insert_agree_on_subset
    (σ : StoreT) X Y z (v : value) :
  Y ⊆ X ->
  z ∉ dom (σ : StoreT) ->
  z ∉ X ->
  store_restrict (<[z := v]> σ) (Y ∪ {[z]}) =
  store_restrict (<[z := v]> (store_restrict σ X : StoreT)) (Y ∪ {[z]}).
Proof.
  intros HYX Hzσ HzX.
  change (storeA_restrict (<[z := v]> (σ : gmap atom value)) (Y ∪ {[z]}) =
    storeA_restrict
      (<[z := v]> (storeA_restrict σ X : gmap atom value)) (Y ∪ {[z]})).
  transitivity (<[z := v]> (storeA_restrict σ Y : gmap atom value)).
  - apply storeA_restrict_insert_fresh_union;
      [apply not_elem_of_dom; exact Hzσ|set_solver].
  - transitivity (<[z := v]>
        (storeA_restrict (storeA_restrict σ X : gmap atom value) Y
          : gmap atom value)).
    + f_equal.
      symmetry. apply storeA_restrict_twice_subset. exact HYX.
    + symmetry.
      apply storeA_restrict_insert_fresh_union.
      * apply storeA_restrict_lookup_none_r. exact HzX.
      * set_solver.
Qed.

Lemma store_restrict_insert_agree_on_observed
    (σ : StoreT) X Z z (v : value) :
  Z ⊆ X ∪ {[z]} ->
  z ∉ dom (σ : StoreT) ->
  z ∉ X ->
  store_restrict (<[z := v]> σ) Z =
  store_restrict (<[z := v]> (store_restrict σ X : StoreT)) Z.
Proof.
  intros HZX Hzσ HzX.
  transitivity
    (store_restrict (store_restrict (<[z := v]> σ) (X ∪ {[z]})) Z).
  - symmetry. apply storeA_restrict_twice_subset. exact HZX.
  - transitivity
      (store_restrict
        (store_restrict (<[z := v]> (store_restrict σ X : StoreT))
          (X ∪ {[z]})) Z).
    + f_equal.
      apply store_restrict_insert_agree_on_subset; set_solver.
    + apply storeA_restrict_twice_subset. exact HZX.
Qed.

Ltac denotation_set_norm :=
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in *;
  rewrite ?dom_insert_L, ?dom_union_L, ?dom_singleton_L in *.

Ltac denotation_set_solve :=
  denotation_set_norm; set_solver.

Ltac denotation_store_norm :=
  rewrite ?storeA_restrict_twice_subset in * by set_solver.

