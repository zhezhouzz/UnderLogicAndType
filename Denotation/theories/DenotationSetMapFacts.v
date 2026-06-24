(** * Denotation.DenotationSetMapFacts

    Small set/map/store facts shared by denotation and soundness proofs.

    This file is intentionally low-tech: it collects deterministic rewrites
    and side-condition helpers that used to be reproved locally in the larger
    transport proofs. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore.

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

Lemma store_lookup_eq_of_restrict_eq
    (σ1 σ2 : StoreT) X x :
  x ∈ X ->
  store_restrict σ1 X = store_restrict σ2 X ->
  σ1 !! x = σ2 !! x.
Proof.
  intros Hx Heq.
  apply option_eq. intros v. split; intros Hlook.
  - eapply storeA_restrict_lookup_transport; [exact Hx|exact Heq|exact Hlook].
  - eapply storeA_restrict_lookup_transport; [exact Hx|symmetry; exact Heq|exact Hlook].
Qed.

Lemma store_lookup_eq_of_restrict_eq_full
    (σbig σsmall : StoreT) X x :
  x ∈ X ->
  store_restrict σbig X = σsmall ->
  σbig !! x = σsmall !! x.
Proof.
  intros Hx Heq.
  change (storeA_restrict σbig X = σsmall) in Heq.
  apply option_eq. intros v. split; intros Hlook.
  - assert (Hrestr : (storeA_restrict σbig X : StoreT) !! x = Some v).
    { apply storeA_restrict_lookup_some_2; [exact Hlook|exact Hx]. }
    rewrite <- Heq. exact Hrestr.
  - replace σsmall with (storeA_restrict σbig X) in Hlook
      by exact Heq.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
Qed.

Ltac denotation_set_norm :=
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in *;
  rewrite ?dom_insert_L, ?dom_union_L, ?dom_singleton_L in *.

Ltac denotation_set_solve :=
  denotation_set_norm; set_solver.

Ltac soundness_fresh_norm :=
  denotation_set_norm;
  rewrite ?dom_empty_L, ?dom_singleton_L in *.

Ltac soundness_fresh_solve :=
  soundness_fresh_norm; better_set_solver.

Ltac denotation_store_norm :=
  rewrite ?storeA_restrict_twice_subset in * by set_solver.

(** ** Regular facts extracted from denotation/resource definitions *)

Ltac denotation_regular_res_extend_dom :=
  match goal with
  | Hext : res_extend_by ?m ?F ?mx |- _ =>
      lazymatch goal with
      | H : world_dom (mx : WorldT) =
            world_dom (m : WorldT) ∪ ext_out F |- _ =>
          fail
      | _ =>
          let H := fresh "Hdom_ext" in
          pose proof (res_extend_by_dom m F mx Hext) as H
      end
  end.

Ltac denotation_regular_res_extend_base :=
  match goal with
  | Hext : res_extend_by ?m ?F ?mx |- _ =>
      lazymatch goal with
      | H : res_restrict mx (world_dom (m : WorldT)) = m |- _ =>
          fail
      | _ =>
          let H := fresh "Hbase_ext" in
          pose proof (res_extend_by_restrict_base m F mx Hext) as H
      end
  end.

Ltac denotation_regular_res_extend_input :=
  match goal with
  | Hext : res_extend_by ?m ?F ?mx |- _ =>
      lazymatch goal with
      | H : ext_in F ⊆ world_dom (m : WorldT) |- _ =>
          fail
      | _ =>
          let H := fresh "Hin_ext" in
          pose proof (res_extend_by_input_dom m F mx Hext) as H
      end
  end.

Ltac denotation_regular_res_extend_output :=
  match goal with
  | Hext : res_extend_by ?m ?F ?mx |- _ =>
      lazymatch goal with
      | H : ext_out F ## world_dom (m : WorldT) |- _ =>
          fail
      | _ =>
          let H := fresh "Hout_ext" in
          pose proof (res_extend_by_output_fresh m F mx Hext) as H
      end
  end.

Ltac denotation_regular :=
  try denotation_regular_res_extend_dom;
  try denotation_regular_res_extend_base;
  try denotation_regular_res_extend_input;
  try denotation_regular_res_extend_output.
