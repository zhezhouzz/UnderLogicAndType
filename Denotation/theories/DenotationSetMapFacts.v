(** * Denotation.DenotationSetMapFacts

    Small set/map/store facts shared by denotation and soundness proofs.

    This file is intentionally low-tech: it collects deterministic rewrites
    and side-condition helpers that used to be reproved locally in the larger
    transport proofs. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore.

Lemma lvars_shift_from_lc k D :
  lc_lvars D ->
  lc_lvars (lvars_shift_from k D).
Proof.
  intros Hlc v Hv.
  unfold lvars_shift_from in Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  destruct u as [n|x]; cbn [logic_var_shift_from].
  - destruct (decide (k <= n)); exfalso; exact (Hlc (LVBound n) Hu).
  - exact I.
Qed.

Lemma lvars_shift_from_lc_eq k D :
  lc_lvars D ->
  lvars_shift_from k D = D.
Proof.
  intros Hlc.
  apply set_eq. intros v. split.
  - unfold lvars_shift_from.
    intros Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    destruct u as [n|x]; cbn [logic_var_shift_from].
    + destruct (decide (k <= n)); exfalso; exact (Hlc (LVBound n) Hu).
    + exact Hu.
  - intros Hv.
    unfold lvars_shift_from.
    destruct v as [n|x].
    + exfalso. exact (Hlc (LVBound n) Hv).
    + apply elem_of_map. exists (LVFree x). split; [reflexivity|exact Hv].
Qed.

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
  apply option_eq. intros v. split; intros Hlook.
  - assert ((store_restrict σbig X : StoreT) !! x = Some v).
    { apply storeA_restrict_lookup_some_2; [exact Hlook|exact Hx]. }
    rewrite Heq in H. exact H.
  - rewrite <- Heq in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
Qed.

Lemma res_restrict_singleton_store_eq
    (m : WfWorldT) X (σX σ : StoreT) :
  res_restrict m X =
    (exist _ (singleton_world σX) (wf_singleton_world σX) : WfWorldT) ->
  (m : WorldT) σ ->
  store_restrict σ X = σX.
Proof.
  intros Hsingle Hσ.
  assert ((res_restrict m X : WorldT) (store_restrict σ X)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  rewrite Hsingle in H. cbn [raw_world raw_worldA singleton_world] in H.
  exact H.
Qed.

Lemma res_extend_by_singleton_output_in_world
    (m mx : WfWorldT) F x :
  res_extend_by m F mx ->
  ext_out F = {[x]} ->
  x ∈ world_dom (mx : WorldT).
Proof.
  intros Hext Hout.
  pose proof (res_extend_by_dom m F mx Hext) as Hdom.
  change (world_dom (mx : WorldT) =
    world_dom (m : WorldT) ∪ ext_out F) in Hdom.
  rewrite Hdom, Hout.
  set_solver.
Qed.

Lemma res_extend_by_singleton_output_notin_base_store
    (m mx : WfWorldT) F x (σ : StoreT) :
  res_extend_by m F mx ->
  ext_out F = {[x]} ->
  (m : WorldT) σ ->
  x ∉ dom (σ : StoreT).
Proof.
  intros Hext Hout Hσ.
  pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh.
  change (ext_out F ## world_dom (m : WorldT)) in Hfresh.
  pose proof (wfworldA_store_dom m σ Hσ) as Hdomσ.
  change (dom (σ : StoreT) = world_dom (m : WorldT)) in Hdomσ.
  rewrite Hdomσ.
  rewrite Hout in Hfresh.
  set_solver.
Qed.

Ltac denotation_set_norm :=
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in *;
  rewrite ?dom_insert_L, ?dom_union_L, ?dom_singleton_L in *.

Ltac denotation_set_solve :=
  denotation_set_norm; set_solver.

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
