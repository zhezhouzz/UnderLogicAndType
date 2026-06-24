(** * Denotation.DenotationSetMapFacts

    Small set/map/store facts shared by denotation and soundness proofs.

    This file is intentionally low-tech: it collects deterministic rewrites
    and side-condition helpers that used to be reproved locally in the larger
    transport proofs. *)

From CoreLang Require Import Syntax.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceExtension ResourceInterface.
From ContextTypeLanguage Require Import Syntax.

Notation StoreT := (Store (V := value)) (only parsing).
Notation WorldT := (World (V := value)) (only parsing).
Notation WfWorldT := (WfWorld (V := value)) (only parsing).

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
  eapply store_lookup_eq_of_restrict_eq; [exact Hx|].
  rewrite <- Heq.
  symmetry.
  apply storeA_restrict_twice_subset.
  set_solver.
Qed.

Lemma store_restrict_insert_same_observed
    (σ1 σ2 : StoreT) X z (v : value) :
  store_restrict σ1 X = store_restrict σ2 X ->
  store_restrict (<[z := v]> σ1) (X ∪ {[z]}) =
  store_restrict (<[z := v]> σ2) (X ∪ {[z]}).
Proof.
  intros Heq.
  change (storeA_restrict (<[z := v]> (σ1 : gmap atom value)) (X ∪ {[z]}) =
    storeA_restrict (<[z := v]> (σ2 : gmap atom value)) (X ∪ {[z]})).
  apply storeA_map_eq. intros a.
  destruct (decide (a = z)) as [->|Haz].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2;
        [apply map_lookup_insert|set_solver].
    + symmetry. apply storeA_restrict_lookup_some_2;
        [apply map_lookup_insert|set_solver].
  - destruct (decide (a ∈ X)) as [HaX|HaX].
    + pose proof (store_lookup_eq_of_restrict_eq σ1 σ2 X a HaX Heq)
        as Hlook_eq.
      destruct ((σ1 : StoreT) !! a) as [va|] eqn:Hlook1.
      * assert (Hlook2 : (σ2 : StoreT) !! a = Some va).
        { symmetry. exact Hlook_eq. }
        transitivity (Some va).
        -- apply storeA_restrict_lookup_some_2.
           ++ transitivity ((σ1 : StoreT) !! a).
              ** apply map_lookup_insert_ne. congruence.
              ** exact Hlook1.
           ++ set_solver.
        -- symmetry. apply storeA_restrict_lookup_some_2.
           ++ transitivity ((σ2 : StoreT) !! a).
              ** apply map_lookup_insert_ne. congruence.
              ** exact Hlook2.
           ++ set_solver.
      * assert (Hlook2 : (σ2 : StoreT) !! a = None).
        { symmetry. exact Hlook_eq. }
        transitivity (@None value).
        -- apply storeA_restrict_lookup_none_l.
           transitivity ((σ1 : StoreT) !! a).
           ++ apply map_lookup_insert_ne. congruence.
           ++ exact Hlook1.
        -- symmetry. apply storeA_restrict_lookup_none_l.
           transitivity ((σ2 : StoreT) !! a).
           ++ apply map_lookup_insert_ne. congruence.
           ++ exact Hlook2.
    + transitivity (@None value).
      * apply storeA_restrict_lookup_none_r. set_solver.
      * symmetry. apply storeA_restrict_lookup_none_r. set_solver.
Qed.

Lemma store_restrict_insert_union_eq_of_restrict_eq
    (σ1 σ2 : StoreT) X z (v : value) :
  z ∉ X ->
  store_restrict σ1 X = store_restrict σ2 X ->
  store_restrict (<[z := v]> σ1) (X ∪ {[z]}) =
  store_restrict (<[z := v]> σ2) (X ∪ {[z]}).
Proof.
  intros _ Heq.
  apply store_restrict_insert_same_observed.
  exact Heq.
Qed.

Lemma store_restrict_insert_agree_on_observed
    (σ : StoreT) X Z z (v : value) :
  Z ⊆ X ∪ {[z]} ->
  z ∉ dom (σ : StoreT) ->
  z ∉ X ->
  store_restrict (<[z := v]> σ) Z =
  store_restrict (<[z := v]> (store_restrict σ X : StoreT)) Z.
Proof.
  intros HZX _ HzX.
  transitivity
    (store_restrict (store_restrict (<[z := v]> σ) (X ∪ {[z]})) Z).
  - symmetry. apply storeA_restrict_twice_subset. exact HZX.
  - rewrite (store_restrict_insert_union_eq_of_restrict_eq
      σ (store_restrict σ X : StoreT) X z v).
    + apply storeA_restrict_twice_subset. exact HZX.
    + exact HzX.
    + symmetry. apply storeA_restrict_twice_subset. set_solver.
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
  apply store_restrict_insert_agree_on_observed; set_solver.
Qed.

Lemma res_extend_rel_store_dom
    (m mx : WfWorldT) (F : fiber_extension)
    (σm : StoreT) (we : WfWorldT) (σe : StoreT) :
  res_extend_by m F mx ->
  (m : WorldT) σm ->
  extA_rel F (store_restrict σm (extA_in F)) we ->
  (we : WorldT) σe ->
  dom (σe : StoreT) = extA_out F.
Proof.
  intros Hext Hσm HFrel Hσe.
  pose proof (wfworld_store_dom we σe Hσe) as Hdomσe.
  change (dom (σe : StoreT) = world_dom (we : WorldT)) in Hdomσe.
  rewrite Hdomσe.
  eapply extA_rel_dom; [|exact HFrel].
  eapply extA_projection_dom.
  - apply resA_extend_by_applicable in Hext. exact Hext.
  - exact Hσm.
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
            world_dom (m : WorldT) ∪ extA_out F |- _ =>
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
      | H : extA_in F ⊆ world_dom (m : WorldT) |- _ =>
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
      | H : extA_out F ## world_dom (m : WorldT) |- _ =>
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
