(** * Denotation.DenotationSetMapFacts

    Small set/map/store facts shared by denotation and soundness proofs.

    This file is intentionally low-tech: it collects deterministic rewrites
    and side-condition helpers that used to be reproved locally in the larger
    transport proofs. *)

From CoreLang Require Import Syntax InstantiationProps.
From ContextStore Require Import Store StoreRestrict.
From ContextAlgebra Require Import ResourceExtension ResourceInterface ResourceInterfaceFacts.
From ContextTypeLanguage Require Import Syntax LtyEnv.
From ContextBasicDenotation Require Import StoreTyping RelevantEnvRegular.

Notation StoreT := (Store (V := value)) (only parsing).
Notation WorldT := (World (V := value)) (only parsing).
Notation WfWorldT := (WfWorld (V := value)) (only parsing).

Lemma union_singleton_empty_r (X : aset) y :
  X ∪ ({[y]} ∪ ∅) = X ∪ {[y]}.
Proof. apply gset_union_singleton_empty_r. Qed.

Lemma empty_union_singleton_l y :
  ∅ ∪ {[y]} = ({[y]} : aset).
Proof. apply gset_empty_union_singleton_l. Qed.

Lemma notin_union4_l (a : atom) (A B C D : aset) :
  a ∉ A ∪ B ∪ C ∪ D ->
  a ∉ A.
Proof. apply gset_notin_union4_l. Qed.

Lemma notin_union4_r1 (a : atom) (A B C D : aset) :
  a ∉ A ∪ B ∪ C ∪ D ->
  a ∉ B.
Proof. apply gset_notin_union4_r1. Qed.

Lemma notin_union4_r2 (a : atom) (A B C D : aset) :
  a ∉ A ∪ B ∪ C ∪ D ->
  a ∉ C.
Proof. apply gset_notin_union4_r2. Qed.

Lemma notin_union4_r3 (a : atom) (A B C D : aset) :
  a ∉ A ∪ B ∪ C ∪ D ->
  a ∉ D.
Proof. apply gset_notin_union4_r3. Qed.

Lemma elem_union_singleton_not_eq_left (A : aset) a y :
  a ∈ A ∪ {[y]} ->
  a <> y ->
  a ∈ A.
Proof. apply gset_elem_union_singleton_not_eq_left. Qed.

Lemma elem_open_world_inter_singleton x y (B : aset) :
  x ∈ B ->
  x ∈ (B ∪ {[y]}) ∩ ({[x]} : aset).
Proof. apply gset_elem_open_world_inter_singleton. Qed.

Lemma store_restrict_union_singleton_ignore_r
    (σ : StoreT) x (v : value) X :
  x ∉ X ->
  store_restrict ((σ : StoreT) ∪ ({[x := v]} : StoreT)) X =
  store_restrict σ X.
Proof.
  intros Hx.
  change ((storeA_restrict
    (@union (gmap atom value) _ (σ : gmap atom value)
      ({[x := v]} : gmap atom value)) X : gmap atom value) =
    storeA_restrict (σ : gmap atom value) X).
  apply storeA_restrict_union_singleton_ignore_r. exact Hx.
Qed.

Lemma store_lookup_eq_of_restrict_eq
    (σ1 σ2 : StoreT) X x :
  x ∈ X ->
  store_restrict σ1 X = store_restrict σ2 X ->
  σ1 !! x = σ2 !! x.
Proof.
  intros Hx Heq.
  eapply storeA_lookup_eq_of_restrict_eq; [exact Hx|exact Heq].
Qed.

Lemma store_lookup_eq_of_restrict_eq_full
    (σbig σsmall : StoreT) X x :
  x ∈ X ->
  store_restrict σbig X = σsmall ->
  σbig !! x = σsmall !! x.
Proof.
  intros Hx Heq.
  eapply storeA_lookup_eq_of_restrict_eq_full; [exact Hx|exact Heq].
Qed.

Lemma store_restrict_obs_result_eq
    (σv σbase σbig : StoreT) Dsmall Dobs Xbase y v :
  Dobs ⊆ Dsmall ->
  lvars_fv Dobs ⊆ Xbase ->
  store_restrict σv (lvars_fv Dsmall) =
    store_restrict σbase (lvars_fv Dsmall) ->
  store_restrict σbase Xbase =
    store_restrict σbig Xbase ->
  σv !! y = Some v ->
  σbig !! y = Some v ->
  store_restrict σv (lvars_fv Dobs ∪ {[y]}) =
    store_restrict σbig (lvars_fv Dobs ∪ {[y]}).
Proof.
  intros HDobs Hobs_base.
  eapply storeA_restrict_obs_result_eq.
  - intros a Ha.
    apply lvars_fv_elem.
    apply HDobs.
    apply lvars_fv_elem. exact Ha.
  - exact Hobs_base.
Qed.

Lemma notin_store_union_singleton_dom
    (σ : StoreT) x vx z :
  z ∉ dom (σ : StoreT) ->
  z <> x ->
  z ∉ dom (((σ : StoreT) ∪ ({[x := vx]} : StoreT)) : StoreT).
Proof.
  apply map_notin_union_singleton_dom.
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
  apply storeA_restrict_insert_same_observed.
  exact Heq.
Qed.

Lemma store_restrict_insert_union_eq_of_restrict_eq
    (σ1 σ2 : StoreT) X z (v : value) :
  z ∉ X ->
  store_restrict σ1 X = store_restrict σ2 X ->
  store_restrict (<[z := v]> σ1) (X ∪ {[z]}) =
  store_restrict (<[z := v]> σ2) (X ∪ {[z]}).
Proof.
  intros HzX Heq.
  change (storeA_restrict (<[z := v]> (σ1 : gmap atom value)) (X ∪ {[z]}) =
    storeA_restrict (<[z := v]> (σ2 : gmap atom value)) (X ∪ {[z]})).
  eapply storeA_restrict_insert_union_eq_of_restrict_eq; [exact HzX|exact Heq].
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
  change (storeA_restrict (<[z := v]> (σ : gmap atom value)) Z =
    storeA_restrict
      (<[z := v]> (storeA_restrict (σ : gmap atom value) X)) Z).
  eapply storeA_restrict_insert_agree_on_observed;
    [exact HZX|exact Hzσ|exact HzX].
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
  apply ContextAlgebra.ResourceInterfaceFacts.res_extend_rel_store_dom.
Qed.

Lemma opened_world_dom_contains_slot
    (m my : WfWorldT) y :
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  y ∈ world_dom (my : WorldT).
Proof.
  intros Hdom.
  exact (ContextAlgebra.ResourceInterfaceFacts.opened_world_dom_contains_slot
    m my y Hdom).
Qed.

Lemma fvar_in_singleton_restrict_dom
    (m my : WfWorldT) (σ : StoreT) x y :
  x ∈ world_dom (m : WorldT) ->
  (my : WorldT) σ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value).
Proof.
  intros Hxm Hσ Hdom.
  exact (ContextAlgebra.ResourceInterfaceFacts.fvar_in_singleton_restrict_dom
    m my σ x y Hxm Hσ Hdom).
Qed.

Lemma notin_union_singleton_of_notin_world
    (A : aset) x y (m : WfWorldT) :
  y ∉ A ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  y ∉ A ∪ {[x]}.
Proof.
  apply gset_notin_union_singleton_of_notin_superset.
Qed.

Lemma notin_union_singleton_swap_ne (A : aset) a x y :
  a ∉ A ∪ {[y]} ->
  a <> x ->
  a ∉ A ∪ {[x]}.
Proof.
  apply gset_notin_union_singleton_swap_ne.
Qed.

Lemma singleton_subset_world_dom (m : WfWorldT) z :
  z ∈ world_dom (m : WorldT) ->
  ({[z]} : aset) ⊆ world_dom (m : WorldT).
Proof.
  apply ContextAlgebra.ResourceInterfaceFacts.singleton_subset_world_dom.
Qed.

Lemma lty_env_insert_free_fresh
    (Σ : gmap logic_var ty) x z T :
  z <> x ->
  LVFree z ∉ dom Σ ->
  LVFree z ∉ dom (<[LVFree x := T]> Σ).
Proof.
  apply ContextTypeLanguage.LtyEnv.lty_env_insert_free_fresh.
Qed.

Lemma value_open_result_alias_fresh vf τ y z :
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty τ ->
  z ∉ fv_value vf ∪ {[y]} ∪ fv_cty (cty_open 0 y τ).
Proof.
  apply ContextBasicDenotation.RelevantEnvRegular.value_open_result_alias_fresh.
Qed.

Lemma cty_open_fresh_notin τ y z :
  z ∉ fv_cty τ ∪ {[y]} ->
  z ∉ fv_cty (cty_open 0 y τ).
Proof.
  apply ContextTypeLanguage.SyntaxRegular.cty_open_fresh_notin.
Qed.

Lemma wfworld_closed_on_open_world_from_base
    (m my : WfWorldT) X :
  X ⊆ world_dom (m : WorldT) ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  wfworld_closed_on X m ->
  wfworld_closed_on X my.
Proof.
  apply ContextBasicDenotation.StoreTyping.wfworld_closed_on_open_world_from_base.
Qed.

Lemma wfworld_closed_on_store_restrict_closed
    X (m : WfWorldT) (σ : StoreT) :
  wfworld_closed_on X m ->
  (m : WorldT) σ ->
  store_closed (store_restrict σ X).
Proof.
  apply ContextBasicDenotation.StoreTyping.wfworld_closed_on_store_restrict_closed.
Qed.

Lemma wfworld_eq_by_dom_stores (m n : WfWorldT) :
  world_dom (m : WorldT) = world_dom (n : WorldT) ->
  (forall σ, (m : WorldT) σ <-> (n : WorldT) σ) ->
  m = n.
Proof.
  apply ContextAlgebra.ResourceInterfaceFacts.wfworld_eq_by_dom_stores.
Qed.

Ltac denotation_set_norm :=
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in *;
  rewrite ?dom_insert_L, ?dom_union_L, ?dom_singleton_L in *.

Ltac denotation_set_solve :=
  denotation_set_norm; better_set_solver!!.

Ltac soundness_fresh_norm :=
  denotation_set_norm;
  rewrite ?dom_empty_L, ?dom_singleton_L in *.

Ltac soundness_fresh_solve :=
  soundness_fresh_norm; better_set_solver.

Ltac denotation_store_norm :=
  rewrite ?storeA_restrict_twice_subset in * by better_set_solver!!.

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
