(** * Logic-variable keyed stores

    This file collects the store facts that are specific to [logic_var] keys
    but independent of the stored value type.  Type-language environments are
    just the [V := ty] instance of these definitions. *)

From LocallyNameless Require Import Classes.
From ContextBase Require Import LogicVar LogicVarOpenEnv LogicVarShift BaseTactics.
From ContextStore Require Import StoreCore.
From ContextStore Require Import StoreFilterMapKey.
From ContextStore Require Import StoreRestrict.

Section LVarStore.

Context {V : Type} `{ValueSig V}.

Local Notation AtomStore := (gmap atom V) (only parsing).
Local Notation LVarStore := (gmap logic_var V) (only parsing).

Definition lvar_store_bind (s : LVarStore) (v : V) : LVarStore :=
  <[LVBound 0 := v]> (lvar_store_shift s).

Lemma lvar_store_open_one_dom k x (s : LVarStore) :
  dom (lvar_store_open_one k x s) = lvars_open k x (dom s).
Proof.
  unfold lvar_store_open_one.
  change (dom (storeA_rekey (logic_var_open k x) s : gmap logic_var V) =
    lvars_open k x (dom (s : gmap logic_var V))).
  rewrite storeA_rekey_dom by apply swap_inj.
  unfold set_swap.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [Hu HuD]]. exists u. split; [|exact HuD].
    exact Hu.
  - intros [u [Hu HuD]]. exists u. split; [|exact HuD].
    exact Hu.
Qed.

Lemma lvar_store_open_lvars_empty (s : LVarStore) :
  lvar_store_open_lvars ∅ s = s.
Proof.
  unfold lvar_store_open_lvars.
  apply storeA_map_eq. intros v.
  change ((storeA_rekey (logic_var_open_env ∅) s : gmap logic_var V) !! v =
    (s : gmap logic_var V) !! v).
  rewrite <- (logic_var_open_env_empty v) at 1.
  apply storeA_rekey_lookup.
  intros a b Hab. rewrite !logic_var_open_env_empty in Hab. exact Hab.
Qed.

Lemma lvar_store_open_lvars_singleton k x (s : LVarStore) :
  LVFree x ∉ dom s ->
  lvar_store_open_lvars (<[k := x]> ∅) s =
  lvar_store_open_one k x s.
Proof.
  intros Hfresh.
  unfold lvar_store_open_lvars, lvar_store_open_one.
  apply storeA_rekey_ext_on_dom. intros v Hv.
  apply logic_var_open_env_singleton_fresh.
  intros ->. apply Hfresh. exact Hv.
Qed.

Lemma lvar_store_open_lvars_open_one_empty k x (s : LVarStore) :
  LVFree x ∉ dom s ->
  lvar_store_open_lvars ∅ (lvar_store_open_one k x s) =
  lvar_store_open_lvars (<[k := x]> ∅) s.
Proof.
  intros Hfresh.
  rewrite lvar_store_open_lvars_empty.
  symmetry. apply lvar_store_open_lvars_singleton. exact Hfresh.
Qed.

Lemma lvar_store_open_one_bound0_singleton y A :
  lvar_store_open_one 0 y
    ((<[LVBound 0 := A]> (∅ : gmap logic_var V)) : LVarStore) =
  ((<[LVFree y := A]> (∅ : gmap logic_var V)) : LVarStore).
Proof.
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
  - replace (lvar_store_open_one 0 y (∅ : LVarStore)) with
      ((∅ : gmap logic_var V) : LVarStore).
    reflexivity.
    unfold lvar_store_open_one.
    apply (storeA_rekey_empty (V := V) (K := logic_var)
      (logic_var_open 0 y)).
  - unfold swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma lvar_store_open_one_succ_bound0_singleton k y A :
  lvar_store_open_one (S k) y
    ((<[LVBound 0 := A]> (∅ : gmap logic_var V)) : LVarStore) =
  ((<[LVBound 0 := A]> (∅ : gmap logic_var V)) : LVarStore).
Proof.
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open (S k) y (LVBound 0)) with (LVBound 0).
  - replace (lvar_store_open_one (S k) y (∅ : LVarStore)) with
      ((∅ : gmap logic_var V) : LVarStore).
    reflexivity.
    unfold lvar_store_open_one.
    apply (storeA_rekey_empty (V := V) (K := logic_var)
      (logic_var_open (S k) y)).
  - unfold swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma lvar_store_open_lvars_dom η (s : LVarStore) :
  open_env_fresh_for_lvars η (dom s) ->
  dom (lvar_store_open_lvars η s) =
  lvars_open_env η (dom s).
Proof.
  intros Hfresh.
  unfold lvar_store_open_lvars, lvars_open_env.
  change (dom (storeA_rekey (logic_var_open_env η) s : gmap logic_var V) =
    set_map (logic_var_open_env η) (dom (s : gmap logic_var V))).
  apply storeA_rekey_dom_inj_on.
  apply open_env_fresh_for_lvars_inj_on. exact Hfresh.
Qed.

Lemma lvar_store_open_lvars_lookup_fresh η v A (s : LVarStore) :
  s !! v = None ->
  open_env_fresh_for_lvars η (dom (<[v := A]> s)) ->
  lvar_store_open_lvars η s !! logic_var_open_env η v = None.
Proof.
  intros Hnone Hfresh.
  unfold lvar_store_open_lvars.
  change ((storeA_rekey (logic_var_open_env η) s : gmap logic_var V) !!
    logic_var_open_env η v = None).
  apply storeA_rekey_lookup_none_inj_on.
  - exact Hnone.
  - intros y Hy Heq.
    assert (Hinj := open_env_fresh_for_lvars_inj_on η
      (dom (<[v := A]> s)) Hfresh).
    assert (HyD : y ∈ dom (<[v := A]> (s : gmap logic_var V))).
    { better_set_solver. }
    assert (HvD : v ∈ dom (<[v := A]> (s : gmap logic_var V))).
    { better_set_solver. }
    pose proof (Hinj y v HyD HvD Heq) as ->.
    apply elem_of_dom in Hy as [U Hy].
    change ((s : gmap logic_var V) !! v = None) in Hnone.
    rewrite Hnone in Hy. discriminate.
Qed.

Lemma lvar_store_open_lvars_insert_entry η v A (s : LVarStore) :
  s !! v = None ->
  logic_var_open_env_inj_on η (dom (<[v := A]> s)) ->
  lvar_store_open_lvars η (<[v := A]> s) =
  <[logic_var_open_env η v := A]> (lvar_store_open_lvars η s).
Proof.
  intros Hnone Hinj.
  unfold lvar_store_open_lvars.
  apply storeA_rekey_insert_inj_on; exact Hnone || exact Hinj.
Qed.

Lemma lvar_store_open_lvars_insert_fresh η k x (s : LVarStore) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η) (dom s) ->
  lvar_store_open_lvars (<[k := x]> η) s =
  lvar_store_open_one k x (lvar_store_open_lvars η s).
Proof.
  intros Hη Havoid Hfresh.
  unfold lvar_store_open_lvars, lvar_store_open_one.
  assert (Hfreshη : open_env_fresh_for_lvars η (dom s)).
  { eapply open_env_fresh_for_lvars_insert_tail; eassumption. }
  assert (Hhead : x ∉ lvars_fv (lvars_open_env η (dom s))).
  { eapply open_env_fresh_for_lvars_insert_head; eassumption. }
  rewrite storeA_rekey_compose_inj_on.
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfreshη. }
  2:{ intros a b _ _ Hab. eapply swap_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v Hv.
  rewrite <- logic_var_open_env_open_fresh by eassumption.
  symmetry. apply logic_var_open_env_open_one_fresh.
  intros ->. apply Hhead. apply lvars_fv_open_env_free. exact Hv.
Qed.

Lemma lvar_store_open_lvars_insert_delete_swap_back
    η k y z (s : LVarStore) :
  η !! k = Some z ->
  y ∉ lvars_fv (dom s) ->
  z ∉ lvars_fv (dom s) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom s) ->
  lvar_store_swap y z
    (lvar_store_open_lvars (<[k := y]> (delete k η)) s) =
  lvar_store_open_lvars η s.
Proof.
  intros Hηk Hy Hz Havoid Hfresh.
  unfold lvar_store_swap, lvar_store_open_lvars.
  assert (Hybig : y ∉ lvars_fv ({[LVBound k]} ∪ dom s)).
  {
    intros Hbad.
    rewrite lvars_fv_union in Hbad.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply lvars_fv_elem in Hbad. better_set_solver.
    - exact (Hy Hbad).
  }
  assert (Hfresh_delete :
    open_env_fresh_for_lvars (delete k η)
      (lvars_open k y ({[LVBound k]} ∪ dom s))).
  {
    apply open_env_fresh_for_lvars_delete_open_fresh_atom; assumption.
  }
  assert (Hfresh_insert :
    open_env_fresh_for_lvars (<[k := y]> (delete k η))
      ({[LVBound k]} ∪ dom s)).
  {
    eapply open_env_fresh_for_lvars_insert_open_back.
    - rewrite lvars_bv_elem.
      apply elem_of_union_l.
      apply elem_of_singleton.
      reflexivity.
    - exact Hybig.
    - exact Hfresh_delete.
  }
  assert (Hfresh_insert_dom :
    open_env_fresh_for_lvars (<[k := y]> (delete k η)) (dom s)).
  {
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh_insert].
    better_set_solver.
  }
  rewrite storeA_rekey_compose_inj_on.
  - apply storeA_rekey_ext_on_dom. intros v Hv.
    apply logic_var_open_env_insert_delete_swap_back_on with
      (D := (dom s : lvset)); assumption.
  - apply open_env_fresh_for_lvars_inj_on. exact Hfresh_insert_dom.
  - intros a b _ _ Hab. eapply swap_inj. exact Hab.
Qed.

Lemma lvar_store_open_lvars_open_one η k x (s : LVarStore) :
  x ∉ lvars_fv (dom s) ->
  open_env_fresh_for_lvars η (dom (lvar_store_open_one k x s)) ->
  lvar_store_open_lvars η (lvar_store_open_one k x s) =
  lvar_store_open_lvars (<[k := x]> η) s.
Proof.
  intros Hx Hfresh.
  unfold lvar_store_open_lvars, lvar_store_open_one.
  rewrite storeA_rekey_compose_inj_on.
  2:{ intros a b _ _ Hab. eapply swap_inj. exact Hab. }
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
  apply storeA_rekey_ext_on_dom. intros v Hv.
  apply logic_var_open_env_open_one_fresh.
  intros ->. apply Hx. apply lvars_fv_elem. exact Hv.
Qed.

Lemma lvar_store_open_lvars_atom_swap x y η (s : LVarStore) :
  open_env_fresh_for_lvars η (dom (lvar_store_swap x y s)) ->
  lvar_store_open_lvars η (lvar_store_swap x y s) =
  lvar_store_swap x y
    (lvar_store_open_lvars (open_env_atom_swap x y η) s).
Proof.
  intros Hfresh.
  assert (HfreshΣ :
    open_env_fresh_for_lvars (open_env_atom_swap x y η) (dom s)).
  {
    apply open_env_fresh_for_lvars_atom_swap.
    rewrite <- lvar_store_swap_dom. exact Hfresh.
  }
  unfold lvar_store_open_lvars, lvar_store_swap.
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_open_env η) (logic_var_swap x y) s).
  2:{ intros a b _ _ Hab. eapply swap_inj. exact Hab. }
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_swap x y) (logic_var_open_env (open_env_atom_swap x y η)) s).
  2:{ apply open_env_fresh_for_lvars_inj_on. exact HfreshΣ. }
  2:{ intros a b _ _ Hab. eapply swap_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_env_atom_swap.
Qed.

Lemma lvar_store_to_atom_store_open_lvars_atom_swap x y η (s : LVarStore) :
  open_env_fresh_for_lvars η (dom (lvar_store_swap x y s)) ->
  lvar_store_to_atom_store (lvar_store_open_lvars η (lvar_store_swap x y s)) =
  (@storeA_swap V atom _ _ x y
    (lvar_store_to_atom_store
      (lvar_store_open_lvars (open_env_atom_swap x y η) s)) : gmap atom V).
Proof.
  intros Hfresh.
  rewrite lvar_store_open_lvars_atom_swap by exact Hfresh.
  apply lvar_store_to_atom_store_swap.
Qed.

Lemma lvar_to_atom_open_insert_delete_swap
    η k y z (s : LVarStore) :
  η !! k = Some z ->
  y ∉ lvars_fv (dom s) ->
  z ∉ lvars_fv (dom s) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom s) ->
  (@storeA_swap V atom _ _ y z
    (lvar_store_to_atom_store
      (lvar_store_open_lvars (<[k := y]> (delete k η)) s)) : gmap atom V) =
  lvar_store_to_atom_store (lvar_store_open_lvars η s).
Proof.
  intros Hηk HyΣ HzΣ Havoid Hfresh.
  rewrite <- lvar_store_to_atom_store_swap.
  f_equal.
  apply lvar_store_open_lvars_insert_delete_swap_back; assumption.
Qed.

Lemma logic_var_bv_elem_singleton v k :
  k ∈ lvars_bv ({[v]} : lvset) <-> v = LVBound k.
Proof.
  rewrite lvars_bv_elem, elem_of_singleton.
  split; intros Hv; [symmetry|symmetry]; exact Hv.
Qed.

Lemma logic_var_open_fresh_noop k x v :
  LVBound k <> v ->
  LVFree x <> v ->
  logic_var_open k x v = v.
Proof.
  intros Hk Hx.
  better_base_solver.
Qed.

Lemma lvar_store_open_one_fresh_noop k x (s : LVarStore) :
  LVBound k ∉ dom s ->
  LVFree x ∉ dom s ->
  lvar_store_open_one k x s = s.
Proof.
  intros Hk Hx.
  unfold lvar_store_open_one.
  change (storeA_swap (LVBound k) (LVFree x) s = s).
  apply storeA_swap_fresh; assumption.
Qed.

Lemma lvar_store_open_one_involutive k x (s : LVarStore) :
  lvar_store_open_one k x (lvar_store_open_one k x s) = s.
Proof.
  unfold lvar_store_open_one.
  change (storeA_swap (LVBound k) (LVFree x)
    (storeA_swap (LVBound k) (LVFree x) s) = s).
  apply storeA_swap_involutive.
Qed.

Lemma lvar_store_swap_open_one x y k (s : LVarStore) :
  lvar_store_swap x y (lvar_store_open_one k x s) =
  lvar_store_open_one k y (lvar_store_swap x y s).
Proof.
  unfold lvar_store_swap, lvar_store_open_one.
  rewrite (storeA_rekey_compose (logic_var_swap x y) (logic_var_open k x)).
  2:{ apply swap_inj. }
  2:{ intros a b Hab. eapply swap_inj. exact Hab. }
  rewrite (storeA_rekey_compose (logic_var_open k y) (logic_var_swap x y)).
  2:{ intros a b Hab. eapply swap_inj. exact Hab. }
  2:{ apply swap_inj. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_swap_open_one.
Qed.

Lemma lvar_store_open_one_insert_fresh k x v A (s : LVarStore) :
  logic_var_open k x v ∉ dom (lvar_store_open_one k x s) ->
  lvar_store_open_one k x (<[v := A]> s) =
  <[logic_var_open k x v := A]> (lvar_store_open_one k x s).
Proof.
  intros _. apply lvar_store_open_one_insert.
Qed.

Lemma lvar_store_open_one_shift_under j k x (s : LVarStore) :
  j <= k ->
  lvar_store_open_one (S (S k)) x (lvar_store_shift_from (S j) s) =
  lvar_store_shift_from (S j) (lvar_store_open_one (S k) x s).
Proof.
  intros Hjk. apply lvar_store_open_one_shift_under_gen. lia.
Qed.

Lemma lvar_store_lvars_open_shift_dom_gen j k x (s : LVarStore) :
  j <= k ->
  lvars_open (S k) x (lvars_shift_from j (dom s)) =
  lvars_shift_from j (lvars_open k x (dom s)).
Proof.
  apply lvars_open_shift_from_under_gen.
Qed.

Lemma lvar_store_lvars_open_shift_dom j k x (s : LVarStore) :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) (dom s)) =
  lvars_shift_from (S j) (lvars_open (S k) x (dom s)).
Proof.
  intros Hjk. apply lvar_store_lvars_open_shift_dom_gen. lia.
Qed.

Lemma lvar_store_open_one_shift_insert_bound k x A (s : LVarStore) :
  lvar_store_open_one (S k) x (lvar_store_shift (<[LVBound k := A]> s)) =
  lvar_store_shift (lvar_store_open_one k x (<[LVBound k := A]> s)).
Proof.
  rewrite lvar_store_shift_insert.
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open (S k) x (logic_var_shift_from 0 (LVBound k)))
    with (LVFree x).
  2:{
    cbn [logic_var_shift_from].
    destruct (decide (0 <= k)) as [_|Hbad]; [|lia].
    unfold swap. repeat destruct decide; try lia; try congruence.
  }
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open k x (LVBound k)) with (LVFree x).
  2:{
    unfold swap. repeat destruct decide; try lia; try congruence.
  }
  rewrite lvar_store_shift_insert_free.
  unfold lvar_store_shift.
  rewrite lvar_store_open_one_shift_under_gen by lia.
  reflexivity.
Qed.

Lemma lvars_bv_of_bvars (B : gset nat) :
  lvars_bv (lvars_of_bvars B) = B.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem.
  unfold lvars_of_bvars.
  rewrite elem_of_map.
  split.
  - intros [n [Heq Hn]]. inversion Heq. subst. exact Hn.
  - intros Hk. exists k. split; [reflexivity|exact Hk].
Qed.

Lemma lvars_bv_shift_from D k :
  lvars_bv (lvars_shift_from k D) =
  set_map (fun n => if decide (k <= n) then S n else n) (lvars_bv D).
Proof.
  apply lvars_shift_from_bv.
Qed.

Lemma lvar_store_bvar_scope_shift_open_noop k x (s : LVarStore) :
  LVBound k ∉ lvar_store_bvar_scope (lvar_store_shift s) ->
  lvars_open k x (lvar_store_bvar_scope (lvar_store_shift s)) =
  lvar_store_bvar_scope (lvar_store_shift s).
Proof.
  intros Hfresh.
  apply set_swap_fresh.
  - exact Hfresh.
  - unfold lvar_store_bvar_scope, lvars_of_bvars.
    intros Hin. apply elem_of_map in Hin as [n [Hbad _]].
    discriminate.
Qed.

Lemma lvar_store_bvar_scope_shift_open_one_noop k x (s : LVarStore) :
  LVBound k ∉ lvar_store_bvar_scope (lvar_store_shift s) ->
  LVFree x ∉ dom (lvar_store_shift s) ->
  lvar_store_bvar_scope (lvar_store_open_one k x (lvar_store_shift s)) =
  lvar_store_bvar_scope (lvar_store_shift s).
Proof.
  intros Hbound Hfree.
  unfold lvar_store_bvar_scope.
  f_equal.
  rewrite lvar_store_open_one_dom.
  apply set_eq. intros n.
  rewrite !lvars_bv_elem.
  rewrite set_swap_elem.
  unfold swap.
  destruct (decide (LVBound n = LVBound k)) as [Hnk|Hnk].
  - inversion Hnk. subst n.
    repeat destruct decide; try congruence.
    split; intros Hin; [exfalso; exact (Hfree Hin)|].
    exfalso. apply Hbound.
    unfold lvar_store_bvar_scope, lvars_of_bvars.
    apply elem_of_map. exists k. split; [reflexivity|].
    rewrite lvars_bv_elem. exact Hin.
  - repeat destruct decide; try congruence.
    reflexivity.
Qed.

Lemma lvar_store_bvar_scope_open_one_shift_under_result k x (s : LVarStore) :
  LVBound (S k) ∉ lvar_store_bvar_scope (lvar_store_shift s) ->
  LVFree x ∉ dom (lvar_store_shift s) ->
  lvar_store_bvar_scope (lvar_store_open_one (S k) x (lvar_store_shift s)) =
  lvar_store_bvar_scope (lvar_store_shift s).
Proof.
  apply lvar_store_bvar_scope_shift_open_one_noop.
Qed.

Lemma lvar_store_lvars_open_shift_union_bound0 k x D :
  lvars_open (S k) x (lvars_shift_from 0 D ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x D) ∪ {[LVBound 0]}.
Proof.
  unfold set_swap.
  rewrite set_map_union_L, set_map_singleton_L.
  pose proof (lvars_open_shift_from_under_gen 0 k x D ltac:(lia)) as Hshift.
  unfold set_swap in Hshift.
  rewrite Hshift.
  rewrite (swap_fresh (LVBound (S k)) (LVFree x) (LVBound 0)) by discriminate.
  reflexivity.
Qed.

Lemma lvar_store_lvars_open_shift_dom_union_bound0 k x (s : LVarStore) :
  lvars_open (S k) x (lvars_shift_from 0 (dom s) ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x (dom s)) ∪ {[LVBound 0]}.
Proof.
  apply lvar_store_lvars_open_shift_union_bound0.
Qed.

Lemma lvar_store_atom_dom_open_one k x (s : LVarStore) :
  lvar_store_atom_dom (lvar_store_open_one k x s) ⊆
  lvar_store_atom_dom s ∪ {[x]}.
Proof.
  unfold lvar_store_atom_dom.
  rewrite lvar_store_open_one_dom.
  apply lvars_fv_open_subset.
Qed.

Lemma lvar_store_bind_dom (s : LVarStore) A :
  dom (lvar_store_bind s A) =
  lvars_shift_from 0 (dom s) ∪ {[LVBound 0]}.
Proof.
  unfold lvar_store_bind, lvar_store_shift, lvar_store_shift_from.
  change (dom ((<[LVBound 0 := A]>
      (storeA_rekey (logic_var_shift_from 0) s) : LVarStore)
      : gmap logic_var V) =
    lvars_shift_from 0 (dom (s : gmap logic_var V)) ∪ {[LVBound 0]}).
  transitivity ({[LVBound 0]} ∪
    dom ((storeA_rekey (logic_var_shift_from 0) s : LVarStore)
      : gmap logic_var V)).
  { rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
      (((storeA_rekey (logic_var_shift_from 0) s : LVarStore)
        : gmap logic_var V)) (LVBound 0) A).
    reflexivity. }
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  unfold lvars_shift_from.
  better_set_solver.
Qed.

Lemma lvar_store_bind_atom_store_insert_dom
    (s : AtomStore) x Ax Ay :
  x ∉ dom s ->
  dom (lvar_store_bind (atom_store_to_lvar_store (<[x := Ax]> s)) Ay) =
  dom (lvar_store_bind (atom_store_to_lvar_store s) Ay) ∪
  {[LVFree x]}.
Proof.
  intros _.
  replace (atom_store_to_lvar_store (<[x := Ax]> s))
    with (<[LVFree x := Ax]> (atom_store_to_lvar_store s)).
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  rewrite !lvar_store_bind_dom.
  change (lvars_shift_from 0
      (dom ((<[LVFree x := Ax]> (atom_store_to_lvar_store s) : LVarStore)
        : gmap logic_var V)) ∪ {[LVBound 0]} =
    (lvars_shift_from 0
      (dom (atom_store_to_lvar_store s : gmap logic_var V)) ∪
      {[LVBound 0]}) ∪ {[LVFree x]}).
  rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
    (((atom_store_to_lvar_store s : LVarStore) : gmap logic_var V))
    (LVFree x) Ax).
  rewrite lvars_shift_from_union.
  replace (lvars_shift_from 0 ({[LVFree x]} : lvset)) with
    ({[LVFree x]} : lvset).
  2:{
    symmetry. apply lvars_shift_from_below_id.
    intros n Hn. apply lvars_bv_elem in Hn.
    rewrite elem_of_singleton in Hn. discriminate.
  }
  apply set_eq. intros v. better_set_solver.
Qed.

Lemma lvar_store_bind_lvars_fv_dom (s : LVarStore) A :
  lvars_fv (dom (lvar_store_bind s A)) = lvars_fv (dom s).
Proof.
  rewrite lvar_store_bind_dom.
  rewrite lvars_fv_union, lvars_shift_from_fv, lvars_fv_singleton_bound.
  better_set_solver.
Qed.

Lemma lvar_store_lvars_fv_dom_insert_free (s : LVarStore) x A :
  lvars_fv (dom (<[LVFree x := A]> s)) =
  {[x]} ∪ lvars_fv (dom s).
Proof.
  change (lvars_fv (dom ((<[LVFree x := A]> (s : gmap logic_var V)) :
    gmap logic_var V)) = {[x]} ∪ lvars_fv (dom (s : gmap logic_var V))).
  rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free.
  better_set_solver.
Qed.

Lemma lvar_store_lvars_fv_subset_insert_free_drop
    (D : lvset) (s : LVarStore) x A :
  LVFree x ∉ D ->
  D ⊆ dom (<[LVFree x := A]> s) ->
  lvars_fv D ⊆ lvars_fv (dom s).
Proof.
  intros Hfresh Hsub.
  eapply lvars_fv_subset_insert_free_drop; [exact Hfresh|].
  intros v Hv.
  specialize (Hsub v Hv).
  change (v ∈ dom ((<[LVFree x := A]> (s : gmap logic_var V)) :
    gmap logic_var V)) in Hsub.
  rewrite dom_insert_L in Hsub.
  exact Hsub.
Qed.

Lemma lvar_store_bind_atom_dom (s : LVarStore) A :
  lvar_store_atom_dom (lvar_store_bind s A) = lvar_store_atom_dom s.
Proof.
  unfold lvar_store_atom_dom.
  apply lvar_store_bind_lvars_fv_dom.
Qed.

Lemma lvar_store_insert_free_commute
    (s : LVarStore) x y Ax Ay :
  x <> y ->
  <[LVFree x := Ax]> (<[LVFree y := Ay]> s) =
  <[LVFree y := Ay]> (<[LVFree x := Ax]> s).
Proof.
  intros Hxy.
  apply (map_eq (M:=gmap logic_var)). intros z.
  change (((<[LVFree x := Ax]> (<[LVFree y := Ay]> (s : gmap logic_var V)))
            : gmap logic_var V) !! z =
          ((<[LVFree y := Ay]> (<[LVFree x := Ax]> (s : gmap logic_var V)))
            : gmap logic_var V) !! z).
  rewrite !lookup_insert.
  repeat case_decide; subst; try congruence; reflexivity.
Qed.

Lemma lvar_store_bind_insert_free
    (s : LVarStore) x Ax A :
  lvar_store_bind (<[LVFree x := Ax]> s) A =
  <[LVFree x := Ax]> (lvar_store_bind s A).
Proof.
  unfold lvar_store_bind.
  rewrite lvar_store_shift_insert_free.
  apply (map_eq (M := gmap logic_var)). intros z.
  change (((<[LVBound 0 := A]> (<[LVFree x := Ax]>
              (lvar_store_shift s : gmap logic_var V)))
            : gmap logic_var V) !! z =
          ((<[LVFree x := Ax]> (<[LVBound 0 := A]>
              (lvar_store_shift s : gmap logic_var V)))
            : gmap logic_var V) !! z).
  rewrite !lookup_insert.
  repeat case_decide; subst; try discriminate; reflexivity.
Qed.

Lemma lvar_store_union_insert_free_singleton
    (s : LVarStore) x y Ax Ay :
  x <> y ->
  LVFree x ∉ dom s ->
  ((@union (gmap logic_var V) _
      (<[LVFree y := Ay]> (s : gmap logic_var V))
      (<[LVFree x := Ax]> (∅ : gmap logic_var V))) : LVarStore) =
  <[LVFree y := Ay]> (<[LVFree x := Ax]> s).
Proof.
  intros Hxy HxΣ.
  change (<[LVFree x := Ax]> (∅ : gmap logic_var V))
    with ({[LVFree x := Ax]} : gmap logic_var V).
  rewrite storeA_union_singleton_insert_fresh.
  - apply lvar_store_insert_free_commute. exact Hxy.
  - rewrite dom_insert_L. better_set_solver.
Qed.

Lemma lvar_store_closed_insert_free (s : LVarStore) x A :
  lvar_store_closed s ->
  lvar_store_closed (<[LVFree x := A]> s).
Proof.
  intros Hclosed.
  unfold lvar_store_closed in *.
  intros [k|y] Hy; cbn [lc_logic_var_key]; [|exact I].
  change (LVBound k ∈ dom ((<[LVFree x := A]> (s : gmap logic_var V))
    : gmap logic_var V)) in Hy.
  rewrite dom_insert_L in Hy.
  apply elem_of_union in Hy as [Hy|Hy].
  - rewrite elem_of_singleton in Hy. discriminate.
  - exact (Hclosed (LVBound k) Hy).
Qed.

Lemma lvar_store_closed_lookup_bound_none (s : LVarStore) k :
  lvar_store_closed s ->
  s !! LVBound k = None.
Proof.
  intros Hclosed.
  change (((s : LVarStore) : gmap logic_var V) !! LVBound k = None).
  apply not_elem_of_dom. intros Hdom.
  unfold lvar_store_closed in Hclosed.
  exact (Hclosed (LVBound k) Hdom).
Qed.

Lemma lvar_store_shift_closed (s : LVarStore) :
  lvar_store_closed s ->
  lvar_store_shift s = s.
Proof.
  intros Hclosed.
  apply storeA_map_eq. intros v.
  destruct v as [k|x].
  - transitivity (@None V).
    + change (((lvar_store_shift s : LVarStore) : gmap logic_var V) !!
        LVBound k = None).
      apply not_elem_of_dom. intros Hdom.
      unfold lvar_store_shift, lvar_store_shift_from in Hdom.
      change (LVBound k ∈
        dom (storeA_rekey (logic_var_shift_from 0) s : gmap logic_var V))
        in Hdom.
      rewrite storeA_rekey_dom in Hdom by apply logic_var_shift_from_inj.
      apply elem_of_map in Hdom as [u [Hu Hudom]].
      destruct u as [n|y]; cbn [logic_var_shift_from] in Hu.
      * destruct (decide (0 <= n)) as [_|Hbad]; [|lia].
        inversion Hu. subst k.
        unfold lvar_store_closed in Hclosed.
        exact (Hclosed (LVBound n) Hudom).
      * discriminate.
    + symmetry. apply lvar_store_closed_lookup_bound_none. exact Hclosed.
  - unfold lvar_store_shift, lvar_store_shift_from.
    unfold kmap.
    change ((kmap (M2:=gmap logic_var) (logic_var_shift_from 0) s) !!
      LVFree x = (s : gmap logic_var V) !! LVFree x).
    change (LVFree x) with (logic_var_shift_from 0 (LVFree x)) at 1.
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj 0)
      (logic_var_shift_from 0) s (LVFree x)).
    reflexivity.
Qed.

Lemma lvar_store_to_atom_store_open_lvars_closed η (s : LVarStore) :
  lvar_store_closed s ->
  lvar_store_to_atom_store (lvar_store_open_lvars η s) =
  lvar_store_to_atom_store s.
Proof.
  intros Hclosed.
  assert (lvar_store_open_lvars η s = s) as ->; [|reflexivity].
  unfold lvar_store_open_lvars.
  assert (Hid : storeA_rekey (fun v : logic_var => v) s = s).
  {
    apply storeA_map_eq. intros z.
    change (((storeA_rekey (fun v : logic_var => v) s : LVarStore)
        : gmap logic_var V) !! z = (s : gmap logic_var V) !! z).
    change z with ((fun v : logic_var => v) z) at 1.
    exact (storeA_rekey_lookup (V:=V) (fun v : logic_var => v)
      ltac:(intros a b Hab; exact Hab) s z).
  }
  transitivity (storeA_rekey (fun v : logic_var => v) s).
  - apply storeA_rekey_ext_on_dom. intros v Hv.
    destruct v as [k|x]; cbn [logic_var_open_env]; [|reflexivity].
    exfalso.
    exact (Hclosed (LVBound k) Hv).
  - exact Hid.
Qed.

Lemma lvar_to_atom_open_insert_free_subset
    η (s : LVarStore) x A :
  LVFree x ∉ dom s ->
  open_env_fresh_for_lvars η (dom (<[LVFree x := A]> s)) ->
  lvar_store_to_atom_store (lvar_store_open_lvars η s) ⊆
  lvar_store_to_atom_store (lvar_store_open_lvars η (<[LVFree x := A]> s)).
Proof.
  intros Hxs Hfresh.
  apply map_subseteq_spec. intros a U Ha.
  apply lvar_store_to_atom_store_lookup_some in Ha as Ha_lv.
  rewrite lvar_store_open_lvars_insert_entry.
  - apply lvar_store_to_atom_store_lookup_free_some.
    destruct (decide (a = x)) as [->|Hax].
    + assert (Hnones : s !! LVFree x = None).
      {
        apply not_elem_of_dom_1.
        exact Hxs.
      }
      pose proof (lvar_store_open_lvars_lookup_fresh
        η (LVFree x) A s Hnones Hfresh) as Hnone.
      cbn [logic_var_open_env] in Hnone.
      change (((lvar_store_open_lvars η s : LVarStore)
        : gmap logic_var V) !! LVFree x = None) in Hnone.
      change (((lvar_store_open_lvars η s : LVarStore)
        : gmap logic_var V) !! LVFree x = Some U) in Ha_lv.
      rewrite Hnone in Ha_lv. discriminate.
    + change (((<[LVFree x := A]>
          ((lvar_store_open_lvars η s : LVarStore) : gmap logic_var V))
          : gmap logic_var V) !! LVFree a = Some U).
      rewrite lookup_insert.
      destruct (decide (LVFree x = LVFree a)) as [Heq|_].
      * inversion Heq. congruence.
      * exact Ha_lv.
  - change (((s : LVarStore) : gmap logic_var V) !! LVFree x = None).
    apply not_elem_of_dom_1.
    exact Hxs.
  - apply open_env_fresh_for_lvars_inj_on. exact Hfresh.
Qed.

Lemma lvar_store_bind_free_notin x (s : LVarStore) A :
  LVFree x ∉ dom s ->
  LVFree x ∉ dom (lvar_store_bind s A).
Proof.
  intros Hfresh Hin.
  rewrite lvar_store_bind_dom in Hin.
  apply elem_of_union in Hin as [Hin|Hin].
  - unfold lvars_shift_from in Hin.
    apply elem_of_map in Hin as [v [Hv HvD]].
    destruct v as [n|y]; cbn [logic_var_shift_from] in Hv.
    + destruct (decide (0 <= n)); discriminate.
    + inversion Hv. subst y. exact (Hfresh HvD).
  - rewrite elem_of_singleton in Hin. discriminate.
Qed.

Lemma logic_var_shift0_ne_bound0 v :
  logic_var_shift_from 0 v <> LVBound 0.
Proof.
  destruct v as [n|x]; cbn [logic_var_shift_from].
  - destruct (decide (0 <= n)) as [_|Hbad]; [discriminate|lia].
  - discriminate.
Qed.

Lemma open_env_shift0_lookup_zero_none η :
  open_env_shift_from 0 η !! 0 = None.
Proof.
  rewrite open_env_shift_from_zero.
  apply eq_None_not_Some. intros [x Hx].
  apply lookup_kmap_Some in Hx as [i [Hi _]].
  - lia.
  - intros i j Hij. lia.
Qed.

Lemma logic_var_open_env_shift0_bound0 η :
  logic_var_open_env (open_env_shift_from 0 η) (LVBound 0) = LVBound 0.
Proof.
  cbn [logic_var_open_env].
  rewrite open_env_shift0_lookup_zero_none. reflexivity.
Qed.

Lemma lvar_store_shift_lookup_bound0_none (s : LVarStore) :
  (lvar_store_shift s : gmap logic_var V) !! LVBound 0 = None.
Proof.
  apply not_elem_of_dom. intros Hin.
  unfold lvar_store_shift, lvar_store_shift_from in Hin.
  rewrite storeA_rekey_dom in Hin by apply logic_var_shift_from_inj.
  unfold lvars_shift_from in Hin.
  apply elem_of_map in Hin as [v [Hv _]].
  symmetry in Hv. exact (logic_var_shift0_ne_bound0 v Hv).
Qed.

Lemma logic_var_open_env_shift0_lvar_store_bind_inj_on η (s : LVarStore) A :
  open_env_fresh_for_lvars η (dom s) ->
  logic_var_open_env_inj_on (open_env_shift_from 0 η)
    (dom (<[LVBound 0 := A]> (lvar_store_shift s))).
Proof.
  intros Hfresh v1 v2 Hv1 Hv2 Heq.
  assert (Hfresh_shift :
    open_env_fresh_for_lvars (open_env_shift_from 0 η)
      (dom (lvar_store_shift s))).
  {
    unfold lvar_store_shift, lvar_store_shift_from.
    change (open_env_fresh_for_lvars (open_env_shift_from 0 η)
      (dom (storeA_rekey (logic_var_shift_from 0) s : gmap logic_var V))).
    rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
    change (open_env_fresh_for_lvars (open_env_shift_from 0 η)
      (lvars_shift_from 0 (dom (s : gmap logic_var V)))).
    apply open_env_shift_from_fresh_for_lvars. exact Hfresh.
  }
  change (v1 ∈ dom (<[LVBound 0 := A]> (lvar_store_shift s : gmap logic_var V))) in Hv1.
  change (v2 ∈ dom (<[LVBound 0 := A]> (lvar_store_shift s : gmap logic_var V))) in Hv2.
  rewrite dom_insert_L in Hv1, Hv2.
  apply elem_of_union in Hv1 as [Hv1|Hv1];
    apply elem_of_union in Hv2 as [Hv2|Hv2].
  - rewrite elem_of_singleton in Hv1.
    rewrite elem_of_singleton in Hv2. congruence.
  - rewrite elem_of_singleton in Hv1. subst v1.
    rewrite logic_var_open_env_shift0_bound0 in Heq.
    unfold lvar_store_shift, lvar_store_shift_from in Hv2.
    rewrite storeA_rekey_dom in Hv2 by apply logic_var_shift_from_inj.
    unfold lvars_shift_from in Hv2.
    apply elem_of_map in Hv2 as [v [Hv _]].
    subst v2.
    rewrite logic_var_open_env_shift_from in Heq.
    exfalso. symmetry in Heq. exact (logic_var_shift0_ne_bound0 _ Heq).
  - rewrite elem_of_singleton in Hv2. subst v2.
    rewrite logic_var_open_env_shift0_bound0 in Heq.
    unfold lvar_store_shift, lvar_store_shift_from in Hv1.
    rewrite storeA_rekey_dom in Hv1 by apply logic_var_shift_from_inj.
    unfold lvars_shift_from in Hv1.
    apply elem_of_map in Hv1 as [v [Hv _]].
    subst v1.
    rewrite logic_var_open_env_shift_from in Heq.
    exfalso. exact (logic_var_shift0_ne_bound0 _ Heq).
  - eapply open_env_fresh_for_lvars_inj_on; eassumption.
Qed.

Lemma lvar_store_bind_open_under k x (s : LVarStore) A :
  LVFree x ∉ dom s ->
  lvar_store_open_one (S k) x (lvar_store_bind s A) =
  lvar_store_bind (lvar_store_open_one k x s) A.
Proof.
  intros _.
  unfold lvar_store_bind.
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open (S k) x (LVBound 0)) with (LVBound 0).
  - unfold lvar_store_shift.
    rewrite lvar_store_open_one_shift_under_gen by lia.
    reflexivity.
  - unfold swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma lvar_store_bind_open_current y (s : LVarStore) A :
  LVFree y ∉ dom s ->
  lvar_store_closed s ->
  lvar_store_open_one 0 y (lvar_store_bind s A) =
  <[LVFree y := A]> s.
Proof.
  intros Hfresh Hclosed.
  unfold lvar_store_bind.
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
  2:{
    unfold swap. repeat destruct decide; try lia; try congruence.
  }
  rewrite lvar_store_shift_closed by exact Hclosed.
  rewrite lvar_store_open_one_fresh_noop.
  - reflexivity.
  - intros Hbound.
    unfold lvar_store_closed in Hclosed.
    exact (Hclosed (LVBound 0) Hbound).
  - exact Hfresh.
Qed.

Lemma lvar_store_open_bind_atom_store (s : AtomStore) A x :
  x ∉ dom s ->
  lvar_store_open_one 0 x
    (lvar_store_bind (atom_store_to_lvar_store s) A) =
  atom_store_to_lvar_store (<[x := A]> s).
Proof.
  intros Hx.
  unfold lvar_store_bind.
  rewrite lvar_store_open_one_bind_atom_store by exact Hx.
  rewrite <- atom_store_to_lvar_store_insert.
  reflexivity.
Qed.

Lemma lvar_store_bind_open_env_shift0 η (s : LVarStore) A :
  open_env_fresh_for_lvars η (dom s) ->
  lvar_store_open_lvars (open_env_shift_from 0 η) (lvar_store_bind s A) =
  lvar_store_bind (lvar_store_open_lvars η s) A.
Proof.
  intros Hfresh.
  unfold lvar_store_bind.
  rewrite (lvar_store_open_lvars_insert_entry
    (open_env_shift_from 0 η) (LVBound 0) A (lvar_store_shift s)).
  - rewrite logic_var_open_env_shift0_bound0.
    unfold lvar_store_shift.
    rewrite (lvar_store_open_lvars_shift_from (V:=V) 0 η s) by exact Hfresh.
    reflexivity.
  - apply lvar_store_shift_lookup_bound0_none.
  - apply logic_var_open_env_shift0_lvar_store_bind_inj_on. exact Hfresh.
Qed.

Lemma lvar_store_bind_open_env_lift η (s : LVarStore) A :
  open_env_fresh_for_lvars η (dom s) ->
  lvar_store_open_lvars ((kmap S η)) (lvar_store_bind s A) =
  lvar_store_bind (lvar_store_open_lvars η s) A.
Proof.
  intros Hfresh.
  rewrite <- open_env_shift_from_zero.
  apply lvar_store_bind_open_env_shift0. exact Hfresh.
Qed.

End LVarStore.
