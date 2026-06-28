(** * Generic stores: restriction lemmas *)

From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import StoreCore.

Section StoreRestrictCore.

Context {V : Type}.

Lemma storeA_restrict_dom {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) :
  dom (storeA_restrict s X) = dom s ∩ X.
Proof.
  unfold storeA_restrict. apply map_restrict_dom.
Qed.

Definition storeA_on_restrict {K : Type} `{Countable K}
    (D' : gset K) {D : gset K} (s : StoreAOn (V:=V) D)
    (Hsub : D' ⊆ D) : StoreAOn (V:=V) D'.
Proof.
  destruct s as [s Hdom].
  refine {| storeAO_store := storeA_restrict s D' |}.
  rewrite storeA_restrict_dom, Hdom. better_set_solver.
Defined.

Lemma storeA_restrict_lookup {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) (z : K) :
  ((storeA_restrict s X : gmap K V) !! z) =
  if decide (z ∈ X) then ((s : gmap K V) !! z) else None.
Proof.
  unfold storeA_restrict, map_restrict.
  destruct (decide (z ∈ X)) as [Hz|Hz].
  - destruct ((s : gmap K V) !! z) eqn:Hs.
    + apply map_lookup_filter_Some_2; [exact Hs | exact Hz].
    + apply map_lookup_filter_None. left. exact Hs.
  - apply map_lookup_filter_None. right. intros v _ Hin. contradiction.
Qed.

Lemma storeA_restrict_lookup_some_2 {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) (x : K) (y : V) :
  ((s : gmap K V) !! x) = Some y →
  x ∈ X →
  ((storeA_restrict s X : gmap K V) !! x) = Some y.
Proof.
  intros Hlookup Hin. rewrite storeA_restrict_lookup.
  destruct (decide (x ∈ X)) as [_|Hnot]; [exact Hlookup|contradiction].
Qed.

Lemma storeA_restrict_lookup_some {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) (x : K) (y : V) :
  ((storeA_restrict s X : gmap K V) !! x) = Some y →
  x ∈ X ∧ ((s : gmap K V) !! x) = Some y.
Proof.
  rewrite storeA_restrict_lookup.
  destruct (decide (x ∈ X)); intros Hlookup; [auto | discriminate].
Qed.

Lemma storeA_restrict_lookup_none_l {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) (z : K) :
  ((s : gmap K V) !! z) = None →
  ((storeA_restrict s X : gmap K V) !! z) = None.
Proof.
  intros Hlook. rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ X)); exact Hlook || reflexivity.
Qed.

Lemma storeA_restrict_fixed_union_piece {K : Type} `{Countable K}
    (Y X : gset K) (sall sfix : gmap K V) :
  dom (sall : gmap K V) ⊆ Y ->
  X ⊆ Y ->
  storeA_restrict sall X = sfix ->
  sall = storeA_restrict sfix Y ∪ storeA_restrict sall (Y ∖ X).
Proof.
  intros Hall HY Hfix.
  apply storeA_map_eq. intros a.
  destruct (decide (a ∈ X)) as [HaX|HaX].
  - assert (HaY : a ∈ Y) by set_solver.
    assert (Hfix_lookup :
        (storeA_restrict sall X : gmap K V) !! a =
        sfix !! a) by (rewrite Hfix; reflexivity).
    destruct (sall !! a) as [va|] eqn:Ha.
    + assert (Hσfixa : sfix !! a = Some va).
      {
        assert (Hr : (storeA_restrict sall X : gmap K V) !! a = Some va).
        { apply (storeA_restrict_lookup_some_2 _ _ _ _ Ha HaX). }
        rewrite Hr in Hfix_lookup. symmetry. exact Hfix_lookup.
      }
      symmetry. apply map_lookup_union_Some_raw. left.
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσfixa HaY).
    + assert (Hσfixa : sfix !! a = None).
      {
        assert (Hr : (storeA_restrict sall X : gmap K V) !! a = None).
        { apply storeA_restrict_lookup_none_l. exact Ha. }
        rewrite Hr in Hfix_lookup. symmetry. exact Hfix_lookup.
      }
      symmetry. apply map_lookup_union_None. split.
      * apply storeA_restrict_lookup_none_l. exact Hσfixa.
      * apply storeA_restrict_lookup_none_l. exact Ha.
  - destruct (decide (a ∈ Y)) as [HaY|HaY].
    + destruct (sall !! a) as [va|] eqn:Ha.
      * symmetry. apply map_lookup_union_Some_raw. right. split.
        -- apply storeA_restrict_lookup_none_l.
           apply not_elem_of_dom_1. intros Hσfix_dom.
           apply elem_of_dom in Hσfix_dom as [u Hσfixa].
           assert (Hr :
             (storeA_restrict sall X : gmap K V) !! a = Some u).
           { rewrite Hfix. exact Hσfixa. }
           apply storeA_restrict_lookup_some in Hr as [HaX' _].
           contradiction.
        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Ha). set_solver.
      * symmetry. apply map_lookup_union_None. split.
        -- apply storeA_restrict_lookup_none_l.
           apply not_elem_of_dom_1. intros Hσfix_dom.
           apply elem_of_dom in Hσfix_dom as [u Hσfixa].
           assert (Hr :
             (storeA_restrict sall X : gmap K V) !! a = Some u).
           { rewrite Hfix. exact Hσfixa. }
           apply storeA_restrict_lookup_some in Hr as [HaX' _].
           contradiction.
        -- apply storeA_restrict_lookup_none_l. exact Ha.
    + assert (Ha_none : sall !! a = None).
      {
        apply not_elem_of_dom_1.
        intros Hadom. apply HaY. apply Hall. exact Hadom.
      }
      rewrite Ha_none. symmetry. apply map_lookup_union_None. split.
      * apply storeA_restrict_lookup_none_l.
        apply not_elem_of_dom_1.
        intros Hσfix_dom.
        apply elem_of_dom in Hσfix_dom as [u Hσfixa].
        assert (Hr :
          (storeA_restrict sall X : gmap K V) !! a = Some u).
        { rewrite Hfix. exact Hσfixa. }
        apply storeA_restrict_lookup_some in Hr as [HaX' _].
        contradiction.
      * apply storeA_restrict_lookup_none_l. exact Ha_none.
Qed.

Lemma storeA_restrict_lookup_none_r {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) (z : K) :
  z ∉ X →
  ((storeA_restrict s X : gmap K V) !! z) = None.
Proof.
  intros Hnot. rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ X)); [contradiction | reflexivity].
Qed.

Lemma storeA_restrict_dom_subset {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) :
  dom (storeA_restrict s X : gmap K V) ⊆ X.
Proof.
  change (dom (storeA_restrict s X) ⊆ X).
  rewrite storeA_restrict_dom. better_set_solver.
Qed.


Lemma storeA_restrict_rekey {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) (s : gmap K V) (X : gset K) :
  (storeA_restrict (storeA_rekey f s) (set_map f X) : gmap K V) =
  storeA_rekey f (storeA_restrict s X).
Proof.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (storeA_rekey f s) (set_map f X) : gmap K V) !! z =
    (storeA_rekey f (storeA_restrict s X) : gmap K V) !! z).
  rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ set_map f X)) as [Hz|Hz].
  - apply elem_of_map in Hz as [u [-> Hu]].
    rewrite !storeA_rekey_lookup by exact Hf.
    rewrite storeA_restrict_lookup.
    destruct (decide (u ∈ X)) as [_|Hnot]; [reflexivity | contradiction].
  - transitivity (@None V).
    + reflexivity.
    + symmetry. apply not_elem_of_dom. intros Hdom.
      change (z ∈ dom (storeA_rekey f (storeA_restrict s X) : gmap K V)) in Hdom.
      rewrite storeA_rekey_dom in Hdom by exact Hf.
      apply elem_of_map in Hdom as [u [-> Hu]].
      apply storeA_restrict_dom_subset in Hu.
      apply Hz. apply elem_of_map. exists u. split; [reflexivity | exact Hu].
Qed.


Lemma storeA_restrict_empty {K : Type} `{Countable K} X :
  storeA_restrict (∅ : gmap K V) X = (∅ : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_idemp. better_set_solver.
Qed.


Lemma storeA_restrict_empty_set {K : Type} `{Countable K} (s : gmap K V) :
  storeA_restrict s ∅ = (∅ : gmap K V).
Proof.
  apply storeA_map_eq. intros z.
  change ((map_restrict V (s : gmap K V) (∅ : gset K)) !! z =
    (∅ : gmap K V) !! z).
  rewrite (lookup_empty (M:=gmap K) (A:=V)).
  unfold map_restrict.
  apply map_lookup_filter_None. right. intros v _ Hin. better_set_solver.
Qed.


Lemma storeA_restrict_idemp {K : Type} `{Countable K}
    (s : gmap K V) X :
  dom (s : gmap K V) ⊆ X → storeA_restrict s X = (s : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_idemp.
Qed.


Lemma storeA_restrict_restrict {K : Type} `{Countable K}
    (s : gmap K V) X Y :
  storeA_restrict (storeA_restrict s X) Y = (storeA_restrict s (X ∩ Y) : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_restrict.
Qed.


Lemma storeA_restrict_twice_same {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) :
  storeA_restrict (storeA_restrict s X) X = (storeA_restrict s X : gmap K V).
Proof.
  rewrite storeA_restrict_restrict.
  replace (X ∩ X) with X by better_set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_twice_subset {K : Type} `{Countable K}
    (s : gmap K V) (X Y : gset K) :
  Y ⊆ X →
  storeA_restrict (storeA_restrict s X) Y = (storeA_restrict s Y : gmap K V).
Proof.
  intros HYX.
  rewrite storeA_restrict_restrict.
  replace (X ∩ Y) with Y by better_set_solver.
  reflexivity.
Qed.

Lemma storeA_restrict_dom_intersection {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) :
  storeA_restrict s X =
  (storeA_restrict s (X ∩ dom (s : gmap K V)) : gmap K V).
Proof.
  apply storeA_map_eq. intros k.
  rewrite (storeA_restrict_lookup s X k).
  rewrite (storeA_restrict_lookup s (X ∩ dom (s : gmap K V)) k).
  destruct (decide (k ∈ X)) as [HkX|HkX].
  - destruct ((s : gmap K V) !! k) as [v|] eqn:Hk.
    + rewrite decide_True by
        (apply elem_of_intersection; split; [exact HkX|by apply elem_of_dom_2 in Hk]).
      reflexivity.
    + destruct (decide (k ∈ X ∩ dom (s : gmap K V))); reflexivity.
  - destruct (decide (k ∈ X ∩ dom (s : gmap K V))) as [Hbad|_].
    + apply elem_of_intersection in Hbad as [Hbad _]. contradiction.
    + reflexivity.
Qed.


Lemma storeA_restrict_comm {K : Type} `{Countable K}
    (s : gmap K V) (X Y : gset K) :
  storeA_restrict (storeA_restrict s X) Y =
  (storeA_restrict (storeA_restrict s Y) X : gmap K V).
Proof.
  rewrite !storeA_restrict_restrict.
  replace (X ∩ Y) with (Y ∩ X) by better_set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_idemp_eq {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) :
  dom (s : gmap K V) = X →
  storeA_restrict s X = (s : gmap K V).
Proof.
  intros Hdom. apply storeA_restrict_idemp. better_set_solver.
Qed.


Lemma storeA_restrict_insert_in {K : Type} `{Countable K}
    (s : gmap K V) X x v :
  x ∈ X →
  storeA_restrict (<[x := v]> s) X =
  <[x := v]> (storeA_restrict s X : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_insert_in.
Qed.


Lemma storeA_restrict_insert_notin {K : Type} `{Countable K}
    (s : gmap K V) X x v :
  x ∉ X →
  storeA_restrict (<[x := v]> s) X =
  (storeA_restrict s X : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_insert_notin.
Qed.

Lemma storeA_restrict_eq_mono {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X Y : gset K) :
  X ⊆ Y →
  (storeA_restrict s1 Y : gmap K V) = storeA_restrict s2 Y →
  (storeA_restrict s1 X : gmap K V) = storeA_restrict s2 X.
Proof.
  intros HXY HY.
  apply storeA_map_eq. intros x.
  change ((storeA_restrict s1 X : gmap K V) !! x =
    (storeA_restrict s2 X : gmap K V) !! x).
  rewrite !storeA_restrict_lookup.
  destruct (decide (x ∈ X)) as [Hx|Hx]; [|reflexivity].
  pose proof (f_equal (fun s : gmap K V => s !! x) HY) as HeqX.
  rewrite !storeA_restrict_lookup in HeqX.
  destruct (decide (x ∈ Y)) as [_|Hbad]; [exact HeqX | better_set_solver].
Qed.

Lemma storeA_restrict_swap_fresh {K : Type} `{Countable K} 
    (x y : K) (s : gmap K V) (X : gset K) :
  x ∉ X →
  y ∉ X →
  (storeA_restrict (storeA_swap x y s) X : gmap K V) =
  storeA_restrict s X.
Proof.
  intros Hx Hy. apply storeA_map_eq. intros z.
  destruct (decide (z ∈ X)) as [Hz | Hz].
  - destruct ((s : gmap K V) !! z) as [v|] eqn:Hs.
    + transitivity (Some v).
      * apply storeA_restrict_lookup_some_2; [| exact Hz].
        rewrite storeA_swap_lookup_inv.
        base_swap_normalize.
        exact Hs.
      * symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs Hz).
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l.
        rewrite storeA_swap_lookup_inv.
        base_swap_normalize. exact Hs.
      * symmetry. by apply storeA_restrict_lookup_none_l.
  - transitivity (@None V).
    + by apply storeA_restrict_lookup_none_r.
    + symmetry. by apply storeA_restrict_lookup_none_r.
Qed.


Lemma storeA_restrict_empty_union_elements {K : Type} `{Countable K}
    (σ : gmap K V) (X : gset K) :
  (storeA_restrict
    (@union (gmap K V) _ (∅ : gmap K V)
      (storeA_restrict σ (list_to_set (elements X) : gset K)))
    X : gmap K V) =
  storeA_restrict σ X.
Proof.
  replace (@union (gmap K V) _ (∅ : gmap K V)
      (storeA_restrict σ (list_to_set (elements X) : gset K)))
    with (storeA_restrict σ (list_to_set (elements X) : gset K) : gmap K V)
    by (symmetry; apply (map_empty_union (M:=gmap K) (A:=V))).
  rewrite storeA_restrict_restrict.
  replace ((list_to_set (elements X) : gset K) ∩ X) with X.
  - reflexivity.
  - apply set_eq. intros z.
    rewrite elem_of_intersection, elem_of_list_to_set, elem_of_elements.
    better_set_solver.
Qed.

Lemma storeA_restrict_lookup_transport {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) (x : K) (v : V) :
  x ∈ X →
  (storeA_restrict s1 X : gmap K V) = storeA_restrict s2 X →
  (s1 : gmap K V) !! x = Some v →
  (s2 : gmap K V) !! x = Some v.
Proof.
  intros Hx Heq Hlook.
  pose proof (f_equal (fun s : gmap K V => s !! x) Heq) as Heqx.
  change ((storeA_restrict s1 X : gmap K V) !! x =
    (storeA_restrict s2 X : gmap K V) !! x) in Heqx.
  assert ((storeA_restrict s1 X : gmap K V) !! x = Some v) as Hrx.
  { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook Hx). }
  rewrite Hrx in Heqx.
  symmetry in Heqx.
  apply storeA_restrict_lookup_some in Heqx as [_ Hlook2].
  exact Hlook2.
Qed.

Lemma storeA_lookup_eq_of_restrict_eq {K : Type} `{Countable K}
    (σ1 σ2 : gmap K V) (X : gset K) (x : K) :
  x ∈ X →
  (storeA_restrict σ1 X : gmap K V) = storeA_restrict σ2 X →
  σ1 !! x = σ2 !! x.
Proof.
  intros Hx Heq.
  apply option_eq. intros v. split; intros Hlook.
  - eapply storeA_restrict_lookup_transport; [exact Hx|exact Heq|exact Hlook].
  - eapply storeA_restrict_lookup_transport; [exact Hx|symmetry; exact Heq|exact Hlook].
Qed.

Lemma storeA_lookup_eq_of_restrict_eq_full {K : Type} `{Countable K}
    (σbig σsmall : gmap K V) (X : gset K) (x : K) :
  x ∈ X →
  (storeA_restrict σbig X : gmap K V) = σsmall →
  σbig !! x = σsmall !! x.
Proof.
  intros Hx Heq.
  eapply storeA_lookup_eq_of_restrict_eq; [exact Hx|].
  rewrite <- Heq.
  symmetry.
  apply storeA_restrict_twice_subset.
  set_solver.
Qed.

Lemma storeA_restrict_insert_same_observed {K : Type} `{Countable K}
    (σ1 σ2 : gmap K V) (X : gset K) (z : K) (v : V) :
  (storeA_restrict σ1 X : gmap K V) = storeA_restrict σ2 X →
  (storeA_restrict (<[z := v]> σ1) (X ∪ {[z]}) : gmap K V) =
  storeA_restrict (<[z := v]> σ2) (X ∪ {[z]}).
Proof.
  intros Heq.
  apply storeA_map_eq. intros a.
  destruct (decide (a = z)) as [->|Haz].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2;
        [apply map_lookup_insert|set_solver].
    + symmetry. apply storeA_restrict_lookup_some_2;
        [apply map_lookup_insert|set_solver].
  - destruct (decide (a ∈ X)) as [HaX|HaX].
    + pose proof (storeA_lookup_eq_of_restrict_eq σ1 σ2 X a HaX Heq)
        as Hlook_eq.
      destruct (σ1 !! a) as [va|] eqn:Hlook1.
      * assert (Hlook2 : σ2 !! a = Some va).
        { symmetry. exact Hlook_eq. }
        transitivity (Some va).
        -- apply storeA_restrict_lookup_some_2.
           ++ transitivity (σ1 !! a).
              ** apply map_lookup_insert_ne. congruence.
              ** exact Hlook1.
           ++ set_solver.
        -- symmetry. apply storeA_restrict_lookup_some_2.
           ++ transitivity (σ2 !! a).
              ** apply map_lookup_insert_ne. congruence.
              ** exact Hlook2.
           ++ set_solver.
      * assert (Hlook2 : σ2 !! a = None).
        { symmetry. exact Hlook_eq. }
        transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l.
           transitivity (σ1 !! a).
           ++ apply map_lookup_insert_ne. congruence.
           ++ exact Hlook1.
        -- symmetry. apply storeA_restrict_lookup_none_l.
           transitivity (σ2 !! a).
           ++ apply map_lookup_insert_ne. congruence.
           ++ exact Hlook2.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. set_solver.
      * symmetry. apply storeA_restrict_lookup_none_r. set_solver.
Qed.

Lemma storeA_restrict_insert_union_eq_of_restrict_eq {K : Type} `{Countable K}
    (σ1 σ2 : gmap K V) (X : gset K) (z : K) (v : V) :
  z ∉ X →
  (storeA_restrict σ1 X : gmap K V) = storeA_restrict σ2 X →
  (storeA_restrict (<[z := v]> σ1) (X ∪ {[z]}) : gmap K V) =
  storeA_restrict (<[z := v]> σ2) (X ∪ {[z]}).
Proof.
  intros _ Heq.
  apply storeA_restrict_insert_same_observed.
  exact Heq.
Qed.

Lemma storeA_restrict_insert_agree_on_observed {K : Type} `{Countable K}
    (σ : gmap K V) (X Z : gset K) (z : K) (v : V) :
  Z ⊆ X ∪ {[z]} →
  z ∉ dom σ →
  z ∉ X →
  (storeA_restrict (<[z := v]> σ) Z : gmap K V) =
  storeA_restrict (<[z := v]> (storeA_restrict σ X)) Z.
Proof.
  intros HZX _ HzX.
  transitivity
    (storeA_restrict (storeA_restrict (<[z := v]> σ) (X ∪ {[z]})) Z).
  - symmetry. apply storeA_restrict_twice_subset. exact HZX.
  - rewrite (storeA_restrict_insert_union_eq_of_restrict_eq
      σ (storeA_restrict σ X) X z v).
    + apply storeA_restrict_twice_subset. exact HZX.
    + exact HzX.
    + symmetry. apply storeA_restrict_twice_subset. set_solver.
Qed.

Lemma storeA_restrict_insert_agree_on_subset {K : Type} `{Countable K}
    (σ : gmap K V) (X Y : gset K) (z : K) (v : V) :
  Y ⊆ X →
  z ∉ dom σ →
  z ∉ X →
  (storeA_restrict (<[z := v]> σ) (Y ∪ {[z]}) : gmap K V) =
  storeA_restrict (<[z := v]> (storeA_restrict σ X)) (Y ∪ {[z]}).
Proof.
  intros HYX Hzσ HzX.
  apply storeA_restrict_insert_agree_on_observed; set_solver.
Qed.

Lemma storeA_restrict_obs_result_eq {K : Type} `{Countable K}
    (σv σbase σbig : gmap K V) Dsmall Dobs Xbase y v :
  Dobs ⊆ Dsmall ->
  Dobs ⊆ Xbase ->
  (storeA_restrict σv Dsmall : gmap K V) =
    storeA_restrict σbase Dsmall ->
  (storeA_restrict σbase Xbase : gmap K V) =
    storeA_restrict σbig Xbase ->
  σv !! y = Some v ->
  σbig !! y = Some v ->
  (storeA_restrict σv (Dobs ∪ {[y]}) : gmap K V) =
    storeA_restrict σbig (Dobs ∪ {[y]}).
Proof.
  intros HDobs Hobs_base Hv_base Hbase_big Hyv Hybig.
  apply storeA_map_eq. intros a.
  destruct (decide (a ∈ Dobs ∪ {[y]})) as [Ha|Ha].
  2:{
    rewrite !storeA_restrict_lookup_none_r by exact Ha.
    reflexivity.
  }
  rewrite !storeA_restrict_lookup.
  destruct (decide (a ∈ Dobs ∪ {[y]})) as [_|Hbad];
    [|contradiction].
  apply elem_of_union in Ha as [HaD|Hay].
  - assert (Ha_small : a ∈ Dsmall) by set_solver.
    assert (Ha_base : a ∈ Xbase) by set_solver.
    transitivity (σbase !! a).
    + eapply storeA_lookup_eq_of_restrict_eq; [exact Ha_small|exact Hv_base].
    + eapply storeA_lookup_eq_of_restrict_eq; [exact Ha_base|exact Hbase_big].
  - apply elem_of_singleton in Hay as ->.
    transitivity (Some v); [exact Hyv|symmetry; exact Hybig].
Qed.

Lemma storeA_restrict_swap {K : Type} `{Countable K} 
    (x y : K) (s : gmap K V) (X : gset K) :
  (storeA_restrict (storeA_swap x y s) (set_swap x y X) : gmap K V) =
  storeA_swap x y (storeA_restrict s X).
Proof.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (storeA_swap x y s) (set_swap x y X) : gmap K V) !! z =
    (storeA_swap x y (storeA_restrict s X) : gmap K V) !! z).
  rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ set_swap x y X)) as [Hz|Hz].
  - rewrite !storeA_swap_lookup_inv.
    rewrite elem_of_set_swap in Hz.
    destruct ((s : gmap K V) !! swap x y z) as [v|] eqn:Hs.
    + symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs Hz).
    + symmetry. apply storeA_restrict_lookup_none_l. exact Hs.
  - rewrite !storeA_swap_lookup_inv.
    symmetry. apply storeA_restrict_lookup_none_r.
    intros Hbad. apply Hz. rewrite elem_of_set_swap. exact Hbad.
Qed.

Lemma storeA_restrict_shift {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : gmap K V) (X : gset K) :
  (storeA_restrict (storeA_shift k s) (set_map (key_shift k) X) : gmap K V) =
  storeA_shift k (storeA_restrict s X).
Proof.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (storeA_shift k s) (set_map (key_shift k) X) : gmap K V)
      !! z =
    (storeA_shift k (storeA_restrict s X) : gmap K V) !! z).
  rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ set_map (key_shift k) X)) as [Hz|Hz].
  - apply elem_of_map in Hz as [u [Heq Hu]]. subst z.
    rewrite !storeA_shift_lookup.
    rewrite storeA_restrict_lookup.
    destruct (decide (u ∈ X)) as [_|Hnot]; [reflexivity | contradiction].
  - transitivity (@None V).
    + reflexivity.
    + symmetry. apply not_elem_of_dom.
      intros Hdom.
      change (z ∈ dom (storeA_shift k
        (storeA_restrict s X) : gmap K V)) in Hdom.
      pose proof (storeA_shift_dom (V:=V) (K:=K) k
        (storeA_restrict s X)) as Hdom_shift.
      change (dom (storeA_shift k
        (storeA_restrict s X) : gmap K V) =
        set_map (key_shift k)
          (dom (storeA_restrict s X : gmap K V))) in Hdom_shift.
      rewrite Hdom_shift in Hdom.
      apply elem_of_map in Hdom as [u [Heq Hdomu]]. subst z.
      apply storeA_restrict_dom_subset in Hdomu.
      apply Hz. apply elem_of_map. exists u. split; [reflexivity | exact Hdomu].
Qed.

End StoreRestrictCore.

(** ** Restriction/union lemmas *)

Section StoreRestrictUnion.

Context {V : Type}.

Lemma storeA_restrict_empty_union_elements_subset {K : Type} `{Countable K}
    (σ τ : gmap K V) (X F : gset K) :
  F ⊆ X →
  (storeA_restrict τ X : gmap K V) = σ →
  (storeA_restrict
    (storeA_restrict
      (@union (gmap K V) _ (∅ : gmap K V)
        (storeA_restrict τ (list_to_set (elements X) : gset K)))
      X)
    F : gmap K V) =
  storeA_restrict σ F.
Proof.
  intros HFX HτX.
  rewrite storeA_restrict_empty_union_elements.
  change (storeA_restrict (storeA_restrict τ X) F =
    storeA_restrict σ F).
  rewrite HτX.
  reflexivity.
Qed.

Lemma storeA_restrict_induce_disjoint {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  (s1 : gmap K V) ##ₘ
    (storeA_restrict s2 (dom (s2 : gmap K V) ∖ dom (s1 : gmap K V)) : gmap K V) ∧
  @union (gmap K V) _ s1 s2 =
  @union (gmap K V) _ s1
    (storeA_restrict s2 (dom (s2 : gmap K V) ∖ dom (s1 : gmap K V))).
Proof.
  pose (s2' := storeA_restrict s2
    (dom (s2 : gmap K V) ∖ dom (s1 : gmap K V))).
  split.
  - rewrite map_disjoint_alt. intros i.
    destruct (decide (i ∈ dom (s1 : gmap K V))) as [Hi|Hi].
    + right. unfold s2'.
      apply storeA_restrict_lookup_none_r. better_set_solver.
    + left. apply not_elem_of_dom. exact Hi.
  - apply storeA_map_eq. intros i.
    destruct ((s1 : gmap K V) !! i) as [v1|] eqn:H1.
    + transitivity ((s1 : gmap K V) !! i).
      * apply (lookup_union_l' (M:=gmap K) (A:=V)); eauto.
      * symmetry. apply (lookup_union_l' (M:=gmap K) (A:=V)); eauto.
    + rewrite !(lookup_union_r (M:=gmap K) (A:=V) _ _ _ H1).
      unfold s2'. rewrite storeA_restrict_lookup.
      destruct (decide (i ∈ dom (s2 : gmap K V) ∖ dom (s1 : gmap K V))) as [Hi|Hi].
      * reflexivity.
      * destruct ((s2 : gmap K V) !! i) as [v2|] eqn:H2; [|reflexivity].
        exfalso. apply Hi. apply elem_of_difference. split.
        -- by apply elem_of_dom_2 in H2.
        -- intros Hin%elem_of_dom. destruct Hin as [v1 Hbad]. congruence.
Qed.

Lemma storeA_restrict_union {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  storeA_compat s1 s2 →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) =
  @union (gmap K V) _ (storeA_restrict s1 X) (storeA_restrict s2 X).
Proof.
  intros _.
  apply storeA_map_eq. intros i.
  change ((storeA_restrict (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) X : gmap K V) !! i =
    (@union (gmap K V) _ (storeA_restrict s1 X : gmap K V)
      (storeA_restrict s2 X : gmap K V)) !! i).
  destruct (decide (i ∈ X)) as [HiX|HiX].
  - destruct ((s1 : gmap K V) !! i) as [v1|] eqn:H1.
    + transitivity (Some v1).
      * apply storeA_restrict_lookup_some_2; [|exact HiX].
        apply map_lookup_union_Some_raw. left. exact H1.
      * symmetry. apply map_lookup_union_Some_raw. left.
        apply (storeA_restrict_lookup_some_2 _ _ _ _ H1 HiX).
    + destruct ((s2 : gmap K V) !! i) as [v2|] eqn:H2.
      * transitivity (Some v2).
        -- apply storeA_restrict_lookup_some_2; [|exact HiX].
           rewrite (lookup_union_r (M:=gmap K) (A:=V) (s1 : gmap K V) (s2 : gmap K V) i H1).
           exact H2.
        -- symmetry. apply map_lookup_union_Some_raw. right.
           split; [apply storeA_restrict_lookup_none_l; exact H1|].
           apply (storeA_restrict_lookup_some_2 _ _ _ _ H2 HiX).
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l.
           rewrite (lookup_union_r (M:=gmap K) (A:=V) (s1 : gmap K V) (s2 : gmap K V) i H1).
           exact H2.
        -- symmetry. apply map_lookup_union_None.
           split; apply storeA_restrict_lookup_none_l; assumption.
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. exact HiX.
    + symmetry. apply map_lookup_union_None.
      split; apply storeA_restrict_lookup_none_r; exact HiX.
Qed.

Lemma storeA_restrict_union_cover {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X1 X2 : gset K) :
  storeA_compat s1 s2 →
  X1 ⊆ dom (s1 : gmap K V) →
  X2 ⊆ dom (s2 : gmap K V) →
  (storeA_restrict (@union (gmap K V) _ s1 s2) (X1 ∪ X2) : gmap K V) =
  @union (gmap K V) _ (storeA_restrict s1 X1) (storeA_restrict s2 X2).
Proof.
  intros Hcompat HX1 HX2.
  apply storeA_map_eq. intros i.
  change ((storeA_restrict (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) (X1 ∪ X2) : gmap K V) !! i =
    (@union (gmap K V) _ (storeA_restrict s1 X1 : gmap K V)
      (storeA_restrict s2 X2 : gmap K V)) !! i).
  destruct (decide (i ∈ X1)) as [Hi1 | Hni1].
  - specialize (HX1 i Hi1).
    apply elem_of_dom in HX1 as [v1 Hlookup1].
    transitivity (Some v1).
    + apply storeA_restrict_lookup_some_2; last better_set_solver.
      apply map_lookup_union_Some_raw. left. exact Hlookup1.
    + symmetry. apply map_lookup_union_Some_raw. left.
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlookup1 Hi1).
  - destruct (decide (i ∈ X2)) as [Hi2 | Hni2].
    + specialize (HX2 i Hi2).
      apply elem_of_dom in HX2 as [v2 Hlookup2].
      transitivity (Some v2).
      * apply storeA_restrict_lookup_some_2; last better_set_solver.
        destruct ((s1 : gmap K V) !! i) as [v1|] eqn:Hlookup1.
        -- apply map_lookup_union_Some_raw. left.
           pose proof (Hcompat _ _ _ Hlookup1 Hlookup2) as Heq.
           rewrite Heq in Hlookup1. exact Hlookup1.
        -- apply map_lookup_union_Some_raw. right. exact (conj Hlookup1 Hlookup2).
      * symmetry. apply map_lookup_union_Some_raw. right.
        split.
        -- apply storeA_restrict_lookup_none_r. exact Hni1.
        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlookup2 Hi2).
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. better_set_solver.
      * symmetry. apply map_lookup_union_None.
        split; apply storeA_restrict_lookup_none_r; assumption.
Qed.

Lemma storeA_restrict_union_same {K : Type} `{Countable K}
    (s : gmap K V) (X Y : gset K) :
  storeA_restrict s (X ∪ Y) =
  @union (gmap K V) _
    (storeA_restrict s X : gmap K V) (storeA_restrict s Y).
Proof.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict s (X ∪ Y) : gmap K V) !! z =
    (@union (gmap K V) _ (storeA_restrict s X : gmap K V)
      (storeA_restrict s Y : gmap K V)) !! z).
  destruct (decide (z ∈ X)) as [HzX|HzX].
  - destruct ((s : gmap K V) !! z) as [v|] eqn:Hz.
    + transitivity (Some v).
      * apply storeA_restrict_lookup_some_2; [exact Hz|set_solver].
      * symmetry. apply map_lookup_union_Some_raw. left.
        apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz HzX).
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l. exact Hz.
      * symmetry. apply map_lookup_union_None.
        split; apply storeA_restrict_lookup_none_l; exact Hz.
  - destruct (decide (z ∈ Y)) as [HzY|HzY].
    + rewrite (lookup_union_r (M:=gmap K) (A:=V)
        (storeA_restrict s X : gmap K V)
        (storeA_restrict s Y : gmap K V) z)
        by (apply storeA_restrict_lookup_none_r; exact HzX).
      destruct ((s : gmap K V) !! z) as [v|] eqn:Hz.
      * transitivity (Some v).
        -- apply storeA_restrict_lookup_some_2; [exact Hz|set_solver].
        -- symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz HzY).
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l. exact Hz.
        -- symmetry. apply storeA_restrict_lookup_none_l. exact Hz.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. set_solver.
      * symmetry. apply map_lookup_union_None.
        split; apply storeA_restrict_lookup_none_r; assumption.
Qed.

Lemma storeA_restrict_projection_dom {K : Type} `{Countable K}
    (s σ : gmap K V) (X : gset K) :
  storeA_restrict s X = σ ->
  storeA_restrict s (dom (σ : gmap K V)) = σ.
Proof.
  intros Hrestrict.
  subst σ.
  apply storeA_map_eq. intros z.
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ dom (storeA_restrict s X : gmap K V))) as [Hzdom|Hzdom];
    destruct (decide (z ∈ X)) as [HzX|HzX]; try reflexivity.
  - exfalso.
    pose proof (storeA_restrict_dom_subset s X z Hzdom). contradiction.
  - destruct ((s : gmap K V) !! z) as [v|] eqn:Hz; [|reflexivity].
    exfalso. apply Hzdom.
    apply elem_of_dom. exists v.
    apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz HzX).
Qed.

Lemma storeA_restrict_union_residual_l {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  storeA_compat s1 s2 ->
  @union (gmap K V) _
    (storeA_restrict s2 (X ∖ dom (s1 : gmap K V)))
    (storeA_restrict s1 X) =
  storeA_restrict (s1 ∪ s2) X.
Proof.
  intros _.
  apply storeA_map_eq. intros z.
  change ((@union (gmap K V) _
    (storeA_restrict s2 (X ∖ dom (s1 : gmap K V)) : gmap K V)
    (storeA_restrict s1 X : gmap K V)) !! z =
    (storeA_restrict (s1 ∪ s2) X : gmap K V) !! z).
  destruct (decide (z ∈ X)) as [HzX|HzX].
  - destruct ((s1 : gmap K V) !! z) as [v1|] eqn:Hs1.
    + transitivity (Some v1).
      * apply (proj2 (map_lookup_union_Some_raw
          (storeA_restrict s2 (X ∖ dom (s1 : gmap K V)) : gmap K V)
          (storeA_restrict s1 X : gmap K V) z v1)).
        right. split.
        -- apply storeA_restrict_lookup_none_r.
           apply elem_of_dom_2 in Hs1 as Hzdom.
           better_set_solver.
        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs1 HzX).
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HzX].
        apply (proj2 (map_lookup_union_Some_raw
          (s1 : gmap K V) (s2 : gmap K V) z v1)).
        left. exact Hs1.
    + destruct ((s2 : gmap K V) !! z) as [v2|] eqn:Hs2.
      * transitivity (Some v2).
        -- apply (proj2 (map_lookup_union_Some_raw
             (storeA_restrict s2 (X ∖ dom (s1 : gmap K V)) : gmap K V)
             (storeA_restrict s1 X : gmap K V) z v2)).
           left.
           apply storeA_restrict_lookup_some_2; [exact Hs2|].
           pose proof Hs1 as Hs1dom.
           apply not_elem_of_dom in Hs1dom.
           better_set_solver.
        -- symmetry. apply storeA_restrict_lookup_some_2; [|exact HzX].
           apply (proj2 (map_lookup_union_Some_raw
             (s1 : gmap K V) (s2 : gmap K V) z v2)).
           right. split; [exact Hs1 | exact Hs2].
      * transitivity (@None V).
        -- apply (proj2 (map_lookup_union_None
             (storeA_restrict s2 (X ∖ dom (s1 : gmap K V)) : gmap K V)
             (storeA_restrict s1 X : gmap K V) z)).
           split.
           ++ apply storeA_restrict_lookup_none_l. exact Hs2.
           ++ apply storeA_restrict_lookup_none_l. exact Hs1.
        -- symmetry. apply storeA_restrict_lookup_none_l.
           apply (proj2 (map_lookup_union_None
             (s1 : gmap K V) (s2 : gmap K V) z)).
           split; assumption.
  - transitivity (@None V).
    + apply (proj2 (map_lookup_union_None
        (storeA_restrict s2 (X ∖ dom (s1 : gmap K V)) : gmap K V)
        (storeA_restrict s1 X : gmap K V) z)).
      split; apply storeA_restrict_lookup_none_r;
        set_solver.
    + symmetry. apply storeA_restrict_lookup_none_r. exact HzX.
Qed.

Lemma storeA_restrict_insert_singleton {K : Type} `{Countable K}
    (σ : gmap K V) (x : K) (v : V) :
  (storeA_restrict (<[x := v]> σ) ({[x]} : gset K) : gmap K V) =
  ({[x := v]} : gmap K V).
Proof.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [better_map_solver | better_set_solver].
    + symmetry. better_map_solver.
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. better_set_solver.
    + symmetry. better_map_solver.
Qed.

Lemma storeA_restrict_singleton_lookup {K : Type} `{Countable K}
    (σ : gmap K V) (x : K) (v : V) :
  (σ : gmap K V) !! x = Some v →
  (storeA_restrict σ ({[x]} : gset K) : gmap K V) =
  ({[x := v]} : gmap K V).
Proof.
  intros Hlook.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook). better_set_solver.
    + symmetry. better_map_solver.
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. better_set_solver.
    + symmetry. better_map_solver.
Qed.

Lemma storeA_restrict_insert_singleton_ne {K : Type} `{Countable K}
    (σ : gmap K V) (x y : K) (v : V) :
  x ≠ y →
  (storeA_restrict (<[x := v]> σ) ({[y]} : gset K) : gmap K V) =
  storeA_restrict σ ({[y]} : gset K).
Proof.
  intros Hxy.
  rewrite storeA_restrict_insert_notin by better_set_solver.
  reflexivity.
Qed.

Lemma storeA_restrict_insert_fresh_union {K : Type} `{Countable K}
    (σ : gmap K V) (X : gset K) (x : K) (v : V) :
  (σ : gmap K V) !! x = None →
  x ∉ X →
  (storeA_restrict (<[x := v]> σ) (X ∪ {[x]}) : gmap K V) =
  <[x := v]> (storeA_restrict σ X : gmap K V).
Proof.
  intros _ Hx.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [better_map_solver | better_set_solver].
    + symmetry. better_map_solver.
  - change ((storeA_restrict (<[x := v]> (σ : gmap K V)) (X ∪ {[x]}) : gmap K V) !! z =
      (<[x := v]> (storeA_restrict σ X : gmap K V) : gmap K V) !! z).
    rewrite map_lookup_insert_ne by congruence.
    destruct (decide (z ∈ X)) as [HzX|HzX].
    + destruct ((σ : gmap K V) !! z) as [vz|] eqn:Hz.
      * transitivity (Some vz).
        -- apply storeA_restrict_lookup_some_2; [rewrite map_lookup_insert_ne by congruence; exact Hz | better_set_solver].
        -- symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz HzX).
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l. rewrite map_lookup_insert_ne by congruence. exact Hz.
        -- symmetry. apply storeA_restrict_lookup_none_l. exact Hz.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. better_set_solver.
      * symmetry. apply storeA_restrict_lookup_none_r. exact HzX.
Qed.

Lemma storeA_restrict_insert_union_none {K : Type} `{Countable K}
    (σ : gmap K V) (X : gset K) (x : K) (v : V) :
  (σ : gmap K V) !! x = None →
  x ∉ X →
  (<[x := v]> (storeA_restrict σ X : gmap K V) : gmap K V) !! x = Some v.
Proof.
  intros _ _.
  better_map_solver.
Qed.

Lemma storeA_restrict_union_singleton_insert {K : Type} `{Countable K}
    (σ : gmap K V) (X : gset K) (x : K) (v : V) :
  dom (σ : gmap K V) ⊆ X →
  x ∉ X →
  (storeA_restrict (@union (gmap K V) _ σ ({[x := v]} : gmap K V)) (X ∪ {[x]}) : gmap K V) =
  <[x := v]> (σ : gmap K V).
Proof.
  intros Hdom Hx.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [|better_set_solver].
      apply map_lookup_union_Some_raw. right. split.
      * apply not_elem_of_dom. better_set_solver.
      * better_map_solver.
    + symmetry. better_map_solver.
  - change ((storeA_restrict (@union (gmap K V) _ (σ : gmap K V) ({[x := v]} : gmap K V)) (X ∪ {[x]}) : gmap K V) !! z =
      (<[x := v]> (σ : gmap K V) : gmap K V) !! z).
    rewrite map_lookup_insert_ne by congruence.
    destruct ((σ : gmap K V) !! z) as [vz|] eqn:Hz.
    + transitivity (Some vz).
      * apply storeA_restrict_lookup_some_2; [apply map_lookup_union_Some_raw; left; exact Hz | apply elem_of_dom_2 in Hz; better_set_solver].
      * reflexivity.
    + transitivity (@None V); [|reflexivity].
      destruct (decide (z ∈ X ∪ {[x]})) as [HzX|HzX].
      * apply storeA_restrict_lookup_none_l.
        apply map_lookup_union_None. split; [exact Hz|].
        better_map_solver.
      * apply storeA_restrict_lookup_none_r. exact HzX.
Qed.

Lemma storeA_restrict_union_from_parts {K : Type} `{Countable K}
    (σ ρ σx : gmap K V) (S : gset K) (x : K) :
  x ∉ S →
  (storeA_restrict σ S : gmap K V) = ρ →
  (storeA_restrict σ ({[x]} : gset K) : gmap K V) = σx →
  (storeA_restrict σ (S ∪ {[x]}) : gmap K V) =
  @union (gmap K V) _ ρ σx.
Proof.
  intros Hx Hρ Hσx.
  rewrite <- Hρ, <- Hσx.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict σ (S ∪ {[x]}) : gmap K V) !! z =
    (@union (gmap K V) _ (storeA_restrict σ S : gmap K V)
      (storeA_restrict σ ({[x]} : gset K) : gmap K V)) !! z).
  destruct (decide (z ∈ S)) as [HzS|HzS].
  - destruct ((σ : gmap K V) !! z) as [vz|] eqn:Hz.
    + transitivity (Some vz).
      * apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz). better_set_solver.
      * symmetry. apply map_lookup_union_Some_raw. left.
        apply storeA_restrict_lookup_some_2; [exact Hz|exact HzS].
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l. exact Hz.
      * symmetry. apply map_lookup_union_None.
        split; apply storeA_restrict_lookup_none_l; exact Hz.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite (lookup_union_r (M:=gmap K) (A:=V)
        (storeA_restrict σ S : gmap K V)
        (storeA_restrict σ ({[x]} : gset K) : gmap K V) x)
        by (apply storeA_restrict_lookup_none_r; exact Hx).
      destruct ((σ : gmap K V) !! x) as [vx|] eqn:Hxlook.
      * transitivity (Some vx).
        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hxlook). better_set_solver.
        -- symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ Hxlook). better_set_solver.
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l. exact Hxlook.
        -- symmetry. apply storeA_restrict_lookup_none_l. exact Hxlook.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. better_set_solver.
      * symmetry. apply map_lookup_union_None.
        split; apply storeA_restrict_lookup_none_r; better_set_solver.
Qed.

Lemma storeA_eq_insert_of_restrict_singleton {K : Type} `{Countable K}
    (X : gset K) (σx σ : gmap K V) (ν : K) (vx : V) :
  dom (σx : gmap K V) = X ∪ {[ν]} →
  ν ∉ X →
  (storeA_restrict σx X : gmap K V) = σ →
  (storeA_restrict σx ({[ν]} : gset K) : gmap K V) = ({[ν := vx]} : gmap K V) →
  (σx : gmap K V) = <[ν := vx]> (σ : gmap K V).
Proof.
  intros Hdom Hν HX Hνsingle.
  apply storeA_map_eq. intros z.
  destruct (decide (z = ν)) as [->|Hzν].
  - rewrite map_lookup_insert.
    pose proof (f_equal (fun s : gmap K V => s !! ν) Hνsingle) as Hlook.
    rewrite map_lookup_singleton in Hlook.
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
  - rewrite map_lookup_insert_ne by congruence.
    destruct ((σx : gmap K V) !! z) as [vz|] eqn:Hz.
    + assert (z ∈ X) as HzX.
      { apply elem_of_dom_2 in Hz. rewrite Hdom in Hz. better_set_solver. }
      rewrite <- HX.
      symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz HzX).
    + rewrite <- HX.
      symmetry. apply storeA_restrict_lookup_none_l. exact Hz.
Qed.

Lemma storeA_restrict_union_partition {K : Type} `{Countable K}
    (s : gmap K V) (X Y : gset K) :
  dom (s : gmap K V) ⊆ X ∪ Y →
  X ∩ Y = ∅ →
  @union (gmap K V) _ (storeA_restrict s X) (storeA_restrict s Y) = s.
Proof.
  intros Hcover Hdisj.
  apply storeA_map_eq. intros z.
  change ((@union (gmap K V) _ (storeA_restrict s X : gmap K V)
    (storeA_restrict s Y : gmap K V)) !! z = (s : gmap K V) !! z).
  destruct (decide (z ∈ X)) as [HzX|HzX].
  - destruct ((s : gmap K V) !! z) as [v|] eqn:Hz.
    + apply map_lookup_union_Some_raw. left.
      apply (storeA_restrict_lookup_some_2 _ _ _ _ Hz HzX).
    + rewrite map_lookup_union_None. split; apply storeA_restrict_lookup_none_l; exact Hz.
  - rewrite (lookup_union_r (M:=gmap K) (A:=V)
      (storeA_restrict s X : gmap K V) (storeA_restrict s Y : gmap K V) z)
      by (apply storeA_restrict_lookup_none_r; exact HzX).
    destruct ((s : gmap K V) !! z) as [v|] eqn:Hz.
    + apply storeA_restrict_lookup_some_2; [exact Hz|].
      apply elem_of_dom_2 in Hz. better_set_solver.
    + apply storeA_restrict_lookup_none_l. exact Hz.
Qed.

Lemma storeA_restrict_union_piece_l {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X Y : gset K) :
  storeA_compat s1 s2 →
  dom (s1 : gmap K V) ⊆ X →
  dom (s2 : gmap K V) ⊆ Y →
  Y ∩ X = ∅ →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) = s1.
Proof.
  intros _ Hdom1 Hdom2 Hdisj.
  apply storeA_map_eq. intros z.
  destruct ((s1 : gmap K V) !! z) as [v1|] eqn:H1.
  - transitivity (Some v1).
    + apply storeA_restrict_lookup_some_2; [|apply elem_of_dom_2 in H1; better_set_solver].
      apply map_lookup_union_Some_raw. left. exact H1.
    + reflexivity.
  - transitivity (@None V); [|reflexivity].
    destruct (decide (z ∈ X)) as [HzX|HzX]; [|apply storeA_restrict_lookup_none_r; exact HzX].
    apply storeA_restrict_lookup_none_l.
    apply map_lookup_union_None. split; [exact H1|].
    apply not_elem_of_dom. intros Hz2. better_set_solver.
Qed.

Lemma storeA_restrict_union_piece_r {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X Y : gset K) :
  storeA_compat s1 s2 →
  dom (s1 : gmap K V) ⊆ X →
  dom (s2 : gmap K V) ⊆ Y →
  X ∩ Y = ∅ →
  (storeA_restrict (@union (gmap K V) _ s1 s2) Y : gmap K V) = s2.
Proof.
  intros Hcompat Hdom1 Hdom2 Hdisj.
  apply storeA_map_eq. intros z.
  destruct ((s2 : gmap K V) !! z) as [v2|] eqn:H2.
  - transitivity (Some v2).
    + apply storeA_restrict_lookup_some_2; [|apply elem_of_dom_2 in H2; better_set_solver].
      destruct ((s1 : gmap K V) !! z) as [v1|] eqn:H1.
      * assert (v1 = v2) by (eapply Hcompat; eauto). subst.
        apply map_lookup_union_Some_raw. left. exact H1.
      * apply map_lookup_union_Some_raw. right. eauto.
    + reflexivity.
  - transitivity (@None V); [|reflexivity].
    destruct (decide (z ∈ Y)) as [HzY|HzY]; [|apply storeA_restrict_lookup_none_r; exact HzY].
    apply storeA_restrict_lookup_none_l.
    apply map_lookup_union_None. split; [|exact H2].
    apply not_elem_of_dom. intros Hz1. better_set_solver.
Qed.

Lemma storeA_restrict_union_ignore_r {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  dom (s2 : gmap K V) ## X →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) =
  storeA_restrict s1 X.
Proof.
  intros Hdisj.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) X
    : gmap K V) !! z = (storeA_restrict s1 X : gmap K V) !! z).
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX | HzX]; [| reflexivity].
  destruct ((s1 : gmap K V) !! z) as [v|] eqn:Hs1.
  - rewrite (lookup_union_l' (s1 : gmap K V) (s2 : gmap K V) z) by eauto.
    rewrite Hs1. reflexivity.
  - rewrite (lookup_union_r (M:=gmap K) (A:=V)
      (s1 : gmap K V) (s2 : gmap K V) z) by exact Hs1.
    assert ((s2 : gmap K V) !! z = None) as Hs2.
      { apply not_elem_of_dom. intros Hz2. better_set_solver. }
    rewrite Hs2. reflexivity.
Qed.

Lemma storeA_restrict_union_singleton_ignore_r {K : Type} `{Countable K}
    (s : gmap K V) x (v : V) (X : gset K) :
  x ∉ X ->
  (storeA_restrict (@union (gmap K V) _ s ({[x := v]} : gmap K V)) X
    : gmap K V) =
  storeA_restrict s X.
Proof.
  intros Hx.
  apply storeA_restrict_union_ignore_r.
  rewrite dom_singleton_L. set_solver.
Qed.

Lemma lookup_union_singleton_r_eq {K : Type} `{Countable K}
    (s : gmap K V) x (u v : V) :
  s !! x = None ->
  (@union (gmap K V) _ s ({[x := u]} : gmap K V)) !! x = Some v ->
  u = v.
Proof.
  intros Hnone Hlook.
  rewrite (lookup_union_r (M:=gmap K) (A:=V)
    s ({[x := u]} : gmap K V) x Hnone) in Hlook.
  rewrite map_lookup_singleton in Hlook.
  inversion Hlook. reflexivity.
Qed.

Lemma storeA_restrict_union_absorb_l_on {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  storeA_compat s1 s2 →
  X ⊆ dom (s1 : gmap K V) →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) =
  storeA_restrict s1 X.
Proof.
  intros Hcompat Hsub.
  apply storeA_map_eq. intros z.
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX | HzX]; [| reflexivity].
  destruct ((s1 : gmap K V) !! z) as [v1|] eqn:H1.
  - rewrite (lookup_union_l' (s1 : gmap K V) (s2 : gmap K V) z) by eauto.
    rewrite H1. reflexivity.
  - exfalso.
    apply not_elem_of_dom in H1.
    apply H1. set_solver.
Qed.

Lemma storeA_restrict_union_absorb_r_on {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  storeA_compat s1 s2 →
  X ⊆ dom (s2 : gmap K V) →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) =
  storeA_restrict s2 X.
Proof.
  intros Hcompat Hsub.
  apply storeA_map_eq. intros z.
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX | HzX]; [| reflexivity].
  destruct ((s2 : gmap K V) !! z) as [v2|] eqn:H2.
  - destruct ((s1 : gmap K V) !! z) as [v1|] eqn:H1.
    + assert (v1 = v2) by (eapply Hcompat; eauto). subst.
      rewrite (lookup_union_l' (s1 : gmap K V) (s2 : gmap K V) z) by eauto.
      rewrite H1. reflexivity.
    + rewrite (lookup_union_r (M:=gmap K) (A:=V)
        (s1 : gmap K V) (s2 : gmap K V) z) by exact H1.
      rewrite H2. reflexivity.
  - exfalso.
    apply not_elem_of_dom in H2.
    apply H2. set_solver.
Qed.

Lemma storeA_restrict_union_ignore_l {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  dom (s1 : gmap K V) ## X →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) =
  storeA_restrict s2 X.
Proof.
  intros Hdisj.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) X
    : gmap K V) !! z = (storeA_restrict s2 X : gmap K V) !! z).
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX | HzX]; [| reflexivity].
  assert ((s1 : gmap K V) !! z = None) as Hs1.
  { apply not_elem_of_dom. intros Hz1. better_set_solver. }
  rewrite (lookup_union_r (M:=gmap K) (A:=V)
    (s1 : gmap K V) (s2 : gmap K V) z) by exact Hs1.
  reflexivity.
Qed.

Lemma storeA_restrict_union_absorb_r {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  storeA_compat s1 s2 →
  X ⊆ dom (s2 : gmap K V) →
  (storeA_restrict (@union (gmap K V) _ s1 s2) X : gmap K V) =
  storeA_restrict s2 X.
Proof.
  intros Hcompat Hsub.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (@union (gmap K V) _ (s1 : gmap K V) (s2 : gmap K V)) X
    : gmap K V) !! z = (storeA_restrict s2 X : gmap K V) !! z).
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ X)) as [HzX | HzX]; [| reflexivity].
  destruct ((s2 : gmap K V) !! z) as [v2|] eqn:Hs2.
  - destruct ((s1 : gmap K V) !! z) as [v1|] eqn:Hs1.
    + assert (v1 = v2) by (eapply Hcompat; eauto). subst.
      rewrite (lookup_union_l' (s1 : gmap K V) (s2 : gmap K V) z) by eauto.
      exact Hs1.
    + rewrite (lookup_union_r (M:=gmap K) (A:=V)
        (s1 : gmap K V) (s2 : gmap K V) z) by exact Hs1.
      exact Hs2.
  - exfalso.
    apply not_elem_of_dom in Hs2. apply Hs2. apply Hsub. exact HzX.
Qed.

Lemma storeA_restrict_union_frame_star {K : Type} `{Countable K}
    (s e1 e2 : gmap K V) (X1 X2 : gset K) :
  dom (s : gmap K V) ⊆ X1 ∪ X2 ->
  dom (s : gmap K V) ## dom (e1 : gmap K V) ->
  ((storeA_restrict s X1 ∪ e1) ∪
    (storeA_restrict s X2 ∪ e2) : gmap K V) =
  (s ∪ (e1 ∪ e2) : gmap K V).
Proof.
  intros Hcover Hdisj.
  apply storeA_map_eq. intros z.
  change ((((storeA_restrict s X1 : gmap K V) ∪ e1) ∪
    ((storeA_restrict s X2 : gmap K V) ∪ e2) : gmap K V) !! z =
    (s ∪ (e1 ∪ e2) : gmap K V) !! z).
  destruct ((s : gmap K V) !! z) as [v|] eqn:Hs.
  - assert (Hzdom : z ∈ dom (s : gmap K V)).
    { apply elem_of_dom_2 in Hs. exact Hs. }
    destruct (decide (z ∈ X1)) as [HzX1|HzX1].
    + transitivity (Some v).
      * apply map_lookup_union_Some_raw. left.
        apply map_lookup_union_Some_raw. left.
        apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs HzX1).
      * symmetry. apply map_lookup_union_Some_raw. left. exact Hs.
    + assert (HzX2 : z ∈ X2) by better_set_solver.
      assert (He1 : (e1 : gmap K V) !! z = None).
      { apply not_elem_of_dom. intros Hze1. better_set_solver. }
      transitivity (Some v).
      * apply map_lookup_union_Some_raw. right. split.
        -- apply map_lookup_union_None. split.
           ++ apply storeA_restrict_lookup_none_r. exact HzX1.
           ++ exact He1.
        -- apply map_lookup_union_Some_raw. left.
           apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs HzX2).
      * symmetry. apply map_lookup_union_Some_raw. left. exact Hs.
  - destruct ((e1 : gmap K V) !! z) as [v1|] eqn:He1.
    + transitivity (Some v1).
      * apply map_lookup_union_Some_raw. left.
        apply map_lookup_union_Some_raw. right. split.
        -- apply storeA_restrict_lookup_none_l. exact Hs.
        -- exact He1.
      * symmetry. apply map_lookup_union_Some_raw. right.
        split; [exact Hs|].
        apply map_lookup_union_Some_raw. left. exact He1.
    + destruct ((e2 : gmap K V) !! z) as [v2|] eqn:He2.
      * transitivity (Some v2).
        -- apply map_lookup_union_Some_raw. right. split.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_l. exact Hs.
              ** exact He1.
           ++ apply map_lookup_union_Some_raw. right. split.
              ** apply storeA_restrict_lookup_none_l. exact Hs.
              ** exact He2.
        -- symmetry. apply map_lookup_union_Some_raw. right.
           split; [exact Hs|].
           apply map_lookup_union_Some_raw. right. split; assumption.
      * transitivity (@None V).
        -- apply map_lookup_union_None. split.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_l. exact Hs.
              ** exact He1.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_l. exact Hs.
              ** exact He2.
        -- symmetry. apply map_lookup_union_None.
           split; [exact Hs|].
           apply map_lookup_union_None. split; assumption.
Qed.

Lemma storeA_restrict_union_frame_comma {K : Type} `{Countable K}
    (s e1 e2 : gmap K V) (X1 X2 D1 : gset K) :
  dom (s : gmap K V) ⊆ X1 ∪ (X2 ∖ D1) ->
  dom (e1 : gmap K V) = D1 ->
  dom (s : gmap K V) ## D1 ->
  ((storeA_restrict s X1 ∪ e1) ∪
    (storeA_restrict (s ∪ e1) X2 ∪ e2) : gmap K V) =
  (s ∪ (e1 ∪ e2) : gmap K V).
Proof.
  intros Hcover Hdom1 Hdisj.
  apply storeA_map_eq. intros z.
  change ((((storeA_restrict s X1 : gmap K V) ∪ e1) ∪
    ((storeA_restrict (s ∪ e1) X2 : gmap K V) ∪ e2) : gmap K V) !! z =
    (s ∪ (e1 ∪ e2) : gmap K V) !! z).
  destruct ((s : gmap K V) !! z) as [v|] eqn:Hs.
  - assert (Hzdom : z ∈ dom (s : gmap K V)).
    { apply elem_of_dom_2 in Hs. exact Hs. }
    destruct (decide (z ∈ X1)) as [HzX1|HzX1].
    + transitivity (Some v).
      * apply map_lookup_union_Some_raw. left.
        apply map_lookup_union_Some_raw. left.
        apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs HzX1).
      * symmetry. apply map_lookup_union_Some_raw. left. exact Hs.
    + assert (HzX2 : z ∈ X2) by better_set_solver.
      assert (He1 : (e1 : gmap K V) !! z = None).
      { apply not_elem_of_dom. intros Hze1. rewrite Hdom1 in Hze1.
        better_set_solver. }
      transitivity (Some v).
      * apply map_lookup_union_Some_raw. right. split.
        -- apply map_lookup_union_None. split.
           ++ apply storeA_restrict_lookup_none_r. exact HzX1.
           ++ exact He1.
        -- apply map_lookup_union_Some_raw. left.
           apply storeA_restrict_lookup_some_2; [|exact HzX2].
           rewrite (lookup_union_l' (s : gmap K V) e1 z) by eauto.
           exact Hs.
      * symmetry. apply map_lookup_union_Some_raw. left. exact Hs.
  - destruct ((e1 : gmap K V) !! z) as [v1|] eqn:He1.
    + transitivity (Some v1).
      * apply map_lookup_union_Some_raw. left.
        apply map_lookup_union_Some_raw. right. split.
        -- apply storeA_restrict_lookup_none_l. exact Hs.
        -- exact He1.
      * symmetry. apply map_lookup_union_Some_raw. right.
        split; [exact Hs|].
        apply map_lookup_union_Some_raw. left. exact He1.
    + destruct ((e2 : gmap K V) !! z) as [v2|] eqn:He2.
      * transitivity (Some v2).
        -- apply map_lookup_union_Some_raw. right. split.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_l. exact Hs.
              ** exact He1.
           ++ apply map_lookup_union_Some_raw. right. split.
              ** destruct (decide (z ∈ X2)) as [HzX2|HzX2].
                 --- apply storeA_restrict_lookup_none_l.
                     apply map_lookup_union_None. split; assumption.
                 --- apply storeA_restrict_lookup_none_r. exact HzX2.
              ** exact He2.
        -- symmetry. apply map_lookup_union_Some_raw. right.
           split; [exact Hs|].
           apply map_lookup_union_Some_raw. right. split; assumption.
      * transitivity (@None V).
        -- apply map_lookup_union_None. split.
           ++ apply map_lookup_union_None. split.
              ** apply storeA_restrict_lookup_none_l. exact Hs.
              ** exact He1.
           ++ apply map_lookup_union_None. split.
              ** destruct (decide (z ∈ X2)) as [HzX2|HzX2].
                 --- apply storeA_restrict_lookup_none_l.
                     apply map_lookup_union_None. split; assumption.
                 --- apply storeA_restrict_lookup_none_r. exact HzX2.
              ** exact He2.
        -- symmetry. apply map_lookup_union_None.
           split; [exact Hs|].
           apply map_lookup_union_None. split; assumption.
Qed.

Lemma storeA_restrict_union_base_singleton {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (D : gset K) (y : K) :
  D ⊆ dom (s1 : gmap K V) →
  dom (s2 : gmap K V) = D ∪ {[y]} →
  y ∉ dom (s1 : gmap K V) →
  (storeA_restrict s1 D : gmap K V) = storeA_restrict s2 D →
  (storeA_restrict (@union (gmap K V) _ s1
    (storeA_restrict s2 ({[y]} : gset K))) (D ∪ {[y]}) : gmap K V) = s2.
Proof.
  intros HDs1 Hdom2 Hy Hagree.
  apply storeA_map_eq. intros i.
  destruct (decide (i ∈ D)) as [HiD|HiD].
  - assert (i ∈ dom (s1 : gmap K V)) as Hi_s1 by better_set_solver.
    apply elem_of_dom in Hi_s1 as [v1 Hs1].
    assert (Hs1D : (storeA_restrict s1 D : gmap K V) !! i = Some v1).
    { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs1 HiD). }
    rewrite Hagree in Hs1D.
    apply storeA_restrict_lookup_some in Hs1D as [_ Hs2].
    transitivity (Some v1); [|symmetry; exact Hs2].
    apply storeA_restrict_lookup_some_2; last better_set_solver.
    apply map_lookup_union_Some_raw. left. exact Hs1.
  - destruct (decide (i = y)) as [->|Hiy].
    + destruct ((s2 : gmap K V) !! y) as [vy|] eqn:Hs2y.
      * transitivity (Some vy); [|reflexivity].
        apply storeA_restrict_lookup_some_2; last better_set_solver.
        apply map_lookup_union_Some_raw. right. split.
        -- by apply not_elem_of_dom.
	        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hs2y). better_set_solver.
      * assert (y ∈ dom (s2 : gmap K V)) by (rewrite Hdom2; better_set_solver).
        apply not_elem_of_dom in Hs2y. contradiction.
    + assert ((s2 : gmap K V) !! i = None) as Hi_none.
      { apply not_elem_of_dom. rewrite Hdom2. better_set_solver. }
      transitivity (@None V); [|symmetry; exact Hi_none].
      apply storeA_restrict_lookup_none_r. better_set_solver.
Qed.

Lemma storeA_restrict_union_base_project {K : Type} `{Countable K}
    (sbase sfull : gmap K V) (X : gset K) (y : K) :
  X ⊆ dom (sbase : gmap K V) ->
  dom (sfull : gmap K V) = dom (sbase : gmap K V) ∪ {[y]} ->
  y ∉ dom (sbase : gmap K V) ->
  (storeA_restrict sfull X : gmap K V) =
    storeA_restrict sbase X ->
  (storeA_restrict
    (@union (gmap K V) _ sbase
      (storeA_restrict sfull ({[y]} : gset K)))
    (X ∪ {[y]}) : gmap K V) =
  storeA_restrict sfull (X ∪ {[y]}).
Proof.
  intros HXsbase Hdomfull Hy Hagree.
  transitivity (storeA_restrict
    (@union (gmap K V) _ sbase
      (storeA_restrict
        (storeA_restrict sfull (X ∪ {[y]}) : gmap K V)
        ({[y]} : gset K)))
    (X ∪ {[y]})).
  - f_equal. f_equal.
    symmetry. apply storeA_restrict_twice_subset. better_set_solver.
  - apply storeA_restrict_union_base_singleton.
    + exact HXsbase.
    + pose proof (storeA_restrict_dom sfull (X ∪ {[y]})) as Hdom_restrict.
      change (dom (storeA_restrict sfull (X ∪ {[y]}) : gmap K V) =
        dom (sfull : gmap K V) ∩ (X ∪ {[y]})) in Hdom_restrict.
      rewrite Hdom_restrict, Hdomfull.
      apply set_eq. intros z. better_set_solver.
    + exact Hy.
    + rewrite storeA_restrict_twice_subset by better_set_solver.
      symmetry. exact Hagree.
Qed.

Lemma storeA_restrict_wand_product {K : Type} `{Countable K}
    (sn sm : gmap K V) (S X Y : gset K) :
  storeA_compat (storeA_restrict sn X) sm →
  storeA_compat sn (storeA_restrict sm S) →
  Y ⊆ S →
  Y ⊆ dom (sm : gmap K V) →
  (storeA_restrict (@union (gmap K V) _ sn (storeA_restrict sm S)) Y : gmap K V) =
  storeA_restrict (@union (gmap K V) _ (storeA_restrict sn X) sm) Y.
Proof.
  intros Hsmall Hfull HYS HYm.
  apply storeA_map_eq. intros i.
  destruct (decide (i ∈ Y)) as [HiY|HiY].
  - specialize (HYm i HiY).
    apply elem_of_dom in HYm as [vm Hsm].
    destruct ((sn : gmap K V) !! i) as [vn|] eqn:Hsn.
	    + assert ((storeA_restrict sm S : gmap K V) !! i = Some vm) as HsmS.
	      { apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsm). better_set_solver. }
	      pose proof (Hfull i vn vm Hsn HsmS) as Heq.
      rewrite Heq in Hsn.
      transitivity (Some vm).
      * apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply map_lookup_union_Some_raw. left. exact Hsn.
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
        destruct (decide (i ∈ X)) as [HiX|HiX].
        -- apply map_lookup_union_Some_raw. left.
           apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsn HiX).
        -- apply map_lookup_union_Some_raw. right. split.
           ++ apply storeA_restrict_lookup_none_r. exact HiX.
           ++ exact Hsm.
    + transitivity (Some vm).
      * apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply map_lookup_union_Some_raw. right. split.
        -- exact Hsn.
	        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsm). better_set_solver.
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply map_lookup_union_Some_raw. right. split.
        -- apply storeA_restrict_lookup_none_l. exact Hsn.
        -- exact Hsm.
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. exact HiY.
    + symmetry. apply storeA_restrict_lookup_none_r. exact HiY.
Qed.

Lemma storeA_restrict_product_frame_common {K : Type} `{Countable K}
    (sn sm : gmap K V) (X S C Y : gset K) :
  S ⊆ C ->
  Y ⊆ (X ∩ dom (sn : gmap K V)) ∪ (S ∩ dom (sm : gmap K V)) ->
  storeA_compat sn (storeA_restrict sm S) ->
  (storeA_restrict
    (@union (gmap K V) _ (storeA_restrict sn X : gmap K V)
      (storeA_restrict sm C : gmap K V)) Y : gmap K V) =
  storeA_restrict
    (@union (gmap K V) _ sn (storeA_restrict sm S : gmap K V)) Y.
Proof.
  intros HSC HY Hcompat.
  apply storeA_map_eq. intros i.
  destruct (decide (i ∈ Y)) as [HiY|HiY].
  - pose proof (HY i HiY) as Hcover.
    destruct (sn !! i) as [vn|] eqn:Hsn.
    + destruct (decide (i ∈ X)) as [HiX|HiX].
      * transitivity (Some vn).
        -- apply storeA_restrict_lookup_some_2; [|exact HiY].
           apply map_lookup_union_Some_raw. left.
           apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsn HiX).
        -- symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
           apply map_lookup_union_Some_raw. left. exact Hsn.
      * assert (HiSdom : i ∈ S ∩ dom (sm : gmap K V)) by set_solver.
        apply elem_of_intersection in HiSdom as [HiS Hism].
        apply elem_of_dom in Hism as [vm Hsm].
        pose proof (Hcompat i vn vm Hsn
          (storeA_restrict_lookup_some_2 sm S i vm Hsm HiS)) as Heq.
        subst vn.
        transitivity (Some vm).
        -- apply storeA_restrict_lookup_some_2; [|exact HiY].
           apply map_lookup_union_Some_raw. right. split.
           ++ apply storeA_restrict_lookup_none_r. exact HiX.
	           ++ apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsm). set_solver.
        -- symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
           apply map_lookup_union_Some_raw. left. exact Hsn.
    + assert (Hinot_sn : i ∉ dom (sn : gmap K V)).
      {
        intros Hin.
        apply elem_of_dom in Hin as [? Hlookup].
        rewrite Hsn in Hlookup. discriminate.
      }
      assert (HiSdom : i ∈ S ∩ dom (sm : gmap K V)) by set_solver.
      apply elem_of_intersection in HiSdom as [HiS Hism].
      apply elem_of_dom in Hism as [vm Hsm].
      transitivity (Some vm).
      * apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply map_lookup_union_Some_raw. right. split.
        -- apply storeA_restrict_lookup_none_l. exact Hsn.
	        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsm). set_solver.
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply map_lookup_union_Some_raw. right. split.
        -- exact Hsn.
        -- apply (storeA_restrict_lookup_some_2 _ _ _ _ Hsm HiS).
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. exact HiY.
    + symmetry. apply storeA_restrict_lookup_none_r. exact HiY.
Qed.

End StoreRestrictUnion.

(** ** Compatibility, bind, and union lemmas *)

Section StoreRestrictCompat.

Context {V : Type}.

Local Notation "s1 ≈A s2" := (storeA_compat s1 s2) (at level 70).

Lemma storeA_compat_refl {K : Type} `{Countable K} (s : gmap K V) :
  storeA_compat s s.
Proof.
  unfold storeA_compat, map_compat. intros x v1 v2 H1 H2. congruence.
Qed.


Lemma storeA_compat_sym {K : Type} `{Countable K} (s1 s2 : gmap K V) :
  storeA_compat s1 s2 → storeA_compat s2 s1.
Proof.
  unfold storeA_compat, map_compat.
  intros Hc x v1 v2 H1 H2. symmetry. eapply Hc; eauto.
Qed.

Lemma storeA_compat_swap {K : Type} `{Countable K} 
    (x y : K) (s1 s2 : gmap K V) :
  storeA_swap x y s1 ≈A storeA_swap x y s2 ↔
  s1 ≈A s2.
Proof.
  split.
  - intros Hc z v1 v2 H1 H2.
    pose proof (Hc (swap x y z) v1 v2) as Hc'.
    rewrite !storeA_swap_lookup in Hc'.
    exact (Hc' H1 H2).
  - intros Hc z v1 v2 H1 H2.
    rewrite storeA_swap_lookup_inv in H1.
    rewrite storeA_swap_lookup_inv in H2.
    exact (Hc _ _ _ H1 H2).
Qed.

Lemma storeA_compat_union_inv_l {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  @union (gmap K V) _ s1 s2 ≈A s3 →
  s1 ≈A s3.
Proof.
  unfold storeA_compat, map_compat.
  intros Hc i v1 v3 H1 H3.
  eapply Hc; [| exact H3].
  apply (proj2 (map_lookup_union_Some_raw
    (s1 : gmap K V) (s2 : gmap K V) i v1)).
  left. exact H1.
Qed.

Lemma storeA_compat_union_inv_r {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  s1 ≈A s2 →
  @union (gmap K V) _ s1 s2 ≈A s3 →
  s2 ≈A s3.
Proof.
  unfold storeA_compat, map_compat.
  intros H12 Hc i v2 v3 H2 H3.
  destruct ((s1 : gmap K V) !! i) as [v1|] eqn:H1.
  - transitivity v1.
    + symmetry. eapply H12; eauto.
    + eapply Hc; [| exact H3].
      apply (proj2 (map_lookup_union_Some_raw
        (s1 : gmap K V) (s2 : gmap K V) i v1)).
      left. exact H1.
  - eapply Hc; [| exact H3].
    apply (proj2 (map_lookup_union_Some_raw
      (s1 : gmap K V) (s2 : gmap K V) i v2)).
    right. split; [exact H1 | exact H2].
Qed.

Lemma storeA_compat_union_r_inv_l {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  s1 ≈A @union (gmap K V) _ s2 s3 →
  s1 ≈A s2.
Proof.
  unfold storeA_compat, map_compat.
  intros Hc i v1 v2 H1 H2.
  eapply Hc; [exact H1 |].
  apply (proj2 (map_lookup_union_Some_raw
    (s2 : gmap K V) (s3 : gmap K V) i v2)).
  left. exact H2.
Qed.

Lemma storeA_compat_union_r_inv_r {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  s2 ≈A s3 →
  s1 ≈A @union (gmap K V) _ s2 s3 →
  s1 ≈A s3.
Proof.
  unfold storeA_compat, map_compat.
  intros H23 Hc i v1 v3 H1 H3.
  destruct ((s2 : gmap K V) !! i) as [v2|] eqn:H2.
  - transitivity v2.
    + eapply Hc; [exact H1 |].
      apply (proj2 (map_lookup_union_Some_raw
        (s2 : gmap K V) (s3 : gmap K V) i v2)).
      left. exact H2.
    + eapply H23; eauto.
  - eapply Hc; [exact H1 |].
    apply (proj2 (map_lookup_union_Some_raw
      (s2 : gmap K V) (s3 : gmap K V) i v3)).
    right. split; [exact H2 | exact H3].
Qed.

Lemma storeA_compat_union_intro_r {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  s1 ≈A s2 →
  s1 ≈A s3 →
  s1 ≈A @union (gmap K V) _ s2 s3.
Proof.
  unfold storeA_compat, map_compat.
  intros H12 H13 i v1 v23 H1 H23.
  apply (proj1 (map_lookup_union_Some_raw
    (s2 : gmap K V) (s3 : gmap K V) i v23)) in H23.
  destruct H23 as [H2 | [H2none H3]].
  - eapply H12; eauto.
  - eapply H13; eauto.
Qed.

Lemma storeA_union_comm {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  s1 ≈A s2 →
  @union (gmap K V) _ s1 s2 = @union (gmap K V) _ s2 s1.
Proof.
  intros Hcompat. apply storeA_map_eq. intros i.
  rewrite option_eq. intros v.
  setoid_rewrite (map_lookup_union_Some_raw).
  split.
  - intros [H1 | [H1 H2]].
    + destruct ((s2 : gmap K V) !! i) as [v2|] eqn:H2.
      * left. assert (Hv : v = v2) by (eapply Hcompat; eauto). subst. reflexivity.
      * right. split; [reflexivity | exact H1].
    + left. exact H2.
  - intros [H2 | [H2 H1]].
    + destruct ((s1 : gmap K V) !! i) as [v1|] eqn:H1.
      * left. assert (Hv : v1 = v) by (eapply Hcompat; eauto). subst. reflexivity.
      * right. split; [reflexivity | exact H2].
    + left. exact H1.
Qed.

Lemma storeA_compat_union_intro_l {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  s1 ≈A s3 →
  s2 ≈A s3 →
  @union (gmap K V) _ s1 s2 ≈A s3.
Proof.
  intros H13 H23.
  apply storeA_compat_sym.
  apply storeA_compat_union_intro_r;
    apply storeA_compat_sym; assumption.
Qed.

Lemma storeA_union_swap_right {K : Type} `{Countable K}
    (s1 s2 s3 : gmap K V) :
  s2 ≈A s3 →
  @union (gmap K V) _ (@union (gmap K V) _ s1 s2) s3 =
  @union (gmap K V) _ (@union (gmap K V) _ s1 s3) s2.
Proof.
  intros Hcompat.
  rewrite <- !map_union_assoc.
  rewrite (storeA_union_comm s2 s3 Hcompat).
  reflexivity.
Qed.

Lemma storeA_union_extend_frame_r {K : Type} `{Countable K}
    (s1 s2 se : gmap K V) :
  se ≈A s2 →
  @union (gmap K V) _ (@union (gmap K V) _ s1 se) s2 =
  @union (gmap K V) _ (@union (gmap K V) _ s1 s2) se.
Proof.
  intros Hcompat.
  rewrite <- !map_union_assoc.
  rewrite (storeA_union_comm se s2 Hcompat).
  reflexivity.
Qed.

Lemma storeA_union_absorb_l {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  s1 ≈A s2 →
  dom (s2 : gmap K V) ⊆ dom (s1 : gmap K V) →
  @union (gmap K V) _ s1 s2 = s1.
Proof.
  intros _ Hsub. apply storeA_map_eq. intros i.
  destruct ((s1 : gmap K V) !! i) as [v1|] eqn:Hs1.
  - transitivity (Some v1).
    + apply (proj2 (map_lookup_union_Some_raw
        (s1 : gmap K V) (s2 : gmap K V) i v1)).
      left. exact Hs1.
    + reflexivity.
  - destruct ((s2 : gmap K V) !! i) as [v2|] eqn:Hs2.
    + exfalso.
      assert (Hin1 : i ∈ dom (s1 : gmap K V)).
      { apply Hsub. by apply elem_of_dom_2 in Hs2. }
      apply not_elem_of_dom in Hs1. contradiction.
    + transitivity (@None V).
      * apply (proj2 (map_lookup_union_None
          (s1 : gmap K V) (s2 : gmap K V) i)).
        split; assumption.
      * reflexivity.
Qed.

Lemma storeA_union_absorb_r {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  s1 ≈A s2 →
  dom (s1 : gmap K V) ⊆ dom (s2 : gmap K V) →
  @union (gmap K V) _ s1 s2 = s2.
Proof.
  intros Hcompat Hsub.
  rewrite storeA_union_comm by exact Hcompat.
  apply storeA_union_absorb_l.
  - apply storeA_compat_sym. exact Hcompat.
  - exact Hsub.
Qed.

Lemma storeA_union_absorb_restrict_r {K : Type} `{Countable K}
    (s : gmap K V) (X : gset K) :
  @union (gmap K V) _ s (storeA_restrict s X : gmap K V) = s.
Proof.
  apply storeA_map_eq. intros i.
  destruct ((s : gmap K V) !! i) as [v|] eqn:Hi.
  - rewrite (lookup_union_l' (M:=gmap K) (A:=V)
      (s : gmap K V) (storeA_restrict s X : gmap K V) i) by eauto.
    exact Hi.
  - rewrite (lookup_union_r (M:=gmap K) (A:=V)
      (s : gmap K V) (storeA_restrict s X : gmap K V) i Hi).
    apply storeA_restrict_lookup_none_l. exact Hi.
Qed.

Lemma storeA_union_absorb_prefix_r {K : Type} `{Countable K}
    (s t : gmap K V) :
  @union (gmap K V) _
    (@union (gmap K V) _ s t) s =
  @union (gmap K V) _ s t.
Proof.
  apply storeA_map_eq. intros i.
  destruct ((s : gmap K V) !! i) as [v|] eqn:Hi.
  - transitivity (Some v).
    + rewrite (lookup_union_l' (M:=gmap K) (A:=V)
        ((s : gmap K V) ∪ t) (s : gmap K V) i)
        by (rewrite (lookup_union_l' (M:=gmap K) (A:=V)
          (s : gmap K V) t i) by eauto; eauto).
      rewrite (lookup_union_l' (M:=gmap K) (A:=V)
        (s : gmap K V) t i) by eauto.
      exact Hi.
    + symmetry. rewrite (lookup_union_l' (M:=gmap K) (A:=V)
        (s : gmap K V) t i) by eauto.
      exact Hi.
  - rewrite (lookup_union_r (M:=gmap K) (A:=V)
      (s : gmap K V) t i Hi).
    destruct ((t : gmap K V) !! i) as [vt|] eqn:Ht.
    + transitivity (Some vt).
      * rewrite (lookup_union_l' (M:=gmap K) (A:=V)
          ((s : gmap K V) ∪ t) (s : gmap K V) i)
          by (rewrite (lookup_union_r (M:=gmap K) (A:=V)
            (s : gmap K V) t i Hi); eauto).
        rewrite (lookup_union_r (M:=gmap K) (A:=V)
          (s : gmap K V) t i Hi). exact Ht.
      * reflexivity.
    + transitivity (@None V).
      * apply map_lookup_union_None. split.
        -- apply map_lookup_union_None. split; assumption.
        -- exact Hi.
      * reflexivity.
Qed.

Lemma storeA_compat_insert_l_fresh {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (x : K) (v : V) :
  s1 ≈A s2 →
  x ∉ dom (s2 : gmap K V) →
  <[x := v]> (s1 : gmap K V) ≈A s2.
Proof.
  unfold storeA_compat, map_compat.
  intros Hcompat Hx z v1 v2 H1 H2.
  destruct (decide (z = x)) as [->|Hzx].
  - exfalso. apply Hx. by apply elem_of_dom_2 in H2.
  - apply (lookup_insert_Some (M:=gmap K) (A:=V)) in H1 as [[Hzx' Hv]|[Hzx' H1]].
    + congruence.
    + eapply Hcompat; eauto.
Qed.

Lemma storeA_compat_insert_r_fresh {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (x : K) (v : V) :
  s1 ≈A s2 →
  x ∉ dom (s1 : gmap K V) →
  s1 ≈A <[x := v]> (s2 : gmap K V).
Proof.
  intros Hcompat Hx.
  apply storeA_compat_sym.
  eapply storeA_compat_insert_l_fresh.
  - apply storeA_compat_sym. exact Hcompat.
  - exact Hx.
Qed.

Lemma storeA_insert_union_l {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (x : K) (v : V) :
  @union (gmap K V) _ (<[x := v]> (s1 : gmap K V)) s2 =
  <[x := v]> (@union (gmap K V) _ s1 s2).
Proof.
  apply storeA_map_eq. intros i.
  pose proof (insert_union_l (M:=gmap K) (A:=V)
    (s1 : gmap K V) (s2 : gmap K V) x v) as Hins.
  exact (f_equal (λ m : gmap K V, m !! i) (eq_sym Hins)).
Qed.

Lemma storeA_insert_union_l_fresh {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (x : K) (v : V) :
  x ∉ dom (s2 : gmap K V) →
  @union (gmap K V) _ (<[x := v]> (s1 : gmap K V)) s2 =
  <[x := v]> (@union (gmap K V) _ s1 s2).
Proof.
  intros _. apply storeA_insert_union_l.
Qed.

Lemma storeA_insert_union_r_fresh {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (x : K) (v : V) :
  x ∉ dom (s1 : gmap K V) →
  @union (gmap K V) _ s1 (<[x := v]> (s2 : gmap K V)) =
  <[x := v]> (@union (gmap K V) _ s1 s2).
Proof.
  intros Hx.
  symmetry. apply insert_union_r.
  apply not_elem_of_dom. exact Hx.
Qed.

Lemma storeA_union_singleton_insert_fresh {K : Type} `{Countable K}
    (σ : gmap K V) (x : K) (v : V) :
  x ∉ dom (σ : gmap K V) →
  @union (gmap K V) _ σ ({[x := v]} : gmap K V) =
  <[x := v]> (σ : gmap K V).
Proof.
  intros Hfresh.
  change ({[x := v]} : gmap K V) with (<[x := v]> (∅ : gmap K V)).
  rewrite storeA_insert_union_r_fresh by exact Hfresh.
  rewrite map_union_empty. reflexivity.
Qed.

Lemma storeA_union_dom {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  s1 ≈A s2 →
  dom (@union (gmap K V) _ s1 s2) =
  dom (s1 : gmap K V) ∪ dom (s2 : gmap K V).
Proof.
  intros _. apply dom_union_L.
Qed.

Lemma storeA_disj_dom_compat {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  dom (s1 : gmap K V) ∩ dom (s2 : gmap K V) = ∅ →
  s1 ≈A s2.
Proof.
  intros Hdisj.
  unfold storeA_compat, map_compat.
  intros x v1 v2 H1 H2.
  assert (x ∈ dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)) as Hin.
  { apply elem_of_intersection. split; [by apply elem_of_dom_2 in H1 | by apply elem_of_dom_2 in H2]. }
  better_set_solver.
Qed.

Lemma storeA_compat_restrict_singleton_fresh {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (y : K) :
  y ∉ dom (s1 : gmap K V) →
  s1 ≈A storeA_restrict s2 ({[y]} : gset K).
Proof.
  intros Hy.
  apply storeA_disj_dom_compat.
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_intersection in Hz as [Hz1 Hz2].
    pose proof (storeA_restrict_dom_subset s2 ({[y]} : gset K) z Hz2) as Hzy.
    rewrite elem_of_singleton in Hzy. subst. contradiction.
  - intros Hz. apply elem_of_empty in Hz. contradiction.
Qed.

Lemma storeA_compat_restrict {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  s1 ≈A s2 →
  storeA_restrict s1 X ≈A storeA_restrict s2 X.
Proof.
  unfold storeA_compat, map_compat.
  intros Hcomp x y z H2 H3.
  apply storeA_restrict_lookup_some in H2 as [_ H2].
  apply storeA_restrict_lookup_some in H3 as [_ H3].
  eapply Hcomp; eauto.
Qed.

Lemma storeA_compat_restrict_r {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  s1 ≈A s2 → s1 ≈A storeA_restrict s2 X.
Proof.
  unfold storeA_compat, map_compat.
  intros Hcomp x y z H2 H3.
  apply storeA_restrict_lookup_some in H3 as [_ H3].
  eapply Hcomp; eauto.
Qed.

Lemma storeA_compat_restrict_overlap {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X Y S : gset K) :
  X ∩ Y ⊆ S ->
  s1 ≈A storeA_restrict s2 S ->
  storeA_restrict s1 X ≈A storeA_restrict s2 Y.
Proof.
  unfold storeA_compat, map_compat.
  intros Hoverlap Hcomp x v1 v2 H1 H2.
  apply storeA_restrict_lookup_some in H1 as [HxX H1].
  apply storeA_restrict_lookup_some in H2 as [HxY H2].
  eapply Hcomp.
  - exact H1.
  - apply storeA_restrict_lookup_some_2; [exact H2|].
    apply Hoverlap. set_solver.
Qed.

Lemma storeA_compat_restricts_same {K : Type} `{Countable K}
    (s : gmap K V) (X Y : gset K) :
  storeA_compat (storeA_restrict s X) (storeA_restrict s Y).
Proof.
  apply storeA_compat_restrict_r.
  apply storeA_compat_sym.
  apply storeA_compat_restrict_r.
  apply storeA_compat_refl.
Qed.

Lemma storeA_compat_restrict_l_full_r {K : Type} `{Countable K}
    (s1 s2 : gmap K V) (X : gset K) :
  dom (s1 : gmap K V) ⊆ X →
  s1 ≈A storeA_restrict s2 X →
  s1 ≈A s2.
Proof.
  unfold storeA_compat, map_compat.
  intros Hdom Hcomp x v1 v2 H1 H2.
  eapply Hcomp; [exact H1 |].
  apply storeA_restrict_lookup_some_2; [exact H2 |].
  apply Hdom. by apply elem_of_dom_2 in H1.
Qed.

Lemma storeA_compat_restrict_eq {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  s1 ≈A s2 →
  dom (s1 : gmap K V) ⊆ dom (s2 : gmap K V) →
  storeA_restrict s2 (dom (s1 : gmap K V)) = s1.
Proof.
  unfold storeA_compat, map_compat. intros Hcomp Hsub.
  apply storeA_map_eq. intros i.
  destruct ((s1 : gmap K V) !! i) as [v1|] eqn:H1.
  - assert (i ∈ dom (s1 : gmap K V)) as Hin1 by (by apply elem_of_dom_2 in H1).
    assert (i ∈ dom (s2 : gmap K V)) as Hin2 by (apply Hsub; exact Hin1).
    apply elem_of_dom in Hin2 as [v2 H2].
    assert (H2' : (s2 : gmap K V) !! i = Some v1).
    { assert (v1 = v2) by (eapply Hcomp; eauto). subst. exact H2. }
    transitivity (Some v1).
    + apply (storeA_restrict_lookup_some_2 _ _ _ _ H2' Hin1).
    + reflexivity.
  - transitivity (@None V); [|reflexivity].
    apply storeA_restrict_lookup_none_r.
    intros Hin.
    apply elem_of_dom in Hin as [v Hlook]. congruence.
Qed.

Lemma storeA_compat_spec {K : Type} `{Countable K}
    (s1 s2 : gmap K V) :
  s1 ≈A s2 ↔
  storeA_restrict s1 (dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)) =
  storeA_restrict s2 (dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)).
Proof.
  split.
  - intros Hcompat.
    unfold storeA_restrict.
    apply map_restrict_agree. intros x Hin.
    apply elem_of_intersection in Hin as [Hin1 Hin2].
    destruct ((s1 : gmap K V) !! x) as [v1|] eqn:H1;
      destruct ((s2 : gmap K V) !! x) as [v2|] eqn:H2.
    + f_equal. eapply Hcompat; eauto.
    + apply not_elem_of_dom in H2. contradiction.
    + apply not_elem_of_dom in H1. contradiction.
    + apply not_elem_of_dom in H1. contradiction.
  - intros Heq.
    unfold storeA_compat, map_compat.
    intros x v1 v2 H1 H2.
    assert (Hin : x ∈ dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)).
    { apply elem_of_intersection. split; [by apply elem_of_dom_2 in H1 | by apply elem_of_dom_2 in H2]. }
    assert (Hr1 : (storeA_restrict s1 (dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)) : gmap K V) !! x = Some v1).
    { apply (storeA_restrict_lookup_some_2 _ _ _ _ H1 Hin). }
    assert (Hr2 : (storeA_restrict s2 (dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)) : gmap K V) !! x = Some v2).
    { apply (storeA_restrict_lookup_some_2 _ _ _ _ H2 Hin). }
    rewrite Heq in Hr1. rewrite Hr2 in Hr1. by inversion Hr1.
Qed.

End StoreRestrictCompat.
