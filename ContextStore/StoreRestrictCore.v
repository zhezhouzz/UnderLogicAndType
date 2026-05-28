(** * Generic stores: restriction lemmas *)

From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import StoreCore StoreKeyAction.

Section AbstractStoreRestrict.

Context {V : Type} `{ValueSig V}.

Lemma storeA_restrict_dom {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) :
  dom (@storeA_restrict V K _ _ s X) = dom s ∩ X.
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
    (s : StoreA K) (X : gset K) (z : K) :
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
    (s : StoreA K) (X : gset K) (x : K) (y : V) :
  ((s : gmap K V) !! x) = Some y →
  x ∈ X →
  ((storeA_restrict s X : gmap K V) !! x) = Some y.
Proof.
  intros Hlookup Hin. rewrite storeA_restrict_lookup.
  destruct (decide (x ∈ X)) as [_|Hnot]; [exact Hlookup|contradiction].
Qed.

Lemma storeA_restrict_lookup_some {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) (x : K) (y : V) :
  ((storeA_restrict s X : gmap K V) !! x) = Some y →
  x ∈ X ∧ ((s : gmap K V) !! x) = Some y.
Proof.
  rewrite storeA_restrict_lookup.
  destruct (decide (x ∈ X)); intros Hlookup; [auto | discriminate].
Qed.

Lemma storeA_restrict_lookup_none_l {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) (z : K) :
  ((s : gmap K V) !! z) = None →
  ((storeA_restrict s X : gmap K V) !! z) = None.
Proof.
  intros Hlook. rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ X)); exact Hlook || reflexivity.
Qed.

Lemma storeA_restrict_lookup_none_r {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) (z : K) :
  z ∉ X →
  ((storeA_restrict s X : gmap K V) !! z) = None.
Proof.
  intros Hnot. rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ X)); [contradiction | reflexivity].
Qed.

Lemma storeA_restrict_dom_subset {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) :
  dom (storeA_restrict s X : gmap K V) ⊆ X.
Proof.
  change (dom (@storeA_restrict V K _ _ s X) ⊆ X).
  rewrite storeA_restrict_dom. better_set_solver.
Qed.


Lemma storeA_restrict_rekey {K : Type} `{Countable K}
    (f : K → K) (Hf : Inj (=) (=) f) (s : StoreA K) (X : gset K) :
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
  storeA_restrict (∅ : StoreA K) X = (∅ : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_idemp. better_set_solver.
Qed.


Lemma storeA_restrict_empty_set {K : Type} `{Countable K} (s : StoreA K) :
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
    (s : StoreA K) X :
  dom (s : gmap K V) ⊆ X → storeA_restrict s X = (s : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_idemp.
Qed.


Lemma storeA_restrict_restrict {K : Type} `{Countable K}
    (s : StoreA K) X Y :
  storeA_restrict (storeA_restrict s X) Y = (storeA_restrict s (X ∩ Y) : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_restrict.
Qed.


Lemma storeA_restrict_twice_same {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) :
  storeA_restrict (storeA_restrict s X) X = (storeA_restrict s X : gmap K V).
Proof.
  rewrite storeA_restrict_restrict.
  replace (X ∩ X) with X by better_set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_twice_subset {K : Type} `{Countable K}
    (s : StoreA K) (X Y : gset K) :
  Y ⊆ X →
  storeA_restrict (storeA_restrict s X) Y = (storeA_restrict s Y : gmap K V).
Proof.
  intros HYX.
  rewrite storeA_restrict_restrict.
  replace (X ∩ Y) with Y by better_set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_comm {K : Type} `{Countable K}
    (s : StoreA K) (X Y : gset K) :
  storeA_restrict (storeA_restrict s X) Y =
  (storeA_restrict (storeA_restrict s Y) X : gmap K V).
Proof.
  rewrite !storeA_restrict_restrict.
  replace (X ∩ Y) with (Y ∩ X) by better_set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_idemp_eq {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) :
  dom (s : gmap K V) = X →
  storeA_restrict s X = (s : gmap K V).
Proof.
  intros Hdom. apply storeA_restrict_idemp. better_set_solver.
Qed.


Lemma storeA_restrict_insert_in {K : Type} `{Countable K}
    (s : StoreA K) X x v :
  x ∈ X →
  storeA_restrict (<[x := v]> s) X =
  <[x := v]> (storeA_restrict s X : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_insert_in.
Qed.


Lemma storeA_restrict_insert_notin {K : Type} `{Countable K}
    (s : StoreA K) X x v :
  x ∉ X →
  storeA_restrict (<[x := v]> s) X =
  (storeA_restrict s X : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_insert_notin.
Qed.

Lemma storeA_restrict_eq_mono {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (X Y : gset K) :
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
    (x y : K) (s : StoreA K) (X : gset K) :
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
      * symmetry. apply storeA_restrict_lookup_some_2; [exact Hs | exact Hz].
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
    (σ : StoreA K) (X : gset K) :
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
    (s1 s2 : StoreA K) (X : gset K) (x : K) (v : V) :
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
  { apply storeA_restrict_lookup_some_2; [exact Hlook | exact Hx]. }
  rewrite Hrx in Heqx.
  symmetry in Heqx.
  apply storeA_restrict_lookup_some in Heqx as [_ Hlook2].
  exact Hlook2.
Qed.

Lemma storeA_restrict_swap {K : Type} `{Countable K} 
    (x y : K) (s : StoreA K) (X : gset K) :
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
    + symmetry. apply storeA_restrict_lookup_some_2; [exact Hs | exact Hz].
    + symmetry. apply storeA_restrict_lookup_none_l. exact Hs.
  - rewrite !storeA_swap_lookup_inv.
    symmetry. apply storeA_restrict_lookup_none_r.
    intros Hbad. apply Hz. rewrite elem_of_set_swap. exact Hbad.
Qed.

Lemma storeA_restrict_shift {K : Type} `{Countable K} `{!ShiftKey K}
    (k : nat) (s : StoreA K) (X : gset K) :
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
      change (z ∈ dom (@storeA_shift V K _ _ _ k
        (@storeA_restrict V K _ _ s X) : gmap K V)) in Hdom.
      pose proof (storeA_shift_dom (V:=V) (K:=K) k
        (@storeA_restrict V K _ _ s X)) as Hdom_shift.
      change (dom (@storeA_shift V K _ _ _ k
        (@storeA_restrict V K _ _ s X) : gmap K V) =
        set_map (key_shift k)
          (dom (@storeA_restrict V K _ _ s X : gmap K V))) in Hdom_shift.
      rewrite Hdom_shift in Hdom.
      apply elem_of_map in Hdom as [u [Heq Hdomu]]. subst z.
      apply storeA_restrict_dom_subset in Hdomu.
      apply Hz. apply elem_of_map. exists u. split; [reflexivity | exact Hdomu].
Qed.

End AbstractStoreRestrict.
