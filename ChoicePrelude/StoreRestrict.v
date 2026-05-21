(** * Generic stores: restriction lemmas *)

From ChoicePrelude Require Export StoreKeyAction.

Section AbstractStoreRestrict.

Context {V : Type} `{ValueSig V}.

Lemma storeA_restrict_dom {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) :
  dom (@storeA_restrict V K _ _ s X) = dom s ∩ X.
Proof.
  unfold storeA_restrict. apply map_restrict_dom.
Qed.


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
  rewrite storeA_restrict_dom. set_solver.
Qed.


Lemma storeA_restrict_empty {K : Type} `{Countable K} X :
  storeA_restrict (∅ : StoreA K) X = (∅ : gmap K V).
Proof.
  unfold storeA_restrict. apply map_restrict_idemp. set_solver.
Qed.


Lemma storeA_restrict_empty_set {K : Type} `{Countable K} (s : StoreA K) :
  storeA_restrict s ∅ = (∅ : gmap K V).
Proof.
  apply storeA_map_eq. intros z.
  change ((map_restrict V (s : gmap K V) (∅ : gset K)) !! z =
    (∅ : gmap K V) !! z).
  rewrite (lookup_empty (M:=gmap K) (A:=V)).
  unfold map_restrict.
  apply map_lookup_filter_None. right. intros v _ Hin. set_solver.
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
  replace (X ∩ X) with X by set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_twice_subset {K : Type} `{Countable K}
    (s : StoreA K) (X Y : gset K) :
  Y ⊆ X →
  storeA_restrict (storeA_restrict s X) Y = (storeA_restrict s Y : gmap K V).
Proof.
  intros HYX.
  rewrite storeA_restrict_restrict.
  replace (X ∩ Y) with Y by set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_comm {K : Type} `{Countable K}
    (s : StoreA K) (X Y : gset K) :
  storeA_restrict (storeA_restrict s X) Y =
  (storeA_restrict (storeA_restrict s Y) X : gmap K V).
Proof.
  rewrite !storeA_restrict_restrict.
  replace (X ∩ Y) with (Y ∩ X) by set_solver.
  reflexivity.
Qed.


Lemma storeA_restrict_idemp_eq {K : Type} `{Countable K}
    (s : StoreA K) (X : gset K) :
  dom (s : gmap K V) = X →
  storeA_restrict s X = (s : gmap K V).
Proof.
  intros Hdom. apply storeA_restrict_idemp. set_solver.
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
  destruct (decide (x ∈ Y)) as [_|Hbad]; [exact HeqX | set_solver].
Qed.




Lemma storeA_restrict_swap_fresh {K : Type} `{Countable K} `{!SwapKey K}
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
        rewrite key_swap_fresh by set_solver.
        exact Hs.
      * symmetry. apply storeA_restrict_lookup_some_2; [exact Hs | exact Hz].
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l.
        rewrite storeA_swap_lookup_inv.
        rewrite key_swap_fresh by set_solver. exact Hs.
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
    set_solver.
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

Lemma storeA_restrict_swap {K : Type} `{Countable K} `{!SwapKey K}
    (x y : K) (s : StoreA K) (X : gset K) :
  (storeA_restrict (storeA_swap x y s) (gset_swap x y X) : gmap K V) =
  storeA_swap x y (storeA_restrict s X).
Proof.
  apply storeA_map_eq. intros z.
  change ((storeA_restrict (storeA_swap x y s) (gset_swap x y X) : gmap K V) !! z =
    (storeA_swap x y (storeA_restrict s X) : gmap K V) !! z).
  rewrite storeA_restrict_lookup.
  destruct (decide (z ∈ gset_swap x y X)) as [Hz|Hz].
  - rewrite !storeA_swap_lookup_inv.
    rewrite elem_of_gset_swap in Hz.
    destruct ((s : gmap K V) !! key_swap x y z) as [v|] eqn:Hs.
    + symmetry. apply storeA_restrict_lookup_some_2; [exact Hs | exact Hz].
    + symmetry. apply storeA_restrict_lookup_none_l. exact Hs.
  - rewrite !storeA_swap_lookup_inv.
    symmetry. apply storeA_restrict_lookup_none_r.
    intros Hbad. apply Hz. rewrite elem_of_gset_swap. exact Hbad.
Qed.

Lemma storeA_restrict_empty_union_elements_subset {K : Type} `{Countable K}
    (σ τ : StoreA K) (X F : gset K) :
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
    (s1 s2 : StoreA K) :
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
      apply storeA_restrict_lookup_none_r. set_solver.
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
    (s1 s2 : StoreA K) (X : gset K) :
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
        apply lookup_union_Some_raw. left. exact H1.
      * symmetry. apply lookup_union_Some_raw. left.
        apply storeA_restrict_lookup_some_2; [exact H1|exact HiX].
    + destruct ((s2 : gmap K V) !! i) as [v2|] eqn:H2.
      * transitivity (Some v2).
        -- apply storeA_restrict_lookup_some_2; [|exact HiX].
           rewrite (lookup_union_r (M:=gmap K) (A:=V) (s1 : gmap K V) (s2 : gmap K V) i H1).
           exact H2.
        -- symmetry. apply lookup_union_Some_raw. right.
           split; [apply storeA_restrict_lookup_none_l; exact H1|].
           apply storeA_restrict_lookup_some_2; [exact H2|exact HiX].
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l.
           rewrite (lookup_union_r (M:=gmap K) (A:=V) (s1 : gmap K V) (s2 : gmap K V) i H1).
           exact H2.
        -- symmetry. apply lookup_union_None.
           split; apply storeA_restrict_lookup_none_l; assumption.
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. exact HiX.
    + symmetry. apply lookup_union_None.
      split; apply storeA_restrict_lookup_none_r; exact HiX.
Qed.

Lemma storeA_restrict_union_cover {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (X1 X2 : gset K) :
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
  - assert (i ∈ dom (s1 : gmap K V)) as Hidom1 by set_solver.
    apply elem_of_dom in Hidom1 as [v1 Hlookup1].
    assert (Hrestrict1 : (storeA_restrict s1 X1 : gmap K V) !! i = Some v1).
    { apply storeA_restrict_lookup_some_2; [exact Hlookup1 | exact Hi1]. }
    transitivity (Some v1).
    + apply storeA_restrict_lookup_some_2; last set_solver.
      apply lookup_union_Some_raw. left. exact Hlookup1.
    + symmetry. apply lookup_union_Some_raw. left. exact Hrestrict1.
  - destruct (decide (i ∈ X2)) as [Hi2 | Hni2].
    + assert (i ∈ dom (s2 : gmap K V)) as Hidom2 by set_solver.
      apply elem_of_dom in Hidom2 as [v2 Hlookup2].
      assert (Hleft_none : (storeA_restrict s1 X1 : gmap K V) !! i = None).
      { apply storeA_restrict_lookup_none_r. exact Hni1. }
      assert (Hrestrict2 : (storeA_restrict s2 X2 : gmap K V) !! i = Some v2).
      { apply storeA_restrict_lookup_some_2; [exact Hlookup2 | exact Hi2]. }
      transitivity (Some v2).
      * apply storeA_restrict_lookup_some_2; last set_solver.
        destruct ((s1 : gmap K V) !! i) as [v1|] eqn:Hlookup1.
        -- apply lookup_union_Some_raw. left.
           assert (v1 = v2) by (eapply Hcompat; eauto). subst. exact Hlookup1.
        -- apply lookup_union_Some_raw. right. exact (conj Hlookup1 Hlookup2).
      * symmetry. apply lookup_union_Some_raw. right.
        split; [exact Hleft_none | exact Hrestrict2].
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. set_solver.
      * symmetry. apply lookup_union_None.
        split; apply storeA_restrict_lookup_none_r; assumption.
Qed.

Lemma storeA_restrict_insert_singleton {K : Type} `{Countable K}
    (σ : StoreA K) (x : K) (v : V) :
  (storeA_restrict (<[x := v]> σ) ({[x]} : gset K) : gmap K V) =
  ({[x := v]} : gmap K V).
Proof.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [change ((<[x:=v]> (σ : gmap K V) : gmap K V) !! x = Some v); rewrite lookup_insert; destruct (decide (x = x)); [reflexivity|congruence] | set_solver].
    + symmetry. change (({[x := v]} : gmap K V) !! x = Some v).
      rewrite lookup_singleton. destruct (decide (x = x)); [reflexivity|congruence].
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. set_solver.
    + symmetry. change (({[x := v]} : gmap K V) !! z = None).
      apply lookup_singleton_ne. congruence.
Qed.

Lemma storeA_restrict_singleton_lookup {K : Type} `{Countable K}
    (σ : StoreA K) (x : K) (v : V) :
  (σ : gmap K V) !! x = Some v →
  (storeA_restrict σ ({[x]} : gset K) : gmap K V) =
  ({[x := v]} : gmap K V).
Proof.
  intros Hlook.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [exact Hlook | set_solver].
    + symmetry. change (({[x := v]} : gmap K V) !! x = Some v).
      rewrite lookup_singleton. destruct (decide (x = x)); [reflexivity|congruence].
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. set_solver.
    + symmetry. change (({[x := v]} : gmap K V) !! z = None).
      apply lookup_singleton_ne. congruence.
Qed.

Lemma storeA_restrict_insert_singleton_ne {K : Type} `{Countable K}
    (σ : StoreA K) (x y : K) (v : V) :
  x ≠ y →
  (storeA_restrict (<[x := v]> σ) ({[y]} : gset K) : gmap K V) =
  storeA_restrict σ ({[y]} : gset K).
Proof.
  intros Hxy.
  rewrite storeA_restrict_insert_notin by set_solver.
  reflexivity.
Qed.

Lemma storeA_restrict_insert_fresh_union {K : Type} `{Countable K}
    (σ : StoreA K) (X : gset K) (x : K) (v : V) :
  (σ : gmap K V) !! x = None →
  x ∉ X →
  (storeA_restrict (<[x := v]> σ) (X ∪ {[x]}) : gmap K V) =
  <[x := v]> (storeA_restrict σ X : gmap K V).
Proof.
  intros _ Hx.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [change ((<[x := v]> (σ : gmap K V) : gmap K V) !! x = Some v); rewrite lookup_insert; destruct (decide (x = x)); [reflexivity|congruence] | set_solver].
    + symmetry. change ((<[x := v]> (storeA_restrict σ X : gmap K V) : gmap K V) !! x = Some v).
      rewrite lookup_insert. destruct (decide (x = x)); [reflexivity|congruence].
  - change ((storeA_restrict (<[x := v]> (σ : gmap K V)) (X ∪ {[x]}) : gmap K V) !! z =
      (<[x := v]> (storeA_restrict σ X : gmap K V) : gmap K V) !! z).
    rewrite lookup_insert_ne by congruence.
    destruct (decide (z ∈ X)) as [HzX|HzX].
    + destruct ((σ : gmap K V) !! z) as [vz|] eqn:Hz.
      * transitivity (Some vz).
        -- apply storeA_restrict_lookup_some_2; [rewrite lookup_insert_ne by congruence; exact Hz | set_solver].
        -- symmetry. apply storeA_restrict_lookup_some_2; [exact Hz | exact HzX].
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l. rewrite lookup_insert_ne by congruence. exact Hz.
        -- symmetry. apply storeA_restrict_lookup_none_l. exact Hz.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. set_solver.
      * symmetry. apply storeA_restrict_lookup_none_r. exact HzX.
Qed.

Lemma storeA_restrict_insert_fresh_union_lookup_none {K : Type} `{Countable K}
    (σ : StoreA K) (X : gset K) (x : K) (v : V) :
  (σ : gmap K V) !! x = None →
  x ∉ X →
  (<[x := v]> (storeA_restrict σ X : gmap K V) : StoreA K) !! x = Some v.
Proof.
  intros _ _.
  change ((<[x := v]> (storeA_restrict σ X : gmap K V) : gmap K V) !! x = Some v).
  rewrite lookup_insert. destruct (decide (x = x)); [reflexivity|congruence].
Qed.

Lemma storeA_restrict_union_singleton_insert {K : Type} `{Countable K}
    (σ : StoreA K) (X : gset K) (x : K) (v : V) :
  dom (σ : gmap K V) ⊆ X →
  x ∉ X →
  (storeA_restrict (@union (gmap K V) _ σ ({[x := v]} : gmap K V)) (X ∪ {[x]}) : gmap K V) =
  <[x := v]> (σ : gmap K V).
Proof.
  intros Hdom Hx.
  apply storeA_map_eq. intros z.
  destruct (decide (z = x)) as [->|Hzx].
  - transitivity (Some v).
    + apply storeA_restrict_lookup_some_2; [|set_solver].
      apply lookup_union_Some_raw. right. split.
      * apply not_elem_of_dom. set_solver.
      * change (({[x := v]} : gmap K V) !! x = Some v).
        rewrite lookup_singleton. destruct (decide (x = x)); [reflexivity|congruence].
    + symmetry. change ((<[x := v]> (σ : gmap K V) : gmap K V) !! x = Some v).
      rewrite lookup_insert. destruct (decide (x = x)); [reflexivity|congruence].
  - change ((storeA_restrict (@union (gmap K V) _ (σ : gmap K V) ({[x := v]} : gmap K V)) (X ∪ {[x]}) : gmap K V) !! z =
      (<[x := v]> (σ : gmap K V) : gmap K V) !! z).
    rewrite lookup_insert_ne by congruence.
    destruct ((σ : gmap K V) !! z) as [vz|] eqn:Hz.
    + transitivity (Some vz).
      * apply storeA_restrict_lookup_some_2; [apply lookup_union_Some_raw; left; exact Hz | apply elem_of_dom_2 in Hz; set_solver].
      * reflexivity.
    + transitivity (@None V); [|reflexivity].
      destruct (decide (z ∈ X ∪ {[x]})) as [HzX|HzX].
      * apply storeA_restrict_lookup_none_l.
        apply lookup_union_None. split; [exact Hz|].
        change (({[x := v]} : gmap K V) !! z = None).
        apply lookup_singleton_ne. congruence.
      * apply storeA_restrict_lookup_none_r. exact HzX.
Qed.

Lemma storeA_restrict_union_from_parts {K : Type} `{Countable K}
    (σ ρ σx : StoreA K) (S : gset K) (x : K) :
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
      * apply storeA_restrict_lookup_some_2; [exact Hz|set_solver].
      * symmetry. apply lookup_union_Some_raw. left.
        apply storeA_restrict_lookup_some_2; [exact Hz|exact HzS].
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l. exact Hz.
      * symmetry. apply lookup_union_None.
        split; apply storeA_restrict_lookup_none_l; exact Hz.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite (lookup_union_r (M:=gmap K) (A:=V)
        (storeA_restrict σ S : gmap K V)
        (storeA_restrict σ ({[x]} : gset K) : gmap K V) x)
        by (apply storeA_restrict_lookup_none_r; exact Hx).
      destruct ((σ : gmap K V) !! x) as [vx|] eqn:Hxlook.
      * transitivity (Some vx).
        -- apply storeA_restrict_lookup_some_2; [exact Hxlook|set_solver].
        -- symmetry. apply storeA_restrict_lookup_some_2; [exact Hxlook|set_solver].
      * transitivity (@None V).
        -- apply storeA_restrict_lookup_none_l. exact Hxlook.
        -- symmetry. apply storeA_restrict_lookup_none_l. exact Hxlook.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_r. set_solver.
      * symmetry. apply lookup_union_None.
        split; apply storeA_restrict_lookup_none_r; set_solver.
Qed.

Lemma storeA_eq_insert_of_restrict_singleton {K : Type} `{Countable K}
    (X : gset K) (σx σ : StoreA K) (ν : K) (vx : V) :
  dom (σx : gmap K V) = X ∪ {[ν]} →
  ν ∉ X →
  (storeA_restrict σx X : gmap K V) = σ →
  (storeA_restrict σx ({[ν]} : gset K) : gmap K V) = ({[ν := vx]} : gmap K V) →
  (σx : gmap K V) = <[ν := vx]> (σ : gmap K V).
Proof.
  intros Hdom Hν HX Hνsingle.
  apply storeA_map_eq. intros z.
  destruct (decide (z = ν)) as [->|Hzν].
  - change ((σx : gmap K V) !! ν =
      (<[ν := vx]> (σ : gmap K V) : gmap K V) !! ν).
    rewrite lookup_insert.
    destruct (decide (ν = ν)) as [_|Hbad]; [|congruence].
    pose proof (f_equal (fun s : gmap K V => s !! ν) Hνsingle) as Hlook.
    change ((storeA_restrict σx ({[ν]} : gset K) : gmap K V) !! ν =
      ({[ν := vx]} : gmap K V) !! ν) in Hlook.
    rewrite lookup_singleton in Hlook.
    destruct (decide (ν = ν)) as [_|Hbad]; [|congruence].
    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
    exact Hlook.
  - change ((σx : gmap K V) !! z =
      (<[ν := vx]> (σ : gmap K V) : gmap K V) !! z).
    rewrite lookup_insert_ne by congruence.
    destruct ((σx : gmap K V) !! z) as [vz|] eqn:Hz.
    + assert (z ∈ X) as HzX.
      { apply elem_of_dom_2 in Hz. rewrite Hdom in Hz. set_solver. }
      rewrite <- HX.
      symmetry. apply storeA_restrict_lookup_some_2; [exact Hz|exact HzX].
    + rewrite <- HX.
      symmetry. apply storeA_restrict_lookup_none_l. exact Hz.
Qed.

Lemma storeA_restrict_union_partition {K : Type} `{Countable K}
    (s : StoreA K) (X Y : gset K) :
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
    + apply lookup_union_Some_raw. left.
      apply storeA_restrict_lookup_some_2; [exact Hz|exact HzX].
    + rewrite lookup_union_None. split; apply storeA_restrict_lookup_none_l; exact Hz.
  - rewrite (lookup_union_r (M:=gmap K) (A:=V)
      (storeA_restrict s X : gmap K V) (storeA_restrict s Y : gmap K V) z)
      by (apply storeA_restrict_lookup_none_r; exact HzX).
    destruct ((s : gmap K V) !! z) as [v|] eqn:Hz.
    + apply storeA_restrict_lookup_some_2; [exact Hz|].
      apply elem_of_dom_2 in Hz. set_solver.
    + apply storeA_restrict_lookup_none_l. exact Hz.
Qed.

Lemma storeA_restrict_union_piece_l {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (X Y : gset K) :
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
    + apply storeA_restrict_lookup_some_2; [|apply elem_of_dom_2 in H1; set_solver].
      apply lookup_union_Some_raw. left. exact H1.
    + symmetry. exact H1.
  - transitivity (@None V); [|symmetry; exact H1].
    destruct (decide (z ∈ X)) as [HzX|HzX]; [|apply storeA_restrict_lookup_none_r; exact HzX].
    apply storeA_restrict_lookup_none_l.
    apply lookup_union_None. split; [exact H1|].
    apply not_elem_of_dom. intros Hz2. set_solver.
Qed.

Lemma storeA_restrict_union_piece_r {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (X Y : gset K) :
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
    + apply storeA_restrict_lookup_some_2; [|apply elem_of_dom_2 in H2; set_solver].
      destruct ((s1 : gmap K V) !! z) as [v1|] eqn:H1.
      * assert (v1 = v2) by (eapply Hcompat; eauto). subst.
        apply lookup_union_Some_raw. left. exact H1.
      * apply lookup_union_Some_raw. right. eauto.
    + symmetry. exact H2.
  - transitivity (@None V); [|symmetry; exact H2].
    destruct (decide (z ∈ Y)) as [HzY|HzY]; [|apply storeA_restrict_lookup_none_r; exact HzY].
    apply storeA_restrict_lookup_none_l.
    apply lookup_union_None. split; [|exact H2].
    apply not_elem_of_dom. intros Hz1. set_solver.
Qed.

Lemma storeA_restrict_union_base_singleton {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (D : gset K) (y : K) :
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
  - assert (i ∈ dom (s1 : gmap K V)) as Hi_s1 by set_solver.
    apply elem_of_dom in Hi_s1 as [v1 Hs1].
    assert (Hs1D : (storeA_restrict s1 D : gmap K V) !! i = Some v1).
    { apply storeA_restrict_lookup_some_2; [exact Hs1|exact HiD]. }
    rewrite Hagree in Hs1D.
    apply storeA_restrict_lookup_some in Hs1D as [_ Hs2].
    transitivity (Some v1); [|symmetry; exact Hs2].
    apply storeA_restrict_lookup_some_2; last set_solver.
    apply lookup_union_Some_raw. left. exact Hs1.
  - destruct (decide (i = y)) as [->|Hiy].
    + destruct ((s2 : gmap K V) !! y) as [vy|] eqn:Hs2y.
      * transitivity (Some vy); [|symmetry; exact Hs2y].
        apply storeA_restrict_lookup_some_2; last set_solver.
        apply lookup_union_Some_raw. right. split.
        -- by apply not_elem_of_dom.
        -- apply storeA_restrict_lookup_some_2; [exact Hs2y|set_solver].
      * assert (y ∈ dom (s2 : gmap K V)) by (rewrite Hdom2; set_solver).
        apply not_elem_of_dom in Hs2y. contradiction.
    + assert ((s2 : gmap K V) !! i = None) as Hi_none.
      { apply not_elem_of_dom. rewrite Hdom2. set_solver. }
      transitivity (@None V); [|symmetry; exact Hi_none].
      apply storeA_restrict_lookup_none_r. set_solver.
Qed.

Lemma storeA_restrict_wand_product {K : Type} `{Countable K}
    (sn sm : StoreA K) (S X Y : gset K) :
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
  - assert (HiS : i ∈ S) by set_solver.
    assert (Him : i ∈ dom (sm : gmap K V)) by set_solver.
    apply elem_of_dom in Him as [vm Hsm].
    destruct ((sn : gmap K V) !! i) as [vn|] eqn:Hsn.
    + assert (vn = vm).
      { eapply Hfull; [exact Hsn|].
        apply storeA_restrict_lookup_some_2; [exact Hsm|exact HiS]. }
      subst vn.
      transitivity (Some vm).
      * apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply lookup_union_Some_raw. left. exact Hsn.
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
        destruct (decide (i ∈ X)) as [HiX|HiX].
        -- apply lookup_union_Some_raw. left.
           apply storeA_restrict_lookup_some_2; [exact Hsn|exact HiX].
        -- apply lookup_union_Some_raw. right. split.
           ++ apply storeA_restrict_lookup_none_r. exact HiX.
           ++ exact Hsm.
    + transitivity (Some vm).
      * apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply lookup_union_Some_raw. right. split.
        -- exact Hsn.
        -- apply storeA_restrict_lookup_some_2; [exact Hsm|exact HiS].
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HiY].
        apply lookup_union_Some_raw. right. split.
        -- apply storeA_restrict_lookup_none_l. exact Hsn.
        -- exact Hsm.
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_r. exact HiY.
    + symmetry. apply storeA_restrict_lookup_none_r. exact HiY.
Qed.

End AbstractStoreRestrict.
