(** * Generic stores: compatibility, bind, and union lemmas *)

From ContextBase Require Import Prelude LogicVarInterface.
From ContextStore Require Import StoreCore StoreKeyAction StoreRestrictCore StoreRestrictUnion.

Section AbstractStoreBind.

Context {V : Type} `{ValueSig V}.

Local Notation "s1 ≈A s2" := (@storeA_compat V _ _ _ s1 s2) (at level 70).

Lemma storeA_compat_refl {K : Type} `{Countable K} (s : StoreA K) :
  @storeA_compat V K _ _ s s.
Proof.
  unfold storeA_compat, map_compat. intros x v1 v2 H1 H2. congruence.
Qed.


Lemma storeA_compat_sym {K : Type} `{Countable K} (s1 s2 : StoreA K) :
  @storeA_compat V K _ _ s1 s2 → @storeA_compat V K _ _ s2 s1.
Proof.
  unfold storeA_compat, map_compat.
  intros Hc x v1 v2 H1 H2. symmetry. eapply Hc; eauto.
Qed.

Lemma storeA_compat_swap {K : Type} `{Countable K} 
    (x y : K) (s1 s2 : StoreA K) :
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
    (s1 s2 s3 : StoreA K) :
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
    (s1 s2 s3 : StoreA K) :
  s1 ≈A s2 →
  @union (gmap K V) _ s1 s2 ≈A s3 →
  s2 ≈A s3.
Proof.
  unfold storeA_compat, map_compat.
  intros H12 Hc i v2 v3 H2 H3.
  destruct ((s1 : gmap K V) !! i) as [v1|] eqn:H1.
  - assert (Hv : v1 = v3).
    { eapply Hc; [| exact H3].
      apply (proj2 (map_lookup_union_Some_raw
        (s1 : gmap K V) (s2 : gmap K V) i v1)).
      left. exact H1. }
    assert (Hv' : v1 = v2) by (eapply H12; eauto).
    congruence.
  - eapply Hc; [| exact H3].
    apply (proj2 (map_lookup_union_Some_raw
      (s1 : gmap K V) (s2 : gmap K V) i v2)).
    right. split; [exact H1 | exact H2].
Qed.

Lemma storeA_compat_union_intro_r {K : Type} `{Countable K}
    (s1 s2 s3 : StoreA K) :
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
    (s1 s2 : StoreA K) :
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

Lemma storeA_union_swap_right {K : Type} `{Countable K}
    (s1 s2 s3 : StoreA K) :
  s2 ≈A s3 →
  @union (gmap K V) _ (@union (gmap K V) _ s1 s2) s3 =
  @union (gmap K V) _ (@union (gmap K V) _ s1 s3) s2.
Proof.
  intros Hcompat.
  apply storeA_map_eq. intros i.
  rewrite option_eq. intros v.
  setoid_rewrite (map_lookup_union_Some_raw).
  split.
  - intros [H12 | [H12none H3]].
    + rewrite map_lookup_union_Some_raw in H12.
      destruct H12 as [H1 | [H1none H2]].
      * left. rewrite map_lookup_union_Some_raw. left. exact H1.
      * destruct ((s3 : gmap K V) !! i) as [v3|] eqn:H3i.
        -- assert (v = v3) by (eapply Hcompat; eauto).
           subst. left. rewrite map_lookup_union_Some_raw. right. eauto.
        -- right. split.
           ++ rewrite map_lookup_union_None. eauto.
           ++ exact H2.
    + rewrite map_lookup_union_None in H12none.
      destruct H12none as [H1none H2none].
      left. rewrite map_lookup_union_Some_raw. right. eauto.
  - intros [H13 | [H13none H2]].
    + rewrite map_lookup_union_Some_raw in H13.
      destruct H13 as [H1 | [H1none H3]].
      * left. rewrite map_lookup_union_Some_raw. left. exact H1.
      * destruct ((s2 : gmap K V) !! i) as [v2|] eqn:H2i.
        -- assert (v2 = v) by (eapply Hcompat; eauto).
           subst. left. rewrite map_lookup_union_Some_raw. right. eauto.
        -- right. split.
           ++ rewrite map_lookup_union_None. eauto.
           ++ exact H3.
    + rewrite map_lookup_union_None in H13none.
      destruct H13none as [H1none H3none].
      left. rewrite map_lookup_union_Some_raw. right. eauto.
Qed.

Lemma storeA_union_absorb_l {K : Type} `{Countable K}
    (s1 s2 : StoreA K) :
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
    + symmetry. exact Hs1.
  - destruct ((s2 : gmap K V) !! i) as [v2|] eqn:Hs2.
    + exfalso.
      assert (Hin1 : i ∈ dom (s1 : gmap K V)).
      { apply Hsub. by apply elem_of_dom_2 in Hs2. }
      apply not_elem_of_dom in Hs1. contradiction.
    + transitivity (@None V).
      * apply (proj2 (map_lookup_union_None
          (s1 : gmap K V) (s2 : gmap K V) i)).
        split; assumption.
      * symmetry. exact Hs1.
Qed.

Lemma storeA_union_absorb_r {K : Type} `{Countable K}
    (s1 s2 : StoreA K) :
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

Lemma storeA_compat_insert_l_fresh {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (x : K) (v : V) :
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
    (s1 s2 : StoreA K) (x : K) (v : V) :
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
    (s1 s2 : StoreA K) (x : K) (v : V) :
  @union (gmap K V) _ (<[x := v]> (s1 : gmap K V)) s2 =
  <[x := v]> (@union (gmap K V) _ s1 s2).
Proof.
  apply storeA_map_eq. intros i.
  pose proof (insert_union_l (M:=gmap K) (A:=V)
    (s1 : gmap K V) (s2 : gmap K V) x v) as Hins.
  exact (f_equal (λ m : gmap K V, m !! i) (eq_sym Hins)).
Qed.

Lemma storeA_insert_union_l_fresh {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (x : K) (v : V) :
  x ∉ dom (s2 : gmap K V) →
  @union (gmap K V) _ (<[x := v]> (s1 : gmap K V)) s2 =
  <[x := v]> (@union (gmap K V) _ s1 s2).
Proof.
  intros _. apply storeA_insert_union_l.
Qed.

Lemma storeA_insert_union_r_fresh {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (x : K) (v : V) :
  x ∉ dom (s1 : gmap K V) →
  @union (gmap K V) _ s1 (<[x := v]> (s2 : gmap K V)) =
  <[x := v]> (@union (gmap K V) _ s1 s2).
Proof.
  intros Hx.
  apply storeA_map_eq. intros i.
  pose proof (insert_union_r (M:=gmap K) (A:=V)
    (s1 : gmap K V) (s2 : gmap K V) x v) as Hins.
  assert (Hnone : (s1 : gmap K V) !! x = None).
  { apply not_elem_of_dom. exact Hx. }
  specialize (Hins Hnone).
  exact (f_equal (λ m : gmap K V, m !! i) (eq_sym Hins)).
Qed.

Lemma storeA_union_singleton_insert_fresh {K : Type} `{Countable K}
    (σ : StoreA K) (x : K) (v : V) :
  x ∉ dom (σ : gmap K V) →
  @union (gmap K V) _ σ ({[x := v]} : gmap K V) =
  <[x := v]> (σ : gmap K V).
Proof.
  intros Hfresh.
  change ({[x := v]} : gmap K V) with (<[x := v]> (∅ : gmap K V)).
  rewrite storeA_insert_union_r_fresh by exact Hfresh.
  apply storeA_map_eq. intros i.
  pose proof (map_union_empty (σ : gmap K V)) as Hempty.
  exact (f_equal (λ m : gmap K V, (<[x := v]> m) !! i) Hempty).
Qed.

Lemma storeA_union_dom {K : Type} `{Countable K}
    (s1 s2 : StoreA K) :
  s1 ≈A s2 →
  dom (@union (gmap K V) _ s1 s2) =
  dom (s1 : gmap K V) ∪ dom (s2 : gmap K V).
Proof.
  intros _. apply dom_union_L.
Qed.

Lemma storeA_disj_dom_compat {K : Type} `{Countable K}
    (s1 s2 : StoreA K) :
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
    (s1 s2 : StoreA K) (y : K) :
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
    (s1 s2 : StoreA K) (X : gset K) :
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
    (s1 s2 : StoreA K) (X : gset K) :
  s1 ≈A s2 → s1 ≈A storeA_restrict s2 X.
Proof.
  unfold storeA_compat, map_compat.
  intros Hcomp x y z H2 H3.
  apply storeA_restrict_lookup_some in H3 as [_ H3].
  eapply Hcomp; eauto.
Qed.

Lemma storeA_compat_restrict_l_full_r {K : Type} `{Countable K}
    (s1 s2 : StoreA K) (X : gset K) :
  dom (s1 : gmap K V) ⊆ X →
  s1 ≈A storeA_restrict s2 X →
  s1 ≈A s2.
Proof.
  unfold storeA_compat, map_compat.
  intros Hdom Hcomp x v1 v2 H1 H2.
  assert (Hx : x ∈ X).
  { apply Hdom. by apply elem_of_dom_2 in H1. }
  eapply Hcomp; [exact H1 |].
  apply storeA_restrict_lookup_some_2; [exact H2 | exact Hx].
Qed.

Lemma storeA_compat_restrict_eq {K : Type} `{Countable K}
    (s1 s2 : StoreA K) :
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
    + apply storeA_restrict_lookup_some_2; [exact H2' | exact Hin1].
    + symmetry. exact H1.
  - transitivity (@None V); [|symmetry; exact H1].
    apply storeA_restrict_lookup_none_r.
    intros Hin.
    apply elem_of_dom in Hin as [v Hlook]. congruence.
Qed.

Lemma storeA_compat_spec {K : Type} `{Countable K}
    (s1 s2 : StoreA K) :
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
    { apply storeA_restrict_lookup_some_2; [exact H1 | exact Hin]. }
    assert (Hr2 : (storeA_restrict s2 (dom (s1 : gmap K V) ∩ dom (s2 : gmap K V)) : gmap K V) !! x = Some v2).
    { apply storeA_restrict_lookup_some_2; [exact H2 | exact Hin]. }
    rewrite Heq in Hr1. rewrite Hr2 in Hr1. by inversion Hr1.
Qed.























End AbstractStoreBind.
