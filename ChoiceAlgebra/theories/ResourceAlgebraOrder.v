From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict.
From Stdlib Require Import Logic.ProofIrrelevance.

From ChoiceAlgebra Require Import ResourceAlgebraBase.

(** * Order and fiber transport lemmas for abstract resource algebra *)

Section ResourceAlgebraA.

Context {K : Type} `{Countable K} `{!SwapKey K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Lemma resA_le_same_dom_eq (w1 w2 : WfWorldAT) :
  w1 ⊑ w2 →
  worldA_dom (w1 : WorldAT) = worldA_dom (w2 : WorldAT) →
  w1 = w2.
Proof.
  intros Hle Hdom.
  apply (anti_symm (⊑)); [exact Hle |].
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      assert (Hw1σ : (w1 : WorldAT) σ).
      {
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
        rewrite Hle. simpl.
        exists σ. split; [exact Hσ |].
        apply storeA_restrict_idemp.
        pose proof (wfworldA_store_dom w2 σ Hσ) as Hσdom.
        change (dom (σ : gmap K V) = worldA_dom (w2 : WorldAT)) in Hσdom.
        set_solver.
      }
      exists σ. split; [exact Hw1σ |].
      apply storeA_restrict_idemp.
      pose proof (wfworldA_store_dom w2 σ Hσ) as Hσdom.
      change (dom (σ : gmap K V) = worldA_dom (w2 : WorldAT)) in Hσdom.
      set_solver.
    + intros [σ' [Hσ' Hrestrict]].
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
      rewrite Hle in Hσ'. simpl in Hσ'.
      destruct Hσ' as [σ2 [Hσ2 Hrestrict2]].
      pose proof (wfworldA_store_dom w2 σ2 Hσ2) as Hσ2dom.
      change (dom (σ2 : gmap K V) = worldA_dom (w2 : WorldAT)) in Hσ2dom.
      rewrite storeA_restrict_idemp in Hrestrict2 by set_solver.
      subst σ'.
      rewrite storeA_restrict_idemp in Hrestrict by set_solver.
      subst. exact Hσ2.
Qed.

Lemma resA_subset_of_le_same_domain (n m : WfWorldAT) :
  n ⊑ m →
  worldA_dom (n : WorldAT) = worldA_dom (m : WorldAT) →
  resA_subset n m.
Proof.
  intros Hle Hdom.
  assert (Heq : n = m) by (eapply resA_le_same_dom_eq; eauto).
  subst. apply resA_subset_refl.
Qed.

Lemma resA_subset_via_sum_left (n1 n2 m : WfWorldAT)
    (Hdef : rawA_sum_defined n1 n2) :
  resA_sum n1 n2 Hdef ⊑ m →
  worldA_dom (n1 : WorldAT) = worldA_dom (m : WorldAT) →
  resA_subset n1 m.
Proof.
  intros Hle Hdom.
  eapply resA_subset_trans.
  - apply resA_sum_subset_l.
  - eapply resA_subset_of_le_same_domain.
    + exact Hle.
    + simpl. exact Hdom.
Qed.

Lemma resA_subset_via_sum_right (n1 n2 m : WfWorldAT)
    (Hdef : rawA_sum_defined n1 n2) :
  resA_sum n1 n2 Hdef ⊑ m →
  worldA_dom (n2 : WorldAT) = worldA_dom (m : WorldAT) →
  resA_subset n2 m.
Proof.
  intros Hle Hdom.
  eapply resA_subset_trans.
  - apply resA_sum_subset_r.
  - eapply resA_subset_of_le_same_domain.
    + exact Hle.
    + simpl. unfold rawA_sum_defined in Hdef.
      change (worldA_dom (n1 : WorldAT) = worldA_dom (n2 : WorldAT)) in Hdef.
      rewrite Hdef. exact Hdom.
Qed.

Lemma worldA_compat_le_r (w m n : WfWorldAT) :
  m ⊑ n →
  worldA_compat w n →
  worldA_compat w m.
Proof.
  intros Hle Hcompat σw σm Hσw Hσm.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
  rewrite Hle in Hσm. simpl in Hσm.
  destruct Hσm as [σn [Hσn Hrestrict]].
  subst σm. apply storeA_compat_restrict_r.
  exact (Hcompat σw σn Hσw Hσn).
Qed.

Lemma worldA_compat_le_l (w m n : WfWorldAT) :
  m ⊑ n →
  worldA_compat n w →
  worldA_compat m w.
Proof.
  intros Hle Hcompat σm σw Hσm Hσw.
  apply storeA_compat_sym.
  eapply worldA_compat_le_r; [exact Hle | | exact Hσw | exact Hσm].
  intros σw' σn Hσw' Hσn. apply storeA_compat_sym.
  exact (Hcompat σn σw' Hσn Hσw').
Qed.

Lemma worldA_compat_restrict_l_full_r (n m : WfWorldAT) (S X : gset K) :
  X ⊆ S →
  worldA_compat n (resA_restrict m S) →
  worldA_compat (resA_restrict n X) m.
Proof.
  intros HXS Hcompat σn σm Hσn Hσm.
  simpl in Hσn. destruct Hσn as [τn [Hτn Hrestrict]]. subst σn.
  assert (Hrσm : (resA_restrict m S : WorldAT) (@storeA_restrict V K _ _ σm S)).
  { simpl. exists σm. split; [exact Hσm | reflexivity]. }
  pose proof (Hcompat τn (@storeA_restrict V K _ _ σm S) Hτn Hrσm) as Hstore.
  apply storeA_compat_restrict_l_full_r with (X := S).
  - pose proof (storeA_restrict_dom τn X) as Hdomr.
    change (dom (@storeA_restrict V K _ _ τn X : gmap K V) =
      dom (τn : gmap K V) ∩ X) in Hdomr.
    rewrite Hdomr. set_solver.
  - apply storeA_compat_sym.
    apply storeA_compat_restrict_r.
    apply storeA_compat_sym. exact Hstore.
Qed.

Lemma worldA_compat_swap (x y : K) (w1 w2 : WfWorldAT) :
  worldA_compat (resA_swap x y w1) (resA_swap x y w2) ↔
  worldA_compat w1 w2.
Proof.
  split.
  - intros Hc σ1 σ2 Hσ1 Hσ2.
    pose proof (Hc (@storeA_swap V K _ _ _ x y σ1)
      (@storeA_swap V K _ _ _ x y σ2)) as Hc'.
    simpl in Hc'.
    assert (Hs1 : rawA_swap x y w1 (@storeA_swap V K _ _ _ x y σ1)).
    { exists σ1. split; [exact Hσ1 | reflexivity]. }
    assert (Hs2 : rawA_swap x y w2 (@storeA_swap V K _ _ _ x y σ2)).
    { exists σ2. split; [exact Hσ2 | reflexivity]. }
    pose proof (Hc' Hs1 Hs2) as Hcompat.
    exact (proj1 (storeA_compat_swap x y σ1 σ2) Hcompat).
  - intros Hc σ1 σ2 Hσ1 Hσ2.
    simpl in Hσ1, Hσ2.
    destruct Hσ1 as [τ1 [Hτ1 Hswap1]].
    destruct Hσ2 as [τ2 [Hτ2 Hswap2]].
    rewrite <- Hswap1, <- Hswap2.
    apply (proj2 (storeA_compat_swap x y τ1 τ2)).
    exact (Hc τ1 τ2 Hτ1 Hτ2).
Qed.

Lemma resA_product_swap (x y : K) (w1 w2 : WfWorldAT)
    (Hc : worldA_compat w1 w2) :
  resA_swap x y (resA_product w1 w2 Hc) =
  resA_product (resA_swap x y w1) (resA_swap x y w2)
    (proj2 (worldA_compat_swap x y w1 w2) Hc).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl.
    change (gset_swap x y (worldA_dom (w1 : WorldAT) ∪ worldA_dom (w2 : WorldAT)) =
      gset_swap x y (worldA_dom (w1 : WorldAT)) ∪
      gset_swap x y (worldA_dom (w2 : WorldAT))).
    rewrite gset_swap_union. reflexivity.
  - intros σ. simpl. split.
    + intros [σ0 [Hprod Hswap]].
      rewrite <- Hswap.
      destruct Hprod as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      exists (@storeA_swap V K _ _ _ x y σ1), (@storeA_swap V K _ _ _ x y σ2).
      repeat split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * exists σ2. split; [exact Hσ2 | reflexivity].
      * exact (proj2 (storeA_compat_swap x y σ1 σ2) Hcompat).
      * rewrite <- storeA_swap_union. reflexivity.
    + intros [σ1' [σ2' [Hσ1' [Hσ2' [Hcompat' ->]]]]].
      destruct Hσ1' as [σ1 [Hσ1 Hswap1]].
      destruct Hσ2' as [σ2 [Hσ2 Hswap2]].
      rewrite <- Hswap1, <- Hswap2.
      exists (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V)). split.
      * exists σ1, σ2. repeat split; eauto.
      * change (@storeA_swap V K _ _ _ x y
          (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V)) =
          @union (gmap K V) _
            (@storeA_swap V K _ _ _ x y σ1 : gmap K V)
            (@storeA_swap V K _ _ _ x y σ2 : gmap K V)).
        rewrite storeA_swap_union. reflexivity.
Qed.

Lemma resA_sum_swap (x y : K) (w1 w2 : WfWorldAT)
    (Hdef : rawA_sum_defined w1 w2)
    (Hdef' : rawA_sum_defined (resA_swap x y w1) (resA_swap x y w2)) :
  resA_swap x y (resA_sum w1 w2 Hdef) =
  resA_sum (resA_swap x y w1) (resA_swap x y w2) Hdef'.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. reflexivity.
  - intros σ. simpl. split.
    + intros [σ0 [[Hσ0 | Hσ0] Hswap]].
      * rewrite <- Hswap. left. exists σ0. split; [exact Hσ0 | reflexivity].
      * rewrite <- Hswap. right. exists σ0. split; [exact Hσ0 | reflexivity].
    + intros [[σ0 [Hσ0 Hswap]] | [σ0 [Hσ0 Hswap]]].
      * rewrite <- Hswap. exists σ0. split; [left; exact Hσ0 | reflexivity].
      * rewrite <- Hswap. exists σ0. split; [right; exact Hσ0 | reflexivity].
Qed.

Lemma resA_product_double_swap_l (x y : K) (w1 w2 : WfWorldAT)
    (Hc : worldA_compat w1 w2)
    (Hc' : worldA_compat (resA_swap x y (resA_swap x y w1)) w2) :
  resA_product (resA_swap x y (resA_swap x y w1)) w2 Hc' =
  resA_product w1 w2 Hc.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl.
    change (gset_swap x y (gset_swap x y (worldA_dom (w1 : WorldAT))) ∪
      worldA_dom (w2 : WorldAT) =
      worldA_dom (w1 : WorldAT) ∪ worldA_dom (w2 : WorldAT)).
    rewrite gset_swap_involutive. reflexivity.
  - intros σ. simpl. split.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      destruct Hσ1 as [τ1 [[τ0 [Hτ0 Hswap0]] Hswap1]].
      rewrite <- Hswap1, <- Hswap0 in Hcompat |- *.
      change (@storeA_compat V K _ _
        (@storeA_swap V K _ _ _ x y (@storeA_swap V K _ _ _ x y τ0)) σ2) in Hcompat.
      rewrite storeA_swap_involutive in Hcompat.
      replace (@storeA_rekey V K _ _ (key_swap x y)
        (@storeA_rekey V K _ _ (key_swap x y) τ0)) with (τ0 : StoreAT).
      2:{
        symmetry. exact (storeA_swap_involutive x y τ0).
      }
      exists τ0, σ2. repeat split; eauto.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      exists σ1, σ2. split.
      * exists (@storeA_swap V K _ _ _ x y σ1). split.
        -- exists σ1. split; [exact Hσ1 | reflexivity].
        -- change (@storeA_swap V K _ _ _ x y
             (@storeA_swap V K _ _ _ x y σ1) = σ1).
           apply storeA_swap_involutive.
      * split; [exact Hσ2 |]. split; [exact Hcompat | reflexivity].
Qed.

Lemma resA_restrict_le (w : WfWorldAT) (X : gset K) :
  resA_restrict w X ⊑ w.
Proof.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σ' [Hσ' Hrestrict]]. subst σ.
      exists σ'. split; [exact Hσ' |].
      pose proof (wfworldA_store_dom w σ' Hσ') as Hdomσ'.
      change (dom (σ' : gmap K V) = worldA_dom (w : WorldAT)) in Hdomσ'.
      rewrite <- (storeA_restrict_idemp σ' (worldA_dom (w : WorldAT))) at 2
        by set_solver.
      rewrite storeA_restrict_restrict. reflexivity.
    + intros [σ' [Hσ' Hrestrict]].
      exists σ'. split; [exact Hσ' |].
      pose proof (wfworldA_store_dom w σ' Hσ') as Hdomσ'.
      change (dom (σ' : gmap K V) = worldA_dom (w : WorldAT)) in Hdomσ'.
      rewrite <- Hrestrict.
      rewrite <- (storeA_restrict_idemp σ' (worldA_dom (w : WorldAT))) at 1
        by set_solver.
      rewrite storeA_restrict_restrict. reflexivity.
Qed.

Lemma resA_restrict_mono (w : WfWorldAT) (X Y : gset K) :
  X ⊆ Y →
  resA_restrict w X ⊑ resA_restrict w Y.
Proof.
  intros HXY.
  replace (resA_restrict w X) with (resA_restrict (resA_restrict w Y) X).
  2:{
    rewrite resA_restrict_restrict_eq.
    replace (Y ∩ X) with X by set_solver.
    reflexivity.
  }
  apply resA_restrict_le.
Qed.

Lemma resA_restrict_eq_of_le (m n : WfWorldAT) :
  m ⊑ n →
  resA_restrict n (worldA_dom (m : WorldAT)) = m.
Proof.
  intros Hle.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
  symmetry. apply wfworldA_ext. exact Hle.
Qed.

Lemma resA_le_restrict (m n : WfWorldAT) (X : gset K) :
  m ⊑ n →
  worldA_dom (m : WorldAT) ⊆ X →
  m ⊑ resA_restrict n X.
Proof.
  intros Hle Hdom.
  rewrite <- (resA_restrict_eq_of_le m n Hle).
  apply resA_restrict_mono. exact Hdom.
Qed.

Lemma resA_restrict_le_mono (m n : WfWorldAT) (X : gset K) :
  m ⊑ n →
  resA_restrict m X ⊑ resA_restrict n X.
Proof.
  intros Hle.
  eapply resA_le_restrict.
  - etrans; [apply resA_restrict_le | exact Hle].
  - simpl. set_solver.
Qed.

Lemma resA_swap_le (x y : K) (w1 w2 : WfWorldAT) :
  w1 ⊑ w2 →
  resA_swap x y w1 ⊑ resA_swap x y w2.
Proof.
  intros Hle.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  change ((resA_swap x y w1 : WorldAT) =
    (resA_restrict (resA_swap x y w2)
      (gset_swap x y (worldA_dom (w1 : WorldAT))) : WorldAT)).
  rewrite (resA_restrict_swap x y w2 (worldA_dom (w1 : WorldAT))).
  rewrite (resA_restrict_eq_of_le w1 w2 Hle). reflexivity.
Qed.

Lemma resA_swap_le_iff (x y : K) (w1 w2 : WfWorldAT) :
  resA_swap x y w1 ⊑ resA_swap x y w2 ↔ w1 ⊑ w2.
Proof.
  split.
  - intros Hle.
    pose proof (resA_swap_le x y _ _ Hle) as Hswap.
    rewrite !resA_swap_involutive in Hswap. exact Hswap.
  - apply resA_swap_le.
Qed.

Lemma resA_restrict_le_eq (m n : WfWorldAT) (X : gset K) :
  m ⊑ n →
  X ⊆ worldA_dom (m : WorldAT) →
  resA_restrict m X = resA_restrict n X.
Proof.
  intros Hle HX.
  rewrite <- (resA_restrict_eq_of_le m n Hle).
  rewrite resA_restrict_restrict_eq.
  replace (worldA_dom (m : WorldAT) ∩ X) with X by set_solver.
  reflexivity.
Qed.

Lemma resA_restrict_le_eq_from_base
    (m n : WfWorldAT) (S X : gset K) :
  resA_restrict m S ⊑ n →
  X ⊆ S →
  X ⊆ worldA_dom (m : WorldAT) →
  resA_restrict n X = resA_restrict m X.
Proof.
  intros Hle HXS HXm.
  rewrite <- (resA_restrict_le_eq (resA_restrict m S) n X Hle).
  - rewrite resA_restrict_restrict_eq.
    replace (S ∩ X) with X by set_solver.
    reflexivity.
  - simpl. set_solver.
Qed.

Lemma resA_restrict_eq_subset
    (m n : WfWorldAT) (X Y : gset K) :
  Y ⊆ X →
  resA_restrict m X = resA_restrict n X →
  resA_restrict m Y = resA_restrict n Y.
Proof.
  intros HYX Hproj.
  transitivity (resA_restrict (resA_restrict m X) Y).
  - rewrite resA_restrict_restrict_eq.
    replace (X ∩ Y) with Y by set_solver.
    reflexivity.
  - rewrite Hproj.
    rewrite resA_restrict_restrict_eq.
    replace (X ∩ Y) with Y by set_solver.
    reflexivity.
Qed.

Lemma resA_fiber_from_projection_le
    (m n wfib_m wfib_n : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_fiber_from_projection m X σ wfib_m →
  resA_fiber_from_projection n X σ wfib_n →
  m ⊑ n →
  X ⊆ worldA_dom (m : WorldAT) →
  wfib_m ⊑ wfib_n.
Proof.
  intros [Hproj_m Heq_m] [Hproj_n Heq_n] Hle HX.
  assert (Hdomσ : dom (σ : gmap K V) ⊆ X).
  {
    simpl in Hproj_n.
    destruct Hproj_n as [σn [Hσn Hrestr]].
    pose proof (f_equal (fun s : gmap K V => dom s) Hrestr) as Hdomrestr.
    change (dom (@storeA_restrict V K _ _ σn X : gmap K V) =
      dom (σ : gmap K V)) in Hdomrestr.
    rewrite <- Hdomrestr.
    pose proof (storeA_restrict_dom σn X) as Hdomr.
    change (dom (@storeA_restrict V K _ _ σn X : gmap K V) =
      dom (σn : gmap K V) ∩ X) in Hdomr.
    rewrite Hdomr. set_solver.
  }
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - rewrite Heq_m, Heq_n. simpl. pose proof (rawA_le_dom m n Hle). set_solver.
  - intros τ. rewrite Heq_m, Heq_n. simpl. split.
    + intros [Hmτ Hτ].
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
      rewrite Hle in Hmτ. simpl in Hmτ.
      destruct Hmτ as [τn [Hnτ Hrestrict]].
      exists τn. split.
      * split; [exact Hnτ |].
        transitivity (@storeA_restrict V K _ _ τ (dom σ)); [| exact Hτ].
        rewrite <- Hrestrict.
        rewrite storeA_restrict_restrict.
        replace (worldA_dom (m : WorldAT) ∩ dom (σ : gmap K V))
          with (dom (σ : gmap K V)) by set_solver.
        reflexivity.
      * exact Hrestrict.
    + intros [τn [[Hnτ Hτn] Hrestrict]].
      split.
      * unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
        rewrite Hle. simpl. exists τn. split; [exact Hnτ | exact Hrestrict].
      * transitivity (@storeA_restrict V K _ _ τn (dom σ)); [| exact Hτn].
        rewrite <- Hrestrict.
        rewrite storeA_restrict_restrict.
        replace (worldA_dom (m : WorldAT) ∩ dom (σ : gmap K V))
          with (dom (σ : gmap K V)) by set_solver.
        reflexivity.
Qed.

Lemma resA_fiber_from_projection_eq_on
    (m n wfib_m wfib_n : WfWorldAT) (D X : gset K) (σ : StoreAT) :
  D ⊆ X →
  resA_restrict m X = resA_restrict n X →
  resA_fiber_from_projection m D σ wfib_m →
  resA_fiber_from_projection n D σ wfib_n →
  resA_restrict wfib_m X = resA_restrict wfib_n X.
Proof.
  intros HDX Hproj [Hσproj_m Heq_m] [Hσproj_n Heq_n].
  assert (HdomσX : dom (σ : gmap K V) ⊆ X).
  {
    destruct Hσproj_m as [σm [Hσm Hrestr]].
    change (dom (σ : gmap K V) ⊆ X).
    rewrite <- Hrestr.
    change (dom (@storeA_restrict V K _ _ σm D : gmap K V) ⊆ X).
    pose proof (storeA_restrict_dom σm D) as Hdomr.
    change (dom (@storeA_restrict V K _ _ σm D : gmap K V) =
      dom (σm : gmap K V) ∩ D) in Hdomr.
    rewrite Hdomr. set_solver.
  }
  apply wfworldA_ext. apply worldA_ext.
  - simpl.
    pose proof (f_equal (fun w : WfWorldAT => worldA_dom (w : WorldAT)) Hproj)
      as Hdom.
    simpl in Hdom. rewrite Heq_m, Heq_n. simpl. set_solver.
  - intros τ. simpl. rewrite Heq_m, Heq_n. split.
    + intros [τm [[Hτm HτD] HτX]].
      assert (HτmX : (resA_restrict m X : WorldAT)
          (@storeA_restrict V K _ _ τm X)).
      { exists τm. split; [exact Hτm | reflexivity]. }
      rewrite Hproj in HτmX.
      destruct HτmX as [τn [Hτn HτnX]].
      exists τn. split.
      * split; [exact Hτn |].
        transitivity (@storeA_restrict V K _ _ τm (dom (σ : gmap K V))).
        -- eapply storeA_restrict_eq_mono; [exact HdomσX | exact HτnX].
        -- exact HτD.
      * rewrite HτnX. exact HτX.
    + intros [τn [[Hτn HτD] HτX]].
      assert (HτnX : (resA_restrict n X : WorldAT)
          (@storeA_restrict V K _ _ τn X)).
      { exists τn. split; [exact Hτn | reflexivity]. }
      rewrite <- Hproj in HτnX.
      destruct HτnX as [τm [Hτm HτmX]].
      exists τm. split.
      * split; [exact Hτm |].
        transitivity (@storeA_restrict V K _ _ τn (dom (σ : gmap K V))).
        -- eapply storeA_restrict_eq_mono; [exact HdomσX | exact HτmX].
        -- exact HτD.
      * rewrite HτmX. exact HτX.
Qed.

Lemma resA_fiber_member_projection_transport_on
    (m n nfib : WfWorldAT) (D X : gset K) :
  D ⊆ X →
  D ⊆ worldA_dom (m : WorldAT) →
  resA_restrict m X = resA_restrict n X →
  resA_fiber_member n D nfib →
  ∃ mfib,
    resA_fiber_member m D mfib ∧
    resA_restrict mfib X = resA_restrict nfib X.
Proof.
  intros HDX HDm Hproj [σ Hfiber_n].
  pose proof (resA_restrict_eq_subset m n X D HDX Hproj) as HprojD.
  destruct Hfiber_n as [Hσproj_n Heq_n].
  assert ((resA_restrict m D : WorldAT) σ) as Hσproj_m.
  { rewrite HprojD. exact Hσproj_n. }
  destruct Hσproj_m as [σm [Hσm Hrestrict_m]].
  assert (Hdomσ : dom (σ : gmap K V) = D).
  {
    rewrite <- Hrestrict_m.
    change (dom (@storeA_restrict V K _ _ σm D : gmap K V) = D).
    pose proof (storeA_restrict_dom σm D) as Hdomr.
    change (dom (@storeA_restrict V K _ _ σm D : gmap K V) =
      dom (σm : gmap K V) ∩ D) in Hdomr.
    rewrite Hdomr.
    pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
    change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
    rewrite Hdomσm. set_solver.
  }
  assert (Hnonempty_m :
      ∃ σm0, (m : WorldAT) σm0 ∧
        @storeA_restrict V K _ _ σm0 (dom (σ : gmap K V)) = σ).
  {
    exists σm. split; [exact Hσm |].
    rewrite Hdomσ. exact Hrestrict_m.
  }
  set (mfib := resA_fiber m σ Hnonempty_m).
  assert (Hfiber_m : resA_fiber_from_projection m D σ mfib).
  {
    split.
    - exists σm. split; [exact Hσm | exact Hrestrict_m].
    - subst mfib. unfold resA_fiber. simpl. reflexivity.
  }
  exists mfib. split.
  - exists σ. exact Hfiber_m.
  - eapply resA_fiber_from_projection_eq_on; eauto.
    split; [exact Hσproj_n | exact Heq_n].
Qed.

End ResourceAlgebraA.
