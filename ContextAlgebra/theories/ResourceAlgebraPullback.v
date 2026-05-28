From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict.
From Stdlib Require Import Logic.ProofIrrelevance.

From ContextAlgebra Require Import ResourceAlgebraBase ResourceAlgebraOrder.

(** * Pullback and product-lifting lemmas for abstract resource algebra *)

Section ResourceAlgebraA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition rawA_pullback_projection (n p : WfWorldAT) : WorldAT := {|
  worldA_dom := worldA_dom (n : WorldAT);
  worldA_stores := fun σ =>
    (n : WorldAT) σ ∧
    (p : WorldAT) (@storeA_restrict V K _ _ σ (worldA_dom (p : WorldAT)));
|}.

Lemma rawA_pullback_projection_wf (n p : WfWorldAT) :
  p ⊑ n →
  wf_worldA (rawA_pullback_projection n p).
Proof.
  intros Hle. constructor.
  - destruct (worldA_wf p) as [[σp Hp] _].
    pose proof (resA_restrict_eq_of_le p n Hle) as Hrestrict.
    change (resA_restrict n (worldA_dom (p : WorldAT)) = p) in Hrestrict.
    assert ((resA_restrict n (worldA_dom (p : WorldAT)) : WorldAT) σp) as Hσp.
    { rewrite Hrestrict. exact Hp. }
    simpl in Hσp.
    destruct Hσp as [σn [Hσn Hproj]].
    exists σn. split; [exact Hσn |].
    rewrite Hproj. exact Hp.
  - intros σ [Hσ _]. simpl. exact (wfworldA_store_dom n σ Hσ).
Qed.

Definition resA_pullback_projection (n p : WfWorldAT) (Hle : p ⊑ n) : WfWorldAT :=
  exist _ (rawA_pullback_projection n p)
    (rawA_pullback_projection_wf n p Hle).

Definition rawA_pullback_subset_projection (n p : WfWorldAT) : WorldAT := {|
  worldA_dom := worldA_dom (n : WorldAT);
  worldA_stores := fun σ =>
    (n : WorldAT) σ ∧
    (p : WorldAT) (@storeA_restrict V K _ _ σ (worldA_dom (p : WorldAT)));
|}.

Lemma rawA_pullback_subset_projection_wf (n p : WfWorldAT) :
  resA_subset p (resA_restrict n (worldA_dom (p : WorldAT))) →
  wf_worldA (rawA_pullback_subset_projection n p).
Proof.
  intros Hsub. constructor.
  - destruct Hsub as [_ Hstores].
    destruct (worldA_wf p) as [[σp Hp] _].
    specialize (Hstores σp Hp).
    simpl in Hstores.
    destruct Hstores as [σn [Hσn Hproj]].
    exists σn. split; [exact Hσn |].
    rewrite Hproj. exact Hp.
  - intros σ [Hσ _]. simpl. exact (wfworldA_store_dom n σ Hσ).
Qed.

Definition resA_pullback_subset_projection (n p : WfWorldAT)
    (Hsub : resA_subset p (resA_restrict n (worldA_dom (p : WorldAT)))) :
    WfWorldAT :=
  exist _ (rawA_pullback_subset_projection n p)
    (rawA_pullback_subset_projection_wf n p Hsub).

Lemma resA_pullback_subset_projection_subset (n p : WfWorldAT) Hsub :
  resA_subset (resA_pullback_subset_projection n p Hsub) n.
Proof.
  split; [reflexivity |].
  intros σ [Hσ _]. exact Hσ.
Qed.

Lemma resA_pullback_subset_projection_restrict (n p : WfWorldAT) Hsub :
  resA_restrict (resA_pullback_subset_projection n p Hsub)
    (worldA_dom (p : WorldAT)) = p.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. destruct Hsub as [Hdom _]. simpl in Hdom. set_solver.
  - intros σ. simpl. split.
    + intros [σn [[Hσn Hpσ] Hrestrict]].
      subst σ. exact Hpσ.
    + intros Hpσ.
      destruct Hsub as [_ Hstores].
      specialize (Hstores σ Hpσ).
      simpl in Hstores.
      destruct Hstores as [σn [Hσn Hproj]].
      exists σn. split; [split; [exact Hσn | rewrite Hproj; exact Hpσ] |].
      exact Hproj.
Qed.

Lemma resA_pullback_projection_subset (n p : WfWorldAT) Hle :
  resA_subset (resA_pullback_projection n p Hle) n.
Proof.
  split; [reflexivity |].
  intros σ [Hσ _]. exact Hσ.
Qed.

Lemma resA_pullback_projection_restrict (n p : WfWorldAT) Hle :
  resA_restrict (resA_pullback_projection n p Hle)
    (worldA_dom (p : WorldAT)) = p.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl.
    pose proof (rawA_le_dom p n Hle). set_solver.
  - intros σ. simpl. split.
    + intros [σn [[Hσn Hpσ] Hrestrict]].
      subst σ. exact Hpσ.
    + intros Hpσ.
      pose proof (resA_restrict_eq_of_le p n Hle) as Hrestrict.
      change (resA_restrict n (worldA_dom (p : WorldAT)) = p) in Hrestrict.
      assert ((resA_restrict n (worldA_dom (p : WorldAT)) : WorldAT) σ) as Hσ.
      { rewrite Hrestrict. exact Hpσ. }
      simpl in Hσ.
      destruct Hσ as [σn [Hσn Hproj]].
      exists σn. split; [split; [exact Hσn | rewrite Hproj; exact Hpσ] |].
      exact Hproj.
Qed.

Lemma resA_sum_pullback_subset_projection_full
    (n n1 n2 : WfWorldAT) (Hdef : rawA_sum_defined n1 n2) :
  resA_sum n1 n2 Hdef ⊑ n →
  ∃ (Hsub1 : resA_subset n1 (resA_restrict n (worldA_dom (n1 : WorldAT))))
    (Hsub2 : resA_subset n2 (resA_restrict n (worldA_dom (n2 : WorldAT))))
    (Hdef_full : rawA_sum_defined
      (resA_pullback_subset_projection n n1 Hsub1)
      (resA_pullback_subset_projection n n2 Hsub2)),
    resA_sum
      (resA_pullback_subset_projection n n1 Hsub1)
      (resA_pullback_subset_projection n n2 Hsub2)
      Hdef_full ⊑ n.
Proof.
  intros Hsum_le.
  change ((resA_sum n1 n2 Hdef : WorldAT) =
    rawA_restrict n (worldA_dom (resA_sum n1 n2 Hdef : WorldAT))) in Hsum_le.
  pose proof (rawA_le_dom (resA_sum n1 n2 Hdef) n Hsum_le) as Hdom_sum_n.
  assert (Hsub1 : resA_subset n1 (resA_restrict n (worldA_dom (n1 : WorldAT)))).
  {
    split.
    - simpl. unfold rawA_sum_defined in Hdef. set_solver.
    - intros σ Hσ.
      assert ((resA_restrict n (worldA_dom (resA_sum n1 n2 Hdef : WorldAT)) : WorldAT) σ)
        as Hrestrict.
      { change ((rawA_restrict n (worldA_dom (resA_sum n1 n2 Hdef : WorldAT))
           : WorldAT) σ).
        rewrite <- Hsum_le. simpl. left. exact Hσ. }
      exact Hrestrict.
  }
  assert (Hsub2 : resA_subset n2 (resA_restrict n (worldA_dom (n2 : WorldAT)))).
  {
    split.
    - simpl. unfold rawA_sum_defined in Hdef. set_solver.
    - intros σ Hσ.
      assert ((resA_restrict n (worldA_dom (resA_sum n1 n2 Hdef : WorldAT)) : WorldAT) σ)
        as Hrestrict.
      { change ((rawA_restrict n (worldA_dom (resA_sum n1 n2 Hdef : WorldAT))
           : WorldAT) σ).
        rewrite <- Hsum_le. simpl. right. exact Hσ. }
      unfold rawA_sum_defined in Hdef.
      replace (worldA_dom (resA_sum n1 n2 Hdef : WorldAT))
        with (worldA_dom (n2 : WorldAT)) in Hrestrict by (simpl; symmetry; exact Hdef).
      exact Hrestrict.
  }
  assert (Hdef_full : rawA_sum_defined
      (resA_pullback_subset_projection n n1 Hsub1)
      (resA_pullback_subset_projection n n2 Hsub2)).
  { unfold rawA_sum_defined. reflexivity. }
  exists Hsub1, Hsub2, Hdef_full.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [Hleft | Hright]; destruct Hleft as [Hσ _] || destruct Hright as [Hσ _].
      * exists σ. split; [exact Hσ |].
        apply storeA_restrict_idemp.
        pose proof (wfworldA_store_dom n σ Hσ) as Hdomσ.
        change (dom (σ : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσ.
        set_solver.
      * exists σ. split; [exact Hσ |].
        apply storeA_restrict_idemp.
        pose proof (wfworldA_store_dom n σ Hσ) as Hdomσ.
        change (dom (σ : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσ.
        set_solver.
    + intros [σn [Hσ Hrestrict]].
      subst σ.
      rewrite storeA_restrict_idemp by
        (pose proof (wfworldA_store_dom n σn Hσ) as Hdomσ;
         change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσ;
         set_solver).
      assert (Hσsum : (resA_sum n1 n2 Hdef : WorldAT)
          (@storeA_restrict V K _ _ σn (worldA_dom (n1 : WorldAT)))).
      {
        rewrite Hsum_le. simpl.
        exists σn. split; [exact Hσ | reflexivity].
      }
      simpl in Hσsum.
      destruct Hσsum as [Hσ1 | Hσ2].
      * left. split; [exact Hσ | exact Hσ1].
	      * right. split; [exact Hσ |].
	        unfold rawA_sum_defined in Hdef.
	        replace (worldA_dom (n2 : WorldAT)) with (worldA_dom (n1 : WorldAT))
	          by exact Hdef.
	        exact Hσ2.
Qed.

Lemma resA_product_le_mono (w1 w2 w1' w2' : WfWorldAT)
    (Hc : worldA_compat w1 w2) (Hc' : worldA_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  resA_product w1 w2 Hc ⊑ resA_product w1' w2' Hc'.
Proof.
  intros Hle1 Hle2.
  pose proof (rawA_le_dom w1 w1' Hle1) as Hdom1.
  pose proof (rawA_le_dom w2 w2' Hle2) as Hdom2.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in *.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      destruct Hσ as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      rewrite Hle1 in Hσ1. simpl in Hσ1.
      rewrite Hle2 in Hσ2. simpl in Hσ2.
      destruct Hσ1 as [σ1' [Hσ1' Hrestr1]].
      destruct Hσ2 as [σ2' [Hσ2' Hrestr2]].
      pose proof (Hc' σ1' σ2' Hσ1' Hσ2') as Hcompat'.
      exists (@union (gmap K V) _ (σ1' : gmap K V) (σ2' : gmap K V)). split.
      * exists σ1', σ2'. repeat split; eauto.
      * rewrite storeA_restrict_union_cover.
        -- rewrite Hrestr1, Hrestr2. reflexivity.
        -- exact Hcompat'.
        -- pose proof (wfworldA_store_dom w1' σ1' Hσ1') as Hdomσ1'.
           change (dom (σ1' : gmap K V) = worldA_dom (w1' : WorldAT)) in Hdomσ1'.
           set_solver.
        -- pose proof (wfworldA_store_dom w2' σ2' Hσ2') as Hdomσ2'.
           change (dom (σ2' : gmap K V) = worldA_dom (w2' : WorldAT)) in Hdomσ2'.
           set_solver.
    + intros [σ' [Hσ' Hrestrict]].
      destruct Hσ' as [σ1' [σ2' [Hσ1' [Hσ2' [Hcompat' ->]]]]].
      set (σ1 := @storeA_restrict V K _ _ σ1' (worldA_dom (w1 : WorldAT))).
      set (σ2 := @storeA_restrict V K _ _ σ2' (worldA_dom (w2 : WorldAT))).
      assert (Hσ1 : (w1 : WorldAT) σ1).
      {
        rewrite Hle1. simpl. exists σ1'. split; [exact Hσ1' | reflexivity].
      }
      assert (Hσ2 : (w2 : WorldAT) σ2).
      {
        rewrite Hle2. simpl. exists σ2'. split; [exact Hσ2' | reflexivity].
      }
      exists σ1, σ2. repeat split.
      * exact Hσ1.
      * exact Hσ2.
      * exact (Hc σ1 σ2 Hσ1 Hσ2).
      * subst σ1 σ2.
        rewrite <- Hrestrict.
        rewrite storeA_restrict_union_cover.
        -- reflexivity.
        -- exact Hcompat'.
        -- pose proof (wfworldA_store_dom w1' σ1' Hσ1') as Hdomσ1'.
           change (dom (σ1' : gmap K V) = worldA_dom (w1' : WorldAT)) in Hdomσ1'.
           set_solver.
        -- pose proof (wfworldA_store_dom w2' σ2' Hσ2') as Hdomσ2'.
           change (dom (σ2' : gmap K V) = worldA_dom (w2' : WorldAT)) in Hdomσ2'.
           set_solver.
Qed.

Lemma resA_subset_lift_under (m n mu : WfWorldAT) :
  m ⊑ n →
  resA_subset mu m →
  ∃ nu : WfWorldAT,
    resA_subset nu n ∧ mu ⊑ nu.
Proof.
  intros Hle [Hdom_mu_m Hin_mu_m].
  pose proof (rawA_le_dom m n Hle) as Hdom_m_n.
  pose (raw_nu := ({|
    worldA_dom := worldA_dom (n : WorldAT);
    worldA_stores := λ σ,
      (n : WorldAT) σ ∧
      (mu : WorldAT) (@storeA_restrict V K _ _ σ (worldA_dom (m : WorldAT)))
  |} : WorldAT)).
  assert (Hwf_nu : wf_worldA raw_nu).
  {
    constructor.
    - destruct (wfA_ne _ (worldA_wf mu)) as [σmu Hσmu].
      assert (Hmσmu : (m : WorldAT) σmu) by exact (Hin_mu_m σmu Hσmu).
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
      rewrite Hle in Hmσmu. simpl in Hmσmu.
      destruct Hmσmu as [σn [Hσn Hrestrict]].
      exists σn. split; [exact Hσn |].
      rewrite Hrestrict. exact Hσmu.
    - intros σ [Hσn _]. simpl. exact (wfworldA_store_dom n σ Hσn).
  }
  exists (exist _ raw_nu Hwf_nu). split.
  - split; [reflexivity | intros σ Hσ; exact (proj1 Hσ)].
  - unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
    apply worldA_ext.
    + simpl. set_solver.
    + intros σ. simpl. split.
      * intros Hσmu.
        assert (Hmσ : (m : WorldAT) σ) by exact (Hin_mu_m σ Hσmu).
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
        rewrite Hle in Hmσ. simpl in Hmσ.
        destruct Hmσ as [σn [Hσn Hrestrict]].
        exists σn. split; [split; [exact Hσn | rewrite Hrestrict; exact Hσmu] |].
        rewrite Hdom_mu_m. exact Hrestrict.
      * intros [σn [[Hσn Hσmu] Hrestrict]].
        rewrite Hdom_mu_m in Hrestrict.
        subst σ. exact Hσmu.
Qed.

Lemma resA_le_product_l (w1 w2 : WfWorldAT) (Hc : worldA_compat w1 w2) :
  w1 ⊑ resA_product w1 w2 Hc.
Proof.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      destruct (wfA_ne _ (worldA_wf w2)) as [σ2 Hσ2].
      exists (@union (gmap K V) _ (σ : gmap K V) (σ2 : gmap K V)). split.
      * exists σ, σ2. repeat split; eauto.
      * rewrite storeA_restrict_union by exact (Hc σ σ2 Hσ Hσ2).
        rewrite storeA_restrict_idemp.
        -- apply storeA_union_absorb_l.
           ++ apply storeA_compat_restrict_r. exact (Hc σ σ2 Hσ Hσ2).
           ++ pose proof (storeA_restrict_dom σ2 (worldA_dom (w1 : WorldAT))) as Hdomr.
              change (dom (@storeA_restrict V K _ _ σ2 (worldA_dom (w1 : WorldAT)) : gmap K V) =
                dom (σ2 : gmap K V) ∩ worldA_dom (w1 : WorldAT)) in Hdomr.
              rewrite Hdomr.
              pose proof (wfworldA_store_dom w1 σ Hσ) as Hdomσ.
              change (dom (σ : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdomσ.
              set_solver.
        -- pose proof (wfworldA_store_dom w1 σ Hσ) as Hdomσ.
           change (dom (σ : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdomσ.
           set_solver.
    + intros [σ12 [Hσ12 Hrestrict]].
      destruct Hσ12 as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      rewrite storeA_restrict_union in Hrestrict by exact Hcompat.
      rewrite storeA_restrict_idemp in Hrestrict.
      * rewrite (storeA_union_absorb_l σ1
          (@storeA_restrict V K _ _ σ2 (worldA_dom (w1 : WorldAT)))) in Hrestrict.
        -- subst. exact Hσ1.
        -- apply storeA_compat_restrict_r. exact Hcompat.
        -- pose proof (storeA_restrict_dom σ2 (worldA_dom (w1 : WorldAT))) as Hdomr.
           change (dom (@storeA_restrict V K _ _ σ2 (worldA_dom (w1 : WorldAT)) : gmap K V) =
             dom (σ2 : gmap K V) ∩ worldA_dom (w1 : WorldAT)) in Hdomr.
           rewrite Hdomr.
           pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdomσ1.
           change (dom (σ1 : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdomσ1.
           set_solver.
      * pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdomσ1.
        change (dom (σ1 : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdomσ1.
        set_solver.
Qed.

Lemma resA_one_point_extension_exists (w : WfWorldAT) (y : K) :
  y ∉ worldA_dom (w : WorldAT) →
  ∃ wy : WfWorldAT,
    worldA_dom (wy : WorldAT) = worldA_dom (w : WorldAT) ∪ {[y]} ∧
    resA_restrict wy (worldA_dom (w : WorldAT)) = w.
Proof.
  intros Hy.
  set (σy := <[y := inhabitant]> (∅ : StoreAT)).
  set (one_y := (exist _ (singleton_worldA σy) (wf_singleton_worldA σy) : WfWorldAT)).
  assert (Hdom_one_y : worldA_dom (one_y : WorldAT) = {[y]}).
  {
    subst one_y σy. simpl.
    apply set_eq. intros z.
    destruct (decide (z = y)) as [->|Hzy].
    - split; intros _.
      + apply elem_of_singleton. reflexivity.
      + change (y ∈ dom (<[y := inhabitant]> (∅ : gmap K V) : gmap K V)).
        eapply elem_of_dom_2.
        rewrite lookup_insert. destruct (decide (y = y)); [reflexivity | congruence].
    - split.
      + intros Hz.
        change (z ∈ dom (<[y := inhabitant]> (∅ : gmap K V) : gmap K V)) in Hz.
        apply elem_of_dom in Hz as [vz Hz].
        change ((<[y := inhabitant]> (∅ : gmap K V)) !! z = Some vz) in Hz.
        rewrite lookup_insert_ne in Hz by congruence.
        rewrite (lookup_empty (M:=gmap K) (A:=V)) in Hz. discriminate.
      + intros Hz. set_solver.
  }
  assert (Hc : worldA_compat w one_y).
  {
    apply disj_dom_worldA_compat. rewrite Hdom_one_y. set_solver.
  }
  exists (resA_product w one_y Hc). split.
  - change (worldA_dom (w : WorldAT) ∪ worldA_dom (one_y : WorldAT) =
      worldA_dom (w : WorldAT) ∪ {[y]}).
    rewrite Hdom_one_y. reflexivity.
  - rewrite <- (resA_restrict_le_eq w (resA_product w one_y Hc)
      (worldA_dom (w : WorldAT)) (resA_le_product_l w one_y Hc)).
    + apply resA_restrict_eq_of_le. reflexivity.
    + set_solver.
Qed.

Lemma resA_product_complement_lift_subset
    (m n mo : WfWorldAT) (Hle : m ⊑ n)
    (Hsub : resA_subset m mo) :
  ∀ Hc : worldA_compat mo
      (resA_restrict n (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT))),
    resA_subset n
      (resA_product mo
        (resA_restrict n (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)))
        Hc).
Proof.
  intros Hc.
  destruct Hsub as [Hdom_m_mo Hin_m_mo].
  pose proof (rawA_le_dom m n Hle) as Hdom_m_n.
  split.
  - simpl.
    apply set_eq. intros x. split.
    + intros Hx.
      apply elem_of_union.
      destruct (decide (x ∈ worldA_dom (m : WorldAT))) as [Hxm|Hxnm].
      * left. rewrite <- Hdom_m_mo. exact Hxm.
      * right. apply elem_of_intersection. split; [exact Hx |].
        apply elem_of_difference. split; [exact Hx | exact Hxnm].
    + intros Hx.
      apply elem_of_union in Hx as [Hxmo|Hxdiff].
      * apply Hdom_m_n. rewrite Hdom_m_mo. exact Hxmo.
      * apply elem_of_intersection in Hxdiff as [Hx _]. exact Hx.
  - intros σ Hσn.
    pose proof (wfworldA_store_dom n σ Hσn) as Hdomσ.
    change (dom (σ : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσ.
    assert (Hm_proj :
        (m : WorldAT) (@storeA_restrict V K _ _ σ (worldA_dom (m : WorldAT)))).
    {
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
      rewrite Hle at 1. simpl. exists σ. split; [exact Hσn | reflexivity].
    }
    assert (Hmo_proj :
        (mo : WorldAT) (@storeA_restrict V K _ _ σ (worldA_dom (m : WorldAT)))).
    { exact (Hin_m_mo _ Hm_proj). }
    assert (Hextra :
        (resA_restrict n (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)) : WorldAT)
          (@storeA_restrict V K _ _ σ
            (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)))).
    {
      simpl. exists σ. split; [exact Hσn | reflexivity].
    }
    assert (Hstore_part_compat :
        @storeA_compat V K _ _
          (@storeA_restrict V K _ _ σ (worldA_dom (m : WorldAT)))
          (@storeA_restrict V K _ _ σ
            (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)))).
    {
      apply storeA_disj_dom_compat.
      apply set_eq. intros x. split.
      - intros Hin.
        apply elem_of_intersection in Hin as [Hin1 Hin2].
        pose proof (storeA_restrict_dom σ (worldA_dom (m : WorldAT))) as Hdom1.
        pose proof (storeA_restrict_dom σ
          (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT))) as Hdom2.
        change (dom (@storeA_restrict V K _ _ σ (worldA_dom (m : WorldAT)) : gmap K V) =
          dom (σ : gmap K V) ∩ worldA_dom (m : WorldAT)) in Hdom1.
        change (dom (@storeA_restrict V K _ _ σ
          (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)) : gmap K V) =
          dom (σ : gmap K V) ∩
            (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT))) in Hdom2.
        rewrite Hdom1 in Hin1. rewrite Hdom2 in Hin2.
        apply elem_of_intersection in Hin1 as [_ Hxm].
        apply elem_of_intersection in Hin2 as [_ Hxdiff].
        apply elem_of_difference in Hxdiff as [_ Hxnotm].
        exfalso. exact (Hxnotm Hxm).
      - intros Hin. apply elem_of_empty in Hin. contradiction.
    }
    simpl.
    exists (@storeA_restrict V K _ _ σ (worldA_dom (m : WorldAT))),
      (@storeA_restrict V K _ _ σ
        (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT))).
    repeat split.
    + exact Hmo_proj.
    + exact Hextra.
    + exact Hstore_part_compat.
    + symmetry. apply storeA_restrict_union_partition.
      * intros x Hx. change (x ∈ dom (σ : gmap K V)) in Hx.
        rewrite Hdomσ in Hx.
        apply elem_of_union.
        destruct (decide (x ∈ worldA_dom (m : WorldAT))) as [Hxm|Hxnm].
        -- left. exact Hxm.
        -- right. apply elem_of_difference. split; [exact Hx | exact Hxnm].
      * apply set_eq. intros x. split.
        -- intros Hin.
           apply elem_of_intersection in Hin as [Hxm Hxdiff].
           apply elem_of_difference in Hxdiff as [_ Hxnotm].
           exfalso. exact (Hxnotm Hxm).
        -- intros Hin. apply elem_of_empty in Hin. contradiction.
Qed.

Lemma resA_subset_lift_over (m n mo : WfWorldAT) :
  m ⊑ n →
  resA_subset m mo →
  ∃ no : WfWorldAT,
    resA_subset n no ∧ mo ⊑ no.
Proof.
  intros Hle Hsub.
  destruct Hsub as [Hdom_m_mo Hin_m_mo].
  set (extra := resA_restrict n
    (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT))).
  assert (Hcompat : worldA_compat mo extra).
  {
    apply disj_dom_worldA_compat.
    subst extra. simpl.
    apply set_eq. intros x. split.
    - intros Hin.
      apply elem_of_intersection in Hin as [Hxmo Hxextra].
      apply elem_of_intersection in Hxextra as [_ Hxdiff].
      apply elem_of_difference in Hxdiff as [_ Hxnotm].
      exfalso. apply Hxnotm. rewrite Hdom_m_mo. exact Hxmo.
    - intros Hin. apply elem_of_empty in Hin. contradiction.
  }
  exists (resA_product mo extra Hcompat). split.
  - subst extra. apply resA_product_complement_lift_subset.
    + exact Hle.
    + split; assumption.
  - apply resA_le_product_l.
Qed.

Lemma resA_subset_lift_under_projection_on
    (m n mu : WfWorldAT) (X : gset K) :
  resA_restrict m X = resA_restrict n X →
  resA_subset mu m →
  ∃ nu : WfWorldAT,
    resA_subset nu n ∧ resA_restrict mu X ⊑ nu.
Proof.
  intros Hproj Hsub.
  assert (HsubX : resA_subset (resA_restrict mu X) (resA_restrict n X)).
  {
    rewrite <- Hproj.
    apply resA_subset_restrict_mono. exact Hsub.
  }
  eapply resA_subset_lift_under.
  - apply resA_restrict_le.
  - exact HsubX.
Qed.

Lemma resA_subset_lift_over_projection_on
    (m n mo : WfWorldAT) (X : gset K) :
  resA_restrict m X = resA_restrict n X →
  resA_subset m mo →
  ∃ no : WfWorldAT,
    resA_subset n no ∧ resA_restrict mo X ⊑ no.
Proof.
  intros Hproj Hsub.
  assert (HsubX : resA_subset (resA_restrict n X) (resA_restrict mo X)).
  {
    rewrite <- Hproj.
    apply resA_subset_restrict_mono. exact Hsub.
  }
  eapply resA_subset_lift_over.
  - apply resA_restrict_le.
  - exact HsubX.
Qed.

Lemma resA_product_restrict_wand_le
    (n m : WfWorldAT) (S X Y : gset K)
    (Hc_small : worldA_compat (resA_restrict n X) m)
    (Hc : worldA_compat n (resA_restrict m S)) :
  Y ⊆ S →
  Y ⊆ worldA_dom (m : WorldAT) →
  resA_restrict (resA_product (resA_restrict n X) m Hc_small) Y ⊑
  resA_product n (resA_restrict m S) Hc.
Proof.
  intros HYS HYm.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [τn [τm [Hτn [Hτm [Hcompat ->]]]]].
      simpl in Hτn. destruct Hτn as [σn [Hσn HnX]]. subst τn.
      assert (Htarget_compat :
          @storeA_compat V K _ _ σn (@storeA_restrict V K _ _ τm S)).
      {
        apply (Hc σn (@storeA_restrict V K _ _ τm S)).
        - exact Hσn.
        - simpl. exists τm. split; [exact Hτm | reflexivity].
      }
      exists (@union (gmap K V) _ (σn : gmap K V)
        (@storeA_restrict V K _ _ τm S : gmap K V)).
      split.
      * simpl. exists σn, (@storeA_restrict V K _ _ τm S).
        repeat split; eauto.
      * replace (((worldA_dom (n : WorldAT) ∩ X) ∪ worldA_dom (m : WorldAT)) ∩ Y)
          with Y by set_solver.
        transitivity (@storeA_restrict V K _ _
          (@union (gmap K V) _ (@storeA_restrict V K _ _ σn X : gmap K V)
            (τm : gmap K V)) Y).
        -- assert (HYτm : Y ⊆ dom (τm : gmap K V)).
           { pose proof (wfworldA_store_dom m τm Hτm) as Hdomτm.
             change (dom (τm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomτm.
             rewrite Hdomτm. exact HYm. }
           exact (@storeA_restrict_wand_product V K _ _ σn τm S X Y
             Hcompat Htarget_compat HYS HYτm).
        -- exact Hrestrict.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [τn [τm [Hτn [Hτm [Hcompat ->]]]]].
      simpl in Hτm. destruct Hτm as [σm [Hσm HmS]]. subst τm.
      set (σnX := @storeA_restrict V K _ _ τn X).
      exists (@union (gmap K V) _ (σnX : gmap K V) (σm : gmap K V)).
      split.
      * exists σnX, σm. repeat split.
        -- subst σnX. simpl. exists τn. split; [exact Hτn | reflexivity].
        -- exact Hσm.
        -- subst σnX. apply (Hc_small (@storeA_restrict V K _ _ τn X) σm).
           ++ simpl. exists τn. split; [exact Hτn | reflexivity].
           ++ exact Hσm.
      * subst σnX.
        replace (((worldA_dom (n : WorldAT) ∩ X) ∪ worldA_dom (m : WorldAT)) ∩ Y)
          with Y in Hrestrict by set_solver.
        rewrite <- Hrestrict.
        symmetry.
        assert (Hsmall_compat :
            @storeA_compat V K _ _ (@storeA_restrict V K _ _ τn X) σm).
        {
          apply (Hc_small (@storeA_restrict V K _ _ τn X) σm).
          - simpl. exists τn. split; [exact Hτn | reflexivity].
          - exact Hσm.
        }
        assert (HYσm : Y ⊆ dom (σm : gmap K V)).
        {
          pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
          change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
          rewrite Hdomσm. exact HYm.
        }
        exact (@storeA_restrict_wand_product V K _ _ τn σm S X Y
          Hsmall_compat Hcompat HYS HYσm).
Qed.

Lemma resA_product_restrict_same_le
    (m m1 m2 : WfWorldAT) (X : gset K)
    (Hc : worldA_compat m1 m2) :
  resA_product m1 m2 Hc ⊑ m →
  ∃ HcX : worldA_compat (resA_restrict m1 X) (resA_restrict m2 X),
    resA_product (resA_restrict m1 X) (resA_restrict m2 X) HcX
      ⊑ resA_restrict m X.
Proof.
  intros Hle.
  assert (Hc_left : worldA_compat (resA_restrict m1 X) m2).
  {
    eapply worldA_compat_le_l.
    - apply resA_restrict_le.
    - exact Hc.
  }
  assert (HcX : worldA_compat (resA_restrict m1 X) (resA_restrict m2 X)).
  {
    eapply worldA_compat_le_r.
    - apply resA_restrict_le.
    - exact Hc_left.
  }
  exists HcX.
  eapply resA_le_restrict.
  - etrans; [| exact Hle].
    eapply resA_product_le_mono; apply resA_restrict_le.
  - simpl. set_solver.
Qed.

End ResourceAlgebraA.
