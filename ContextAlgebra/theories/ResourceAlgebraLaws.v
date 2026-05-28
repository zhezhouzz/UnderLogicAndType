From ContextBase Require Import Prelude LogicVarInterface.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebraCore.

(** * Algebraic laws for abstract resources *)

Section ResourceAlgebraA.

Context {K : Type} `{Countable K} `{!SwapKey K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Lemma resA_product_comm (w1 w2 : WfWorldAT) (Hc : worldA_compat w1 w2)
    (Hc' : worldA_compat w2 w1) :
  ∀ σ, resA_product w1 w2 Hc σ ↔ resA_product w2 w1 Hc' σ.
Proof.
  intros σ. simpl. split.
  - intros [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
    exists σ2, σ1. repeat split; eauto.
    apply storeA_union_comm. exact Hcompat.
  - intros [σ2 [σ1 [Hσ2 [Hσ1 [Hcompat ->]]]]].
    exists σ1, σ2. repeat split; eauto.
    symmetry. apply storeA_union_comm. apply storeA_compat_sym. exact Hcompat.
Qed.

Lemma resA_product_unit_r_any (w : WfWorldAT) (Hc : worldA_compat w resA_unit) :
  ∀ σ, resA_product w resA_unit Hc σ ↔ (w : WorldAT) σ.
Proof.
  intros σ. simpl. split.
  - intros (σ1 & σ2 & Hσ1 & Hσ2 & _ & ->).
    subst σ2.
    replace (@union (gmap K V) _ (σ1 : gmap K V) (∅ : gmap K V)) with σ1.
    + exact Hσ1.
    + symmetry. apply (map_eq (M:=gmap K)). intros i.
      apply (lookup_union_l (M:=gmap K) (A:=V)).
      apply (lookup_empty (M:=gmap K) (A:=V)).
  - intros Hσ.
    exists σ, ∅. repeat split; eauto.
    + exact (Hc σ ∅ Hσ eq_refl).
    + symmetry. apply (map_eq (M:=gmap K)). intros i.
      apply (lookup_union_l (M:=gmap K) (A:=V)).
      apply (lookup_empty (M:=gmap K) (A:=V)).
Qed.

Lemma resA_product_unit_r (w : WfWorldAT) :
  ∀ σ, resA_product w resA_unit (rawA_compat_unit_r w) σ ↔ (w : WorldAT) σ.
Proof. apply resA_product_unit_r_any. Qed.

Lemma resA_product_unit_r_eq (w : WfWorldAT) :
  resA_product w resA_unit (rawA_compat_unit_r w) = w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - apply resA_product_unit_r.
Qed.

Lemma resA_product_unit_r_eq_any (w : WfWorldAT) (Hc : worldA_compat w resA_unit) :
  resA_product w resA_unit Hc = w.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - apply resA_product_unit_r_any.
Qed.

Lemma resA_sum_comm (w1 w2 : WfWorldAT) (Hdef : rawA_sum_defined w1 w2)
    (Hdef' : rawA_sum_defined w2 w1) :
  ∀ σ, resA_sum w1 w2 Hdef σ ↔ resA_sum w2 w1 Hdef' σ.
Proof. intros σ. unfold resA_sum. simpl. tauto. Qed.

Lemma resA_product_comm_eq (w1 w2 : WfWorldAT) (Hc : worldA_compat w1 w2) :
  ∃ Hc' : worldA_compat w2 w1,
    resA_product w1 w2 Hc = resA_product w2 w1 Hc'.
Proof.
  exists (fun σ1 σ2 Hσ1 Hσ2 => storeA_compat_sym _ _ (Hc σ2 σ1 Hσ2 Hσ1)).
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - apply resA_product_comm.
Qed.

Lemma resA_sum_comm_eq (w1 w2 : WfWorldAT) (Hdef : rawA_sum_defined w1 w2) :
  ∃ Hdef' : rawA_sum_defined w2 w1,
    resA_sum w1 w2 Hdef = resA_sum w2 w1 Hdef'.
Proof.
  exists (eq_sym Hdef).
  apply wfworldA_ext. apply worldA_ext.
  - simpl. exact Hdef.
  - apply resA_sum_comm.
Qed.

Lemma resA_product_assoc_eq (w1 w2 w3 : WfWorldAT)
    (H12 : worldA_compat w1 w2)
    (H123 : worldA_compat (resA_product w1 w2 H12) w3) :
  ∃ (H23 : worldA_compat w2 w3)
    (H1_23 : worldA_compat w1 (resA_product w2 w3 H23)),
    resA_product (resA_product w1 w2 H12) w3 H123 =
    resA_product w1 (resA_product w2 w3 H23) H1_23.
Proof.
  assert (H23 : worldA_compat w2 w3).
  { intros σ2 σ3 Hσ2 Hσ3.
    destruct (wfA_ne _ (worldA_wf w1)) as [σ1 Hσ1].
    pose proof (H12 σ1 σ2 Hσ1 Hσ2) as Hc12.
    assert (Hprod : resA_product w1 w2 H12
      (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V))).
    { simpl. exists σ1, σ2. repeat split; eauto. }
    eapply storeA_compat_union_inv_r; [exact Hc12 |].
    exact (H123 (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V))
      σ3 Hprod Hσ3). }
  assert (H1_23 : worldA_compat w1 (resA_product w2 w3 H23)).
  { intros σ1 σ23 Hσ1 Hσ23.
    simpl in Hσ23.
    destruct Hσ23 as [σ2 [σ3 [Hσ2 [Hσ3 [Hc23 ->]]]]].
    apply storeA_compat_union_intro_r.
    - exact (H12 σ1 σ2 Hσ1 Hσ2).
    - assert (Hprod : resA_product w1 w2 H12
        (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V))).
      { simpl. exists σ1, σ2. repeat split; eauto. }
      eapply storeA_compat_union_inv_l.
      exact (H123 (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V))
        σ3 Hprod Hσ3). }
  exists H23, H1_23.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros (σ12 & σ3 & Hσ12 & Hσ3 & Hc123 & ->).
      simpl in Hσ12.
      destruct Hσ12 as [σ1 [σ2 [Hσ1 [Hσ2 [Hc12 ->]]]]].
      exists σ1, (@union (gmap K V) _ (σ2 : gmap K V) (σ3 : gmap K V)).
      split; [exact Hσ1 |].
      split.
      * exists σ2, σ3. repeat split; eauto.
      * split.
        -- assert (Hprod23 : resA_product w2 w3 H23
             (@union (gmap K V) _ (σ2 : gmap K V) (σ3 : gmap K V))).
           { simpl. exists σ2, σ3. repeat split; eauto. }
           exact (H1_23 σ1
             (@union (gmap K V) _ (σ2 : gmap K V) (σ3 : gmap K V))
             Hσ1 Hprod23).
        -- exact (eq_sym (assoc_L (∪) (σ1 : gmap K V) σ2 σ3)).
    + intros (σ1 & σ23 & Hσ1 & Hσ23 & Hc1_23 & ->).
      simpl in Hσ23.
      destruct Hσ23 as [σ2 [σ3 [Hσ2 [Hσ3 [Hc23 ->]]]]].
      exists (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V)), σ3.
      split.
      * simpl. exists σ1, σ2. repeat split; eauto.
      * split; [exact Hσ3 |].
        split.
        -- assert (Hprod12 : resA_product w1 w2 H12
             (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V))).
           { simpl. exists σ1, σ2. repeat split; eauto. }
           exact (H123
             (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V))
             σ3 Hprod12 Hσ3).
        -- exact (assoc_L (∪) (σ1 : gmap K V) σ2 σ3).
Qed.

Lemma resA_sum_assoc_eq (w1 w2 w3 : WfWorldAT)
    (H12 : rawA_sum_defined w1 w2)
    (H123 : rawA_sum_defined (resA_sum w1 w2 H12) w3) :
  ∃ (H23 : rawA_sum_defined w2 w3)
    (H1_23 : rawA_sum_defined w1 (resA_sum w2 w3 H23)),
    resA_sum (resA_sum w1 w2 H12) w3 H123 =
    resA_sum w1 (resA_sum w2 w3 H23) H1_23.
Proof.
  assert (H23 : rawA_sum_defined w2 w3).
  { unfold rawA_sum_defined in *. simpl in H123. congruence. }
  assert (H1_23 : rawA_sum_defined w1 (resA_sum w2 w3 H23)).
  { unfold rawA_sum_defined in *. simpl. exact H12. }
  exists H23, H1_23.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. reflexivity.
  - intros σ. simpl. tauto.
Qed.

Lemma worldA_compat_spec (w1 w2 : WfWorldAT) :
  let X := worldA_dom (w1 : WorldAT) ∩ worldA_dom (w2 : WorldAT) in
  worldA_compat w1 w2 ↔
    exists σ,
      rawA_restrict w1 X = singleton_worldA σ ∧
      rawA_restrict w2 X = singleton_worldA σ.
Proof.
  set (X := worldA_dom (w1 : WorldAT) ∩ worldA_dom (w2 : WorldAT)).
  split.
  - intros Hcompat.
    destruct (wfA_ne _ (worldA_wf w1)) as [σ1 Hσ1].
    destruct (wfA_ne _ (worldA_wf w2)) as [σ2 Hσ2].
    exists (@storeA_restrict V K _ _ σ1 X). split.
    + apply rawA_restrict_to_singleton_if_projection_constant.
      intros σ Hσ.
      pose proof (worldA_compat_store_restrict_overlap
        w1 w2 X σ σ2 eq_refl Hcompat Hσ Hσ2) as Hσ_2.
      pose proof (worldA_compat_store_restrict_overlap
        w1 w2 X σ1 σ2 eq_refl Hcompat Hσ1 Hσ2) as Hσ12.
      etrans; [exact Hσ_2 | symmetry; exact Hσ12].
    + apply rawA_restrict_to_singleton_if_projection_constant.
      intros σ Hσ.
      pose proof (worldA_compat_store_restrict_overlap
        w1 w2 X σ1 σ eq_refl Hcompat Hσ1 Hσ) as Hσ1_.
      symmetry. exact Hσ1_.
  - intros [σ [Hw1 Hw2]].
    eapply worldA_compat_of_common_overlap_singleton.
    + exact eq_refl.
    + exact Hw1.
    + exact Hw2.
Qed.

End ResourceAlgebraA.
