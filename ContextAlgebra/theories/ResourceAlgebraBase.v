From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Algebraic operations on abstract resources *)

Section ResourceAlgebraA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition worldA_compat (m1 m2 : WorldAT) : Prop :=
  ∀ σ1 σ2, m1 σ1 → m2 σ2 → @storeA_compat V K _ _ σ1 σ2.

Lemma disj_dom_worldA_compat (w1 w2 : WfWorldAT) :
  worldA_dom (w1 : WorldAT) ∩ worldA_dom (w2 : WorldAT) = ∅ →
  worldA_compat w1 w2.
Proof.
  intros Hdisj σ1 σ2 Hσ1 Hσ2.
  apply storeA_disj_dom_compat.
  pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdom1.
  pose proof (wfworldA_store_dom w2 σ2 Hσ2) as Hdom2.
  change (dom (σ1 : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdom1.
  change (dom (σ2 : gmap K V) = worldA_dom (w2 : WorldAT)) in Hdom2.
  rewrite Hdom1, Hdom2. exact Hdisj.
Qed.

Lemma worldA_compat_store_restrict_overlap
    (w1 w2 : WfWorldAT) (X : gset K) (σ1 σ2 : StoreAT) :
  X = worldA_dom (w1 : WorldAT) ∩ worldA_dom (w2 : WorldAT) →
  worldA_compat w1 w2 →
  w1 σ1 →
  w2 σ2 →
  @storeA_restrict V K _ _ σ1 X = @storeA_restrict V K _ _ σ2 X.
Proof.
  intros -> Hcompat Hσ1 Hσ2.
  pose proof (proj1 (storeA_compat_spec σ1 σ2)
    (Hcompat σ1 σ2 Hσ1 Hσ2)) as Hrestrict.
  pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdom1.
  pose proof (wfworldA_store_dom w2 σ2 Hσ2) as Hdom2.
  change (dom (σ1 : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdom1.
  change (dom (σ2 : gmap K V) = worldA_dom (w2 : WorldAT)) in Hdom2.
  rewrite Hdom1, Hdom2 in Hrestrict. exact Hrestrict.
Qed.

Definition rawA_unit : WorldAT := {|
  worldA_dom    := ∅;
  worldA_stores := λ σ, σ = ∅;
|}.

Definition rawA_product (m1 m2 : WorldAT) : WorldAT := {|
  worldA_dom    := worldA_dom m1 ∪ worldA_dom m2;
  worldA_stores := λ σ, ∃ σ1 σ2 : StoreAT,
    m1 σ1 ∧ m2 σ2 ∧ @storeA_compat V K _ _ σ1 σ2 ∧
    σ = @union (gmap K V) _ σ1 σ2;
|}.

Definition rawA_sum (m1 m2 : WorldAT) : WorldAT := {|
  worldA_dom    := worldA_dom m1;
  worldA_stores := λ σ, m1 σ ∨ m2 σ;
|}.

Definition rawA_sum_defined (m1 m2 : WorldAT) : Prop :=
  worldA_dom m1 = worldA_dom m2.

Definition rawA_bind (m1 m2 m : WorldAT) : Prop :=
  worldA_dom m1 ## worldA_dom m2 ∧ m = rawA_product m1 m2.

Definition rawA_le (m1 m2 : WorldAT) : Prop :=
  m1 = rawA_restrict m2 (worldA_dom m1).

Definition resA_unit : WfWorldAT.
Proof.
  refine (exist _ rawA_unit _).
  split.
  - exists (∅ : StoreAT). reflexivity.
  - intros σ ->. reflexivity.
Defined.

Definition resA_product (w1 w2 : WfWorldAT) (Hc : worldA_compat w1 w2) : WfWorldAT.
Proof.
  refine (exist _ (rawA_product w1 w2) _).
  destruct (worldA_wf w1) as [Hne1 Hdom1].
  destruct (worldA_wf w2) as [Hne2 Hdom2].
  split.
  - destruct Hne1 as [σ1 Hσ1].
    destruct Hne2 as [σ2 Hσ2].
    exists (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V)).
    exists σ1, σ2. repeat split; auto.
  - intros σ [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat Heq]]]]]. subst σ.
    change (dom (@union (gmap K V) _ (σ1 : gmap K V) (σ2 : gmap K V)) =
      worldA_dom (w1 : WorldAT) ∪ worldA_dom (w2 : WorldAT)).
    rewrite dom_union_L.
    pose proof (Hdom1 σ1 Hσ1) as Hd1.
    pose proof (Hdom2 σ2 Hσ2) as Hd2.
    change (dom (σ1 : gmap K V) = worldA_dom (w1 : WorldAT)) in Hd1.
    change (dom (σ2 : gmap K V) = worldA_dom (w2 : WorldAT)) in Hd2.
    rewrite Hd1, Hd2. reflexivity.
Defined.

Definition resA_sum (w1 w2 : WfWorldAT) (Hdef : rawA_sum_defined w1 w2) : WfWorldAT.
Proof.
  refine (exist _ (rawA_sum w1 w2) _).
  destruct (worldA_wf w1) as [Hne1 Hdom1].
  destruct (worldA_wf w2) as [Hne2 Hdom2].
  split.
  - destruct Hne1 as [σ Hσ]. exists σ. left. exact Hσ.
  - intros σ [Hσ | Hσ].
    + exact (Hdom1 σ Hσ).
    + pose proof (Hdom2 σ Hσ) as Hd2.
      change (dom (σ : gmap K V) = worldA_dom (w2 : WorldAT)) in Hd2.
      unfold rawA_sum_defined in Hdef.
      change (worldA_dom (w1 : WorldAT) = worldA_dom (w2 : WorldAT)) in Hdef.
      change (dom (σ : gmap K V) = worldA_dom (w1 : WorldAT)).
      rewrite Hdef. exact Hd2.
Defined.

Definition resA_bind (w1 w2 w : WfWorldAT) : Prop :=
  rawA_bind w1 w2 w.

Definition resA_subset (w1 w2 : WfWorldAT) : Prop :=
  worldA_dom (w1 : WorldAT) = worldA_dom (w2 : WorldAT) ∧
  ∀ σ, (w1 : WorldAT) σ → (w2 : WorldAT) σ.

Definition resA_le (w1 w2 : WfWorldAT) : Prop :=
  rawA_le w1 w2.

#[global] Instance wf_worldA_sqsubseteq : SqSubsetEq WfWorldAT :=
  resA_le.

Lemma rawA_le_dom (m1 m2 : WorldAT) :
  rawA_le m1 m2 →
  worldA_dom m1 ⊆ worldA_dom m2.
Proof.
  unfold rawA_le. intros Heq.
  assert (Hd : worldA_dom m1 = worldA_dom m2 ∩ worldA_dom m1).
  { pattern m1 at 1. rewrite Heq. simpl. reflexivity. }
  set_solver.
Qed.

Lemma rawA_le_refl (m : WorldAT) :
  wf_worldA m →
  rawA_le m m.
Proof.
  intros [_ Hdom]. unfold rawA_le. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      pose proof (Hdom σ Hσ) as Hd. exists σ. split; [exact Hσ |].
      better_store_solver.
    + intros (σ' & Hσ' & Heq).
      pose proof (Hdom σ' Hσ') as Hd.
      assert (Hstep : @storeA_restrict V K _ _ σ' (worldA_dom m) = σ')
        by better_store_solver.
      rewrite Hstep in Heq. subst. exact Hσ'.
Qed.

Lemma rawA_le_antisym (m1 m2 : WorldAT) :
  wf_worldA m1 →
  wf_worldA m2 →
  rawA_le m1 m2 →
  rawA_le m2 m1 →
  m1 = m2.
Proof.
  intros Hwf1 Hwf2 H12 H21.
  pose proof (rawA_le_dom m1 m2 H12) as Hd12.
  pose proof (rawA_le_dom m2 m1 H21) as Hd21.
  assert (Hdeq : worldA_dom m1 = worldA_dom m2) by set_solver.
  apply worldA_ext; [exact Hdeq |].
  unfold rawA_le in H12, H21.
  intros σ. split.
  - intros Hσ1.
    rewrite H12 in Hσ1. cbn in Hσ1.
    destruct Hσ1 as [σ' [Hσ2 Hrestrict]].
    pose proof (wfA_dom _ Hwf2 σ' Hσ2) as Hd2.
    rewrite Hdeq in Hrestrict.
    rewrite storeA_restrict_idemp in Hrestrict by better_store_solver.
    subst. exact Hσ2.
  - intros Hσ2.
    rewrite H21 in Hσ2. cbn in Hσ2.
    destruct Hσ2 as [σ' [Hσ1 Hrestrict]].
    pose proof (wfA_dom _ Hwf1 σ' Hσ1) as Hd1.
    rewrite <- Hdeq in Hrestrict.
    rewrite storeA_restrict_idemp in Hrestrict by better_store_solver.
    subst. exact Hσ1.
Qed.

Lemma rawA_le_trans (m1 m2 m3 : WorldAT) :
  rawA_le m1 m2 →
  rawA_le m2 m3 →
  rawA_le m1 m3.
Proof.
  intros H12 H23.
  pose proof (rawA_le_dom m1 m2 H12) as Hd12.
  pose proof (rawA_le_dom m2 m3 H23) as Hd23.
  unfold rawA_le in *.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. split.
    + intros Hσ1.
      rewrite H12 in Hσ1. cbn in Hσ1.
      destruct Hσ1 as [σ2 [Hσ2 Hrestrict12]].
      rewrite H23 in Hσ2. cbn in Hσ2.
      destruct Hσ2 as [σ3 [Hσ3 Hrestrict23]].
      cbn. exists σ3. split; [exact Hσ3 |].
      rewrite <- Hrestrict12, <- Hrestrict23, storeA_restrict_restrict.
      f_equal. set_solver.
    + intros Hσ1.
      cbn in Hσ1.
      destruct Hσ1 as [σ3 [Hσ3 Hrestrict]].
      rewrite H12. cbn.
      exists (@storeA_restrict V K _ _ σ3 (worldA_dom m2)).
      split.
      * assert (Hm2store :
          (rawA_restrict m3 (worldA_dom m2) : WorldAT)
            (@storeA_restrict V K _ _ σ3 (worldA_dom m2))).
        { cbn. exists σ3. split; [exact Hσ3 | reflexivity]. }
        rewrite <- H23 in Hm2store. exact Hm2store.
      * rewrite storeA_restrict_restrict.
        replace (worldA_dom m2 ∩ worldA_dom m1) with (worldA_dom m1) by set_solver.
        exact Hrestrict.
Qed.

#[global] Instance wf_worldA_preorder : PreOrder (sqsubseteq (A := WfWorldAT)).
Proof.
  split.
  - intros [m Hwf]. exact (rawA_le_refl m Hwf).
  - intros [m1 Hwf1] [m2 Hwf2] [m3 Hwf3]. exact (rawA_le_trans m1 m2 m3).
Qed.

#[global] Instance wf_worldA_antisym : AntiSymm eq (sqsubseteq (A := WfWorldAT)).
Proof.
  intros [m1 H1] [m2 H2] H12 H21. simpl in *.
  assert (Heq : m1 = m2) by exact (rawA_le_antisym m1 m2 H1 H2 H12 H21).
  subst. f_equal. apply proof_irrelevance.
Qed.

Lemma resA_subset_refl (w : WfWorldAT) : resA_subset w w.
Proof. split; [reflexivity | tauto]. Qed.

Lemma resA_subset_trans (w1 w2 w3 : WfWorldAT) :
  resA_subset w1 w2 → resA_subset w2 w3 → resA_subset w1 w3.
Proof.
  intros [Hdom12 Hin12] [Hdom23 Hin23].
  split; [congruence | intros σ Hσ; exact (Hin23 σ (Hin12 σ Hσ))].
Qed.

Lemma resA_subset_antisym (w1 w2 : WfWorldAT) :
  resA_subset w1 w2 → resA_subset w2 w1 → w1 = w2.
Proof.
  intros [Hdom12 Hin12] [Hdom21 Hin21].
  destruct w1 as [m1 Hwf1], w2 as [m2 Hwf2]. simpl in *.
  assert (Heq : m1 = m2).
  { apply worldA_ext; [exact Hdom12 |].
    intros σ. split; [apply Hin12 | apply Hin21]. }
  subst. f_equal. apply proof_irrelevance.
Qed.

Lemma resA_subset_swap (x y : K) (w1 w2 : WfWorldAT) :
  resA_subset (resA_swap x y w1) (resA_swap x y w2) ↔ resA_subset w1 w2.
Proof.
  split.
  - intros [Hdom Hin]. split.
    + simpl in Hdom.
      change (set_swap x y (worldA_dom (w1 : WorldAT)) =
        set_swap x y (worldA_dom (w2 : WorldAT))) in Hdom.
      rewrite <- (set_swap_involutive x y (worldA_dom (w1 : WorldAT))).
      rewrite <- (set_swap_involutive x y (worldA_dom (w2 : WorldAT))).
      by rewrite Hdom.
    + intros σ Hσ.
      pose proof (Hin (@storeA_swap V K _ _ x y σ)) as Hin'.
      simpl in Hin'.
      assert (Hs1 : rawA_swap x y w1 (@storeA_swap V K _ _ x y σ)).
      { exists σ. split; [exact Hσ | reflexivity]. }
      destruct (Hin' Hs1) as [σ2 [Hσ2 Hswap]].
      assert (σ2 = σ).
      {
        rewrite <- (storeA_swap_involutive x y σ2).
        change (@storeA_swap V K _ _ x y σ2 =
          @storeA_swap V K _ _ x y σ) in Hswap.
        rewrite Hswap. apply storeA_swap_involutive.
      }
      subst. exact Hσ2.
  - intros [Hdom Hin]. split.
    + simpl. by rewrite Hdom.
    + intros σ Hσ.
      simpl in Hσ. destruct Hσ as [σ0 [Hσ0 Hswap]]. subst.
      exists σ0. split; [apply Hin; exact Hσ0 | reflexivity].
Qed.

Lemma resA_subset_restrict_mono (w1 w2 : WfWorldAT) (X : gset K) :
  resA_subset w1 w2 →
  resA_subset (resA_restrict w1 X) (resA_restrict w2 X).
Proof.
  intros [Hdom Hin]. split.
  - simpl. rewrite Hdom. reflexivity.
  - intros σ [σ0 [Hσ0 Hrestrict]].
    exists σ0. split; [apply Hin; exact Hσ0 | exact Hrestrict].
Qed.

Lemma resA_sum_subset_l (w1 w2 : WfWorldAT) (Hdef : rawA_sum_defined w1 w2) :
  resA_subset w1 (resA_sum w1 w2 Hdef).
Proof.
  split; [reflexivity |].
  intros σ Hσ. simpl. left. exact Hσ.
Qed.

Lemma resA_sum_subset_r (w1 w2 : WfWorldAT) (Hdef : rawA_sum_defined w1 w2) :
  resA_subset w2 (resA_sum w1 w2 Hdef).
Proof.
  split.
  - simpl. unfold rawA_sum_defined in Hdef. symmetry. exact Hdef.
  - intros σ Hσ. simpl. right. exact Hσ.
Qed.

Lemma rawA_sum_le_mono (m1 m2 m1' m2' : WorldAT) :
  rawA_sum_defined m1 m2 → rawA_sum_defined m1' m2' →
  rawA_le m1 m1' → rawA_le m2 m2' →
  rawA_le (rawA_sum m1 m2) (rawA_sum m1' m2').
Proof.
  intros Hdef Hdef' Hle1 Hle2.
  pose proof (rawA_le_dom m1 m1' Hle1) as Hdom1.
  unfold rawA_le in *.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [Hσ | Hσ].
      * rewrite Hle1 in Hσ. simpl in Hσ.
        destruct Hσ as [σ' [Hσ' Hrestrict]].
        exists σ'. split; [left; exact Hσ' | exact Hrestrict].
      * rewrite Hle2 in Hσ. simpl in Hσ.
        destruct Hσ as [σ' [Hσ' Hrestrict]].
        exists σ'. split; [right; exact Hσ' |].
        rewrite Hdef. exact Hrestrict.
    + intros [σ' [[Hσ' | Hσ'] Hrestrict]].
      * left. rewrite Hle1. simpl. exists σ'. split; [exact Hσ' | exact Hrestrict].
      * right. rewrite Hle2. simpl. exists σ'. split; [exact Hσ' |].
        rewrite <- Hdef. exact Hrestrict.
Qed.

Lemma rawA_compat_unit (m : WorldAT) : worldA_compat rawA_unit m.
Proof.
  intros σ1 σ2 Hσ1 Hσ2. simpl in Hσ1. subst.
  unfold storeA_compat, map_compat. intros z v1 v2 H1 _.
  change ((∅ : gmap K V) !! z = Some v1) in H1.
  rewrite lookup_empty in H1. discriminate.
Qed.

Lemma rawA_compat_unit_r (m : WorldAT) : worldA_compat m rawA_unit.
Proof.
  intros σ1 σ2 Hσ1 Hσ2. simpl in Hσ2. subst.
  unfold storeA_compat, map_compat. intros z v1 v2 _ H2.
  change ((∅ : gmap K V) !! z = Some v2) in H2.
  rewrite lookup_empty in H2. discriminate.
Qed.

Definition singleton_worldA (σ : StoreAT) : WorldAT := {|
  worldA_dom    := dom σ;
  worldA_stores := λ σ0, σ0 = σ;
|}.

Lemma rawA_restrict_to_singleton_if_projection_constant
    (w : WfWorldAT) (X : gset K) (σX : StoreAT) :
  (∀ σ, (w : WorldAT) σ →
    @storeA_restrict V K _ _ σ X = σX) →
  rawA_restrict w X = singleton_worldA σX.
Proof.
  intros Hconst.
  destruct (wfA_ne _ (worldA_wf w)) as [σw Hσw].
  apply worldA_ext.
  - simpl.
    pose proof (Hconst σw Hσw) as HσX.
    pose proof (f_equal (fun s : gmap K V => dom s) HσX) as HdomσX.
    change (dom (@storeA_restrict V K _ _ σw X : gmap K V) =
      dom (σX : gmap K V)) in HdomσX.
    change (worldA_dom (w : WorldAT) ∩ X = dom (σX : gmap K V)).
    rewrite <- HdomσX.
    pose proof (storeA_restrict_dom σw X) as Hdomr.
    change (dom (@storeA_restrict V K _ _ σw X : gmap K V) =
      dom (σw : gmap K V) ∩ X) in Hdomr.
    rewrite Hdomr.
    pose proof (wfworldA_store_dom w σw Hσw) as Hdomw.
    change (dom (σw : gmap K V) = worldA_dom (w : WorldAT)) in Hdomw.
    rewrite Hdomw. reflexivity.
  - intros σ. simpl. split.
    + intros [σ0 [Hσ0 Hrestrict]]. subst σ.
      apply Hconst. exact Hσ0.
    + intros ->.
      exists σw. split; [exact Hσw |].
      apply Hconst. exact Hσw.
Qed.

Lemma worldA_compat_of_common_overlap_singleton
    (w1 w2 : WfWorldAT) (X : gset K) (σX : StoreAT) :
  X = worldA_dom (w1 : WorldAT) ∩ worldA_dom (w2 : WorldAT) →
  rawA_restrict w1 X = singleton_worldA σX →
  rawA_restrict w2 X = singleton_worldA σX →
  worldA_compat w1 w2.
Proof.
  intros HX Hw1 Hw2 σ1 σ2 Hσ1 Hσ2.
  apply (proj2 (storeA_compat_spec σ1 σ2)).
  assert (H1 : @storeA_restrict V K _ _ σ1 X = σX).
  {
    assert (Hraw : rawA_restrict w1 X (@storeA_restrict V K _ _ σ1 X)).
    { exists σ1. split; [exact Hσ1 | reflexivity]. }
    rewrite Hw1 in Hraw. simpl in Hraw. exact Hraw.
  }
  assert (H2 : @storeA_restrict V K _ _ σ2 X = σX).
  {
    assert (Hraw : rawA_restrict w2 X (@storeA_restrict V K _ _ σ2 X)).
    { exists σ2. split; [exact Hσ2 | reflexivity]. }
    rewrite Hw2 in Hraw. simpl in Hraw. exact Hraw.
  }
  replace (dom (σ1 : gmap K V) ∩ dom (σ2 : gmap K V)) with X.
  - rewrite H1, H2. reflexivity.
  - rewrite HX.
    pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdom1.
    pose proof (wfworldA_store_dom w2 σ2 Hσ2) as Hdom2.
    change (dom (σ1 : gmap K V) = worldA_dom (w1 : WorldAT)) in Hdom1.
    change (dom (σ2 : gmap K V) = worldA_dom (w2 : WorldAT)) in Hdom2.
    rewrite Hdom1, Hdom2. reflexivity.
Qed.

Lemma wf_singleton_worldA (σ : StoreAT) : wf_worldA (singleton_worldA σ).
Proof.
  constructor.
  - exists σ. reflexivity.
  - intros σ0 ->. reflexivity.
Qed.

Lemma resA_swap_singleton_world (x y : K) (σ : StoreAT) :
  (resA_swap x y (exist _ (singleton_worldA σ) (wf_singleton_worldA σ)) : WorldAT) =
  singleton_worldA (@storeA_swap V K _ _ x y σ).
Proof.
  apply worldA_ext.
  - simpl. symmetry. apply storeA_swap_dom.
  - intros τ. simpl. split.
    + intros [σ0 [-> Hswap]]. symmetry. exact Hswap.
    + intros ->. exists σ. split; reflexivity.
Qed.

Lemma resA_swap_singleton_wfworld (x y : K) (σ : StoreAT) :
  resA_swap x y (exist _ (singleton_worldA σ) (wf_singleton_worldA σ)) =
  exist _ (singleton_worldA (@storeA_swap V K _ _ x y σ))
    (wf_singleton_worldA (@storeA_swap V K _ _ x y σ)).
Proof.
  apply wfworldA_ext. apply resA_swap_singleton_world.
Qed.

Lemma resA_restrict_fiber_from_projection_dom_singleton
    (w wfib : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_fiber_from_projection w X σ wfib →
  (resA_restrict wfib (dom σ) : WorldAT) = singleton_worldA σ.
Proof.
  intros [Hproj Heq].
  simpl in Hproj.
  destruct Hproj as [σw [Hσw Hrestr]].
  pose proof (wfworldA_store_dom w σw Hσw) as Hdomσw.
  change (dom (σw : gmap K V) = worldA_dom (w : WorldAT)) in Hdomσw.
  assert (Hdomσ : dom (σ : gmap K V) = worldA_dom (w : WorldAT) ∩ X).
  {
    pose proof (f_equal (fun s : gmap K V => dom s) Hrestr) as Hdomrestr.
    change (dom (@storeA_restrict V K _ _ σw X : gmap K V) =
      dom (σ : gmap K V)) in Hdomrestr.
    pose proof (storeA_restrict_dom σw X) as Hdomr.
    change (dom (@storeA_restrict V K _ _ σw X : gmap K V) =
      dom (σw : gmap K V) ∩ X) in Hdomr.
    rewrite <- Hdomrestr, Hdomr. set_solver.
  }
  apply worldA_ext.
  - simpl. rewrite Heq. simpl.
    change (worldA_dom (w : WorldAT) ∩ dom (σ : gmap K V) =
      dom (σ : gmap K V)).
    rewrite Hdomσ. set_solver.
  - intros τ. simpl. rewrite Heq. simpl. split.
    + intros [τ0 [[Hτ0 Hτ0σ] Hτ]].
      rewrite Hτ0σ in Hτ. subst τ. reflexivity.
    + intros ->.
      exists σw. split.
      * split; [exact Hσw |].
        transitivity (@storeA_restrict V K _ _
          (@storeA_restrict V K _ _ σw X) (dom σ)).
        -- rewrite storeA_restrict_restrict.
           replace (X ∩ dom (σ : gmap K V)) with (dom (σ : gmap K V))
             by (rewrite Hdomσ; set_solver).
           reflexivity.
        -- rewrite Hrestr. apply storeA_restrict_idemp; better_store_solver.
      * transitivity (@storeA_restrict V K _ _
          (@storeA_restrict V K _ _ σw X) (dom σ)).
        -- rewrite storeA_restrict_restrict.
           replace (X ∩ dom (σ : gmap K V)) with (dom (σ : gmap K V))
             by (rewrite Hdomσ; set_solver).
           reflexivity.
        -- rewrite Hrestr. apply storeA_restrict_idemp; better_store_solver.
Qed.

Lemma resA_restrict_fiber_from_projection_eq_singleton
    (w wfib : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_fiber_from_projection w X σ wfib →
  dom σ = X →
  (resA_restrict wfib X : WorldAT) = singleton_worldA σ.
Proof.
  intros Hfiber Hdomσ.
  rewrite <- Hdomσ.
  apply resA_restrict_fiber_from_projection_dom_singleton with (w := w) (X := X).
  exact Hfiber.
Qed.

Lemma rawA_restrict_fiber_from_projection_eq_singleton
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (resA_restrict w X : WorldAT) σ →
  dom σ = X →
  rawA_restrict (rawA_fiber w σ) X = singleton_worldA σ.
Proof.
  intros Hproj Hdomσ.
  simpl in Hproj.
  destruct Hproj as [σw [Hσw Hrestr]].
  apply worldA_ext.
  - simpl.
    pose proof (wfworldA_store_dom w σw Hσw) as Hdomw.
    change (dom (σw : gmap K V) = worldA_dom (w : WorldAT)) in Hdomw.
    rewrite <- Hdomw.
    rewrite <- Hrestr, storeA_restrict_dom. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hτ0σ] Hτ]].
      rewrite Hdomσ in Hτ0σ.
      congruence.
    + intros ->.
      exists σw. split.
      * split; [exact Hσw |].
        rewrite Hdomσ. exact Hrestr.
      * exact Hrestr.
Qed.

Definition rawA_slice_restrict (n : WfWorldAT) (X : gset K) (p : WfWorldAT) : WorldAT := {|
  worldA_dom := worldA_dom (n : WorldAT);
  worldA_stores := fun σ =>
    (n : WorldAT) σ ∧ (p : WorldAT) (@storeA_restrict V K _ _ σ X);
|}.

Lemma rawA_slice_restrict_wf (n : WfWorldAT) (X : gset K) (p : WfWorldAT) :
  resA_subset p (resA_restrict n X) →
  wf_worldA (rawA_slice_restrict n X p).
Proof.
  intros [_ Hin]. constructor.
  - destruct (wfA_ne _ (worldA_wf p)) as [σp Hσp].
    pose proof (Hin σp Hσp) as Hproj.
    simpl in Hproj.
    destruct Hproj as [σn [Hσn Hrestrict]].
    exists σn. split; [exact Hσn |].
    rewrite Hrestrict. exact Hσp.
  - intros σ [Hσn _]. simpl.
    exact (wfworldA_store_dom n σ Hσn).
Qed.

Definition resA_slice_restrict
    (n : WfWorldAT) (X : gset K) (p : WfWorldAT)
    (Hsub : resA_subset p (resA_restrict n X)) : WfWorldAT :=
  exist _ (rawA_slice_restrict n X p)
    (rawA_slice_restrict_wf n X p Hsub).

Lemma resA_slice_restrict_subset
    (n : WfWorldAT) (X : gset K) (p : WfWorldAT) Hsub :
  resA_subset (resA_slice_restrict n X p Hsub) n.
Proof.
  split; [reflexivity |].
  intros σ Hσ. exact (proj1 Hσ).
Qed.

Lemma resA_slice_restrict_restrict
    (n : WfWorldAT) (X : gset K) (p : WfWorldAT) Hsub :
  resA_restrict (resA_slice_restrict n X p Hsub) X = p.
Proof.
  destruct Hsub as [Hdom Hin].
  apply wfworldA_ext. apply worldA_ext.
  - simpl in Hdom |- *. set_solver.
  - intros σ. simpl. split.
    + intros [σn [[Hσn Hp] Hrestrict]].
      rewrite <- Hrestrict. exact Hp.
    + intros Hp.
      pose proof (Hin σ Hp) as Hproj.
      simpl in Hproj.
      destruct Hproj as [σn [Hσn Hrestrict]].
      exists σn. split; [split; [exact Hσn | rewrite Hrestrict; exact Hp] |].
      exact Hrestrict.
Qed.

End ResourceAlgebraA.
