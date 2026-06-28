From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Algebraic operations on abstract resources *)

(** ** Abstract context algebra *)

Class ContextAlgebra (M : Type) := {
  ca_one  : M;
  ca_times_def : M → M → Prop;
  ca_plus_def  : M → M → Prop;
  ca_times : ∀ m1 m2, ca_times_def m1 m2 → M;
  ca_plus  : ∀ m1 m2, ca_plus_def m1 m2 → M;
  ca_le    : M → M → Prop;

  ca_times_unit_def : ∀ m, ca_times_def m ca_one;
  ca_times_unit : ∀ m, ca_times m ca_one (ca_times_unit_def m) = m;

  ca_times_comm : ∀ m1 m2 (H12 : ca_times_def m1 m2),
    ∃ H21 : ca_times_def m2 m1,
      ca_times m1 m2 H12 = ca_times m2 m1 H21;

  ca_plus_comm  : ∀ m1 m2 (H12 : ca_plus_def m1 m2),
    ∃ H21 : ca_plus_def m2 m1,
      ca_plus m1 m2 H12 = ca_plus m2 m1 H21;

  ca_times_assoc : ∀ m1 m2 m3
    (H12 : ca_times_def m1 m2)
    (H123 : ca_times_def (ca_times m1 m2 H12) m3),
    ∃ (H23 : ca_times_def m2 m3)
      (H1_23 : ca_times_def m1 (ca_times m2 m3 H23)),
      ca_times (ca_times m1 m2 H12) m3 H123 =
      ca_times m1 (ca_times m2 m3 H23) H1_23;

  ca_plus_assoc  : ∀ m1 m2 m3
    (H12 : ca_plus_def m1 m2)
    (H123 : ca_plus_def (ca_plus m1 m2 H12) m3),
    ∃ (H23 : ca_plus_def m2 m3)
      (H1_23 : ca_plus_def m1 (ca_plus m2 m3 H23)),
      ca_plus (ca_plus m1 m2 H12) m3 H123 =
      ca_plus m1 (ca_plus m2 m3 H23) H1_23;

  ca_le_refl : ∀ m, ca_le m m;

  ca_times_le_mono : ∀ m1 m2 m1' m2'
    (H12 : ca_times_def m1 m2) (H12' : ca_times_def m1' m2'),
    ca_le m1 m1' → ca_le m2 m2' →
    ca_le (ca_times m1 m2 H12) (ca_times m1' m2' H12');

  ca_plus_le_mono  : ∀ m1 m2 m1' m2'
    (H12 : ca_plus_def m1 m2) (H12' : ca_plus_def m1' m2'),
    ca_le m1 m1' → ca_le m2 m2' →
    ca_le (ca_plus m1 m2 H12) (ca_plus m1' m2' H12');
}.

Section ContextAlgebraLemmas.
Context `{ContextAlgebra M}.
End ContextAlgebraLemmas.

Section ResourceAlgebraA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition worldA_compat (m1 m2 : WorldAT) : Prop :=
  ∀ σ1 σ2, m1 σ1 → m2 σ2 → storeA_compat σ1 σ2.

Lemma disj_dom_worldA_compat (w1 w2 : WfWorldAT) :
  worldA_dom (w1 : WorldAT) ∩ worldA_dom (w2 : WorldAT) = ∅ →
  worldA_compat w1 w2.
Proof.
  intros Hdisj σ1 σ2 Hσ1 Hσ2.
  apply storeA_disj_dom_compat.
  pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdom1.
  pose proof (wfworldA_store_dom w2 σ2 Hσ2) as Hdom2.
  rewrite Hdom1, Hdom2. exact Hdisj.
Qed.

Definition rawA_unit : WorldAT := {|
  worldA_dom    := ∅;
  worldA_stores := λ σ, σ = ∅;
|}.

Definition rawA_product (m1 m2 : WorldAT) : WorldAT := {|
  worldA_dom    := worldA_dom m1 ∪ worldA_dom m2;
  worldA_stores := λ σ, ∃ σ1 σ2 : StoreAT,
    m1 σ1 ∧ m2 σ2 ∧ storeA_compat σ1 σ2 ∧
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
    rewrite dom_union_L.
    pose proof (Hdom1 σ1 Hσ1) as Hd1.
    pose proof (Hdom2 σ2 Hσ2) as Hd2.
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
      assert (Hstep : storeA_restrict σ' (worldA_dom m) = σ')
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
      exists (storeA_restrict σ3 (worldA_dom m2)).
      split.
      * assert (Hm2store :
          (rawA_restrict m3 (worldA_dom m2) : WorldAT)
            (storeA_restrict σ3 (worldA_dom m2))).
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

Lemma resA_subset_restrict_mono (w1 w2 : WfWorldAT) (X : gset K) :
  resA_subset w1 w2 →
  resA_subset (resA_restrict w1 X) (resA_restrict w2 X).
Proof.
  intros [Hdom Hin]. split.
  - simpl. rewrite Hdom. reflexivity.
  - intros σ [σ0 [Hσ0 Hrestrict]].
    exists σ0. split; [apply Hin; exact Hσ0 | exact Hrestrict].
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

Lemma rawA_compat_unit_r (m : WorldAT) : worldA_compat m rawA_unit.
Proof.
  intros σ1 σ2 Hσ1 Hσ2. simpl in Hσ2. subst.
  unfold storeA_compat, map_compat. intros z v1 v2 _ H2.
  better_map_solver.
Qed.

Definition singleton_worldA (σ : StoreAT) : WorldAT := {|
  worldA_dom    := dom σ;
  worldA_stores := λ σ0, σ0 = σ;
|}.

Lemma wf_singleton_worldA (σ : StoreAT) : wf_worldA (singleton_worldA σ).
Proof.
  constructor.
  - exists σ. reflexivity.
  - intros σ0 ->. reflexivity.
Qed.

Definition rawA_slice_restrict (n : WfWorldAT) (X : gset K) (p : WfWorldAT) : WorldAT := {|
  worldA_dom := worldA_dom (n : WorldAT);
  worldA_stores := fun σ =>
    (n : WorldAT) σ ∧ (p : WorldAT) (storeA_restrict σ X);
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

(** * Order and fiber transport lemmas for abstract resource algebra *)

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
  assert (Hrσm : (resA_restrict m S : WorldAT) (storeA_restrict σm S)).
  { simpl. exists σm. split; [exact Hσm | reflexivity]. }
  pose proof (Hcompat τn (storeA_restrict σm S) Hτn Hrσm) as Hstore.
  apply storeA_compat_restrict_l_full_r with (X := S).
  - pose proof (storeA_restrict_dom τn X) as Hdomr.
    change (dom (storeA_restrict τn X : gmap K V) =
      dom (τn : gmap K V) ∩ X) in Hdomr.
    rewrite Hdomr. set_solver.
  - apply storeA_compat_sym.
	    apply storeA_compat_restrict_r.
	    apply storeA_compat_sym. exact Hstore.
Qed.

Lemma worldA_compat_restrict_overlap
    (n m : WfWorldAT) (X Y S : gset K) :
  X ∩ Y ⊆ S ->
  worldA_compat n (resA_restrict m S) ->
  worldA_compat (resA_restrict n X) (resA_restrict m Y).
Proof.
  intros Hoverlap Hcompat σn σm Hσn Hσm.
  simpl in Hσn, Hσm.
  destruct Hσn as [τn [Hτn Hrestrict_n]].
  destruct Hσm as [τm [Hτm Hrestrict_m]].
  subst σn σm.
  assert (Hrτm : (resA_restrict m S : WorldAT) (storeA_restrict τm S)).
  { simpl. exists τm. split; [exact Hτm | reflexivity]. }
  pose proof (Hcompat τn (storeA_restrict τm S) Hτn Hrτm) as Hstore.
  eapply storeA_compat_restrict_overlap; eauto.
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
      rewrite <- (storeA_restrict_idemp σ' (worldA_dom (w : WorldAT))) at 2
        by set_solver.
      rewrite storeA_restrict_restrict. reflexivity.
    + intros [σ' [Hσ' Hrestrict]].
      exists σ'. split; [exact Hσ' |].
      pose proof (wfworldA_store_dom w σ' Hσ') as Hdomσ'.
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

Lemma resA_restrict_swap (x y : K) (w : WfWorldAT) (X : gset K) :
  resA_restrict (resA_swap x y w) (set_swap x y X) =
  resA_swap x y (resA_restrict w X).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. apply set_eq. intros z.
    change (z ∈ set_swap x y (worldA_dom (w : WorldAT)) ∩
              set_swap x y X <->
            z ∈ set_swap x y (worldA_dom (w : WorldAT) ∩ X)).
    rewrite elem_of_intersection.
    rewrite (set_swap_elem x y z (worldA_dom (w : WorldAT))).
    rewrite (set_swap_elem x y z X).
    rewrite (set_swap_elem x y z (worldA_dom (w : WorldAT) ∩ X)).
    rewrite elem_of_intersection. tauto.
  - intros σ. simpl. split.
    + intros [σsw [[σ0 [Hσ0 Hswap]] Hrestrict]]. subst σsw σ.
      exists (storeA_restrict σ0 X). split.
      * exists σ0. split; [exact Hσ0 | reflexivity].
      * symmetry. apply storeA_restrict_swap.
    + intros [σ0 [[σw [Hσw Hrestrict]] Hswap]]. subst σ0 σ.
      exists (storeA_swap x y σw). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite storeA_restrict_swap. reflexivity.
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
	    rewrite <- Hrestr.
	    pose proof (storeA_restrict_dom σm D) as Hdomr.
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
          (storeA_restrict τm X)).
      { exists τm. split; [exact Hτm | reflexivity]. }
      rewrite Hproj in HτmX.
      destruct HτmX as [τn [Hτn HτnX]].
      exists τn. split.
      * split; [exact Hτn |].
        transitivity (storeA_restrict τm (dom (σ : gmap K V))).
        -- eapply storeA_restrict_eq_mono; [exact HdomσX | exact HτnX].
        -- exact HτD.
      * rewrite HτnX. exact HτX.
    + intros [τn [[Hτn HτD] HτX]].
      assert (HτnX : (resA_restrict n X : WorldAT)
          (storeA_restrict τn X)).
      { exists τn. split; [exact Hτn | reflexivity]. }
      rewrite <- Hproj in HτnX.
      destruct HτnX as [τm [Hτm HτmX]].
      exists τm. split.
      * split; [exact Hτm |].
        transitivity (storeA_restrict τn (dom (σ : gmap K V))).
        -- eapply storeA_restrict_eq_mono; [exact HdomσX | exact HτmX].
        -- exact HτD.
      * rewrite HτmX. exact HτX.
Qed.

Lemma resA_fiber_from_projection_transport_on
    (m n nfib : WfWorldAT) (σ : StoreAT) (D X : gset K) :
  D ⊆ X →
  D ⊆ worldA_dom (m : WorldAT) →
  resA_restrict m X = resA_restrict n X →
  resA_fiber_from_projection n D σ nfib →
  ∃ mfib,
    resA_fiber_from_projection m D σ mfib ∧
    resA_restrict mfib X = resA_restrict nfib X.
Proof.
  intros HDX HDm Hproj Hfiber_n.
  pose proof (resA_restrict_eq_subset m n X D HDX Hproj) as HprojD.
  destruct Hfiber_n as [Hσproj_n Heq_n].
  assert ((resA_restrict m D : WorldAT) σ) as Hσproj_m.
  { rewrite HprojD. exact Hσproj_n. }
  destruct Hσproj_m as [σm [Hσm Hrestrict_m]].
  assert (Hdomσ : dom (σ : gmap K V) = D).
  {
    rewrite <- Hrestrict_m.
    change (dom (storeA_restrict σm D : gmap K V) = D).
    pose proof (storeA_restrict_dom σm D) as Hdomr.
    change (dom (storeA_restrict σm D : gmap K V) =
      dom (σm : gmap K V) ∩ D) in Hdomr.
    rewrite Hdomr.
    pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
    rewrite Hdomσm. set_solver.
  }
  assert (Hnonempty_m :
      ∃ σm0, (m : WorldAT) σm0 ∧
        storeA_restrict σm0 (dom (σ : gmap K V)) = σ).
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
  exists mfib. split; [exact Hfiber_m |].
  eapply resA_fiber_from_projection_eq_on; eauto.
  split; [exact Hσproj_n | exact Heq_n].
Qed.

(** * Pullback and product-lifting lemmas for abstract resource algebra *)

Definition rawA_pullback_projection (n p : WfWorldAT) : WorldAT := {|
  worldA_dom := worldA_dom (n : WorldAT);
  worldA_stores := fun σ =>
    (n : WorldAT) σ ∧
    (p : WorldAT) (storeA_restrict σ (worldA_dom (p : WorldAT)));
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
    (p : WorldAT) (storeA_restrict σ (worldA_dom (p : WorldAT)));
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

Lemma resA_pullback_subset_projection_subset (n p : WfWorldAT) Hsub :
  resA_subset (resA_pullback_subset_projection n p Hsub) n.
Proof.
  split; [reflexivity |].
  intros σ [Hσ _]. exact Hσ.
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
        set_solver.
      * exists σ. split; [exact Hσ |].
        apply storeA_restrict_idemp.
        pose proof (wfworldA_store_dom n σ Hσ) as Hdomσ.
        set_solver.
    + intros [σn [Hσ Hrestrict]].
      subst σ.
      rewrite storeA_restrict_idemp by
        (pose proof (wfworldA_store_dom n σn Hσ) as Hdomσ;
         set_solver).
      assert (Hσsum : (resA_sum n1 n2 Hdef : WorldAT)
          (storeA_restrict σn (worldA_dom (n1 : WorldAT)))).
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
           set_solver.
        -- pose proof (wfworldA_store_dom w2' σ2' Hσ2') as Hdomσ2'.
           set_solver.
    + intros [σ' [Hσ' Hrestrict]].
      destruct Hσ' as [σ1' [σ2' [Hσ1' [Hσ2' [Hcompat' ->]]]]].
      set (σ1 := storeA_restrict σ1' (worldA_dom (w1 : WorldAT))).
      set (σ2 := storeA_restrict σ2' (worldA_dom (w2 : WorldAT))).
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
           set_solver.
        -- pose proof (wfworldA_store_dom w2' σ2' Hσ2') as Hdomσ2'.
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
      (mu : WorldAT) (storeA_restrict σ (worldA_dom (m : WorldAT)))
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
              change (dom (storeA_restrict σ2 (worldA_dom (w1 : WorldAT)) : gmap K V) =
                dom (σ2 : gmap K V) ∩ worldA_dom (w1 : WorldAT)) in Hdomr.
              rewrite Hdomr.
              pose proof (wfworldA_store_dom w1 σ Hσ) as Hdomσ.
              set_solver.
        -- pose proof (wfworldA_store_dom w1 σ Hσ) as Hdomσ.
           set_solver.
    + intros [σ12 [Hσ12 Hrestrict]].
      destruct Hσ12 as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      rewrite storeA_restrict_union in Hrestrict by exact Hcompat.
      rewrite storeA_restrict_idemp in Hrestrict.
      * rewrite (storeA_union_absorb_l σ1
          (storeA_restrict σ2 (worldA_dom (w1 : WorldAT)))) in Hrestrict.
        -- subst. exact Hσ1.
        -- apply storeA_compat_restrict_r. exact Hcompat.
        -- pose proof (storeA_restrict_dom σ2 (worldA_dom (w1 : WorldAT))) as Hdomr.
           change (dom (storeA_restrict σ2 (worldA_dom (w1 : WorldAT)) : gmap K V) =
             dom (σ2 : gmap K V) ∩ worldA_dom (w1 : WorldAT)) in Hdomr.
           rewrite Hdomr.
           pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdomσ1.
           set_solver.
      * pose proof (wfworldA_store_dom w1 σ1 Hσ1) as Hdomσ1.
        set_solver.
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
    assert (Hm_proj :
        (m : WorldAT) (storeA_restrict σ (worldA_dom (m : WorldAT)))).
    {
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hle.
      rewrite Hle at 1. simpl. exists σ. split; [exact Hσn | reflexivity].
    }
    assert (Hmo_proj :
        (mo : WorldAT) (storeA_restrict σ (worldA_dom (m : WorldAT)))).
    { exact (Hin_m_mo _ Hm_proj). }
    assert (Hextra :
        (resA_restrict n (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)) : WorldAT)
          (storeA_restrict σ
            (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)))).
    {
      simpl. exists σ. split; [exact Hσn | reflexivity].
    }
    assert (Hstore_part_compat :
        storeA_compat
          (storeA_restrict σ (worldA_dom (m : WorldAT)))
          (storeA_restrict σ
            (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT)))).
    {
      apply storeA_disj_dom_compat.
      apply set_eq. intros x. split.
      - intros Hin.
        apply elem_of_intersection in Hin as [Hin1 Hin2].
        pose proof (storeA_restrict_dom σ (worldA_dom (m : WorldAT))) as Hdom1.
        pose proof (storeA_restrict_dom σ
          (worldA_dom (n : WorldAT) ∖ worldA_dom (m : WorldAT))) as Hdom2.
        change (dom (storeA_restrict σ (worldA_dom (m : WorldAT)) : gmap K V) =
          dom (σ : gmap K V) ∩ worldA_dom (m : WorldAT)) in Hdom1.
        change (dom (storeA_restrict σ
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
    exists (storeA_restrict σ (worldA_dom (m : WorldAT))),
      (storeA_restrict σ
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
          storeA_compat σn (storeA_restrict τm S)).
      {
        apply (Hc σn (storeA_restrict τm S)).
        - exact Hσn.
        - simpl. exists τm. split; [exact Hτm | reflexivity].
      }
      exists (@union (gmap K V) _ (σn : gmap K V)
        (storeA_restrict τm S : gmap K V)).
      split.
      * simpl. exists σn, (storeA_restrict τm S).
        repeat split; eauto.
      * replace (((worldA_dom (n : WorldAT) ∩ X) ∪ worldA_dom (m : WorldAT)) ∩ Y)
          with Y by set_solver.
        transitivity (storeA_restrict
          (@union (gmap K V) _ (storeA_restrict σn X : gmap K V)
            (τm : gmap K V)) Y).
        -- assert (HYτm : Y ⊆ dom (τm : gmap K V)).
           { pose proof (wfworldA_store_dom m τm Hτm) as Hdomτm.
             rewrite Hdomτm. exact HYm. }
           exact (storeA_restrict_wand_product σn τm S X Y
             Hcompat Htarget_compat HYS HYτm).
        -- exact Hrestrict.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [τn [τm [Hτn [Hτm [Hcompat ->]]]]].
      simpl in Hτm. destruct Hτm as [σm [Hσm HmS]]. subst τm.
      set (σnX := storeA_restrict τn X).
      exists (@union (gmap K V) _ (σnX : gmap K V) (σm : gmap K V)).
      split.
      * exists σnX, σm. repeat split.
        -- subst σnX. simpl. exists τn. split; [exact Hτn | reflexivity].
        -- exact Hσm.
        -- subst σnX. apply (Hc_small (storeA_restrict τn X) σm).
           ++ simpl. exists τn. split; [exact Hτn | reflexivity].
           ++ exact Hσm.
      * subst σnX.
        replace (((worldA_dom (n : WorldAT) ∩ X) ∪ worldA_dom (m : WorldAT)) ∩ Y)
          with Y in Hrestrict by set_solver.
        rewrite <- Hrestrict.
        symmetry.
        assert (Hsmall_compat :
            storeA_compat (storeA_restrict τn X) σm).
        {
          apply (Hc_small (storeA_restrict τn X) σm).
          - simpl. exists τn. split; [exact Hτn | reflexivity].
          - exact Hσm.
        }
        assert (HYσm : Y ⊆ dom (σm : gmap K V)).
        {
          pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
          rewrite Hdomσm. exact HYm.
        }
        exact (storeA_restrict_wand_product τn σm S X Y
          Hsmall_compat Hcompat HYS HYσm).
Qed.

Lemma resA_product_restrict_frame_common_eq
    (n m : WfWorldAT) (X S C Y : gset K)
    (Hc_common : worldA_compat (resA_restrict n X) (resA_restrict m C))
    (Hc_tgt : worldA_compat n (resA_restrict m S)) :
  S ⊆ C ->
  Y ⊆ (X ∩ worldA_dom (n : WorldAT)) ∪
        (S ∩ worldA_dom (m : WorldAT)) ->
  resA_restrict
    (resA_product (resA_restrict n X) (resA_restrict m C) Hc_common)
    Y =
  resA_restrict (resA_product n (resA_restrict m S) Hc_tgt) Y.
Proof.
  intros HSC HY.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [τn [τm [Hτn [Hτm [Hcompat ->]]]]].
      simpl in Hτn. destruct Hτn as [σn [Hσn HnX]]. subst τn.
      simpl in Hτm. destruct Hτm as [σm [Hσm HmC]]. subst τm.
      assert (Htarget_compat :
          storeA_compat σn (storeA_restrict σm S)).
      {
        apply (Hc_tgt σn (storeA_restrict σm S)).
        - exact Hσn.
        - simpl. exists σm. split; [exact Hσm | reflexivity].
      }
      exists (@union (gmap K V) _ (σn : gmap K V)
        (storeA_restrict σm S : gmap K V)).
      split.
      * simpl. exists σn, (storeA_restrict σm S).
        split; [exact Hσn|].
        split.
        -- simpl. exists σm. split; [exact Hσm | reflexivity].
        -- split; [exact Htarget_compat|reflexivity].
      * pose proof (wfworldA_store_dom n σn Hσn) as Hdomn.
        pose proof (wfworldA_store_dom m σm Hσm) as Hdomm.
        assert (HYstores :
            Y ⊆ (X ∩ dom (σn : gmap K V)) ∪
                  (S ∩ dom (σm : gmap K V))).
        { rewrite Hdomn, Hdomm. exact HY. }
        pose proof (storeA_restrict_product_frame_common
          σn σm X S C Y HSC HYstores Htarget_compat) as Hstore.
        rewrite <- Hstore. exact Hrestrict.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [σn [τm [Hσn [Hτm [Hcompat ->]]]]].
      simpl in Hτm. destruct Hτm as [σm [Hσm HmS]]. subst τm.
      assert (Hcommon_compat :
          storeA_compat (storeA_restrict σn X) (storeA_restrict σm C)).
      {
        apply (Hc_common (storeA_restrict σn X)
          (storeA_restrict σm C)).
        - simpl. exists σn. split; [exact Hσn | reflexivity].
        - simpl. exists σm. split; [exact Hσm | reflexivity].
      }
      exists (@union (gmap K V) _ (storeA_restrict σn X : gmap K V)
        (storeA_restrict σm C : gmap K V)).
      split.
      * simpl.
        exists (storeA_restrict σn X), (storeA_restrict σm C).
        split.
        -- simpl. exists σn. split; [exact Hσn | reflexivity].
        -- split.
           ++ simpl. exists σm. split; [exact Hσm | reflexivity].
           ++ split; [exact Hcommon_compat|reflexivity].
      * pose proof (wfworldA_store_dom n σn Hσn) as Hdomn.
        pose proof (wfworldA_store_dom m σm Hσm) as Hdomm.
        assert (HYstores :
            Y ⊆ (X ∩ dom (σn : gmap K V)) ∪
                  (S ∩ dom (σm : gmap K V))).
        { rewrite Hdomn, Hdomm. exact HY. }
        pose proof (storeA_restrict_product_frame_common
          σn σm X S C Y HSC HYstores Hcompat) as Hstore.
        rewrite Hstore. exact Hrestrict.
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



(** * Sum/restrict lifting lemmas for abstract resource algebra *)

Lemma resA_sum_le_mono (w1 w2 w1' w2' : WfWorldAT)
    (Hdef : rawA_sum_defined w1 w2) (Hdef' : rawA_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  resA_sum w1 w2 Hdef ⊑ resA_sum w1' w2' Hdef'.
Proof.
  intros Hle1 Hle2.
  exact (rawA_sum_le_mono w1 w2 w1' w2' Hdef Hdef' Hle1 Hle2).
Qed.

Lemma resA_sum_restrict_same_le
    (m m1 m2 : WfWorldAT) (X : gset K)
    (Hdef : rawA_sum_defined m1 m2) :
  resA_sum m1 m2 Hdef ⊑ m →
  ∃ HdefX : rawA_sum_defined (resA_restrict m1 X) (resA_restrict m2 X),
    resA_sum (resA_restrict m1 X) (resA_restrict m2 X) HdefX
      ⊑ resA_restrict m X.
Proof.
  intros Hle.
  assert (HdefX : rawA_sum_defined (resA_restrict m1 X) (resA_restrict m2 X)).
  {
    unfold rawA_sum_defined in *. simpl.
    rewrite Hdef. reflexivity.
  }
  exists HdefX.
  eapply resA_le_restrict.
  - etrans; [| exact Hle].
    eapply resA_sum_le_mono; apply resA_restrict_le.
  - simpl. set_solver.
Qed.

(** * Algebraic laws for abstract resources *)

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

Lemma resA_le_product_r (w1 w2 : WfWorldAT) (Hc : worldA_compat w1 w2) :
  w2 ⊑ resA_product w1 w2 Hc.
Proof.
  destruct (resA_product_comm_eq w1 w2 Hc) as [Hc' Heq].
  rewrite Heq.
  apply resA_le_product_l.
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

#[global] Program Instance WfWorldA_ContextAlgebra :
  ContextAlgebra WfWorldAT := {|
  ca_one       := resA_unit;
  ca_times_def := fun w1 w2 => worldA_compat w1 w2;
  ca_plus_def  := fun w1 w2 => rawA_sum_defined w1 w2;
  ca_times     := resA_product;
  ca_plus      := resA_sum;
  ca_le        := sqsubseteq (A := WfWorldAT);
|}.
Next Obligation. intro m. exact (rawA_compat_unit_r (m : WorldAT)). Qed.
Next Obligation. intro m. apply resA_product_unit_r_eq_any. Qed.
Next Obligation. apply resA_product_comm_eq. Qed.
Next Obligation. apply resA_sum_comm_eq. Qed.
Next Obligation. apply resA_product_assoc_eq. Qed.
Next Obligation. apply resA_sum_assoc_eq. Qed.
Next Obligation. intro w. exact (reflexivity w). Qed.
Next Obligation. eapply resA_product_le_mono; eauto. Qed.
Next Obligation. eapply resA_sum_le_mono; eauto. Qed.

End ResourceAlgebraA.
