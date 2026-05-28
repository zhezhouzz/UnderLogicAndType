From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict.
From Stdlib Require Import Logic.ProofIrrelevance.

From ContextAlgebra Require Import ResourceAlgebraBase ResourceAlgebraOrder ResourceAlgebraPullback.

(** * Sum/restrict lifting lemmas for abstract resource algebra *)

Section ResourceAlgebraA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Lemma resA_sum_le_mono (w1 w2 w1' w2' : WfWorldAT)
    (Hdef : rawA_sum_defined w1 w2) (Hdef' : rawA_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  resA_sum w1 w2 Hdef ⊑ resA_sum w1' w2' Hdef'.
Proof.
  intros Hle1 Hle2.
  exact (rawA_sum_le_mono w1 w2 w1' w2' Hdef Hdef' Hle1 Hle2).
Qed.

Lemma resA_restrict_sum
    (w1 w2 : WfWorldAT) (X : gset K)
    (Hdef : rawA_sum_defined w1 w2)
    (HdefX : rawA_sum_defined (resA_restrict w1 X) (resA_restrict w2 X)) :
  resA_sum (resA_restrict w1 X) (resA_restrict w2 X) HdefX =
  resA_restrict (resA_sum w1 w2 Hdef) X.
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. unfold rawA_sum_defined in Hdef. set_solver.
  - intros σ. simpl. split.
    + intros [[σ1 [Hσ1 Hrestrict]] | [σ2 [Hσ2 Hrestrict]]].
      * exists σ1. split; [left; exact Hσ1 | exact Hrestrict].
      * exists σ2. split; [right; exact Hσ2 | exact Hrestrict].
    + intros [σ0 [[Hσ0 | Hσ0] Hrestrict]].
      * left. exists σ0. split; [exact Hσ0 | exact Hrestrict].
      * right. exists σ0. split; [exact Hσ0 | exact Hrestrict].
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

Lemma resA_slice_sum_le_base
    (m n1 n2 : WfWorldAT) (X : gset K)
    (Hdef : rawA_sum_defined n1 n2)
    (Hsum_eq : resA_sum n1 n2 Hdef = resA_restrict m X)
    (Hsub1 : resA_subset n1 (resA_restrict m X))
    (Hsub2 : resA_subset n2 (resA_restrict m X))
    (Hdef' : rawA_sum_defined
      (resA_slice_restrict m X n1 Hsub1)
      (resA_slice_restrict m X n2 Hsub2)) :
  resA_sum
    (resA_slice_restrict m X n1 Hsub1)
    (resA_slice_restrict m X n2 Hsub2)
    Hdef' ⊑ m.
Proof.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
  apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [[Hσm _] | [Hσm _]].
      * exists σ. split; [exact Hσm |].
        apply storeA_restrict_idemp.
        pose proof (wfworldA_store_dom m σ Hσm) as Hdomσ.
        change (dom (σ : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσ.
        rewrite Hdomσ. set_solver.
      * exists σ. split; [exact Hσm |].
        apply storeA_restrict_idemp.
        pose proof (wfworldA_store_dom m σ Hσm) as Hdomσ.
        change (dom (σ : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσ.
        rewrite Hdomσ. set_solver.
    + intros [σm [Hσm Hrestrict]].
      pose proof (wfworldA_store_dom m σm Hσm) as Hdomσm.
      change (dom (σm : gmap K V) = worldA_dom (m : WorldAT)) in Hdomσm.
      rewrite storeA_restrict_idemp in Hrestrict by (rewrite Hdomσm; set_solver).
      subst σ.
      assert (Hproj : (resA_restrict m X : WorldAT) (@storeA_restrict V K _ _ σm X)).
      { exists σm. split; [exact Hσm | reflexivity]. }
      rewrite <- Hsum_eq in Hproj.
      simpl in Hproj.
      destruct Hproj as [Hn1 | Hn2].
      * left. split; [exact Hσm | exact Hn1].
      * right. split; [exact Hσm | exact Hn2].
Qed.

Lemma resA_sum_lift_along_restrict
    (m n1 n2 : WfWorldAT) (X : gset K) (Hdef : rawA_sum_defined n1 n2) :
  worldA_dom (n1 : WorldAT) = worldA_dom (resA_restrict m X : WorldAT) →
  resA_sum n1 n2 Hdef ⊑ resA_restrict m X →
  ∃ (m1 m2 : WfWorldAT) (Hdef' : rawA_sum_defined m1 m2),
    worldA_dom (m1 : WorldAT) = worldA_dom (m : WorldAT) ∧
    worldA_dom (m2 : WorldAT) = worldA_dom (m : WorldAT) ∧
    resA_subset m1 m ∧
    resA_subset m2 m ∧
    resA_restrict m1 X = n1 ∧
    resA_restrict m2 X = n2 ∧
    resA_sum m1 m2 Hdef' ⊑ m.
Proof.
  intros Hdom1 Hle.
  assert (Hdom_sum :
      worldA_dom (resA_sum n1 n2 Hdef : WorldAT) =
      worldA_dom (resA_restrict m X : WorldAT)).
  { simpl. exact Hdom1. }
  assert (Hsum_eq : resA_sum n1 n2 Hdef = resA_restrict m X).
  {
    pose proof (resA_restrict_eq_of_le
      (resA_sum n1 n2 Hdef) (resA_restrict m X) Hle) as Hrestrict.
    change (resA_restrict (resA_restrict m X)
      (worldA_dom (resA_sum n1 n2 Hdef : WorldAT)) =
      resA_sum n1 n2 Hdef) in Hrestrict.
    rewrite Hdom_sum in Hrestrict.
    rewrite resA_restrict_self in Hrestrict.
    symmetry. exact Hrestrict.
  }
  assert (Hsub1 : resA_subset n1 (resA_restrict m X)).
  { rewrite <- Hsum_eq. apply resA_sum_subset_l. }
  assert (Hsub2 : resA_subset n2 (resA_restrict m X)).
  { rewrite <- Hsum_eq. apply resA_sum_subset_r. }
  set (m1 := resA_slice_restrict m X n1 Hsub1).
  set (m2 := resA_slice_restrict m X n2 Hsub2).
  assert (Hdef' : rawA_sum_defined m1 m2).
  { unfold rawA_sum_defined. subst m1 m2. reflexivity. }
  exists m1, m2, Hdef'. split.
  - unfold m1. reflexivity.
  - split.
    + unfold m2. reflexivity.
    + split.
      * unfold m1. apply resA_slice_restrict_subset.
      * split.
        -- unfold m2. apply resA_slice_restrict_subset.
        -- split.
           ++ unfold m1. apply resA_slice_restrict_restrict.
           ++ split.
              ** unfold m2. apply resA_slice_restrict_restrict.
              ** unfold m1, m2.
                 apply (resA_slice_sum_le_base m n1 n2 X Hdef Hsum_eq Hsub1 Hsub2).
Qed.

End ResourceAlgebraA.
