(** * Concrete resource key action and order interface lemmas *)

From ContextPrelude Require Import Prelude Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebra ResourceExtension ResourceExtensionDerived.
From ContextAlgebra Require Export ResourceInterfaceBasic.
From Stdlib Require Import Logic.ProofIrrelevance.

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@Store V) (only parsing).
Local Notation World := (@World V) (only parsing).
Local Notation WfWorld := (@WfWorld V) (only parsing).

Lemma res_restrict_restrict_eq (w : WfWorld) (X Y : aset) :
  res_restrict (res_restrict w X) Y =
  res_restrict w (X ∩ Y).
Proof. apply resA_restrict_restrict_eq. Qed.

Lemma res_restrict_le (w : WfWorld) (X : aset) :
  res_restrict w X ⊑ w.
Proof. apply resA_restrict_le. Qed.

Lemma res_restrict_mono (w : WfWorld) (X Y : aset) :
  X ⊆ Y →
  res_restrict w X ⊑ res_restrict w Y.
Proof. apply resA_restrict_mono. Qed.

Lemma res_restrict_eq_of_le (m n : WfWorld) :
  m ⊑ n →
  res_restrict n (world_dom (m : World)) = m.
Proof. apply resA_restrict_eq_of_le. Qed.

Lemma res_restrict_le_eq (m n : WfWorld) (X : aset) :
  m ⊑ n →
  X ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X.
Proof. apply resA_restrict_le_eq. Qed.

Lemma res_restrict_eq_subset
    (m n : WfWorld) (X Y : aset) :
  Y ⊆ X →
  res_restrict m X = res_restrict n X →
  res_restrict m Y = res_restrict n Y.
Proof. apply resA_restrict_eq_subset. Qed.

Lemma res_fiber_member_projection_transport_on
    (m n nfib : WfWorld) (D X : aset) :
  D ⊆ X →
  D ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X →
  res_fiber_member n D nfib →
  ∃ mfib,
    res_fiber_member m D mfib ∧
    res_restrict mfib X = res_restrict nfib X.
Proof. apply resA_fiber_member_projection_transport_on. Qed.

Lemma world_compat_le_r (w m n : WfWorld) :
  m ⊑ n →
  world_compat w n →
  world_compat w m.
Proof. apply worldA_compat_le_r. Qed.

Lemma world_compat_le_l (w m n : WfWorld) :
  m ⊑ n →
  world_compat n w →
  world_compat m w.
Proof. apply worldA_compat_le_l. Qed.

Lemma world_compat_restrict_l_full_r (n m : WfWorld) (S X : aset) :
  X ⊆ S →
  world_compat n (res_restrict m S) →
  world_compat (res_restrict n X) m.
Proof. apply worldA_compat_restrict_l_full_r. Qed.

Definition res_pullback_subset_projection (n p : WfWorld)
    (Hsub : res_subset p (res_restrict n (world_dom (p : World)))) : WfWorld :=
  resA_pullback_subset_projection n p Hsub.

Lemma res_pullback_subset_projection_restrict (n p : WfWorld) Hsub :
  res_restrict (res_pullback_subset_projection n p Hsub)
    (world_dom (p : World)) = p.
Proof. apply resA_pullback_subset_projection_restrict. Qed.

Lemma res_sum_pullback_subset_projection_full
    (n n1 n2 : WfWorld) (Hdef : raw_sum_defined n1 n2) :
  res_sum n1 n2 Hdef ⊑ n →
  ∃ (Hsub1 : res_subset n1 (res_restrict n (world_dom (n1 : World))))
    (Hsub2 : res_subset n2 (res_restrict n (world_dom (n2 : World))))
    (Hdef_full : raw_sum_defined
      (res_pullback_subset_projection n n1 Hsub1)
      (res_pullback_subset_projection n n2 Hsub2)),
    res_sum
      (res_pullback_subset_projection n n1 Hsub1)
      (res_pullback_subset_projection n n2 Hsub2)
      Hdef_full ⊑ n.
Proof. apply resA_sum_pullback_subset_projection_full. Qed.

Lemma res_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_product w1 w2 Hc ⊑ res_product w1' w2' Hc'.
Proof. apply resA_product_le_mono. Qed.

Lemma res_subset_lift_under_projection_on
    (m n mu : WfWorld) (X : aset) :
  res_restrict m X = res_restrict n X →
  res_subset mu m →
  ∃ nu : WfWorld,
    res_subset nu n ∧ res_restrict mu X ⊑ nu.
Proof. apply resA_subset_lift_under_projection_on. Qed.

Lemma res_subset_lift_over_projection_on
    (m n mo : WfWorld) (X : aset) :
  res_restrict m X = res_restrict n X →
  res_subset m mo →
  ∃ no : WfWorld,
    res_subset n no ∧ res_restrict mo X ⊑ no.
Proof. apply resA_subset_lift_over_projection_on. Qed.

Lemma res_product_restrict_wand_le
    (n m : WfWorld) (S X Y : aset)
    (Hc_small : world_compat (res_restrict n X) m)
    (Hc : world_compat n (res_restrict m S)) :
  Y ⊆ S →
  Y ⊆ world_dom (m : World) →
  res_restrict (res_product (res_restrict n X) m Hc_small) Y ⊑
  res_product n (res_restrict m S) Hc.
Proof. apply resA_product_restrict_wand_le. Qed.

Lemma res_product_restrict_same_le
    (m m1 m2 : WfWorld) (X : aset)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  ∃ HcX : world_compat (res_restrict m1 X) (res_restrict m2 X),
    res_product (res_restrict m1 X) (res_restrict m2 X) HcX
      ⊑ res_restrict m X.
Proof. apply resA_product_restrict_same_le. Qed.

Lemma res_sum_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hdef : raw_sum_defined w1 w2) (Hdef' : raw_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_sum w1 w2 Hdef ⊑ res_sum w1' w2' Hdef'.
Proof. apply resA_sum_le_mono. Qed.

Lemma res_sum_restrict_same_le
    (m m1 m2 : WfWorld) (X : aset)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  ∃ HdefX : raw_sum_defined (res_restrict m1 X) (res_restrict m2 X),
    res_sum (res_restrict m1 X) (res_restrict m2 X) HdefX
      ⊑ res_restrict m X.
Proof. apply resA_sum_restrict_same_le. Qed.

Lemma res_product_unit_r_eq_any (w : WfWorld) (Hc : world_compat w res_unit) :
  res_product w res_unit Hc = w.
Proof. apply resA_product_unit_r_eq_any. Qed.

Lemma res_product_comm_eq (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  ∃ Hc' : world_compat w2 w1,
    res_product w1 w2 Hc = res_product w2 w1 Hc'.
Proof. apply resA_product_comm_eq. Qed.

Lemma res_sum_comm_eq (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2) :
  ∃ Hdef' : raw_sum_defined w2 w1,
    res_sum w1 w2 Hdef = res_sum w2 w1 Hdef'.
Proof. apply resA_sum_comm_eq. Qed.

Lemma res_product_assoc_eq (w1 w2 w3 : WfWorld)
    (H12 : world_compat w1 w2)
    (H123 : world_compat (res_product w1 w2 H12) w3) :
  ∃ (H23 : world_compat w2 w3)
    (H1_23 : world_compat w1 (res_product w2 w3 H23)),
    res_product (res_product w1 w2 H12) w3 H123 =
    res_product w1 (res_product w2 w3 H23) H1_23.
Proof. apply resA_product_assoc_eq. Qed.

Lemma res_sum_assoc_eq (w1 w2 w3 : WfWorld)
    (H12 : raw_sum_defined w1 w2)
    (H123 : raw_sum_defined (res_sum w1 w2 H12) w3) :
  ∃ (H23 : raw_sum_defined w2 w3)
    (H1_23 : raw_sum_defined w1 (res_sum w2 w3 H23)),
    res_sum (res_sum w1 w2 H12) w3 H123 =
    res_sum w1 (res_sum w2 w3 H23) H1_23.
Proof. apply resA_sum_assoc_eq. Qed.

End ResourceInterface.
