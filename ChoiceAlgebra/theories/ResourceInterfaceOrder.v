(** * Concrete resource key action and order interface lemmas *)

From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebra ResourceExtension ResourceExtensionDerived.
From ChoiceAlgebra Require Export ResourceInterfaceBasic.
From Stdlib Require Import Logic.ProofIrrelevance.

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@Store V) (only parsing).
Local Notation World := (@World V) (only parsing).
Local Notation WfWorld := (@WfWorld V) (only parsing).

Lemma res_swap_involutive (x y : atom) (w : WfWorld) :
  res_swap x y (res_swap x y w) = w.
Proof. apply resA_swap_involutive. Qed.

Lemma res_swap_sym (x y : atom) (w : WfWorld) :
  res_swap x y w = res_swap y x w.
Proof. apply resA_swap_sym. Qed.

Lemma res_swap_conjugate a b x y (w : WfWorld) :
  res_swap a b (res_swap x y w) =
  res_swap (atom_swap a b x) (atom_swap a b y) (res_swap a b w).
Proof. apply resA_swap_conjugate. Qed.

Lemma res_swap_conjugate_inv a b x y (w : WfWorld) :
  res_swap x y (res_swap a b w) =
  res_swap a b (res_swap (atom_swap a b x) (atom_swap a b y) w).
Proof. apply resA_swap_conjugate_inv. Qed.

Lemma res_restrict_swap (x y : atom) (w : WfWorld) (X : aset) :
  res_restrict (res_swap x y w) (gset_swap x y X) =
  res_swap x y (res_restrict w X).
Proof. apply resA_restrict_swap. Qed.

Lemma res_restrict_swap_projection x y (w : WfWorld) (X : aset) (σ : Store) :
  res_restrict w X σ →
  res_restrict (res_swap x y w) (aset_swap x y X) (store_swap x y σ).
Proof. apply resA_restrict_swap_projection. Qed.

Lemma res_swap_extension_dom (x y : atom) (m my : WfWorld) (z : atom) :
  world_dom (my : World) = world_dom (m : World) ∪ {[z]} →
  world_dom (res_swap x y my : World) =
  world_dom (res_swap x y m : World) ∪ {[atom_swap x y z]}.
Proof. apply resA_swap_extension_dom. Qed.

Lemma res_swap_extension_dom_cancel
    (x y : atom) (m my : WfWorld) (z : atom) :
  world_dom (my : World) = world_dom (res_swap x y m : World) ∪ {[z]} →
  world_dom (res_swap x y my : World) =
  world_dom (m : World) ∪ {[atom_swap x y z]}.
Proof. apply resA_swap_extension_dom_cancel. Qed.

Lemma res_swap_restrict_extension
    (x y : atom) (m my : WfWorld) :
  res_restrict my (world_dom (m : World)) = m →
  res_restrict (res_swap x y my) (world_dom (res_swap x y m : World)) =
  res_swap x y m.
Proof. apply resA_swap_restrict_extension. Qed.

Lemma res_swap_restrict_extension_cancel
    (x y : atom) (m my : WfWorld) :
  res_restrict my (world_dom (res_swap x y m : World)) = res_swap x y m →
  res_restrict (res_swap x y my) (world_dom (m : World)) = m.
Proof. apply resA_swap_restrict_extension_cancel. Qed.

Lemma res_restrict_shift (k : nat) (w : WfWorld) (X : aset) :
  res_restrict (res_shift k w) (set_map (key_shift k) X) =
  res_shift k (res_restrict w X).
Proof. apply resA_restrict_shift. Qed.

Lemma res_restrict_restrict_eq (w : WfWorld) (X Y : aset) :
  res_restrict (res_restrict w X) Y =
  res_restrict w (X ∩ Y).
Proof. apply resA_restrict_restrict_eq. Qed.

Lemma res_restrict_self (w : WfWorld) :
  res_restrict w (world_dom (w : World)) = w.
Proof. apply resA_restrict_self. Qed.

Lemma res_fiber_swap x y (w : WfWorld) (σ : Store)
    (Hne : ∃ σ0, (w : World) σ0 ∧ store_restrict σ0 (dom σ) = σ)
    (Hne' : ∃ σ0, (res_swap x y w : World) σ0 ∧
      store_restrict σ0 (dom (store_swap x y σ)) = store_swap x y σ) :
  res_swap x y (res_fiber w σ Hne) =
  res_fiber (res_swap x y w) (store_swap x y σ) Hne'.
Proof. apply resA_fiber_swap. Qed.

Lemma res_fiber_from_projection_swap x y (w wfib wfib' : WfWorld)
    (X : aset) (σ : Store) :
  res_fiber_from_projection w X σ wfib →
  res_fiber_from_projection (res_swap x y w) (gset_swap x y X)
    (store_swap x y σ) wfib' →
  res_swap x y wfib = wfib'.
Proof. apply resA_fiber_from_projection_swap. Qed.

Lemma world_compat_swap (x y : atom) (w1 w2 : WfWorld) :
  world_compat (res_swap x y w1) (res_swap x y w2) ↔
  world_compat w1 w2.
Proof. apply worldA_compat_swap. Qed.

Lemma res_product_swap (x y : atom) (w1 w2 : WfWorld)
    (Hc : world_compat w1 w2)
    (Hc' : world_compat (res_swap x y w1) (res_swap x y w2)) :
  res_swap x y (res_product w1 w2 Hc) =
  res_product (res_swap x y w1) (res_swap x y w2) Hc'.
Proof.
  transitivity (res_product (res_swap x y w1) (res_swap x y w2)
    (proj2 (worldA_compat_swap x y w1 w2) Hc)).
  - unfold res_swap, res_product, world_compat. apply resA_product_swap.
  - unfold res_product. f_equal. apply proof_irrelevance.
Qed.

Lemma res_product_double_swap_l (x y : atom) (w1 w2 : WfWorld)
    (Hc : world_compat w1 w2)
    (Hc' : world_compat (res_swap x y (res_swap x y w1)) w2) :
  res_product (res_swap x y (res_swap x y w1)) w2 Hc' =
  res_product w1 w2 Hc.
Proof. apply resA_product_double_swap_l. Qed.

Lemma res_sum_swap (x y : atom) (w1 w2 : WfWorld)
    (Hdef : raw_sum_defined w1 w2)
    (Hdef' : raw_sum_defined (res_swap x y w1) (res_swap x y w2)) :
  res_swap x y (res_sum w1 w2 Hdef) =
  res_sum (res_swap x y w1) (res_swap x y w2) Hdef'.
Proof. apply resA_sum_swap. Qed.

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

Lemma res_le_restrict (m n : WfWorld) (X : aset) :
  m ⊑ n →
  world_dom (m : World) ⊆ X →
  m ⊑ res_restrict n X.
Proof. apply resA_le_restrict. Qed.

Lemma res_restrict_le_mono (m n : WfWorld) (X : aset) :
  m ⊑ n →
  res_restrict m X ⊑ res_restrict n X.
Proof. apply resA_restrict_le_mono. Qed.

Lemma res_swap_le (x y : atom) (w1 w2 : WfWorld) :
  w1 ⊑ w2 →
  res_swap x y w1 ⊑ res_swap x y w2.
Proof. apply resA_swap_le. Qed.

Lemma res_swap_le_iff (x y : atom) (w1 w2 : WfWorld) :
  res_swap x y w1 ⊑ res_swap x y w2 ↔ w1 ⊑ w2.
Proof. apply resA_swap_le_iff. Qed.

Lemma res_restrict_le_eq (m n : WfWorld) (X : aset) :
  m ⊑ n →
  X ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X.
Proof. apply resA_restrict_le_eq. Qed.

Lemma res_restrict_le_eq_from_base
    (m n : WfWorld) (S X : aset) :
  res_restrict m S ⊑ n →
  X ⊆ S →
  X ⊆ world_dom (m : World) →
  res_restrict n X = res_restrict m X.
Proof. apply resA_restrict_le_eq_from_base. Qed.

Lemma res_restrict_eq_subset
    (m n : WfWorld) (X Y : aset) :
  Y ⊆ X →
  res_restrict m X = res_restrict n X →
  res_restrict m Y = res_restrict n Y.
Proof. apply resA_restrict_eq_subset. Qed.

Lemma res_fiber_from_projection_le
    (m n wfib_m wfib_n : WfWorld) (X : aset) (σ : Store) :
  res_fiber_from_projection m X σ wfib_m →
  res_fiber_from_projection n X σ wfib_n →
  m ⊑ n →
  X ⊆ world_dom (m : World) →
  wfib_m ⊑ wfib_n.
Proof. apply resA_fiber_from_projection_le. Qed.

Lemma res_fiber_from_projection_eq_on
    (m n wfib_m wfib_n : WfWorld) (D X : aset) (σ : Store) :
  D ⊆ X →
  res_restrict m X = res_restrict n X →
  res_fiber_from_projection m D σ wfib_m →
  res_fiber_from_projection n D σ wfib_n →
  res_restrict wfib_m X = res_restrict wfib_n X.
Proof. apply resA_fiber_from_projection_eq_on. Qed.

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

Lemma res_le_same_dom_eq (w1 w2 : WfWorld) :
  w1 ⊑ w2 →
  world_dom (w1 : World) = world_dom (w2 : World) →
  w1 = w2.
Proof. apply resA_le_same_dom_eq. Qed.

Lemma res_subset_of_le_same_domain (n m : WfWorld) :
  n ⊑ m →
  world_dom (n : World) = world_dom (m : World) →
  res_subset n m.
Proof. apply resA_subset_of_le_same_domain. Qed.

Lemma res_subset_via_sum_left (n1 n2 m : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  res_sum n1 n2 Hdef ⊑ m →
  world_dom (n1 : World) = world_dom (m : World) →
  res_subset n1 m.
Proof. apply resA_subset_via_sum_left. Qed.

Lemma res_subset_via_sum_right (n1 n2 m : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  res_sum n1 n2 Hdef ⊑ m →
  world_dom (n2 : World) = world_dom (m : World) →
  res_subset n2 m.
Proof. apply resA_subset_via_sum_right. Qed.

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

Lemma res_pullback_projection_subset (n p : WfWorld) Hle :
  res_subset (res_pullback_projection n p Hle) n.
Proof. apply resA_pullback_projection_subset. Qed.

Lemma res_pullback_projection_restrict (n p : WfWorld) Hle :
  res_restrict (res_pullback_projection n p Hle)
    (world_dom (p : World)) = p.
Proof. apply resA_pullback_projection_restrict. Qed.

Lemma res_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_product w1 w2 Hc ⊑ res_product w1' w2' Hc'.
Proof. apply resA_product_le_mono. Qed.

Lemma res_subset_lift_under (m n mu : WfWorld) :
  m ⊑ n →
  res_subset mu m →
  ∃ nu : WfWorld,
    res_subset nu n ∧ mu ⊑ nu.
Proof. apply resA_subset_lift_under. Qed.

Lemma res_le_product_l (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w1 ⊑ res_product w1 w2 Hc.
Proof. apply resA_le_product_l. Qed.

Lemma res_one_point_extension_exists (w : WfWorld) (y : atom) :
  y ∉ world_dom (w : World) →
  ∃ wy : WfWorld,
    world_dom (wy : World) = world_dom (w : World) ∪ {[y]} ∧
    res_restrict wy (world_dom (w : World)) = w.
Proof. apply resA_one_point_extension_exists. Qed.

Lemma res_subset_lift_over (m n mo : WfWorld) :
  m ⊑ n →
  res_subset m mo →
  ∃ no : WfWorld,
    res_subset n no ∧ mo ⊑ no.
Proof. apply resA_subset_lift_over. Qed.

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

Lemma res_restrict_sum
    (w1 w2 : WfWorld) (X : aset)
    (Hdef : raw_sum_defined w1 w2)
    (HdefX : raw_sum_defined (res_restrict w1 X) (res_restrict w2 X)) :
  res_sum (res_restrict w1 X) (res_restrict w2 X) HdefX =
  res_restrict (res_sum w1 w2 Hdef) X.
Proof. apply resA_restrict_sum. Qed.

Lemma res_sum_restrict_same_le
    (m m1 m2 : WfWorld) (X : aset)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  ∃ HdefX : raw_sum_defined (res_restrict m1 X) (res_restrict m2 X),
    res_sum (res_restrict m1 X) (res_restrict m2 X) HdefX
      ⊑ res_restrict m X.
Proof. apply resA_sum_restrict_same_le. Qed.

Lemma res_sum_lift_along_restrict
    (m n1 n2 : WfWorld) (X : aset) (Hdef : raw_sum_defined n1 n2) :
  world_dom (n1 : World) = world_dom (res_restrict m X : World) →
  res_sum n1 n2 Hdef ⊑ res_restrict m X →
  ∃ (m1 m2 : WfWorld) (Hdef' : raw_sum_defined m1 m2),
    world_dom (m1 : World) = world_dom (m : World) ∧
    world_dom (m2 : World) = world_dom (m : World) ∧
    res_subset m1 m ∧
    res_subset m2 m ∧
    res_restrict m1 X = n1 ∧
    res_restrict m2 X = n2 ∧
    res_sum m1 m2 Hdef' ⊑ m.
Proof. apply resA_sum_lift_along_restrict. Qed.

Lemma res_product_comm (w1 w2 : WfWorld) (Hc : world_compat w1 w2)
    (Hc' : world_compat w2 w1) :
  ∀ σ, res_product w1 w2 Hc σ ↔ res_product w2 w1 Hc' σ.
Proof. apply resA_product_comm. Qed.

Lemma res_product_unit_r_any (w : WfWorld) (Hc : world_compat w res_unit) :
  ∀ σ, res_product w res_unit Hc σ ↔ (w : World) σ.
Proof. apply resA_product_unit_r_any. Qed.

Lemma res_product_unit_r (w : WfWorld) :
  ∀ σ, res_product w res_unit (raw_compat_unit_r w) σ ↔ (w : World) σ.
Proof. apply res_product_unit_r_any. Qed.

Lemma res_product_unit_r_eq (w : WfWorld) :
  res_product w res_unit (raw_compat_unit_r w) = w.
Proof.
  transitivity (res_product w res_unit (rawA_compat_unit_r (w : World))).
  - unfold res_product. f_equal. apply proof_irrelevance.
  - apply resA_product_unit_r_eq.
Qed.

Lemma res_product_unit_r_eq_any (w : WfWorld) (Hc : world_compat w res_unit) :
  res_product w res_unit Hc = w.
Proof. apply resA_product_unit_r_eq_any. Qed.

Lemma res_sum_comm (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2)
    (Hdef' : raw_sum_defined w2 w1) :
  ∀ σ, res_sum w1 w2 Hdef σ ↔ res_sum w2 w1 Hdef' σ.
Proof. apply resA_sum_comm. Qed.

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

Lemma world_compat_spec (w1 w2 : WfWorld) :
  let X := world_dom (w1 : World) ∩ world_dom (w2 : World) in
  world_compat w1 w2 ↔
    exists σ,
      raw_restrict w1 X = singleton_world σ ∧
      raw_restrict w2 X = singleton_world σ.
Proof. apply worldA_compat_spec. Qed.

End ResourceInterface.
