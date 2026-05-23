(** * Concrete resource basic interface lemmas *)

From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebra ResourceExtension ResourceExtensionDerived.
From ChoiceAlgebra Require Export ResourceInterfaceCore.
From Stdlib Require Import Logic.ProofIrrelevance.

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@Store V) (only parsing).
Local Notation World := (@World V) (only parsing).
Local Notation WfWorld := (@WfWorld V) (only parsing).

Lemma world_ext (m1 m2 : World) :
  world_dom m1 = world_dom m2 →
  (∀ σ, m1 σ ↔ m2 σ) →
  m1 = m2.
Proof. apply worldA_ext. Qed.

Lemma wfworld_ext (w1 w2 : WfWorld) :
  (w1 : World) = (w2 : World) →
  w1 = w2.
Proof. apply wfworldA_ext. Qed.

Lemma wfworld_store_dom (w : WfWorld) (σ : Store) :
  w σ → dom σ = world_dom (w : World).
Proof. apply wfworldA_store_dom. Qed.

Lemma wfworld_store_dom_subset (w : WfWorld) (σ : Store) (X : aset) :
  w σ →
  world_dom (w : World) ⊆ X →
  dom σ ⊆ X.
Proof. apply wfworldA_store_dom_subset. Qed.

Lemma wfworld_store_restrict_dom (w : WfWorld) (σ : Store) (X : aset) :
  w σ → dom (store_restrict σ X) = world_dom (w : World) ∩ X.
Proof. apply wfworldA_store_restrict_dom. Qed.

Lemma disj_dom_world_compat (w1 w2 : WfWorld) :
  world_dom (w1 : World) ∩ world_dom (w2 : World) = ∅ →
  world_compat w1 w2.
Proof. apply disj_dom_worldA_compat. Qed.

Lemma world_compat_store_restrict_overlap
    (w1 w2 : WfWorld) (X : aset) (σ1 σ2 : Store) :
  X = world_dom (w1 : World) ∩ world_dom (w2 : World) →
  world_compat w1 w2 →
  w1 σ1 →
  w2 σ2 →
  store_restrict σ1 X = store_restrict σ2 X.
Proof. apply worldA_compat_store_restrict_overlap. Qed.

Lemma raw_fiber_commute (m : World) (σ1 σ2 : Store) :
  raw_fiber (raw_fiber m σ1) σ2 =
  raw_fiber (raw_fiber m σ2) σ1.
Proof. apply rawA_fiber_commute. Qed.

Lemma raw_le_dom (m1 m2 : World) :
  raw_le m1 m2 →
  world_dom m1 ⊆ world_dom m2.
Proof. apply rawA_le_dom. Qed.

Lemma raw_le_refl (m : World) : wf_world m → raw_le m m.
Proof. apply rawA_le_refl. Qed.

Lemma raw_le_antisym (m1 m2 : World) :
  wf_world m1 → wf_world m2 → raw_le m1 m2 → raw_le m2 m1 → m1 = m2.
Proof. apply rawA_le_antisym. Qed.

Lemma raw_le_trans (m1 m2 m3 : World) :
  raw_le m1 m2 → raw_le m2 m3 → raw_le m1 m3.
Proof. apply rawA_le_trans. Qed.

Lemma res_restrict_lift_store
    (w : WfWorld) (X : aset) (σ : Store) :
  (res_restrict w X : World) σ →
  ∃ σw, (w : World) σw ∧ store_restrict σw X = σ.
Proof. apply resA_restrict_lift_store. Qed.

Lemma res_restrict_eq_lift_store
    (w wX : WfWorld) (X : aset) (σ : Store) :
  res_restrict w X = wX →
  (wX : World) σ →
  ∃ σw, (w : World) σw ∧ store_restrict σw X = σ.
Proof. apply resA_restrict_eq_lift_store. Qed.

Lemma res_fiber_commute (w : WfWorld) (σ1 σ2 : Store)
    H1 H2 H1' H2' :
  res_fiber (res_fiber w σ1 H1) σ2 H2 =
  res_fiber (res_fiber w σ2 H1') σ1 H2'.
Proof. apply resA_fiber_commute. Qed.

Lemma res_fiber_from_projection_member
    (w wfib : WfWorld) (X : aset) (σ σw : Store) :
  res_fiber_from_projection w X σ wfib →
  (w : World) σw →
  store_restrict σw X = σ →
  (wfib : World) σw.
Proof. apply resA_fiber_from_projection_member. Qed.

Lemma res_projection_from_fiber_projection
    (w wfib : WfWorld) (X Y : aset) (σX σY : Store) :
  res_fiber_from_projection w X σX wfib →
  (res_restrict wfib Y : World) σY →
  (res_restrict w Y : World) σY.
Proof. apply resA_projection_from_fiber_projection. Qed.

Lemma res_projection_into_other_fiber
    (w wfibX wfibY : WfWorld) (X Y : aset) (σX σY : Store) :
  res_fiber_from_projection w X σX wfibX →
  res_fiber_from_projection w Y σY wfibY →
  (res_restrict wfibX Y : World) σY →
  (res_restrict wfibY (dom σX) : World) σX.
Proof. apply resA_projection_into_other_fiber. Qed.

Lemma res_subset_refl (w : WfWorld) : res_subset w w.
Proof. apply resA_subset_refl. Qed.

Lemma res_subset_trans (w1 w2 w3 : WfWorld) :
  res_subset w1 w2 → res_subset w2 w3 → res_subset w1 w3.
Proof. apply resA_subset_trans. Qed.

Lemma res_subset_antisym (w1 w2 : WfWorld) :
  res_subset w1 w2 → res_subset w2 w1 → w1 = w2.
Proof. apply resA_subset_antisym. Qed.

Lemma res_subset_swap (x y : atom) (w1 w2 : WfWorld) :
  res_subset (res_swap x y w1) (res_swap x y w2) ↔ res_subset w1 w2.
Proof. apply resA_subset_swap. Qed.

Lemma res_subset_restrict_mono (w1 w2 : WfWorld) (X : aset) :
  res_subset w1 w2 →
  res_subset (res_restrict w1 X) (res_restrict w2 X).
Proof. apply resA_subset_restrict_mono. Qed.

Lemma res_sum_subset_l (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2) :
  res_subset w1 (res_sum w1 w2 Hdef).
Proof. apply resA_sum_subset_l. Qed.

Lemma res_sum_subset_r (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2) :
  res_subset w2 (res_sum w1 w2 Hdef).
Proof. apply resA_sum_subset_r. Qed.

Lemma raw_sum_le_mono (m1 m2 m1' m2' : World) :
  raw_sum_defined m1 m2 → raw_sum_defined m1' m2' →
  raw_le m1 m1' → raw_le m2 m2' →
  raw_le (raw_sum m1 m2) (raw_sum m1' m2').
Proof. apply rawA_sum_le_mono. Qed.

Lemma raw_compat_unit (m : World) : world_compat raw_unit m.
Proof. apply rawA_compat_unit. Qed.

Lemma raw_compat_unit_r (m : World) : world_compat m raw_unit.
Proof. apply rawA_compat_unit_r. Qed.

Lemma wf_singleton_world (σ : Store) : wf_world (singleton_world σ).
Proof. apply wf_singleton_worldA. Qed.

Lemma res_swap_singleton_world (x y : atom) (σ : Store) :
  (res_swap x y (exist _ (singleton_world σ) (wf_singleton_world σ)) : World) =
  singleton_world (store_swap x y σ).
Proof. apply resA_swap_singleton_world. Qed.

Lemma res_swap_singleton_wfworld (x y : atom) (σ : Store) :
  res_swap x y (exist _ (singleton_world σ) (wf_singleton_world σ)) =
  exist _ (singleton_world (store_swap x y σ))
    (wf_singleton_world (store_swap x y σ)).
Proof.
  apply wfworldA_ext. apply res_swap_singleton_world.
Qed.

Lemma res_restrict_fiber_from_projection_dom_singleton
    (w wfib : WfWorld) (X : aset) (σ : Store) :
  res_fiber_from_projection w X σ wfib →
  (res_restrict wfib (dom σ) : World) = singleton_world σ.
Proof. apply resA_restrict_fiber_from_projection_dom_singleton. Qed.

Lemma res_restrict_fiber_from_projection_eq_singleton
    (w wfib : WfWorld) (X : aset) (σ : Store) :
  res_fiber_from_projection w X σ wfib →
  dom σ = X →
  (res_restrict wfib X : World) = singleton_world σ.
Proof. apply resA_restrict_fiber_from_projection_eq_singleton. Qed.

Lemma raw_restrict_fiber_from_projection_eq_singleton
    (w : WfWorld) (X : aset) (σ : Store) :
  res_restrict w X σ →
  dom σ = X →
  raw_restrict (raw_fiber w σ) X = singleton_world σ.
Proof. apply rawA_restrict_fiber_from_projection_eq_singleton. Qed.

Lemma raw_slice_restrict_wf (n : WfWorld) (X : aset) (p : WfWorld) :
  res_subset p (res_restrict n X) →
  wf_world (raw_slice_restrict n X p).
Proof. apply rawA_slice_restrict_wf. Qed.

Lemma res_slice_restrict_subset
    (n : WfWorld) (X : aset) (p : WfWorld) Hsub :
  res_subset (res_slice_restrict n X p Hsub) n.
Proof. apply resA_slice_restrict_subset. Qed.

Lemma res_slice_restrict_restrict
    (n : WfWorld) (X : aset) (p : WfWorld) Hsub :
  res_restrict (res_slice_restrict n X p Hsub) X = p.
Proof. apply resA_slice_restrict_restrict. Qed.

Lemma raw_pullback_projection_wf (n p : WfWorld) :
  p ⊑ n →
  wf_world (raw_pullback_projection n p).
Proof. apply rawA_pullback_projection_wf. Qed.

End ResourceInterface.
