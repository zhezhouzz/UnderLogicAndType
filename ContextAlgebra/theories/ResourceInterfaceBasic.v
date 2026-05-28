(** * Concrete resource basic interface lemmas *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict ResourceAlgebraBase ResourceAlgebraOrder ResourceAlgebraPullback ResourceAlgebraSum ResourceAlgebraLaws ResourceExtensionCore ResourceExtensionEquiv ResourceExtensionDerived.
From ContextAlgebra Require Export ResourceInterfaceCore.
From Stdlib Require Import Logic.ProofIrrelevance.

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
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

Lemma wfworld_store_dom (w : WfWorld) (σ : StoreT) :
  w σ → dom σ = world_dom (w : World).
Proof. apply wfworldA_store_dom. Qed.

Lemma raw_le_dom (m1 m2 : World) :
  raw_le m1 m2 →
  world_dom m1 ⊆ world_dom m2.
Proof. apply rawA_le_dom. Qed.

Lemma res_subset_refl (w : WfWorld) : res_subset w w.
Proof. apply resA_subset_refl. Qed.

Lemma res_subset_trans (w1 w2 w3 : WfWorld) :
  res_subset w1 w2 → res_subset w2 w3 → res_subset w1 w3.
Proof. apply resA_subset_trans. Qed.

Lemma raw_compat_unit_r (m : World) : world_compat m raw_unit.
Proof. apply rawA_compat_unit_r. Qed.

Lemma wf_singleton_world (σ : StoreT) : wf_world (singleton_world σ).
Proof. apply wf_singleton_worldA. Qed.

End ResourceInterface.
