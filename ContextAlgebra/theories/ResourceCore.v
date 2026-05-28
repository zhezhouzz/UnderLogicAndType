From ContextBase Require Import Prelude LogicVarInterface.
From ContextStore Require Import Store.
From Stdlib Require Import Logic.PropExtensionality Logic.FunctionalExtensionality
  Logic.ProofIrrelevance.

(** * Abstract resources over a countable key *)

Section ResourceCoreA.

Context {K : Type} `{Countable K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).

Record WorldA := mk_worldA {
  worldA_dom    : gset K;
  worldA_stores : StoreAT → Prop;
}.

Coercion worldA_stores : WorldA >-> Funclass.

Record wf_worldA (m : WorldA) : Prop := {
  wfA_ne  : ∃ σ, m σ;
  wfA_dom : ∀ σ, m σ → dom σ = worldA_dom m;
}.

Definition WfWorldA : Type := { m : WorldA | wf_worldA m }.

Coercion raw_worldA (w : WfWorldA) : WorldA := proj1_sig w.
Definition worldA_wf (w : WfWorldA) : wf_worldA (raw_worldA w) := proj2_sig w.

Lemma worldA_ext (m1 m2 : WorldA) :
  worldA_dom m1 = worldA_dom m2 →
  (∀ σ, m1 σ ↔ m2 σ) →
  m1 = m2.
Proof.
  destruct m1, m2. simpl. intros -> Hstores.
  f_equal. apply functional_extensionality. intros σ.
  apply propositional_extensionality. exact (Hstores σ).
Qed.

Lemma wfworldA_ext (w1 w2 : WfWorldA) :
  (w1 : WorldA) = (w2 : WorldA) →
  w1 = w2.
Proof.
  destruct w1 as [m1 Hwf1], w2 as [m2 Hwf2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Lemma wfworldA_store_dom (w : WfWorldA) (σ : StoreAT) :
  w σ → dom σ = worldA_dom (w : WorldA).
Proof. apply (wfA_dom _ (worldA_wf w)). Qed.

Lemma wfworldA_store_dom_subset (w : WfWorldA) (σ : StoreAT) (X : gset K) :
  w σ →
  worldA_dom (w : WorldA) ⊆ X →
  dom σ ⊆ X.
Proof.
  intros Hσ HX. rewrite (wfworldA_store_dom w σ Hσ). exact HX.
Qed.

End ResourceCoreA.
