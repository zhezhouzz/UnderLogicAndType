From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From Stdlib Require Import Logic.PropExtensionality Logic.FunctionalExtensionality
  Logic.ProofIrrelevance.

(** * Abstract resources over a countable key *)

Section ResourceCoreA.

Context {K : Type} `{Countable K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).

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



(** ** Key actions lifted from stores to resources *)

Local Notation WorldAT := WorldA (only parsing).
Local Notation WfWorldAT := WfWorldA (only parsing).

Definition rawA_rekey (f : K → K) (m : WorldAT) : WorldAT := {|
  worldA_dom    := set_map f (worldA_dom m);
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ storeA_map_key f σ0 = σ;
|}.

Definition resA_rekey (f : K → K) (Hf : Inj (=) (=) f)
    (w : WfWorldAT) : WfWorldAT.
Proof.
  refine (exist _ (rawA_rekey f w) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (storeA_map_key f σ). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hrekey]].
    rewrite <- Hrekey.
    change (dom (storeA_map_key f σ0 : gmap K V) =
      set_map f (worldA_dom (w : WorldAT) : gset K)).
    rewrite storeA_rekey_dom by exact Hf.
    pose proof (Hdom σ0 Hσ0) as Hσdom.
    change (dom (σ0 : gmap K V) = worldA_dom (w : WorldAT)) in Hσdom.
    rewrite Hσdom. reflexivity.
Defined.

Definition rawA_swap (x y : K) (m : WorldAT) : WorldAT :=
  rawA_rekey (swap x y) m.

Definition resA_swap (x y : K) (w : WfWorldAT) : WfWorldAT :=
  resA_rekey (swap x y) (swap_inj x y) w.


Lemma resA_swap_conjugate a b x y (w : WfWorldAT) :
  resA_swap a b (resA_swap x y w) =
  resA_swap (swap a b x) (swap a b y) (resA_swap a b w).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. better_base_solver.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (storeA_swap a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply storeA_swap_conjugate.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (storeA_swap x y σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply storeA_swap_conjugate.
Qed.

Context `{!ShiftKey K}.

Definition rawA_shift (k : nat) (m : WorldAT) : WorldAT :=
  rawA_rekey (key_shift k) m.

Definition resA_shift (k : nat) (w : WfWorldAT) : WfWorldAT :=
  resA_rekey (key_shift k) (key_shift_inj k) w.

End ResourceCoreA.

Section ResourceOpenA.

Context {V : Type} `{ValueSig V}.

Definition rawA_open (k : nat) (x : atom)
    (m : @WorldA logic_var _ _ V) : @WorldA logic_var _ _ V :=
  rawA_swap (LVBound k) (LVFree x) m.

Definition resA_open (k : nat) (x : atom)
    (w : @WfWorldA logic_var _ _ V) : @WfWorldA logic_var _ _ V :=
  resA_swap (LVBound k) (LVFree x) w.

End ResourceOpenA.



(** * Restriction and fibers for abstract resources *)

Section ResourceRestrictA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Definition rawA_restrict (m : WorldAT) (X : gset K) : WorldAT := {|
  worldA_dom    := worldA_dom m ∩ X;
  worldA_stores := λ σ, ∃ σ0 : StoreAT,
    m σ0 ∧ storeA_restrict σ0 X = σ;
|}.

Definition resA_restrict (w : WfWorldAT) (X : gset K) : WfWorldAT.
Proof.
  refine (exist _ (rawA_restrict w X) _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (storeA_restrict σ X). exists σ. split; [exact Hσ | reflexivity].
  - intros σ [σ0 [Hσ0 Hrestrict]]. subst σ.
    rewrite storeA_restrict_dom.
    rewrite (Hdom σ0 Hσ0). reflexivity.
Defined.

Lemma resA_restrict_project_store
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) :
  (w : WorldAT) σ →
  (resA_restrict w X : WorldAT) (storeA_restrict σ X).
Proof.
  intros Hσ. exists σ. split; [exact Hσ | reflexivity].
Qed.

Lemma resA_restrict_eq_project_store
    (w wX : WfWorldAT) (X : gset K) (σ : StoreAT) :
  resA_restrict w X = wX →
  (w : WorldAT) σ →
  (wX : WorldAT) (storeA_restrict σ X).
Proof.
  intros <- Hσ. apply resA_restrict_project_store. exact Hσ.
Qed.

Definition rawA_fiber (m : WorldAT) (σ : StoreAT) : WorldAT := {|
  worldA_dom    := worldA_dom m;
  worldA_stores := λ σ0, m σ0 ∧ storeA_restrict σ0 (dom σ) = σ;
|}.

Lemma rawA_fiber_empty (m : WorldAT) :
  rawA_fiber m (∅ : StoreAT) = m.
Proof.
  apply worldA_ext; [reflexivity |].
  intros σ. simpl. split.
  - tauto.
  - intros Hσ. split; [exact Hσ |].
    apply storeA_restrict_empty_set.
Qed.

Definition resA_fiber (w : WfWorldAT) (σ : StoreAT)
    (Hne : ∃ σ0, (w : WorldAT) σ0 ∧ storeA_restrict σ0 (dom σ) = σ)
    : WfWorldAT.
Proof.
  refine (exist _ (rawA_fiber w σ) _).
  destruct (worldA_wf w) as [_ Hdom].
  split.
  - destruct Hne as [σ0 [Hσ0 Hrestrict]].
    exists σ0. split; [exact Hσ0 | exact Hrestrict].
  - intros σ0 [Hσ0 _]. exact (Hdom σ0 Hσ0).
Defined.

Definition resA_fiber_from_projection
    (w : WfWorldAT) (X : gset K) (σ : StoreAT) (wfib : WfWorldAT) : Prop :=
  (resA_restrict w X : WorldAT) σ ∧
  (wfib : WorldAT) = rawA_fiber w σ.

Definition resA_fiber_member (w : WfWorldAT) (X : gset K) (wfib : WfWorldAT) : Prop :=
  ∃ σ, resA_fiber_from_projection w X σ wfib.

Lemma resA_restrict_restrict_eq (w : WfWorldAT) (X Y : gset K) :
  resA_restrict (resA_restrict w X) Y =
  resA_restrict w (X ∩ Y).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σw [Hσw Hx]] Hy]]. subst σx σ.
      exists σw. split; [exact Hσw |].
      rewrite storeA_restrict_restrict. reflexivity.
    + intros [σw [Hσw Hxy]]. subst σ.
      exists (storeA_restrict σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite storeA_restrict_restrict. reflexivity.
Qed.

Context `{!ShiftKey K}.

End ResourceRestrictA.
