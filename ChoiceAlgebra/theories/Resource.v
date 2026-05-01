From ChoiceAlgebra Require Import Prelude Store.
From Stdlib Require Import Logic.PropExtensionality Logic.FunctionalExtensionality
  Logic.ProofIrrelevance.

(** * Resources  (Definitions 1.2–1.5)

    Two-layer design:
    - [World]   : raw record (domain + store predicate); operations are total
    - [WfWorld] : sigma type [{m | wf_world m}]; the intended interface

    All algebra operations and the partial order are defined on [WfWorld].
    [World]-level helpers are kept local where possible. *)

Section Resource.

Context `{Countable Var} `{EqDecision Value} `{Inhabited Value}.

Local Notation StoreT := (gmap Var Value) (only parsing).

(** ** Worlds *)

Record World := mk_world {
  world_dom    : gset Var;
  world_stores : StoreT → Prop;
}.

(** Coercion: treat a World as a predicate on stores. *)
Coercion world_stores : World >-> Funclass.

(** Extensionality: two worlds are equal iff same domain and same stores. *)
Lemma world_ext (m1 m2 : World) :
  world_dom m1 = world_dom m2 →
  (∀ s, m1 s ↔ m2 s) →
  m1 = m2.
Proof.
  destruct m1, m2. simpl. intros -> Hstores.
  f_equal. apply functional_extensionality. intros s.
  apply propositional_extensionality. exact (Hstores s).
Qed.

(** ** Well-formedness (Definition 1.2) *)

Record wf_world (m : World) : Prop := {
  wf_ne  : ∃ s, m s;
  wf_dom : ∀ s, m s → dom s = world_dom m;
}.

Definition WfWorld : Type := { m : World | wf_world m }.

(** Coercion and wf-proof accessor. *)
Coercion raw_world (w : WfWorld) : World := proj1_sig w.
Definition world_wf (w : WfWorld) : wf_world (raw_world w) := proj2_sig w.

(** ** Compatibility (Definition 1.2, extended) *)

Definition world_compat (m1 m2 : World) : Prop :=
  ∀ s1 s2, m1 s1 → m2 s2 → store_compat s1 s2.

(** ** Raw resource operations (Definition 1.3) — used internally by WfWorld ops *)

Definition raw_unit : World := {|
  world_dom    := ∅;
  world_stores := λ s, s = ∅;
|}.

Definition raw_product (m1 m2 : World) : World := {|
  world_dom    := world_dom m1 ∪ world_dom m2;
  world_stores := λ s, ∃ s1 s2,
      m1 s1 ∧ m2 s2 ∧ store_compat s1 s2 ∧ s = s1 ∪ s2;
|}.

Definition raw_sum (m1 m2 : World) : World := {|
  world_dom    := world_dom m1;
  world_stores := λ s, m1 s ∨ m2 s;
|}.

Definition raw_sum_defined (m1 m2 : World) : Prop :=
  world_dom m1 = world_dom m2.

Definition raw_restrict (m : World) (X : gset Var) : World := {|
  world_dom    := world_dom m ∩ X;
  world_stores := λ s, ∃ s', m s' ∧ store_restrict s' X = s;
|}.

Definition raw_fiber (m : World) (σ : StoreT) : World := {|
  world_dom    := world_dom m;
  world_stores := λ s, m s ∧ store_restrict s (dom σ) = σ;
|}.

(** ** Partial order on raw worlds (Definition 1.4)

    [raw_le m1 m2] is simply the equation [m1 = raw_restrict m2 (world_dom m1)].
    Well-formedness is NOT bundled here; it is the responsibility of [WfWorld]. *)

Definition raw_le (m1 m2 : World) : Prop :=
  m1 = raw_restrict m2 (world_dom m1).

Local Infix "≤ᵣ" := raw_le (at level 70).

Lemma raw_le_dom (m1 m2 : World) : m1 ≤ᵣ m2 → world_dom m1 ⊆ world_dom m2.
Proof.
  unfold raw_le. intros Heq.
  assert (Hd : world_dom m1 = world_dom m2 ∩ world_dom m1).
  { pattern m1 at 1. rewrite Heq. simpl. reflexivity. }
  set_solver.
Qed.

Lemma raw_le_refl (m : World) : wf_world m → m ≤ᵣ m.
Proof.
  intros [_ Hdom]. unfold raw_le. apply world_ext.
  - simpl. set_solver.
  - intros s. simpl. split.
    + intros Hs.
      pose proof (Hdom s Hs) as Hd. exists s. split; [exact Hs |].
      apply store_restrict_idemp. set_solver.
    + intros (s' & Hs' & Heq).
      pose proof (Hdom s' Hs') as Hd.
      assert (Hstep : store_restrict s' (world_dom m) = s')
        by (apply store_restrict_idemp; set_solver).
      rewrite Hstep in Heq. subst. exact Hs'.
Qed.

Lemma raw_le_antisym (m1 m2 : World) :
  wf_world m1 → wf_world m2 → m1 ≤ᵣ m2 → m2 ≤ᵣ m1 → m1 = m2.
Proof.
  intros Hwf1 Hwf2 H12 H21.
  pose proof (raw_le_dom m1 m2 H12) as Hd12.
  pose proof (raw_le_dom m2 m1 H21) as Hd21.
  assert (Hdeq : world_dom m1 = world_dom m2) by set_solver.
  apply world_ext; [exact Hdeq |].
  unfold raw_le in H12, H21.
  intros s. split.
  - intros Hs1.
    rewrite H12 in Hs1. cbn in Hs1.
    destruct Hs1 as [s' [Hs2 Hrestr]].
    pose proof (wf_dom _ Hwf2 s' Hs2) as Hd2.
    rewrite Hdeq in Hrestr.
    rewrite store_restrict_idemp in Hrestr by set_solver.
    subst. exact Hs2.
  - intros Hs2.
    rewrite H21 in Hs2. cbn in Hs2.
    destruct Hs2 as [s' [Hs1 Hrestr]].
    pose proof (wf_dom _ Hwf1 s' Hs1) as Hd1.
    rewrite <- Hdeq in Hrestr.
    rewrite store_restrict_idemp in Hrestr by set_solver.
    subst. exact Hs1.
Qed.

Lemma raw_le_trans (m1 m2 m3 : World) :
  m1 ≤ᵣ m2 → m2 ≤ᵣ m3 → m1 ≤ᵣ m3.
Proof.
  intros H12 H23.
  pose proof (raw_le_dom m1 m2 H12) as Hd12.
  pose proof (raw_le_dom m2 m3 H23) as Hd23.
  unfold raw_le in *.
  apply world_ext.
  - (* world_dom m1 = world_dom (raw_restrict m3 (world_dom m1)) *)
    unfold raw_restrict. simpl. set_solver.
  - intros s. split.
    + intros Hs1.
      rewrite H12 in Hs1. cbn in Hs1.
      destruct Hs1 as [s2 [Hs2 Hrestr12]].
      rewrite H23 in Hs2. cbn in Hs2.
      destruct Hs2 as [s3 [Hs3 Hrestr23]].
      cbn. exists s3. split; [exact Hs3 |].
      rewrite <- Hrestr12, <- Hrestr23, store_restrict_restrict.
      f_equal. set_solver.
    + intros Hs1.
      cbn in Hs1.
      destruct Hs1 as [s3 [Hs3 Hrestr]].
      (* Need: m1 s.  Use H12 : m1 = raw_restrict m2 (world_dom m1). *)
      rewrite H12. cbn.
      (* Witness: store_restrict s3 (world_dom m2) *)
      exists (store_restrict s3 (world_dom m2)).
      split.
      * (* Need: m2 (store_restrict s3 (world_dom m2)) *)
        enough (Hm2 : (raw_restrict m3 (world_dom m2)) (store_restrict s3 (world_dom m2))).
        { rewrite <- H23 in Hm2. exact Hm2. }
        cbn. exists s3. exact (conj Hs3 eq_refl).
      * (* store_restrict (store_restrict s3 (world_dom m2)) (world_dom m1) = s *)
        rewrite store_restrict_restrict.
        assert (Heq : world_dom m2 ∩ world_dom m1 = world_dom m1) by set_solver.
        rewrite Heq. exact Hrestr.
Qed.

(** ** Operations on WfWorld *)

Definition res_unit : WfWorld.
Proof.
  refine (exist _ raw_unit _).
  constructor.
  - exists ∅. simpl. reflexivity.
  - intros s Hs. simpl in Hs. subst. simpl. set_solver.
Defined.

Definition res_product (w1 w2 : WfWorld) (Hc : world_compat w1 w2) : WfWorld.
Proof.
  refine (exist _ (raw_product w1 w2) _).
  destruct (world_wf w1) as [Hne1 Hdom1].
  destruct (world_wf w2) as [Hne2 Hdom2].
  constructor.
  - destruct Hne1 as [s1 Hs1], Hne2 as [s2 Hs2].
    exists (s1 ∪ s2). simpl. exists s1, s2.
    exact (conj Hs1 (conj Hs2 (conj (Hc s1 s2 Hs1 Hs2) eq_refl))).
  - intros s Hs. simpl in Hs.
    destruct Hs as [s1 [s2 [Hs1 [Hs2 [Hcompat Heq]]]]]. subst.
    unfold raw_product; simpl.
    rewrite <- (Hdom1 s1 Hs1), <- (Hdom2 s2 Hs2).
    exact (store_union_dom s1 s2 Hcompat).
Defined.

Definition res_sum (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2) : WfWorld.
Proof.
  refine (exist _ (raw_sum w1 w2) _).
  destruct (world_wf w1) as [Hne1 Hdom1].
  destruct (world_wf w2) as [_ Hdom2].
  constructor.
  - destruct Hne1 as [s Hs]. exists s. simpl. left. exact Hs.
  - intros s Hs. simpl in Hs. destruct Hs as [Hs | Hs].
    + simpl. exact (Hdom1 s Hs).
    + simpl. rewrite (Hdom2 s Hs). symmetry. exact Hdef.
Defined.

Definition res_restrict (w : WfWorld) (X : gset Var) : WfWorld.
Proof.
  refine (exist _ (raw_restrict w X) _).
  destruct (world_wf w) as [Hne Hdom].
  constructor.
  - destruct Hne as [s Hs].
    exists (store_restrict s X). simpl.
    exists s. exact (conj Hs eq_refl).
  - intros s' Hs'. simpl in Hs'.
    destruct Hs' as [t [Ht Heq]]. subst.
    unfold raw_restrict; simpl.
    rewrite <- (Hdom t Ht).
    exact (store_restrict_dom t X).
Defined.

Definition res_fiber (w : WfWorld) (σ : StoreT)
    (Hne : ∃ s, (w : World) s ∧ store_restrict s (dom σ) = σ) : WfWorld.
Proof.
  refine (exist _ (raw_fiber w σ) _).
  destruct (world_wf w) as [_ Hdom].
  constructor.
  - destruct Hne as [s [Hs Hrestr]].
    exists s. simpl. split; [exact Hs | exact Hrestr].
  - intros s' [Hs' _]. simpl. exact (Hdom s' Hs').
Defined.

Definition res_fiber_from_projection (w : WfWorld) (X : gset Var) (σ : StoreT)
    (Hproj : res_restrict w X σ) : WfWorld.
Proof.
  refine (res_fiber w σ _).
  simpl in Hproj.
  destruct Hproj as [s [Hs Hrestr]].
  exists s. split; [exact Hs |].
  assert (Hdomσ : dom σ ⊆ X).
  { rewrite <- Hrestr. rewrite store_restrict_dom. set_solver. }
  rewrite <- (store_restrict_idemp σ (dom σ)) at 2 by set_solver.
  rewrite <- Hrestr.
  rewrite store_restrict_restrict.
  replace (X ∩ dom (store_restrict s X)) with (dom (store_restrict s X)).
  reflexivity.
  rewrite store_restrict_dom. set_solver.
Defined.

(** Same-domain subset relation on well-formed worlds.

    This is the extensional inclusion relation used by approximation
    modalities.  Unlike [⊑], it does not restrict or enlarge the domain:
    [res_subset w1 w2] only compares worlds with the same domain. *)
Definition res_subset (w1 w2 : WfWorld) : Prop :=
  world_dom w1 = world_dom w2 ∧ ∀ σ, w1 σ → w2 σ.

(** Total WfWorld operations for algebraic structures that encode partiality
    with separate definedness predicates.  Their wf obligations are meaningful
    only under the corresponding definedness assumptions, so we keep them
    abstract at this layer. *)

Program Definition res_product_total (w1 w2 : WfWorld) : WfWorld :=
  exist _ (raw_product w1 w2) _.
Next Obligation. Admitted.

Program Definition res_sum_total (w1 w2 : WfWorld) : WfWorld :=
  exist _ (raw_sum w1 w2) _.
Next Obligation. Admitted.

(** ** Raw order-monotonicity lemmas (used by ChoiceAlgebra instance) *)

Lemma raw_product_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  raw_product m1 m2 ≤ᵣ raw_product m1' m2'.
Proof. Admitted.

Lemma raw_sum_le_mono (m1 m2 m1' m2' : World) :
  raw_sum_defined m1 m2 → raw_sum_defined m1' m2' →
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  raw_sum m1 m2 ≤ᵣ raw_sum m1' m2'.
Proof. Admitted.

(** ** Compatibility lemmas *)

Lemma raw_compat_unit (m : World) : world_compat raw_unit m.
Proof.
  unfold world_compat, store_compat. simpl.
  intros s1 s2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv1. discriminate.
Qed.

Lemma raw_compat_unit_r (m : World) : world_compat m raw_unit.
Proof.
  unfold world_compat, store_compat. simpl.
  intros s1 s2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv2. discriminate.
Qed.

(** ** Singleton world

    [singleton_world σ] is the world that contains exactly the store [σ]. *)

Definition singleton_world (σ : StoreT) : World := {|
  world_dom    := dom σ;
  world_stores := λ s, s = σ;
|}.

Lemma wf_singleton_world (σ : StoreT) : wf_world (singleton_world σ).
Proof.
  constructor.
  - exists σ. exact eq_refl.
  - intros s Hs. simpl in Hs. subst. reflexivity.
Qed.

(** *** Partial order on WfWorld

    [⊑] is the stdpp [SqSubsetEq] relation.  Together with [PreOrder] and
    [AntiSymm] it forms a genuine partial order — the stdpp convention for
    expressing this. *)

#[global] Instance wf_world_sqsubseteq : SqSubsetEq WfWorld :=
  fun w1 w2 => (w1 : World) ≤ᵣ (w2 : World).

#[global] Instance wf_world_preorder : PreOrder (sqsubseteq (A := WfWorld)).
Proof.
  constructor.
  - intros w. exact (raw_le_refl w (world_wf w)).
  - intros w1 w2 w3 H12 H23. exact (raw_le_trans w1 w2 w3 H12 H23).
Qed.

#[global] Instance wf_world_antisym : AntiSymm eq (sqsubseteq (A := WfWorld)).
Proof.
  intros [m1 H1] [m2 H2] H12 H21. simpl in *.
  assert (Heq : m1 = m2) by exact (raw_le_antisym m1 m2 H1 H2 H12 H21).
  subst. f_equal. apply proof_irrelevance.
Qed.

(** *** Order properties on WfWorld *)

Lemma res_le_product_l (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w1 ⊑ res_product w1 w2 Hc.
Proof. Admitted.

Lemma res_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_product w1 w2 Hc ⊑ res_product w1' w2' Hc'.
Proof. Admitted.

Lemma res_sum_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hdef : raw_sum_defined w1 w2) (Hdef' : raw_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_sum w1 w2 Hdef ⊑ res_sum w1' w2' Hdef'.
Proof. Admitted.

(** *** Algebraic laws (stated on WfWorld) *)

Lemma res_product_comm (w1 w2 : WfWorld) (Hc : world_compat w1 w2)
    (Hc' : world_compat w2 w1) :
  ∀ s, res_product w1 w2 Hc s ↔ res_product w2 w1 Hc' s.
Proof. Admitted.

Lemma res_product_unit_r (w : WfWorld) :
  ∀ s, res_product w res_unit (raw_compat_unit_r w) s ↔ (w : World) s.
Proof. Admitted.

Lemma res_sum_comm (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2)
    (Hdef' : raw_sum_defined w2 w1) :
  ∀ s, res_sum w1 w2 Hdef s ↔ res_sum w2 w1 Hdef' s.
Proof. intros s. unfold res_sum. simpl. tauto. Qed.

End Resource.

Infix "≤ᵣ" := raw_le (at level 70).

#[global] Instance stale_world {Value} : Stale (@World atom _ _ Value) :=
  world_dom.
Arguments stale_world /.

#[global] Instance stale_wfworld {Value} : Stale (@WfWorld atom _ _ Value) :=
  λ w, world_dom (w : @World atom _ _ Value).
Arguments stale_wfworld /.
