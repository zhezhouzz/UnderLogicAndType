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

(** ** Compatibility (Definition 1.2, extended) *)

Definition world_compat (m1 m2 : World) : Prop :=
  ∀ s1 s2, m1 s1 → m2 s2 → store_compat s1 s2.

(** ** Raw resource operations (Definition 1.3) — used internally by WfWorld ops *)

Definition res_unit : World := {|
  world_dom    := ∅;
  world_stores := λ s, s = ∅;
|}.

Definition res_product (m1 m2 : World) : World := {|
  world_dom    := world_dom m1 ∪ world_dom m2;
  world_stores := λ s, ∃ s1 s2,
      m1 s1 ∧ m2 s2 ∧ store_compat s1 s2 ∧ s = s1 ∪ s2;
|}.

Definition res_sum (m1 m2 : World) : World := {|
  world_dom    := world_dom m1;
  world_stores := λ s, m1 s ∨ m2 s;
|}.

Definition res_sum_defined (m1 m2 : World) : Prop :=
  world_dom m1 = world_dom m2.

Definition res_restrict (m : World) (X : gset Var) : World := {|
  world_dom    := world_dom m ∩ X;
  world_stores := λ s, ∃ s', m s' ∧ store_restrict s' X = s;
|}.

Definition fiber (m : World) (σ : StoreT) : World := {|
  world_dom    := world_dom m;
  world_stores := λ s, m s ∧ store_restrict s (dom σ) = σ;
|}.

(** ** Partial order on raw worlds (Definition 1.4)

    [res_le m1 m2] is simply the equation [m1 = res_restrict m2 (world_dom m1)].
    Well-formedness is NOT bundled here; it is the responsibility of [WfWorld]. *)

Definition res_le (m1 m2 : World) : Prop :=
  m1 = res_restrict m2 (world_dom m1).

Local Infix "≤ᵣ" := res_le (at level 70).

Lemma res_le_dom (m1 m2 : World) : m1 ≤ᵣ m2 → world_dom m1 ⊆ world_dom m2.
Proof.
  unfold res_le. intros Heq.
  assert (Hd : world_dom m1 = world_dom m2 ∩ world_dom m1).
  { pattern m1 at 1. rewrite Heq. simpl. reflexivity. }
  set_solver.
Qed.

Lemma res_le_refl (m : World) : wf_world m → m ≤ᵣ m.
Proof.
  intros [_ Hdom]. unfold res_le. apply world_ext.
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

Lemma res_le_antisym (m1 m2 : World) :
  wf_world m1 → wf_world m2 → m1 ≤ᵣ m2 → m2 ≤ᵣ m1 → m1 = m2.
Proof.
  intros Hwf1 Hwf2 H12 H21.
  pose proof (res_le_dom m1 m2 H12) as Hd12.
  pose proof (res_le_dom m2 m1 H21) as Hd21.
  assert (Hdeq : world_dom m1 = world_dom m2) by set_solver.
  apply world_ext; [exact Hdeq |].
  unfold res_le in H12, H21.
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

Lemma res_le_trans (m1 m2 m3 : World) :
  m1 ≤ᵣ m2 → m2 ≤ᵣ m3 → m1 ≤ᵣ m3.
Proof.
  intros H12 H23.
  pose proof (res_le_dom m1 m2 H12) as Hd12.
  pose proof (res_le_dom m2 m3 H23) as Hd23.
  unfold res_le in *.
  apply world_ext.
  - (* world_dom m1 = world_dom (res_restrict m3 (world_dom m1)) *)
    unfold res_restrict. simpl. set_solver.
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
      (* Need: m1 s.  Use H12 : m1 = res_restrict m2 (world_dom m1). *)
      rewrite H12. cbn.
      (* Witness: store_restrict s3 (world_dom m2) *)
      exists (store_restrict s3 (world_dom m2)).
      split.
      * (* Need: m2 (store_restrict s3 (world_dom m2)) *)
        enough (Hm2 : (res_restrict m3 (world_dom m2)) (store_restrict s3 (world_dom m2))).
        { rewrite <- H23 in Hm2. exact Hm2. }
        cbn. exists s3. exact (conj Hs3 eq_refl).
      * (* store_restrict (store_restrict s3 (world_dom m2)) (world_dom m1) = s *)
        rewrite store_restrict_restrict.
        assert (Heq : world_dom m2 ∩ world_dom m1 = world_dom m1) by set_solver.
        rewrite Heq. exact Hrestr.
Qed.

(** ** Well-formedness of operations *)

Lemma wf_res_unit : wf_world res_unit.
Proof.
  constructor.
  - exists ∅. simpl. reflexivity.
  - intros s Hs. simpl in Hs. subst. simpl. set_solver.
Qed.

Lemma wf_res_product (m1 m2 : World) :
  wf_world m1 → wf_world m2 → world_compat m1 m2 →
  wf_world (res_product m1 m2).
Proof.
  intros [Hne1 Hdom1] [Hne2 Hdom2] Hcomp.
  constructor.
  - destruct Hne1 as [s1 Hs1], Hne2 as [s2 Hs2].
    exists (s1 ∪ s2). simpl. exists s1, s2.
    exact (conj Hs1 (conj Hs2 (conj (Hcomp s1 s2 Hs1 Hs2) eq_refl))).
  - intros s Hs. simpl in Hs.
    destruct Hs as [s1 [s2 [Hs1 [Hs2 [Hc Heq]]]]]. subst.
    unfold res_product; simpl.
    rewrite <- (Hdom1 s1 Hs1), <- (Hdom2 s2 Hs2).
    exact (store_union_dom s1 s2 Hc).
Qed.

Lemma wf_res_sum (m1 m2 : World) :
  wf_world m1 → wf_world m2 → res_sum_defined m1 m2 →
  wf_world (res_sum m1 m2).
Proof.
  intros [Hne1 Hdom1] [_ Hdom2] Hdef.
  constructor.
  - destruct Hne1 as [s Hs]. exists s. simpl. left. exact Hs.
  - intros s Hs. simpl in Hs. destruct Hs as [Hs | Hs].
    + simpl. exact (Hdom1 s Hs).
    + simpl. rewrite (Hdom2 s Hs). symmetry. exact Hdef.
Qed.

Lemma wf_res_restrict (m : World) (X : gset Var) :
  wf_world m → (∃ s, m s) →
  wf_world (res_restrict m X).
Proof.
  intros [_ Hdom] [s Hs].
  constructor.
  - exists (store_restrict s X). simpl.
    exists s. exact (conj Hs eq_refl).
  - intros s' Hs'. simpl in Hs'.
    destruct Hs' as [t [Ht Heq]]. subst.
    unfold res_restrict; simpl.
    rewrite <- (Hdom t Ht).
    exact (store_restrict_dom t X).
Qed.

Lemma wf_fiber (m : World) (σ : StoreT) :
  wf_world m → (∃ s, m s ∧ store_restrict s (dom σ) = σ) →
  wf_world (fiber m σ).
Proof.
  intros [_ Hdom] [s [Hs Hrestr]].
  constructor.
  - exists s. simpl. split; [exact Hs | exact Hrestr].
  - intros s' [Hs' _]. simpl. exact (Hdom s' Hs').
Qed.

(** ** Raw order-monotonicity lemmas (used by ChoiceAlgebra instance) *)

Lemma res_product_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  res_product m1 m2 ≤ᵣ res_product m1' m2'.
Proof. Admitted.

Lemma res_sum_le_mono (m1 m2 m1' m2' : World) :
  res_sum_defined m1 m2 → res_sum_defined m1' m2' →
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  res_sum m1 m2 ≤ᵣ res_sum m1' m2'.
Proof. Admitted.

(** ** Compatibility lemmas *)

Lemma world_compat_unit (m : World) : world_compat res_unit m.
Proof.
  unfold world_compat, store_compat. simpl.
  intros s1 s2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv1. discriminate.
Qed.

Lemma world_compat_unit_r (m : World) : world_compat m res_unit.
Proof.
  unfold world_compat, store_compat. simpl.
  intros s1 s2 H1 H2 x v1 v2 Hv1 Hv2.
  subst. rewrite lookup_empty in Hv2. discriminate.
Qed.

(** ** Singleton world

    [singleton_world σ] is the world that contains exactly the store [σ].
    It appears in the semantics of [FInd] and in the independence lemmas. *)

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

(** ** WfWorld: the intended interface  (sigma type of well-formed worlds)

    All algebra operations and the partial order live here.  There are no
    separate [World]-level and [WfWorld]-level versions of the operations;
    the raw definitions above are only helpers. *)

Definition WfWorld : Type := { m : World | wf_world m }.

(** Coercion and wf-proof accessor. *)
Coercion wfw_world (w : WfWorld) : World := proj1_sig w.
Definition wfw_wf   (w : WfWorld) : wf_world (wfw_world w) := proj2_sig w.

(** *** Operations on WfWorld *)

Definition wfw_unit : WfWorld :=
  exist _ res_unit wf_res_unit.

Definition wfw_product (w1 w2 : WfWorld) (Hc : world_compat w1 w2) : WfWorld :=
  exist _ (res_product w1 w2)
    (wf_res_product w1 w2 (wfw_wf w1) (wfw_wf w2) Hc).

Definition wfw_sum (w1 w2 : WfWorld) (Hdef : res_sum_defined w1 w2) : WfWorld :=
  exist _ (res_sum w1 w2)
    (wf_res_sum w1 w2 (wfw_wf w1) (wfw_wf w2) Hdef).

Definition wfw_restrict (w : WfWorld) (X : gset Var)
    (Hne : ∃ s, (w : World) s) : WfWorld :=
  exist _ (res_restrict w X) (wf_res_restrict w X (wfw_wf w) Hne).

Definition wfw_fiber (w : WfWorld) (σ : StoreT)
    (Hne : ∃ s, (w : World) s ∧ store_restrict s (dom σ) = σ) : WfWorld :=
  exist _ (fiber w σ) (wf_fiber w σ (wfw_wf w) Hne).

(** *** Partial order on WfWorld

    [⊑] is the stdpp [SqSubsetEq] relation.  Together with [PreOrder] and
    [AntiSymm] it forms a genuine partial order — the stdpp convention for
    expressing this. *)

#[global] Instance wf_world_sqsubseteq : SqSubsetEq WfWorld :=
  fun w1 w2 => (w1 : World) ≤ᵣ (w2 : World).

#[global] Instance wf_world_preorder : PreOrder (sqsubseteq (A := WfWorld)).
Proof.
  constructor.
  - intros w. exact (res_le_refl w (wfw_wf w)).
  - intros w1 w2 w3 H12 H23. exact (res_le_trans w1 w2 w3 H12 H23).
Qed.

#[global] Instance wf_world_antisym : AntiSymm eq (sqsubseteq (A := WfWorld)).
Proof.
  intros [m1 H1] [m2 H2] H12 H21. simpl in *.
  assert (Heq : m1 = m2) by exact (res_le_antisym m1 m2 H1 H2 H12 H21).
  subst. f_equal. apply proof_irrelevance.
Qed.

(** *** Order properties on WfWorld *)

Lemma wfw_le_product_l (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w1 ⊑ wfw_product w1 w2 Hc.
Proof. Admitted.

Lemma wfw_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  wfw_product w1 w2 Hc ⊑ wfw_product w1' w2' Hc'.
Proof. Admitted.

Lemma wfw_sum_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hdef : res_sum_defined w1 w2) (Hdef' : res_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  wfw_sum w1 w2 Hdef ⊑ wfw_sum w1' w2' Hdef'.
Proof. Admitted.

(** *** Algebraic laws (stated on WfWorld) *)

Lemma wfw_product_comm (w1 w2 : WfWorld) (Hc : world_compat w1 w2)
    (Hc' : world_compat w2 w1) :
  ∀ s, wfw_product w1 w2 Hc s ↔ wfw_product w2 w1 Hc' s.
Proof. Admitted.

Lemma wfw_product_unit_r (w : WfWorld) :
  ∀ s, wfw_product w wfw_unit (world_compat_unit_r w) s ↔ (w : World) s.
Proof. Admitted.

Lemma wfw_sum_comm (w1 w2 : WfWorld) (Hdef : res_sum_defined w1 w2)
    (Hdef' : res_sum_defined w2 w1) :
  ∀ s, wfw_sum w1 w2 Hdef s ↔ wfw_sum w2 w1 Hdef' s.
Proof. intros s. unfold wfw_sum. simpl. tauto. Qed.

End Resource.

Infix "≤ᵣ" := res_le (at level 70).
