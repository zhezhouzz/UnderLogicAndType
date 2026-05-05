From ChoiceAlgebra Require Import Prelude.
From ChoicePrelude Require Import Store.
From Stdlib Require Import Logic.PropExtensionality Logic.FunctionalExtensionality
  Logic.ProofIrrelevance.

(** * Resources  (Definitions 1.2–1.5)

    Two-layer design:
    - [World]   : raw record (domain + store predicate); operations are total
    - [WfWorld] : sigma type [{m | wf_world m}]; the intended interface

    All algebra operations and the partial order are defined on [WfWorld].
    [World]-level helpers are kept local where possible. *)

Section Resource.

Context {V : Type} `{ValueSig V}.

(** ** Worlds *)

Local Notation StoreT := (gmap atom V) (only parsing).

Record World := mk_world {
  world_dom    : aset;
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

Lemma wfworld_ext (w1 w2 : WfWorld) :
  (w1 : World) = (w2 : World) →
  w1 = w2.
Proof.
  destruct w1 as [m1 Hwf1], w2 as [m2 Hwf2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Lemma wfworld_store_dom (w : WfWorld) (σ : StoreT) :
  w σ → dom σ = world_dom (w : World).
Proof. apply (wf_dom _ (world_wf w)). Qed.

Lemma wfworld_store_restrict_dom (w : WfWorld) (σ : StoreT) (X : aset) :
  w σ → dom (store_restrict σ X) = world_dom (w : World) ∩ X.
Proof.
  intros Hσ. rewrite store_restrict_dom.
  replace (world_dom (w : World) ∩ X) with (dom σ ∩ X)
    by (rewrite (wfworld_store_dom w σ Hσ); reflexivity).
  reflexivity.
Qed.

(** Small domain-normalization tactics for resource proofs.  They expose the
    canonical world-domain shape behind store-domain side conditions. *)
Ltac solve_disjoint_world_domains w1 σ1 Hσ1 w2 σ2 Hσ2 :=
  replace (dom σ1 ∩ dom σ2)
    with (world_dom (w1 : World) ∩ world_dom (w2 : World))
    by (rewrite (wfworld_store_dom w1 σ1 Hσ1);
        rewrite (wfworld_store_dom w2 σ2 Hσ2);
        reflexivity).

Ltac normalize_store_overlap H w1 σ1 Hσ1 w2 σ2 Hσ2 :=
  replace (dom σ1 ∩ dom σ2)
    with (world_dom (w1 : World) ∩ world_dom (w2 : World)) in H
    by (rewrite (wfworld_store_dom w1 σ1 Hσ1);
        rewrite (wfworld_store_dom w2 σ2 Hσ2);
        reflexivity).

Ltac normalize_restrict_domain_of w σ X Hσ :=
  replace (dom (store_restrict σ X))
    with (world_dom (w : World) ∩ X)
    by (symmetry; exact (wfworld_store_restrict_dom w σ X Hσ)).

(** ** Compatibility (Definition 1.2, extended) *)

Definition world_compat (m1 m2 : World) : Prop :=
  ∀ s1 s2, m1 s1 → m2 s2 → store_compat s1 s2.

Lemma disj_dom_world_compat (w1 w2 : WfWorld) :
  world_dom (w1 : World) ∩ world_dom (w2 : World) = ∅ →
  world_compat w1 w2.
Proof.
  intros Hdisj s1 s2 Hs1 Hs2.
  apply disj_dom_store_compat.
  solve_disjoint_world_domains w1 s1 Hs1 w2 s2 Hs2.
  hauto.
Qed.

Lemma world_compat_store_restrict_overlap
    (w1 w2 : WfWorld) (X : aset) (σ1 σ2 : StoreT) :
  X = world_dom (w1 : World) ∩ world_dom (w2 : World) →
  world_compat w1 w2 →
  w1 σ1 →
  w2 σ2 →
  store_restrict σ1 X = store_restrict σ2 X.
Proof.
  intros -> Hcompat Hσ1 Hσ2.
  pose proof (proj1 (store_compat_spec σ1 σ2)
    (Hcompat σ1 σ2 Hσ1 Hσ2)) as Hrestrict.
  normalize_store_overlap Hrestrict w1 σ1 Hσ1 w2 σ2 Hσ2.
  hauto.
Qed.

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

Definition raw_restrict (m : World) (X : aset) : World := {|
  world_dom    := world_dom m ∩ X;
  world_stores := λ s, ∃ s', m s' ∧ store_restrict s' X = s;
|}.

Definition raw_fiber (m : World) (σ : StoreT) : World := {|
  world_dom    := world_dom m;
  world_stores := λ s, m s ∧ store_restrict s (dom σ) = σ;
|}.

Definition raw_rename_atom (x y : atom) (m : World) : World := {|
  world_dom    := aset_rename x y (world_dom m);
  world_stores := λ s, ∃ s0, m s0 ∧ store_rename_atom x y s0 = s;
|}.

(** ** Internal partial order on raw worlds (Definition 1.4)

    [raw_le m1 m2] is simply the equation [m1 = raw_restrict m2 (world_dom m1)].
    Well-formedness is NOT bundled here; it is the responsibility of [WfWorld].
    This raw relation is used to implement the exported [⊑] relation below. *)

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

Definition res_restrict (w : WfWorld) (X : aset) : WfWorld.
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

Definition res_rename_atom (x y : atom) (w : WfWorld) : WfWorld.
Proof.
  refine (exist _ (raw_rename_atom x y w) _).
Admitted.

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

Definition res_fiber_from_projection (w : WfWorld) (X : aset) (σ : StoreT)
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

Lemma res_subset_refl (w : WfWorld) : res_subset w w.
Proof. split; [reflexivity | tauto]. Qed.

Lemma res_subset_trans (w1 w2 w3 : WfWorld) :
  res_subset w1 w2 → res_subset w2 w3 → res_subset w1 w3.
Proof.
  intros [Hdom12 Hin12] [Hdom23 Hin23].
  split; [congruence | intros σ Hσ; exact (Hin23 σ (Hin12 σ Hσ))].
Qed.

Lemma res_subset_antisym (w1 w2 : WfWorld) :
  res_subset w1 w2 → res_subset w2 w1 → w1 = w2.
Proof.
  intros [Hdom12 Hin12] [Hdom21 Hin21].
  destruct w1 as [m1 Hwf1], w2 as [m2 Hwf2]. simpl in *.
  assert (Heq : m1 = m2).
  { apply world_ext; [exact Hdom12 |].
    intros σ. split; [apply Hin12 | apply Hin21]. }
  subst. f_equal. apply proof_irrelevance.
Qed.

(** ** Raw order-monotonicity lemmas (used by ChoiceAlgebra instance) *)

Lemma raw_product_le_mono (m1 m2 m1' m2' : World) :
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  raw_product m1 m2 ≤ᵣ raw_product m1' m2'.
Proof. Admitted.

Lemma raw_sum_le_mono (m1 m2 m1' m2' : World) :
  raw_sum_defined m1 m2 → raw_sum_defined m1' m2' →
  m1 ≤ᵣ m1' → m2 ≤ᵣ m2' →
  raw_sum m1 m2 ≤ᵣ raw_sum m1' m2'.
Proof.
  intros Hdef Hdef' Hle1 Hle2.
  pose proof (raw_le_dom m1 m1' Hle1) as Hdom1.
  unfold raw_le in *.
  apply world_ext.
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

(** ** Compatibility lemmas *)

Lemma raw_compat_unit (m : World) : world_compat raw_unit m.
Proof.
  intros s1 s2 Hs1 Hs2. simpl in Hs1. subst.
  apply disj_dom_store_compat. set_solver.
Qed.

Lemma raw_compat_unit_r (m : World) : world_compat m raw_unit.
Proof.
  intros s1 s2 Hs1 Hs2. simpl in Hs2. subst.
  apply disj_dom_store_compat. set_solver.
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
    expressing this.  This is the order exported for clients of [Resource]. *)

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
Proof.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      destruct (wf_ne _ (world_wf w2)) as [σ2 Hσ2].
      exists (σ ∪ σ2). split.
      * exists σ, σ2. repeat split; eauto.
      * rewrite store_restrict_union by exact (Hc σ σ2 Hσ Hσ2).
        rewrite store_restrict_idemp.
        -- apply store_union_absorb_l.
           ++ apply store_compat_restrict_r. exact (Hc σ σ2 Hσ Hσ2).
           ++ rewrite store_restrict_dom.
              pose proof (wfworld_store_dom w1 σ Hσ) as Hdomσ.
              set_solver.
        -- pose proof (wfworld_store_dom w1 σ Hσ) as Hdomσ. set_solver.
    + intros [σ12 [Hσ12 Hrestrict]].
      destruct Hσ12 as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      rewrite store_restrict_union in Hrestrict by exact Hcompat.
      rewrite store_restrict_idemp in Hrestrict.
      * rewrite (store_union_absorb_l σ1 (store_restrict σ2 (world_dom w1))) in Hrestrict.
        -- subst. exact Hσ1.
        -- apply store_compat_restrict_r. exact Hcompat.
        -- rewrite store_restrict_dom.
           pose proof (wfworld_store_dom w1 σ1 Hσ1) as Hdomσ1.
           set_solver.
      * pose proof (wfworld_store_dom w1 σ1 Hσ1) as Hdomσ1. set_solver.
Qed.

Lemma res_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_product w1 w2 Hc ⊑ res_product w1' w2' Hc'.
Proof. Admitted.

Lemma res_sum_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hdef : raw_sum_defined w1 w2) (Hdef' : raw_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_sum w1 w2 Hdef ⊑ res_sum w1' w2' Hdef'.
Proof.
  intros Hle1 Hle2.
  exact (raw_sum_le_mono w1 w2 w1' w2' Hdef Hdef' Hle1 Hle2).
Qed.

(** *** Algebraic laws (stated on WfWorld) *)

Lemma res_product_comm (w1 w2 : WfWorld) (Hc : world_compat w1 w2)
    (Hc' : world_compat w2 w1) :
  ∀ s, res_product w1 w2 Hc s ↔ res_product w2 w1 Hc' s.
Proof.
  intros s. simpl. split.
  - intros (s1 & s2 & Hs1 & Hs2 & Hcompat & ->).
    exists s2, s1. split; [exact Hs2 |].
    split; [exact Hs1 |].
    split; [apply store_compat_sym; exact Hcompat |].
    apply store_union_comm. exact Hcompat.
  - intros (s2 & s1 & Hs2 & Hs1 & Hcompat & ->).
    exists s1, s2. split; [exact Hs1 |].
    split; [exact Hs2 |].
    split; [apply store_compat_sym; exact Hcompat |].
    apply store_union_comm. exact Hcompat.
Qed.

Lemma res_product_unit_r (w : WfWorld) :
  ∀ s, res_product w res_unit (raw_compat_unit_r w) s ↔ (w : World) s.
Proof.
  intros s. simpl. split.
  - intros (s1 & s2 & Hs1 & Hs2 & _ & ->).
    subst s2. rewrite map_union_empty. exact Hs1.
  - intros Hs.
    exists s, ∅. repeat split; eauto.
    + exact (raw_compat_unit_r (w : World) s ∅ Hs eq_refl).
    + rewrite map_union_empty. reflexivity.
Qed.

Lemma res_product_unit_r_eq (w : WfWorld) :
  res_product w res_unit (raw_compat_unit_r w) = w.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - apply res_product_unit_r.
Qed.

Lemma res_product_unit_r_eq_any (w : WfWorld) (Hc : world_compat w res_unit) :
  res_product w res_unit Hc = w.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros s. simpl. split.
    + intros (s1 & s2 & Hs1 & Hs2 & _ & ->).
      subst s2. rewrite map_union_empty. exact Hs1.
    + intros Hs.
      exists s, ∅. repeat split; eauto.
      * exact (Hc s ∅ Hs eq_refl).
      * rewrite map_union_empty. reflexivity.
Qed.

Lemma res_sum_comm (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2)
    (Hdef' : raw_sum_defined w2 w1) :
  ∀ s, res_sum w1 w2 Hdef s ↔ res_sum w2 w1 Hdef' s.
Proof. intros s. unfold res_sum. simpl. tauto. Qed.

Lemma res_product_comm_eq (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  ∃ Hc' : world_compat w2 w1,
    res_product w1 w2 Hc = res_product w2 w1 Hc'.
Proof.
  exists (fun s1 s2 Hs1 Hs2 => store_compat_sym _ _ (Hc s2 s1 Hs2 Hs1)).
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - apply res_product_comm.
Qed.

Lemma res_sum_comm_eq (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2) :
  ∃ Hdef' : raw_sum_defined w2 w1,
    res_sum w1 w2 Hdef = res_sum w2 w1 Hdef'.
Proof.
  exists (eq_sym Hdef).
  apply wfworld_ext. apply world_ext.
  - simpl. exact Hdef.
  - apply res_sum_comm.
Qed.

Lemma res_product_assoc_eq (w1 w2 w3 : WfWorld)
    (H12 : world_compat w1 w2)
    (H123 : world_compat (res_product w1 w2 H12) w3) :
  ∃ (H23 : world_compat w2 w3)
    (H1_23 : world_compat w1 (res_product w2 w3 H23)),
    res_product (res_product w1 w2 H12) w3 H123 =
    res_product w1 (res_product w2 w3 H23) H1_23.
Proof.
  assert (H23 : world_compat w2 w3).
  { intros s2 s3 Hs2 Hs3.
    destruct (wf_ne _ (world_wf w1)) as [s1 Hs1].
    pose proof (H12 s1 s2 Hs1 Hs2) as Hc12.
    assert (Hprod : res_product w1 w2 H12 (s1 ∪ s2)).
    { simpl. exists s1, s2. repeat split; eauto. }
    eapply store_compat_union_inv_r; [exact Hc12 |].
    exact (H123 (s1 ∪ s2) s3 Hprod Hs3). }
  assert (H1_23 : world_compat w1 (res_product w2 w3 H23)).
  { intros s1 s23 Hs1 Hs23.
    simpl in Hs23.
    destruct Hs23 as [s2 [s3 [Hs2 [Hs3 [Hc23 ->]]]]].
    apply store_compat_union_intro_r.
    - exact (H12 s1 s2 Hs1 Hs2).
    - assert (Hprod : res_product w1 w2 H12 (s1 ∪ s2)).
      { simpl. exists s1, s2. repeat split; eauto. }
      eapply store_compat_union_inv_l.
      exact (H123 (s1 ∪ s2) s3 Hprod Hs3). }
  exists H23, H1_23.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros (s12 & s3 & Hs12 & Hs3 & Hc123 & ->).
      simpl in Hs12.
      destruct Hs12 as [s1 [s2 [Hs1 [Hs2 [Hc12 ->]]]]].
      exists s1, (s2 ∪ s3). split; [exact Hs1 |].
      split.
      * exists s2, s3. split; [exact Hs2 |].
        split; [exact Hs3 |].
        split; [exact (H23 s2 s3 Hs2 Hs3) | reflexivity].
      * split.
        -- assert (Hprod23 : res_product w2 w3 H23 (s2 ∪ s3)).
           { simpl. exists s2, s3. split; [exact Hs2 |].
             split; [exact Hs3 |].
             split; [exact (H23 s2 s3 Hs2 Hs3) | reflexivity]. }
           exact (H1_23 s1 (s2 ∪ s3) Hs1 Hprod23).
        -- exact (eq_sym (assoc_L (∪) s1 s2 s3)).
    + intros (s1 & s23 & Hs1 & Hs23 & Hc1_23 & ->).
      simpl in Hs23.
      destruct Hs23 as [s2 [s3 [Hs2 [Hs3 [Hc23 ->]]]]].
      exists (s1 ∪ s2), s3.
      split.
      * simpl. exists s1, s2. repeat split; eauto.
      * split; [exact Hs3 |].
        split.
        -- assert (Hprod12 : res_product w1 w2 H12 (s1 ∪ s2)).
           { simpl. exists s1, s2. repeat split; eauto. }
           exact (H123 (s1 ∪ s2) s3 Hprod12 Hs3).
        -- exact (assoc_L (∪) s1 s2 s3).
Qed.

Lemma res_sum_assoc_eq (w1 w2 w3 : WfWorld)
    (H12 : raw_sum_defined w1 w2)
    (H123 : raw_sum_defined (res_sum w1 w2 H12) w3) :
  ∃ (H23 : raw_sum_defined w2 w3)
    (H1_23 : raw_sum_defined w1 (res_sum w2 w3 H23)),
    res_sum (res_sum w1 w2 H12) w3 H123 =
    res_sum w1 (res_sum w2 w3 H23) H1_23.
Proof.
  assert (H23 : raw_sum_defined w2 w3).
  { unfold raw_sum_defined in *. simpl in H123. congruence. }
  assert (H1_23 : raw_sum_defined w1 (res_sum w2 w3 H23)).
  { unfold raw_sum_defined in *. simpl. exact H12. }
  exists H23, H1_23.
  apply wfworld_ext. apply world_ext.
  - simpl. reflexivity.
  - intros σ. simpl. tauto.
Qed.

(** Compatibility can be characterized by the common projection of two
    well-formed worlds: over the overlapping domain, both worlds restrict to
    the same singleton world. *)
Lemma world_compat_spec (w1 w2 : WfWorld) :
  let X := world_dom (w1 : World) ∩ world_dom (w2 : World) in
  world_compat w1 w2 ↔
    exists σ,
      raw_restrict w1 X = singleton_world σ ∧
      raw_restrict w2 X = singleton_world σ.
Proof.
  set (X := world_dom (w1 : World) ∩ world_dom (w2 : World)).
  split.
  - intros Hcompat.
    destruct (wf_ne _ (world_wf w1)) as [σ1 Hσ1].
    destruct (wf_ne _ (world_wf w2)) as [σ2 Hσ2].
    exists (store_restrict σ1 X). split.
    + apply world_ext.
      * simpl. normalize_restrict_domain_of w1 σ1 X Hσ1.
        reflexivity.
      * intros σ. simpl. split.
        -- intros [σ' [Hσ' Hrestr]]. subst σ.
           pose proof (world_compat_store_restrict_overlap
             w1 w2 X σ' σ2 eq_refl Hcompat Hσ' Hσ2) as Hσ'2.
           pose proof (world_compat_store_restrict_overlap
             w1 w2 X σ1 σ2 eq_refl Hcompat Hσ1 Hσ2) as Hσ12.
           etrans; [exact Hσ'2 | symmetry; exact Hσ12].
        -- intros ->. exists σ1. split; [exact Hσ1 | reflexivity].
    + apply world_ext.
      * simpl. normalize_restrict_domain_of w1 σ1 X Hσ1.
        unfold X. set_solver.
      * intros σ. simpl. split.
        -- intros [σ' [Hσ' Hrestr]]. subst σ.
           pose proof (world_compat_store_restrict_overlap
             w1 w2 X σ1 σ' eq_refl Hcompat Hσ1 Hσ') as Hσ1'.
           symmetry. exact Hσ1'.
        -- intros ->. exists σ2. split; [exact Hσ2 |].
           pose proof (world_compat_store_restrict_overlap
             w1 w2 X σ1 σ2 eq_refl Hcompat Hσ1 Hσ2) as Hσ12.
           symmetry. exact Hσ12.
  - intros [σ [Hw1 Hw2]] σ1 σ2 Hσ1 Hσ2.
    apply (proj2 (store_compat_spec σ1 σ2)).
    assert (H1 : store_restrict σ1 X = σ).
    { assert (Hraw : raw_restrict w1 X (store_restrict σ1 X)).
      { exists σ1. split; [exact Hσ1 | reflexivity]. }
      rewrite Hw1 in Hraw. simpl in Hraw. exact Hraw. }
    assert (H2 : store_restrict σ2 X = σ).
    { assert (Hraw : raw_restrict w2 X (store_restrict σ2 X)).
      { exists σ2. split; [exact Hσ2 | reflexivity]. }
      rewrite Hw2 in Hraw. simpl in Hraw. exact Hraw. }
    replace (dom σ1 ∩ dom σ2) with X.
    { rewrite H1, H2. reflexivity. }
    rewrite (wfworld_store_dom w1 σ1 Hσ1).
    rewrite (wfworld_store_dom w2 σ2 Hσ2).
    reflexivity.
Qed.

End Resource.

#[global] Instance stale_world {V : Type} `{ValueSig V} : Stale (World (V := V)) :=
  world_dom.
Arguments stale_world /.

#[global] Instance stale_wfworld {V : Type} `{ValueSig V} : Stale (WfWorld (V := V)) :=
  λ w, world_dom (w : World (V := V)).
Arguments stale_wfworld /.
