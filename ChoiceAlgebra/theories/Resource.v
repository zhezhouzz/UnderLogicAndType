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

Definition raw_swap (x y : atom) (m : World) : World := {|
  world_dom    := aset_swap x y (world_dom m);
  world_stores := λ s, ∃ s0, m s0 ∧ store_swap x y s0 = s;
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

Lemma res_restrict_lift_store
    (w : WfWorld) (X : aset) (σ : StoreT) :
  (res_restrict w X : World) σ →
  ∃ σw, (w : World) σw ∧ store_restrict σw X = σ.
Proof.
  intros Hσ. exact Hσ.
Qed.

Lemma res_restrict_eq_lift_store
    (w wX : WfWorld) (X : aset) (σ : StoreT) :
  res_restrict w X = wX →
  (wX : World) σ →
  ∃ σw, (w : World) σw ∧ store_restrict σw X = σ.
Proof.
  intros <- Hσ. exact Hσ.
Qed.

Definition res_rename_atom (x y : atom) (w : WfWorld) : WfWorld.
Proof.
  refine (exist _ (raw_rename_atom x y w) _).
  destruct (world_wf w) as [Hne Hdom].
  constructor.
  - destruct Hne as [σ Hσ].
    exists (store_rename_atom x y σ). simpl.
    exists σ. split; [exact Hσ | reflexivity].
  - intros σ' Hσ'. simpl in Hσ'.
    destruct Hσ' as [σ [Hσ Hrename]]. subst σ'.
    rewrite store_rename_atom_dom.
    change (aset_rename x y (dom σ) = aset_rename x y (world_dom (w : World))).
    rewrite (Hdom σ Hσ). reflexivity.
Defined.

Definition res_swap (x y : atom) (w : WfWorld) : WfWorld.
Proof.
  refine (exist _ (raw_swap x y w) _).
  destruct (world_wf w) as [Hne Hdom].
  constructor.
  - destruct Hne as [σ Hσ].
    exists (store_swap x y σ). simpl.
    exists σ. split; [exact Hσ | reflexivity].
  - intros σ' Hσ'. simpl in Hσ'.
    destruct Hσ' as [σ [Hσ Hswap]]. subst σ'.
    rewrite store_swap_dom.
    change (aset_swap x y (dom σ) = aset_swap x y (world_dom (w : World))).
    rewrite (Hdom σ Hσ). reflexivity.
Defined.

Lemma res_swap_involutive (x y : atom) (w : WfWorld) :
  res_swap x y (res_swap x y w) = w.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. apply aset_swap_involutive.
  - intros σ. simpl. split.
    + intros [σ1 [[σ0 [Hσ0 Hswap0]] Hswap1]]. subst σ1 σ.
      rewrite store_swap_involutive. exact Hσ0.
    + intros Hσ.
      exists (store_swap x y σ). split.
      * exists σ. split; [exact Hσ | reflexivity].
      * apply store_swap_involutive.
Qed.

Lemma res_swap_conjugate a b x y (w : WfWorld) :
  res_swap a b (res_swap x y w) =
  res_swap (atom_swap a b x) (atom_swap a b y) (res_swap a b w).
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. apply aset_swap_conjugate.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (store_swap a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply store_swap_conjugate.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (store_swap x y σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply store_swap_conjugate.
Qed.

Lemma res_swap_conjugate_inv a b x y (w : WfWorld) :
  res_swap x y (res_swap a b w) =
  res_swap a b (res_swap (atom_swap a b x) (atom_swap a b y) w).
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. apply aset_swap_conjugate_inv.
  - intros σ. simpl. split.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (store_swap (atom_swap a b x) (atom_swap a b y) σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * symmetry. apply store_swap_conjugate_inv.
    + intros [σ0 [[σ1 [Hσ1 Hswap1]] Hswap0]]. subst σ0 σ.
      exists (store_swap a b σ1). split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * apply store_swap_conjugate_inv.
Qed.

Lemma res_restrict_swap (x y : atom) (w : WfWorld) (X : aset) :
  res_restrict (res_swap x y w) (aset_swap x y X) =
  res_swap x y (res_restrict w X).
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. apply set_eq. intros z.
    rewrite elem_of_intersection, !elem_of_aset_swap, elem_of_intersection.
    reflexivity.
  - intros σ. simpl. split.
    + intros [σ0 [[σw [Hσw Hswap]] Hrestrict]]. subst σ0 σ.
      exists (store_restrict σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * symmetry. apply store_restrict_swap.
    + intros [σ0 [[σw [Hσw Hrestrict]] Hswap]]. subst σ0 σ.
      exists (store_swap x y σw). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * apply store_restrict_swap.
Qed.

Lemma res_restrict_swap_projection x y (w : WfWorld) (X : aset) (σ : StoreT) :
  res_restrict w X σ →
  res_restrict (res_swap x y w) (aset_swap x y X) (store_swap x y σ).
Proof.
  intros Hproj.
  change ((res_restrict (res_swap x y w) (aset_swap x y X) : World)
    (store_swap x y σ)).
  rewrite res_restrict_swap. simpl.
  exists σ. split; [exact Hproj | reflexivity].
Qed.

Lemma res_swap_extension_dom (x y : atom) (m my : WfWorld) (z : atom) :
  world_dom (my : World) = world_dom (m : World) ∪ {[z]} →
  world_dom (res_swap x y my : World) =
  world_dom (res_swap x y m : World) ∪ {[atom_swap x y z]}.
Proof.
  intros Hdom. simpl. rewrite Hdom, aset_swap_union, aset_swap_singleton.
  reflexivity.
Qed.

Lemma res_swap_extension_dom_cancel
    (x y : atom) (m my : WfWorld) (z : atom) :
  world_dom (my : World) = world_dom (res_swap x y m : World) ∪ {[z]} →
  world_dom (res_swap x y my : World) =
  world_dom (m : World) ∪ {[atom_swap x y z]}.
Proof.
  intros Hdom. simpl in Hdom |- *.
  rewrite Hdom, aset_swap_union, aset_swap_involutive, aset_swap_singleton.
  reflexivity.
Qed.

Lemma res_swap_restrict_extension
    (x y : atom) (m my : WfWorld) :
  res_restrict my (world_dom (m : World)) = m →
  res_restrict (res_swap x y my) (world_dom (res_swap x y m : World)) =
  res_swap x y m.
Proof.
  intros Hrestr.
  change (res_restrict (res_swap x y my)
    (aset_swap x y (world_dom (m : World))) = res_swap x y m).
  rewrite res_restrict_swap, Hrestr. reflexivity.
Qed.

Lemma res_swap_restrict_extension_cancel
    (x y : atom) (m my : WfWorld) :
  res_restrict my (world_dom (res_swap x y m : World)) = res_swap x y m →
  res_restrict (res_swap x y my) (world_dom (m : World)) = m.
Proof.
  intros Hrestr.
  change (res_restrict my (aset_swap x y (world_dom (m : World))) =
    res_swap x y m) in Hrestr.
  rewrite <- (aset_swap_involutive x y (world_dom (m : World))).
  rewrite res_restrict_swap, Hrestr, res_swap_involutive. reflexivity.
Qed.

Lemma res_restrict_rename_atom (x y : atom) (w : WfWorld) (X : aset) :
  res_restrict (res_rename_atom y x w) X =
  res_rename_atom y x (res_restrict w (aset_rename x y X)).
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl.
    change (aset_rename y x (world_dom (w : World)) ∩ X =
      aset_rename y x (world_dom (w : World) ∩ aset_rename x y X)).
    apply set_eq. intros z.
    rewrite elem_of_intersection, !elem_of_aset_rename.
    split.
    + intros [Hzren HzX].
      destruct Hzren as [[Hzx Hyw] | [Hzx [Hzy Hzw]]].
      * subst z. left. split; [reflexivity |].
        apply elem_of_intersection. split; [exact Hyw |].
        rewrite elem_of_aset_rename. left. split; [reflexivity | exact HzX].
      * right. repeat split; try congruence.
        apply elem_of_intersection. split; [exact Hzw |].
        rewrite elem_of_aset_rename. right. repeat split; try congruence; exact HzX.
    + intros Hzren.
      destruct Hzren as [[Hzx Hin] | [Hzx [Hzy Hin]]].
      * apply elem_of_intersection in Hin as [Hw HX].
        subst z.
        split.
        -- left. split; [reflexivity | exact Hw].
        -- rewrite elem_of_aset_rename in HX.
           destruct HX as [[_ HxX] | [Hyy [_ _]]]; [exact HxX | congruence].
      * apply elem_of_intersection in Hin as [Hw HX].
        split.
        -- right. repeat split; try congruence; exact Hw.
        -- rewrite elem_of_aset_rename in HX.
           destruct HX as [[Hzy' _] | [_ [_ HzX]]]; [congruence | exact HzX].
  - intros σ. split.
    + intros [σ0 [[σw [Hσw Hrename]] Hrestrict]]. subst σ0 σ.
      simpl. exists (store_restrict σw (aset_rename x y X)). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * symmetry. apply store_restrict_rename_atom.
    + intros [σ0 [[σw [Hσw Hrestrict]] Hrename]]. subst σ0 σ.
      simpl. exists (store_rename_atom y x σw). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * apply store_restrict_rename_atom.
Qed.

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

Lemma res_fiber_from_projection_member
    (w : WfWorld) (X : aset) (σ σw : StoreT)
    (Hproj : res_restrict w X σ) :
  (w : World) σw →
  store_restrict σw X = σ →
  (res_fiber_from_projection w X σ Hproj : World) σw.
Proof.
  intros Hσw Hrestrict. simpl. split; [exact Hσw |].
  rewrite <- Hrestrict.
  rewrite <- (store_restrict_idemp
    (store_restrict σw X) (dom (store_restrict σw X))) at 2 by set_solver.
  rewrite store_restrict_restrict.
  replace (X ∩ dom (store_restrict σw X)) with (dom (store_restrict σw X)).
  - reflexivity.
  - rewrite store_restrict_dom. set_solver.
Qed.

Lemma res_fiber_from_projection_proof_irrel
    (w : WfWorld) (X : aset) (σ : StoreT)
    (Hproj1 Hproj2 : res_restrict w X σ) :
  res_fiber_from_projection w X σ Hproj1 =
  res_fiber_from_projection w X σ Hproj2.
Proof.
  apply wfworld_ext. reflexivity.
Qed.

Lemma res_fiber_from_projection_swap_cancel
    (x y z : atom) (w : WfWorld) (σ : StoreT)
    (Hproj1 : res_restrict (res_swap x y w)
      (aset_swap x y {[atom_swap x y z]}) (store_swap x y (store_swap x y σ)))
    (Hproj2 : res_restrict (res_swap x y w) {[z]} σ) :
  res_fiber_from_projection (res_swap x y w)
    (aset_swap x y {[atom_swap x y z]})
    (store_swap x y (store_swap x y σ)) Hproj1 =
  res_fiber_from_projection (res_swap x y w) {[z]} σ Hproj2.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. try rewrite aset_swap_singleton; try rewrite atom_swap_involutive.
    reflexivity.
  - intros τ. simpl. try rewrite aset_swap_singleton; try rewrite atom_swap_involutive;
      try rewrite store_swap_involutive. reflexivity.
Qed.

Lemma res_fiber_from_projection_swap_singleton_cancel
    (x y z : atom) (w : WfWorld) (σ : StoreT)
    (Hproj1 : res_restrict (res_swap x y w)
      (aset_swap x y {[atom_swap x y z]}) σ)
    (Hproj2 : res_restrict (res_swap x y w) {[z]} σ) :
  res_fiber_from_projection (res_swap x y w)
    (aset_swap x y {[atom_swap x y z]}) σ Hproj1 =
  res_fiber_from_projection (res_swap x y w) {[z]} σ Hproj2.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. try rewrite aset_swap_singleton; try rewrite atom_swap_involutive.
    reflexivity.
  - intros τ. simpl. try rewrite aset_swap_singleton; try rewrite atom_swap_involutive.
    reflexivity.
Qed.

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

Lemma res_subset_swap (x y : atom) (w1 w2 : WfWorld) :
  res_subset (res_swap x y w1) (res_swap x y w2) ↔ res_subset w1 w2.
Proof.
  split.
  - intros [Hdom Hin]. split.
    + simpl in Hdom.
      rewrite <- (aset_swap_involutive x y (world_dom (w1 : World))).
      rewrite <- (aset_swap_involutive x y (world_dom (w2 : World))).
      by rewrite Hdom.
    + intros σ Hσ.
      pose proof (Hin (store_swap x y σ)) as Hin'.
      simpl in Hin'.
      assert (Hs1 : raw_swap x y w1 (store_swap x y σ)).
      { exists σ. split; [exact Hσ | reflexivity]. }
      destruct (Hin' Hs1) as [σ2 [Hσ2 Hswap]].
      assert (σ2 = σ).
      {
        rewrite <- (store_swap_involutive x y σ2).
        rewrite Hswap. apply store_swap_involutive.
      }
      subst. exact Hσ2.
  - intros [Hdom Hin]. split.
    + simpl. by rewrite Hdom.
    + intros σ Hσ.
      simpl in Hσ. destruct Hσ as [σ0 [Hσ0 Hswap]]. subst σ.
      exists σ0. split; [apply Hin; exact Hσ0 | reflexivity].
Qed.

Lemma res_subset_swap_intro (x y : atom) (w1 w2 : WfWorld) :
  res_subset w1 w2 →
  res_subset (res_swap x y w1) (res_swap x y w2).
Proof. apply (proj2 (res_subset_swap x y w1 w2)). Qed.

Lemma res_subset_swap_elim (x y : atom) (w1 w2 : WfWorld) :
  res_subset (res_swap x y w1) (res_swap x y w2) →
  res_subset w1 w2.
Proof. apply (proj1 (res_subset_swap x y w1 w2)). Qed.

(** ** Raw order-monotonicity lemmas (used by ChoiceAlgebra instance) *)

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

Lemma res_restrict_fiber_from_projection_dom_singleton
    (w : WfWorld) (X : aset) (σ : StoreT)
    (Hproj : res_restrict w X σ) :
  (res_restrict (res_fiber_from_projection w X σ Hproj) (dom σ) : World) =
  singleton_world σ.
Proof.
  simpl in Hproj.
  destruct Hproj as [σw [Hσw Hrestr]].
  pose proof (wfworld_store_dom w σw Hσw) as Hdomσw.
  assert (Hdomσ : dom σ = world_dom (w : World) ∩ X).
  { rewrite <- Hrestr. rewrite store_restrict_dom. set_solver. }
  apply world_ext.
  - simpl. rewrite Hdomσ. set_solver.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hτ0σ] Hτ]].
      rewrite Hτ0σ in Hτ. subst τ. reflexivity.
    + intros ->.
      exists σw. split.
      * split; [exact Hσw |].
        transitivity (store_restrict (store_restrict σw X) (dom σ)).
        -- rewrite store_restrict_restrict.
           replace (X ∩ dom σ) with (dom σ) by (rewrite Hdomσ; set_solver).
           reflexivity.
        -- rewrite Hrestr. apply store_restrict_idemp. set_solver.
      * transitivity (store_restrict (store_restrict σw X) (dom σ)).
        -- rewrite store_restrict_restrict.
           replace (X ∩ dom σ) with (dom σ) by (rewrite Hdomσ; set_solver).
           reflexivity.
        -- rewrite Hrestr. apply store_restrict_idemp. set_solver.
Qed.

Lemma res_restrict_fiber_from_projection_eq_singleton
    (w : WfWorld) (X : aset) (σ : StoreT)
    (Hproj : res_restrict w X σ) :
  dom σ = X →
  (res_restrict (res_fiber_from_projection w X σ Hproj) X : World) =
  singleton_world σ.
Proof.
  intros Hdomσ.
  simpl in Hproj.
  destruct Hproj as [σw [Hσw Hrestr]].
  apply world_ext.
  - change (world_dom (w : World) ∩ X = dom σ).
    rewrite <- (wfworld_store_dom w σw Hσw).
    rewrite <- Hrestr, store_restrict_dom. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hτ0σ] Hτ]].
      rewrite Hdomσ in Hτ0σ.
      congruence.
    + intros ->.
      exists σw. split.
      * split; [exact Hσw |].
        rewrite Hdomσ. exact Hrestr.
      * exact Hrestr.
Qed.

Lemma raw_restrict_fiber_from_projection_eq_singleton
    (w : WfWorld) (X : aset) (σ : StoreT) :
  res_restrict w X σ →
  dom σ = X →
  raw_restrict (raw_fiber w σ) X = singleton_world σ.
Proof.
  intros Hproj Hdomσ.
  simpl in Hproj.
  destruct Hproj as [σw [Hσw Hrestr]].
  apply world_ext.
  - simpl.
    rewrite <- (wfworld_store_dom w σw Hσw).
    rewrite <- Hrestr, store_restrict_dom. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hτ0σ] Hτ]].
      rewrite Hdomσ in Hτ0σ.
      congruence.
    + intros ->.
      exists σw. split.
      * split; [exact Hσw |].
        rewrite Hdomσ. exact Hrestr.
      * exact Hrestr.
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

Lemma res_le_same_dom_eq (w1 w2 : WfWorld) :
  w1 ⊑ w2 →
  world_dom (w1 : World) = world_dom (w2 : World) →
  w1 = w2.
Proof.
  intros Hle Hdom.
  apply (anti_symm (⊑)); [exact Hle |].
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      assert (Hw1σ : (w1 : World) σ).
      {
        unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
        rewrite Hle. simpl.
        exists σ. split; [exact Hσ |].
        apply store_restrict_idemp.
        pose proof (wfworld_store_dom w2 σ Hσ) as Hσdom.
        set_solver.
      }
      exists σ. split; [exact Hw1σ |].
      apply store_restrict_idemp.
      pose proof (wfworld_store_dom w2 σ Hσ) as Hσdom.
      set_solver.
    + intros [σ' [Hσ' Hrestrict]].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hσ'. simpl in Hσ'.
      destruct Hσ' as [σ2 [Hσ2 Hrestrict2]].
      pose proof (wfworld_store_dom w2 σ2 Hσ2) as Hσ2dom.
      rewrite store_restrict_idemp in Hrestrict2 by set_solver.
      subst σ'.
      rewrite store_restrict_idemp in Hrestrict by set_solver.
      subst. exact Hσ2.
Qed.

Lemma world_compat_le_r (w m n : WfWorld) :
  m ⊑ n →
  world_compat w n →
  world_compat w m.
Proof.
  intros Hle Hcompat σw σm Hσw Hσm.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  rewrite Hle in Hσm. simpl in Hσm.
  destruct Hσm as [σn [Hσn Hrestrict]].
  subst σm. apply store_compat_restrict_r.
  exact (Hcompat σw σn Hσw Hσn).
Qed.

Lemma world_compat_le_l (w m n : WfWorld) :
  m ⊑ n →
  world_compat n w →
  world_compat m w.
Proof.
  intros Hle Hcompat σm σw Hσm Hσw.
  apply store_compat_sym.
  eapply world_compat_le_r; [exact Hle | | exact Hσw | exact Hσm].
	  intros σw' σn Hσw' Hσn. apply store_compat_sym.
	  exact (Hcompat σn σw' Hσn Hσw').
Qed.

Lemma world_compat_restrict_l_full_r (n m : WfWorld) (S X : aset) :
  X ⊆ S →
  world_compat n (res_restrict m S) →
  world_compat (res_restrict n X) m.
Proof.
  intros HXS Hcompat σn σm Hσn Hσm.
  simpl in Hσn. destruct Hσn as [τn [Hτn Hrestrict]]. subst σn.
  assert (Hrσm : (res_restrict m S : World) (store_restrict σm S)).
  { simpl. exists σm. split; [exact Hσm | reflexivity]. }
  pose proof (Hcompat τn (store_restrict σm S) Hτn Hrσm) as Hstore.
  apply store_compat_restrict_l_full_r with (X := S).
  - rewrite store_restrict_dom. set_solver.
  - apply store_compat_sym.
    apply store_compat_restrict_r.
    apply store_compat_sym. exact Hstore.
Qed.

Lemma world_compat_swap (x y : atom) (w1 w2 : WfWorld) :
  world_compat (res_swap x y w1) (res_swap x y w2) ↔
  world_compat w1 w2.
Proof.
  split.
  - intros Hc σ1 σ2 Hσ1 Hσ2.
    pose proof (Hc (store_swap x y σ1) (store_swap x y σ2)) as Hc'.
    simpl in Hc'.
    assert (Hs1 : raw_swap x y w1 (store_swap x y σ1)).
    { exists σ1. split; [exact Hσ1 | reflexivity]. }
    assert (Hs2 : raw_swap x y w2 (store_swap x y σ2)).
    { exists σ2. split; [exact Hσ2 | reflexivity]. }
    pose proof (Hc' Hs1 Hs2) as Hcompat.
    exact (proj1 (store_compat_swap x y σ1 σ2) Hcompat).
  - intros Hc σ1 σ2 Hσ1 Hσ2.
    simpl in Hσ1, Hσ2.
    destruct Hσ1 as [τ1 [Hτ1 Hswap1]].
    destruct Hσ2 as [τ2 [Hτ2 Hswap2]]. subst.
    apply (proj2 (store_compat_swap x y τ1 τ2)).
    exact (Hc τ1 τ2 Hτ1 Hτ2).
Qed.

Lemma world_compat_swap_intro (x y : atom) (w1 w2 : WfWorld) :
  world_compat w1 w2 →
  world_compat (res_swap x y w1) (res_swap x y w2).
Proof. apply (proj2 (world_compat_swap x y w1 w2)). Qed.

Lemma world_compat_swap_elim (x y : atom) (w1 w2 : WfWorld) :
  world_compat (res_swap x y w1) (res_swap x y w2) →
  world_compat w1 w2.
Proof. apply (proj1 (world_compat_swap x y w1 w2)). Qed.

Lemma res_product_swap (x y : atom) (w1 w2 : WfWorld)
    (Hc : world_compat w1 w2)
    (Hc' : world_compat (res_swap x y w1) (res_swap x y w2)) :
  res_swap x y (res_product w1 w2 Hc) =
  res_product (res_swap x y w1) (res_swap x y w2) Hc'.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite aset_swap_union. reflexivity.
  - intros σ. simpl. split.
    + intros [σ0 [Hprod Hswap]]. subst σ.
      destruct Hprod as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      exists (store_swap x y σ1), (store_swap x y σ2). repeat split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * exists σ2. split; [exact Hσ2 | reflexivity].
      * exact (proj2 (store_compat_swap x y σ1 σ2) Hcompat).
      * rewrite <- store_swap_union. reflexivity.
    + intros [σ1' [σ2' [Hσ1' [Hσ2' [Hcompat' ->]]]]].
      destruct Hσ1' as [σ1 [Hσ1 Hswap1]].
      destruct Hσ2' as [σ2 [Hσ2 Hswap2]]. subst σ1' σ2'.
      exists (σ1 ∪ σ2). split.
      * exists σ1, σ2. repeat split; eauto.
      * rewrite store_swap_union.
        reflexivity.
Qed.

Lemma res_product_double_swap_l (x y : atom) (w1 w2 : WfWorld)
    (Hc : world_compat w1 w2)
    (Hc' : world_compat (res_swap x y (res_swap x y w1)) w2) :
  res_product (res_swap x y (res_swap x y w1)) w2 Hc' =
  res_product w1 w2 Hc.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite aset_swap_involutive. reflexivity.
  - intros σ. simpl. split.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      destruct Hσ1 as [τ1 [[τ0 [Hτ0 Hswap0]] Hswap1]].
      subst τ1 σ1. rewrite store_swap_involutive in Hcompat |- *.
      exists τ0, σ2. repeat split; eauto.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      exists σ1, σ2. split.
      * exists (store_swap x y σ1). split.
        -- exists σ1. split; [exact Hσ1 | reflexivity].
        -- apply store_swap_involutive.
      * split; [exact Hσ2 |]. split; [exact Hcompat | reflexivity].
Qed.

Lemma res_sum_swap (x y : atom) (w1 w2 : WfWorld)
    (Hdef : raw_sum_defined w1 w2)
    (Hdef' : raw_sum_defined (res_swap x y w1) (res_swap x y w2)) :
  res_swap x y (res_sum w1 w2 Hdef) =
  res_sum (res_swap x y w1) (res_swap x y w2) Hdef'.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. reflexivity.
  - intros σ. simpl. split.
    + intros [σ0 [[Hσ0 | Hσ0] Hswap]]; subst σ.
      * left. exists σ0. split; [exact Hσ0 | reflexivity].
      * right. exists σ0. split; [exact Hσ0 | reflexivity].
    + intros [[σ0 [Hσ0 Hswap]] | [σ0 [Hσ0 Hswap]]]; subst σ.
      * exists σ0. split; [left; exact Hσ0 | reflexivity].
      * exists σ0. split; [right; exact Hσ0 | reflexivity].
Qed.

Lemma res_restrict_le (w : WfWorld) (X : aset) :
  res_restrict w X ⊑ w.
Proof.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σ' [Hσ' Hrestrict]]. subst σ.
      exists σ'. split; [exact Hσ' |].
      pose proof (wfworld_store_dom w σ' Hσ') as Hdomσ'.
      rewrite <- (store_restrict_idemp σ' (world_dom (w : World))) at 2
        by set_solver.
      rewrite store_restrict_restrict. reflexivity.
    + intros [σ' [Hσ' Hrestrict]].
      exists σ'. split; [exact Hσ' |].
      pose proof (wfworld_store_dom w σ' Hσ') as Hdomσ'.
      rewrite <- Hrestrict.
      rewrite <- (store_restrict_idemp σ' (world_dom (w : World))) at 1
        by set_solver.
      rewrite store_restrict_restrict. reflexivity.
Qed.

Lemma res_restrict_restrict_eq (w : WfWorld) (X Y : aset) :
  res_restrict (res_restrict w X) Y = res_restrict w (X ∩ Y).
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [σx [[σw [Hσw Hx]] Hy]]. subst σx σ.
      exists σw. split; [exact Hσw |].
      rewrite store_restrict_restrict. reflexivity.
    + intros [σw [Hσw Hxy]]. subst σ.
      exists (store_restrict σw X). split.
      * exists σw. split; [exact Hσw | reflexivity].
      * rewrite store_restrict_restrict. reflexivity.
Qed.

Lemma res_restrict_mono (w : WfWorld) (X Y : aset) :
  X ⊆ Y →
  res_restrict w X ⊑ res_restrict w Y.
Proof.
  intros HXY.
  replace (res_restrict w X) with (res_restrict (res_restrict w Y) X).
  2:{
    rewrite res_restrict_restrict_eq.
    replace (Y ∩ X) with X by set_solver.
    reflexivity.
  }
  apply res_restrict_le.
Qed.

Lemma res_restrict_eq_of_le (m n : WfWorld) :
  m ⊑ n →
  res_restrict n (world_dom (m : World)) = m.
Proof.
  intros Hle.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  symmetry. apply wfworld_ext. exact Hle.
Qed.

Lemma res_le_restrict (m n : WfWorld) (X : aset) :
  m ⊑ n →
  world_dom (m : World) ⊆ X →
  m ⊑ res_restrict n X.
Proof.
  intros Hle Hdom.
  rewrite <- (res_restrict_eq_of_le m n Hle).
  apply res_restrict_mono. exact Hdom.
Qed.

Lemma res_restrict_le_mono (m n : WfWorld) (X : aset) :
  m ⊑ n →
  res_restrict m X ⊑ res_restrict n X.
Proof.
  intros Hle.
  eapply res_le_restrict.
  - etrans; [apply res_restrict_le | exact Hle].
  - simpl. set_solver.
Qed.

Lemma res_swap_le (x y : atom) (w1 w2 : WfWorld) :
  w1 ⊑ w2 →
  res_swap x y w1 ⊑ res_swap x y w2.
Proof.
  intros Hle.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  change ((res_swap x y w1 : World) =
    (res_restrict (res_swap x y w2) (aset_swap x y (world_dom (w1 : World))) : World)).
  rewrite (res_restrict_swap x y w2 (world_dom (w1 : World))).
  rewrite (res_restrict_eq_of_le w1 w2 Hle). reflexivity.
Qed.

Lemma res_swap_le_iff (x y : atom) (w1 w2 : WfWorld) :
  res_swap x y w1 ⊑ res_swap x y w2 ↔ w1 ⊑ w2.
Proof.
  split.
  - intros Hle.
    pose proof (res_swap_le x y _ _ Hle) as Hswap.
    rewrite !res_swap_involutive in Hswap. exact Hswap.
  - apply res_swap_le.
Qed.

Lemma res_swap_le_elim (x y : atom) (w1 w2 : WfWorld) :
  res_swap x y w1 ⊑ res_swap x y w2 →
  w1 ⊑ w2.
Proof. apply (proj1 (res_swap_le_iff x y w1 w2)). Qed.

Lemma res_restrict_le_eq (m n : WfWorld) (X : aset) :
  m ⊑ n →
  X ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X.
Proof.
  intros Hle HX.
  rewrite <- (res_restrict_eq_of_le m n Hle).
  rewrite res_restrict_restrict_eq.
  replace (world_dom (m : World) ∩ X) with X by set_solver.
  reflexivity.
Qed.

Lemma res_restrict_le_eq_from_base
    (m n : WfWorld) (S X : aset) :
  res_restrict m S ⊑ n →
  X ⊆ S →
  X ⊆ world_dom (m : World) →
  res_restrict n X = res_restrict m X.
Proof.
  intros Hle HXS HXm.
  rewrite <- (res_restrict_le_eq (res_restrict m S) n X Hle).
  - rewrite res_restrict_restrict_eq.
    replace (S ∩ X) with X by set_solver.
    reflexivity.
  - simpl. set_solver.
Qed.

Lemma res_fiber_from_projection_le
    (m n : WfWorld) (X : aset) (σ : StoreT)
    (Hproj_m : res_restrict m X σ)
    (Hproj_n : res_restrict n X σ) :
  m ⊑ n →
  X ⊆ world_dom (m : World) →
  res_fiber_from_projection m X σ Hproj_m ⊑
  res_fiber_from_projection n X σ Hproj_n.
Proof.
  intros Hle HX.
  assert (Hdomσ : dom σ ⊆ X).
  {
    simpl in Hproj_n.
    destruct Hproj_n as [σn [Hσn Hrestr]].
    rewrite <- Hrestr. rewrite store_restrict_dom. set_solver.
  }
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl. pose proof (raw_le_dom m n Hle). set_solver.
  - intros τ. simpl. split.
    + intros [Hmτ Hτ].
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hmτ. simpl in Hmτ.
      destruct Hmτ as [τn [Hnτ Hrestrict]].
      exists τn. split.
      * split; [exact Hnτ |].
        transitivity (store_restrict τ (dom σ)); [| exact Hτ].
        rewrite <- Hrestrict.
        rewrite store_restrict_restrict.
        replace (world_dom (m : World) ∩ dom σ) with (dom σ) by set_solver.
        reflexivity.
      * exact Hrestrict.
    + intros [τn [[Hnτ Hτn] Hrestrict]].
      split.
      * unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
        rewrite Hle. simpl. exists τn. split; [exact Hnτ | exact Hrestrict].
      * transitivity (store_restrict τn (dom σ)); [| exact Hτn].
        rewrite <- Hrestrict.
        rewrite store_restrict_restrict.
        replace (world_dom (m : World) ∩ dom σ) with (dom σ) by set_solver.
        reflexivity.
Qed.

Lemma res_fiber_swap x y (w : WfWorld) (σ : StoreT)
    (Hne : ∃ s, (w : World) s ∧ store_restrict s (dom σ) = σ)
    (Hne' : ∃ s, (res_swap x y w : World) s ∧
        store_restrict s (dom (store_swap x y σ)) = store_swap x y σ) :
  res_swap x y (res_fiber w σ Hne) =
  res_fiber (res_swap x y w) (store_swap x y σ) Hne'.
Proof.
  apply wfworld_ext. apply world_ext.
  - simpl. reflexivity.
  - intros τ. simpl. split.
    + intros [τ0 [[Hτ0 Hrestr] Hswap]]. subst τ.
      split.
      * exists τ0. split; [exact Hτ0 | reflexivity].
      * change (store_restrict (store_swap x y τ0) (dom (store_swap x y σ)) =
            store_swap x y σ).
        rewrite (store_swap_dom x y σ), store_restrict_swap. f_equal.
        exact Hrestr.
    + intros [[τ0 [Hτ0 Hswap]] Hrestr]. subst τ.
      exists τ0. split.
      * split; [exact Hτ0 |].
        change (store_restrict (store_swap x y τ0) (dom (store_swap x y σ)) =
            store_swap x y σ) in Hrestr.
        rewrite store_swap_dom, store_restrict_swap in Hrestr.
        apply (f_equal (store_swap x y)) in Hrestr.
        rewrite !store_swap_involutive in Hrestr. exact Hrestr.
      * reflexivity.
Qed.

Lemma res_fiber_from_projection_swap x y (w : WfWorld) (X : aset)
    (σ : StoreT)
    (Hproj : res_restrict w X σ)
    (Hproj' : res_restrict (res_swap x y w) (aset_swap x y X)
        (store_swap x y σ)) :
  res_swap x y (res_fiber_from_projection w X σ Hproj) =
  res_fiber_from_projection (res_swap x y w) (aset_swap x y X)
    (store_swap x y σ) Hproj'.
Proof.
  unfold res_fiber_from_projection.
  apply res_fiber_swap.
Qed.

Lemma res_one_point_extension_pushout
    (m n my : WfWorld) (y : atom) :
  m ⊑ n →
  y ∉ world_dom (n : World) →
  world_dom (my : World) = world_dom (m : World) ∪ {[y]} →
  res_restrict my (world_dom (m : World)) = m →
  ∃ ny : WfWorld,
    world_dom (ny : World) = world_dom (n : World) ∪ {[y]} ∧
    res_restrict ny (world_dom (n : World)) = n ∧
    my ⊑ ny.
Proof.
  intros Hmn Hy_n Hdom_my Hrestr_my.
  pose proof (raw_le_dom m n Hmn) as Hdom_m_n.
  pose (raw_ny := ({|
    world_dom := world_dom (n : World) ∪ {[y]};
    world_stores := λ τ,
      ∃ σn σy,
        (n : World) σn ∧
        (my : World) σy ∧
        store_restrict σn (world_dom (m : World)) =
          store_restrict σy (world_dom (m : World)) ∧
        τ = σn ∪ store_restrict σy {[y]}
  |} : World)).
  assert (Hwf_ny : wf_world raw_ny).
  {
    constructor.
    - destruct (wf_ne _ (world_wf my)) as [σy Hσy].
      assert (Hm_proj : (m : World) (store_restrict σy (world_dom (m : World)))).
      {
        assert (Hraw : raw_restrict my (world_dom (m : World))
            (store_restrict σy (world_dom (m : World)))).
        { exists σy. split; [exact Hσy | reflexivity]. }
        assert (Heq : raw_restrict my (world_dom (m : World)) = (m : World)).
        { change ((res_restrict my (world_dom (m : World)) : World) = (m : World)).
          rewrite Hrestr_my. reflexivity. }
        rewrite Heq in Hraw. exact Hraw.
      }
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hmn.
      rewrite Hmn in Hm_proj. simpl in Hm_proj.
      destruct Hm_proj as [σn [Hσn Hrestrict]].
      exists (σn ∪ store_restrict σy {[y]}). simpl.
      exists σn, σy. repeat split; eauto.
      replace (world_dom (n : World) ∩ world_dom (m : World))
        with (world_dom (m : World)) in Hrestrict by set_solver.
      exact Hrestrict.
    - intros τ [σn [σy [Hσn [Hσy [Hagree ->]]]]].
      pose proof (wfworld_store_dom n σn Hσn) as Hdomσn.
      pose proof (wfworld_store_dom my σy Hσy) as Hdomσy.
      assert (Hcompat :
          store_compat σn (store_restrict σy {[y]})).
      {
        apply disj_dom_store_compat.
        apply set_eq. intros z. split.
        - intros Hz.
          apply elem_of_intersection in Hz as [Hzn Hzy].
          change (z ∈ (dom σn : aset)) in Hzn.
          change (z ∈ (dom (store_restrict σy {[y]}) : aset)) in Hzy.
          rewrite store_restrict_dom in Hzy.
          rewrite Hdomσn in Hzn.
          apply elem_of_intersection in Hzy as [Hzy Hy].
          change (z ∈ (dom σy : aset)) in Hzy.
          rewrite Hdomσy, Hdom_my in Hzy.
          set_solver.
        - intros Hz. apply elem_of_empty in Hz. contradiction.
      }
      rewrite store_union_dom by exact Hcompat.
      change ((dom σn : aset) ∪ dom (store_restrict σy {[y]}) =
        world_dom (n : World) ∪ {[y]}).
      rewrite store_restrict_dom. rewrite Hdomσn.
      apply set_eq. intros z. split.
      * intros Hz.
        apply elem_of_union in Hz as [Hz|Hz]; [set_solver |].
        apply elem_of_intersection in Hz as [Hzy Hy].
        change (z ∈ (dom σy : aset)) in Hzy.
        rewrite Hdomσy, Hdom_my in Hzy. set_solver.
      * intros Hz.
        apply elem_of_union.
        destruct (decide (z ∈ world_dom (n : World))) as [Hzn|Hzn].
        -- left. exact Hzn.
        -- right. apply elem_of_intersection. split.
           ++ change (z ∈ (dom σy : aset)).
              rewrite Hdomσy, Hdom_my. set_solver.
           ++ set_solver.
  }
  exists (exist _ raw_ny Hwf_ny). split.
  - reflexivity.
  - split.
    + apply wfworld_ext. apply world_ext.
      * simpl. set_solver.
      * intros τ. simpl. split.
        -- intros [τny [[σn [σy [Hσn [Hσy [Hagree ->]]]]] Hrestrict]].
           rewrite (store_restrict_union_piece_l
             σn (store_restrict σy {[y]}) (world_dom (n : World)) {[y]}) in Hrestrict.
           ++ subst τ. exact Hσn.
           ++ apply store_compat_restrict_singleton_fresh.
              pose proof (wfworld_store_dom n σn Hσn) as Hdomσn.
              change (y ∉ (dom σn : aset)). rewrite Hdomσn. exact Hy_n.
           ++ pose proof (wfworld_store_dom n σn Hσn) as Hdomσn.
              intros z Hz. change (z ∈ (dom σn : aset)) in Hz.
              rewrite Hdomσn in Hz. exact Hz.
           ++ apply store_restrict_dom_subset.
           ++ set_solver.
        -- intros Hτn.
           assert (Hm_proj : (m : World) (store_restrict τ (world_dom (m : World)))).
           {
             unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hmn.
             rewrite Hmn at 1. simpl. exists τ. split; [exact Hτn | reflexivity].
           }
           assert (Hraw_my :
               raw_restrict my (world_dom (m : World))
                 (store_restrict τ (world_dom (m : World)))).
           {
             assert (Heq : raw_restrict my (world_dom (m : World)) = (m : World)).
             { change ((res_restrict my (world_dom (m : World)) : World) = (m : World)).
               rewrite Hrestr_my. reflexivity. }
             rewrite Heq. exact Hm_proj.
           }
           simpl in Hraw_my.
           destruct Hraw_my as [σy [Hσy Hσy_restrict]].
           exists (τ ∪ store_restrict σy {[y]}). split.
           ++ simpl. exists τ, σy. repeat split; eauto.
           ++ apply (store_restrict_union_piece_l
                τ (store_restrict σy {[y]}) (world_dom (n : World)) {[y]}).
              ** apply store_compat_restrict_singleton_fresh.
                 pose proof (wfworld_store_dom n τ Hτn) as Hdomτ.
                 change (y ∉ (dom τ : aset)). rewrite Hdomτ. exact Hy_n.
              ** pose proof (wfworld_store_dom n τ Hτn) as Hdomτ.
                 intros z Hz. change (z ∈ (dom τ : aset)) in Hz.
                 rewrite Hdomτ in Hz. exact Hz.
              ** apply store_restrict_dom_subset.
              ** set_solver.
    + unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
      apply world_ext.
      * simpl. rewrite Hdom_my. set_solver.
      * intros τ. simpl. split.
        -- intros Hτmy.
           assert (Hm_proj : (m : World) (store_restrict τ (world_dom (m : World)))).
           {
             assert (Hraw : raw_restrict my (world_dom (m : World))
                 (store_restrict τ (world_dom (m : World)))).
             { exists τ. split; [exact Hτmy | reflexivity]. }
             assert (Heq : raw_restrict my (world_dom (m : World)) = (m : World)).
             { change ((res_restrict my (world_dom (m : World)) : World) = (m : World)).
               rewrite Hrestr_my. reflexivity. }
             rewrite Heq in Hraw. exact Hraw.
           }
           unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hmn.
	           rewrite Hmn in Hm_proj. simpl in Hm_proj.
	           destruct Hm_proj as [σn [Hσn Hrestrict]].
	           exists (σn ∪ store_restrict τ {[y]}). split.
	           ++ simpl. exists σn, τ. repeat split; eauto.
	              replace (world_dom (n : World) ∩ world_dom (m : World))
	                with (world_dom (m : World)) in Hrestrict by set_solver.
	              exact Hrestrict.
	           ++ pose proof (wfworld_store_dom n σn Hσn) as Hdomσn.
	              pose proof (wfworld_store_dom my τ Hτmy) as Hdomτ.
	              rewrite Hdom_my.
	              apply store_restrict_union_base_singleton.
	              ** intros z Hz. change (z ∈ (dom σn : aset)).
	                 rewrite Hdomσn. apply Hdom_m_n. exact Hz.
	              ** change ((dom τ : aset) = world_dom (m : World) ∪ {[y]}).
	                 rewrite Hdomτ, Hdom_my. reflexivity.
	              ** change (y ∉ (dom σn : aset)). rewrite Hdomσn. exact Hy_n.
	              ** replace (world_dom (n : World) ∩ world_dom (m : World))
	                   with (world_dom (m : World)) in Hrestrict by set_solver.
	                 exact Hrestrict.
	        -- intros [τny [[σn [σy [Hσn [Hσy [Hagree ->]]]]] Hrestrict]].
	           rewrite Hdom_my in Hrestrict.
	           replace ((world_dom (n : World) ∪ {[y]}) ∩
	             (world_dom (m : World) ∪ {[y]}))
	             with (world_dom (m : World) ∪ {[y]}) in Hrestrict by set_solver.
	           change (store_restrict (σn ∪ store_restrict σy {[y]})
	             (world_dom (m : World) ∪ {[y]}) = τ) in Hrestrict.
	           assert (Hglue :
	             store_restrict (σn ∪ store_restrict σy {[y]})
	               (world_dom (m : World) ∪ {[y]}) = σy).
	           {
	             apply store_restrict_union_base_singleton.
	             - pose proof (wfworld_store_dom n σn Hσn) as Hdomσn.
	               intros z Hz. change (z ∈ (dom σn : aset)).
	               rewrite Hdomσn. apply Hdom_m_n. exact Hz.
	             - pose proof (wfworld_store_dom my σy Hσy) as Hdomσy.
	               change ((dom σy : aset) = world_dom (m : World) ∪ {[y]}).
	               rewrite Hdomσy, Hdom_my. reflexivity.
	             - pose proof (wfworld_store_dom n σn Hσn) as Hdomσn.
	               change (y ∉ (dom σn : aset)). rewrite Hdomσn. exact Hy_n.
	             - exact Hagree.
	           }
	           rewrite Hglue in Hrestrict. subst τ. exact Hσy.
Qed.

Lemma res_subset_lift_under (m n mu : WfWorld) :
  m ⊑ n →
  res_subset mu m →
  ∃ nu : WfWorld,
    res_subset nu n ∧ mu ⊑ nu.
Proof.
  intros Hle [Hdom_mu_m Hin_mu_m].
  pose proof (raw_le_dom m n Hle) as Hdom_m_n.
  pose (raw_nu := ({|
    world_dom := world_dom (n : World);
    world_stores := λ σ,
      (n : World) σ ∧ (mu : World) (store_restrict σ (world_dom (m : World)))
  |} : World)).
  assert (Hwf_nu : wf_world raw_nu).
  {
    constructor.
    - destruct (wf_ne _ (world_wf mu)) as [σmu Hσmu].
      assert (Hmσmu : (m : World) σmu) by exact (Hin_mu_m σmu Hσmu).
      unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
      rewrite Hle in Hmσmu. simpl in Hmσmu.
      destruct Hmσmu as [σn [Hσn Hrestrict]].
      exists σn. split; [exact Hσn |].
      rewrite Hrestrict. exact Hσmu.
    - intros σ [Hσn _]. simpl. exact (wfworld_store_dom n σ Hσn).
  }
  exists (exist _ raw_nu Hwf_nu). split.
  - split; [reflexivity | intros σ Hσ; exact (proj1 Hσ)].
  - unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
    apply world_ext.
    + simpl. set_solver.
    + intros σ. simpl. split.
      * intros Hσmu.
        assert (Hmσ : (m : World) σ) by exact (Hin_mu_m σ Hσmu).
        unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
        rewrite Hle in Hmσ. simpl in Hmσ.
        destruct Hmσ as [σn [Hσn Hrestrict]].
        exists σn. split; [split; [exact Hσn | rewrite Hrestrict; exact Hσmu] |].
        rewrite Hdom_mu_m. exact Hrestrict.
      * intros [σn [[Hσn Hσmu] Hrestrict]].
        rewrite Hdom_mu_m in Hrestrict.
        subst σ. exact Hσmu.
Qed.

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

Lemma res_one_point_extension_exists (w : WfWorld) (y : atom) :
  y ∉ world_dom (w : World) →
  ∃ wy : WfWorld,
    world_dom (wy : World) = world_dom (w : World) ∪ {[y]} ∧
    res_restrict wy (world_dom (w : World)) = w.
Proof.
  intros Hy.
  set (σy := <[y := inhabitant]> (∅ : StoreT)).
  set (one_y := (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorld)).
  assert (Hdom_one_y : world_dom (one_y : World) = {[y]}).
  {
    subst one_y σy. simpl.
    rewrite dom_insert_L, dom_empty_L. set_solver.
  }
  assert (Hc : world_compat w one_y).
  {
    apply disj_dom_world_compat. rewrite Hdom_one_y. set_solver.
  }
  exists (res_product w one_y Hc). split.
  - change (world_dom (w : World) ∪ world_dom (one_y : World) =
      world_dom (w : World) ∪ {[y]}).
    rewrite Hdom_one_y. reflexivity.
  - rewrite <- (res_restrict_le_eq w (res_product w one_y Hc)
      (world_dom (w : World)) (res_le_product_l w one_y Hc)).
    + apply res_restrict_eq_of_le. reflexivity.
    + set_solver.
Qed.

Lemma res_subset_lift_over (m n mo : WfWorld) :
  m ⊑ n →
  res_subset m mo →
  ∃ no : WfWorld,
    res_subset n no ∧ mo ⊑ no.
Proof.
  intros Hle [Hdom_m_mo Hin_m_mo].
  pose proof (raw_le_dom m n Hle) as Hdom_m_n.
  set (extra := res_restrict n (world_dom (n : World) ∖ world_dom (m : World))).
  assert (Hcompat : world_compat mo extra).
  {
    apply disj_dom_world_compat. subst extra. simpl. set_solver.
  }
  exists (res_product mo extra Hcompat). split.
  - split.
    + unfold extra. simpl.
      apply set_eq. intros x. split.
      * intros Hx.
        apply elem_of_union.
        destruct (decide (x ∈ world_dom (m : World))) as [Hxm|Hxnm].
        -- left. rewrite <- Hdom_m_mo. exact Hxm.
        -- right. apply elem_of_intersection. split; [exact Hx |].
           apply elem_of_difference. split; [exact Hx | exact Hxnm].
      * intros Hx.
        apply elem_of_union in Hx as [Hxmo|Hxdiff].
        -- apply Hdom_m_n. rewrite Hdom_m_mo. exact Hxmo.
        -- apply elem_of_intersection in Hxdiff as [Hx _]. exact Hx.
    + intros σ Hσn.
      pose proof (wfworld_store_dom n σ Hσn) as Hdomσ.
      assert (Hm_proj : (m : World) (store_restrict σ (world_dom (m : World)))).
      {
        unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
        rewrite Hle at 1. simpl. exists σ. split; [exact Hσn | reflexivity].
      }
      assert (Hmo_proj : (mo : World) (store_restrict σ (world_dom (m : World)))).
      { exact (Hin_m_mo _ Hm_proj). }
      assert (Hextra :
          (extra : World)
            (store_restrict σ (world_dom (n : World) ∖ world_dom (m : World)))).
      {
        subst extra. simpl. exists σ. split; [exact Hσn | reflexivity].
      }
      assert (Hstore_part_compat :
          store_compat (store_restrict σ (world_dom (m : World)))
            (store_restrict σ (world_dom (n : World) ∖ world_dom (m : World)))).
      {
        apply disj_dom_store_compat.
        apply set_eq. intros x. split.
        - intros Hin.
          apply elem_of_intersection in Hin as [Hin1 Hin2].
          rewrite store_restrict_dom in Hin1.
          rewrite store_restrict_dom in Hin2.
          apply elem_of_intersection in Hin1 as [_ Hxm].
          apply elem_of_intersection in Hin2 as [_ Hxdiff].
          apply elem_of_difference in Hxdiff as [_ Hxnotm].
          exfalso. exact (Hxnotm Hxm).
        - intros Hin. apply elem_of_empty in Hin. contradiction.
      }
      simpl. exists (store_restrict σ (world_dom (m : World))),
        (store_restrict σ (world_dom (n : World) ∖ world_dom (m : World))).
      repeat split.
      * exact Hmo_proj.
      * exact Hextra.
      * exact Hstore_part_compat.
      * symmetry. apply store_restrict_union_partition.
        -- intros x Hx. change (x ∈ dom σ) in Hx. rewrite Hdomσ in Hx.
           apply elem_of_union.
           destruct (decide (x ∈ world_dom (m : World))) as [Hxm|Hxnm].
           ++ left. exact Hxm.
           ++ right. apply elem_of_difference. split; [exact Hx | exact Hxnm].
        -- apply set_eq. intros x. split.
           ++ intros Hin.
              apply elem_of_intersection in Hin as [Hxm Hxdiff].
              apply elem_of_difference in Hxdiff as [_ Hxnotm].
              exfalso. exact (Hxnotm Hxm).
           ++ intros Hin. apply elem_of_empty in Hin. contradiction.
  - exact (res_le_product_l mo extra Hcompat).
Qed.

Lemma res_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_product w1 w2 Hc ⊑ res_product w1' w2' Hc'.
Proof.
  intros Hle1 Hle2.
  pose proof (raw_le_dom w1 w1' Hle1) as Hdom1.
  pose proof (raw_le_dom w2 w2' Hle2) as Hdom2.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in *.
  apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros Hσ.
      destruct Hσ as [σ1 [σ2 [Hσ1 [Hσ2 [Hcompat ->]]]]].
      rewrite Hle1 in Hσ1. simpl in Hσ1.
      rewrite Hle2 in Hσ2. simpl in Hσ2.
      destruct Hσ1 as [σ1' [Hσ1' Hrestr1]].
      destruct Hσ2 as [σ2' [Hσ2' Hrestr2]].
      pose proof (Hc' σ1' σ2' Hσ1' Hσ2') as Hcompat'.
      exists (σ1' ∪ σ2'). split.
      * exists σ1', σ2'. repeat split; eauto.
      * rewrite store_restrict_union_cover.
        -- rewrite Hrestr1, Hrestr2. reflexivity.
        -- exact Hcompat'.
        -- pose proof (wfworld_store_dom w1' σ1' Hσ1') as Hdomσ1'.
           set_solver.
        -- pose proof (wfworld_store_dom w2' σ2' Hσ2') as Hdomσ2'.
           set_solver.
    + intros [σ' [Hσ' Hrestrict]].
      destruct Hσ' as [σ1' [σ2' [Hσ1' [Hσ2' [Hcompat' ->]]]]].
      set (σ1 := store_restrict σ1' (world_dom (w1 : World))).
      set (σ2 := store_restrict σ2' (world_dom (w2 : World))).
      assert (Hσ1 : (w1 : World) σ1).
      {
        rewrite Hle1. simpl. exists σ1'. split; [exact Hσ1' | reflexivity].
      }
      assert (Hσ2 : (w2 : World) σ2).
      {
        rewrite Hle2. simpl. exists σ2'. split; [exact Hσ2' | reflexivity].
      }
      exists σ1, σ2. repeat split.
      * exact Hσ1.
      * exact Hσ2.
      * exact (Hc σ1 σ2 Hσ1 Hσ2).
      * subst σ1 σ2.
        rewrite <- Hrestrict.
        rewrite store_restrict_union_cover.
        -- reflexivity.
        -- exact Hcompat'.
        -- pose proof (wfworld_store_dom w1' σ1' Hσ1') as Hdomσ1'.
           set_solver.
        -- pose proof (wfworld_store_dom w2' σ2' Hσ2') as Hdomσ2'.
           set_solver.
Qed.

Lemma res_product_restrict_wand_le
    (n m : WfWorld) (S X Y : aset)
    (Hc_small : world_compat (res_restrict n X) m)
    (Hc : world_compat n (res_restrict m S)) :
  Y ⊆ S →
  Y ⊆ world_dom (m : World) →
  res_restrict (res_product (res_restrict n X) m Hc_small) Y ⊑
  res_product n (res_restrict m S) Hc.
Proof.
  intros HYS HYm.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le.
  apply world_ext.
  - simpl. set_solver.
  - intros σ. simpl. split.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [τn [τm [Hτn [Hτm [Hcompat ->]]]]].
      simpl in Hτn. destruct Hτn as [σn [Hσn HnX]]. subst τn.
      assert (Htarget_compat : store_compat σn (store_restrict τm S)).
      {
        apply (Hc σn (store_restrict τm S)).
        - exact Hσn.
        - simpl. exists τm. split; [exact Hτm | reflexivity].
      }
      exists ((σn : StoreT) ∪ (store_restrict τm S : StoreT)). split.
      * simpl. exists σn, (store_restrict τm S). split; [exact Hσn |].
        split.
        -- simpl. exists τm. split; [exact Hτm | reflexivity].
        -- split; [exact Htarget_compat | reflexivity].
      * replace (((world_dom (n : World) ∩ X) ∪ world_dom (m : World)) ∩ Y)
          with Y by set_solver.
        transitivity (store_restrict ((store_restrict σn X : StoreT) ∪ (τm : StoreT)) Y).
        -- assert (HYτm : Y ⊆ dom τm).
           { pose proof (wfworld_store_dom m τm Hτm) as Hdomτm.
             rewrite Hdomτm. exact HYm. }
           exact (store_restrict_wand_product σn τm S X Y
             Hcompat Htarget_compat HYS HYτm).
        -- exact Hrestrict.
    + intros [τ [Hτ Hrestrict]].
      destruct Hτ as [τn [τm [Hτn [Hτm [Hcompat ->]]]]].
      simpl in Hτm. destruct Hτm as [σm [Hσm HmS]]. subst τm.
      set (σnX := store_restrict τn X).
      exists ((σnX : StoreT) ∪ (σm : StoreT)). split.
      * exists σnX, σm. split.
        -- subst σnX. simpl. exists τn. split; [exact Hτn | reflexivity].
        -- split; [exact Hσm |].
           split.
           ++ subst σnX. apply (Hc_small (store_restrict τn X) σm).
              ** simpl. exists τn. split; [exact Hτn | reflexivity].
              ** exact Hσm.
           ++ reflexivity.
      * subst σnX.
        replace (((world_dom (n : World) ∩ X) ∪ world_dom (m : World)) ∩ Y)
          with Y in Hrestrict by set_solver.
        rewrite <- Hrestrict.
        symmetry.
        assert (Hsmall_compat : store_compat (store_restrict τn X) σm).
        {
          apply (Hc_small (store_restrict τn X) σm).
          - simpl. exists τn. split; [exact Hτn | reflexivity].
          - exact Hσm.
        }
        assert (HYσm : Y ⊆ dom σm).
        {
          pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
          rewrite Hdomσm. exact HYm.
        }
        exact (store_restrict_wand_product τn σm S X Y
          Hsmall_compat Hcompat HYS HYσm).
Qed.

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
