From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra ResourceExtension.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Atom-keyed resource interface *)

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).

Definition World : Type := @WorldA atom _ _ V.
Definition WfWorld : Type := @WfWorldA atom _ _ V.
Definition LWorld : Type := @WorldA logic_var _ _ V.
Definition LWfWorld : Type := @WfWorldA logic_var _ _ V.

Definition world_dom (m : World) : aset := worldA_dom m.
Definition lworld_dom (m : LWorld) : lvset := worldA_dom m.
Definition world_stores (m : World) : StoreT → Prop := worldA_stores m.
Definition wf_world (m : World) : Prop := wf_worldA m.
Definition raw_world (w : WfWorld) : World := proj1_sig w.
Definition lraw_world (w : LWfWorld) : LWorld := proj1_sig w.
Definition world_wf (w : WfWorld) : wf_world (raw_world w) := proj2_sig w.

Coercion world_stores : World >-> Funclass.
Coercion raw_world : WfWorld >-> World.
Coercion lraw_world : LWfWorld >-> LWorld.

Definition raw_unit : World := rawA_unit.
Definition raw_restrict (m : World) (X : aset) : World := rawA_restrict m X.
Definition raw_fiber (m : World) (σ : StoreT) : World := rawA_fiber m σ.
Definition raw_le (m1 m2 : World) : Prop := rawA_le m1 m2.

Definition res_unit : WfWorld := resA_unit.
Definition res_restrict (w : WfWorld) (X : aset) : WfWorld := resA_restrict w X.
Definition lres_swap (x y : logic_var) (w : LWfWorld) : LWfWorld := resA_swap x y w.

Lemma lworld_dom_lres_swap (x y : logic_var) (w : LWfWorld) :
  lworld_dom (lres_swap x y w : LWorld) =
  set_swap x y (lworld_dom (lraw_world w)).
Proof. reflexivity. Qed.

Lemma lres_open_swap_commute_fresh i j x y (w : LWfWorld) :
  i <> j ->
  x <> y ->
  lres_swap (LVBound i) (LVFree x)
    (lres_swap (LVBound j) (LVFree y) w) =
  lres_swap (LVBound j) (LVFree y)
    (lres_swap (LVBound i) (LVFree x) w).
Proof.
  intros Hij Hxy.
  unfold lres_swap.
  rewrite resA_swap_conjugate.
  better_base_solver.
Qed.

(** Atom worlds can be viewed as locally-nameless worlds whose keys are all
    free logic variables.  The implementation lives at the concrete interface
    because it relates the two public key instances [atom] and [logic_var]. *)
Definition lstore_lift_free
    (σ : gmap atom V) : gmap logic_var V :=
  kmap LVFree σ.

Lemma dom_lstore_lift_free (σ : gmap atom V) :
  dom (lstore_lift_free σ : gmap logic_var V) = lvars_of_atoms (dom σ).
Proof.
  unfold lstore_lift_free, lvars_of_atoms.
  change (dom (kmap (M2:=gmap logic_var) LVFree (σ : gmap atom V)) =
    set_map LVFree (dom (σ : gmap atom V))).
  assert (Hinj : Inj (=) (=) LVFree).
  { intros x y Heq. inversion Heq. reflexivity. }
  rewrite (dom_kmap_L (M:=gmap atom) (M2:=gmap logic_var)
    (Inj0:=Hinj) LVFree (σ : gmap atom V)).
  reflexivity.
Qed.

Lemma lstore_lift_free_lookup_free (σ : gmap atom V) x :
  (lstore_lift_free σ : gmap logic_var V) !! LVFree x = (σ : gmap atom V) !! x.
Proof.
  unfold lstore_lift_free.
  change ((kmap (M2:=gmap logic_var) LVFree (σ : gmap atom V)) !! LVFree x =
    (σ : gmap atom V) !! x).
  assert (Hinj : Inj (=) (=) LVFree).
  { intros a b Heq. inversion Heq. reflexivity. }
  rewrite (lookup_kmap (M1:=gmap atom) (M2:=gmap logic_var)
    (Inj0:=Hinj) LVFree (σ : gmap atom V) x).
  reflexivity.
Qed.

Lemma lstore_lift_free_lookup_bound (σ : gmap atom V) k :
  (lstore_lift_free σ : gmap logic_var V) !! LVBound k = None.
Proof.
  apply not_elem_of_dom.
  rewrite dom_lstore_lift_free.
  unfold lvars_of_atoms.
  rewrite elem_of_map.
  intros [x [Hbad _]]. discriminate.
Qed.

Definition res_lift_free
    (w : @WfWorldA atom _ _ V) : @WfWorldA logic_var _ _ V.
Proof.
  refine (exist _ {|
    worldA_dom := lvars_of_atoms (world_dom (w : World));
    worldA_stores := fun τ =>
      ∃ σ : gmap atom V, (w : World) σ ∧ τ = lstore_lift_free σ
  |} _).
  destruct (worldA_wf w) as [Hne Hdom].
  split.
  - destruct Hne as [σ Hσ].
    exists (lstore_lift_free σ). exists σ. split; [exact Hσ | reflexivity].
  - intros τ [σ [Hσ ->]].
    rewrite dom_lstore_lift_free.
    rewrite (Hdom σ Hσ).
    reflexivity.
Defined.

Lemma res_lift_free_dom (w : @WfWorldA atom _ _ V) :
  lworld_dom (res_lift_free w : LWorld) = lvars_of_atoms (world_dom (w : World)).
Proof. reflexivity. Qed.

Record LWorldOn (D : lvset) : Type := {
  lw : LWfWorld;
  lw_dom : lworld_dom (lraw_world lw) = D;
}.

Arguments lw {_} _.
Arguments lw_dom {_} _.

Definition lworld_on_lift
    (D : lvset) (m : WfWorld)
    (Hlc : lc_lvars D)
    (Hsub : lvars_fv D ⊆ world_dom (m : World)) : LWorldOn D.
Proof.
  refine {| lw :=
    @resA_restrict logic_var _ _ V (res_lift_free (res_restrict m (lvars_fv D))) D |}.
  simpl.
  apply set_eq. intros v. split.
  - intros Hv. apply elem_of_intersection in Hv as [_ Hv]. exact Hv.
  - intros Hv. apply elem_of_intersection. split; [| exact Hv].
    unfold lvars_of_atoms. apply elem_of_map.
    destruct v as [k | x].
    + exfalso. exact (Hlc (LVBound k) Hv).
    + exists x. split; [reflexivity |].
      simpl. apply elem_of_intersection. split.
      * apply Hsub. rewrite lvars_fv_elem. exact Hv.
      * rewrite lvars_fv_elem. exact Hv.
Defined.

Definition lworld_on_open_back
    (k : nat) (x : atom) (D : lvset)
    (w : LWorldOn (lvars_open k x D)) : LWorldOn D.
Proof.
  refine {| lw := lres_swap (LVBound k) (LVFree x) (lw w) |}.
  rewrite lworld_dom_lres_swap, (lw_dom w).
  better_base_solver.
Defined.

Lemma lworld_on_store_dom_eq D (w : LWorldOn D) (τ : gmap logic_var V) :
  worldA_stores (lw w : LWorld) τ ->
  dom (τ : gmap logic_var V) = D.
Proof.
  intros Hτ.
  pose proof (wfworldA_store_dom (lw w) τ Hτ) as Hdom.
  change (dom (τ : gmap logic_var V) = lworld_dom (lw w : LWorld)) in Hdom.
  rewrite Hdom, (lw_dom w). reflexivity.
Qed.

Lemma lworld_on_open_back_store_swap_member
    k x D (w : LWorldOn (lvars_open k x D)) (τ : gmap logic_var V) :
  worldA_stores (lw w : LWorld) τ ->
  worldA_stores
    (lw (lworld_on_open_back k x D w) : LWorld)
    (lstore_swap (LVBound k) (LVFree x) τ).
Proof.
  intros Hτ.
  unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_stores].
  exists τ. split; [exact Hτ|reflexivity].
Qed.

Lemma lworld_on_open_back_store_swap_inv
    k x D (w : LWorldOn (lvars_open k x D)) (σ : gmap logic_var V) :
  worldA_stores
    (lw (lworld_on_open_back k x D w) : LWorld) σ ->
  exists σ0 : gmap logic_var V,
    worldA_stores (lw w : LWorld) σ0 /\
    σ = lstore_swap (LVBound k) (LVFree x) σ0.
Proof.
  unfold lworld_on_open_back.
  cbn [lw lraw_world raw_worldA worldA_stores].
  intros [σ0 [Hσ0 Hσ]]. exists σ0. split; [exact Hσ0|].
  unfold lstore_swap, lstore_rekey.
  symmetry. exact Hσ.
Qed.

Lemma lworld_on_open_back_commute_fresh i j x y D
    (w1 : LWorldOn (lvars_open i x (lvars_open j y D)))
    (w2 : LWorldOn (lvars_open j y (lvars_open i x D))) :
  i <> j ->
  x <> y ->
  lw w1 = lw w2 ->
  lw (lworld_on_open_back j y D
        (lworld_on_open_back i x (lvars_open j y D) w1)) =
  lw (lworld_on_open_back i x D
        (lworld_on_open_back j y (lvars_open i x D) w2)).
Proof.
  intros Hij Hxy Hlw.
  cbn [lworld_on_open_back lw].
  rewrite Hlw.
  symmetry. apply lres_open_swap_commute_fresh; assumption.
Qed.

Lemma lworld_on_ext D (w1 w2 : LWorldOn D) :
  lw w1 = lw w2 →
  w1 = w2.
Proof.
  destruct w1 as [w1 Hdom1], w2 as [w2 Hdom2]. simpl.
  intros ->. f_equal. apply proof_irrelevance.
Qed.

Definition world_compat (m1 m2 : World) : Prop := worldA_compat m1 m2.
Definition raw_product (m1 m2 : World) : World := rawA_product m1 m2.
Definition raw_sum (m1 m2 : World) : World := rawA_sum m1 m2.
Definition raw_sum_defined (m1 m2 : World) : Prop := rawA_sum_defined m1 m2.
Definition res_product (w1 w2 : WfWorld) (Hc : world_compat (w1 : World) (w2 : World)) : WfWorld :=
  resA_product w1 w2 Hc.
Definition res_sum (w1 w2 : WfWorld) (Hdef : raw_sum_defined (w1 : World) (w2 : World)) : WfWorld :=
  resA_sum w1 w2 Hdef.
Definition res_subset (w1 w2 : WfWorld) : Prop := resA_subset w1 w2.

Definition singleton_world (σ : StoreT) : World := singleton_worldA σ.

Definition fiber_extension : Type := @fiber_extensionA atom _ _ V.
Definition extension_applicable (F : fiber_extension) (m : WfWorld) : Prop :=
  extension_applicableA F m.
Definition res_extend_by (m : WfWorld) (F : fiber_extension) (n : WfWorld) : Prop :=
  resA_extend_by m F n.
Definition fiber_extension_functional_on (m : WfWorld) (F : fiber_extension) : Prop :=
  fiber_extensionA_functional_on m F.
Definition res_fiber_from_projection
    (w : WfWorld) (X : aset) (σ : StoreT) (wfib : WfWorld) : Prop :=
  resA_fiber_from_projection w X σ wfib.
Definition res_fiber_member (w : WfWorld) (X : aset) (wfib : WfWorld) : Prop :=
  resA_fiber_member w X wfib.

Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).
Notation "wfib ∈ᶠ Fiber( w , X )" :=
  (res_fiber_member w X wfib) (at level 70).



(** * Concrete resource basic interface lemmas *)




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

Lemma raw_le_refl (w : WfWorld) :
  raw_le w w.
Proof. apply rawA_le_refl. exact (world_wf w). Qed.

Lemma res_subset_refl (w : WfWorld) : res_subset w w.
Proof. apply resA_subset_refl. Qed.

Lemma raw_compat_unit_r (m : World) : world_compat m raw_unit.
Proof. apply rawA_compat_unit_r. Qed.

Lemma wf_singleton_world (σ : StoreT) : wf_world (singleton_world σ).
Proof. apply wf_singleton_worldA. Qed.

Lemma res_fiber_from_projection_empty_store_dom
    (m mfib : WfWorld) (σ : StoreT) :
  res_fiber_from_projection m ∅ σ mfib ->
  dom (σ : StoreT) = ∅.
Proof.
  intros [Hproj _].
  pose proof (wfworld_store_dom (res_restrict m ∅) σ Hproj) as Hdom.
  change (dom (σ : StoreT) = world_dom (res_restrict m ∅ : World)) in Hdom.
  simpl in Hdom. set_solver.
Qed.

Lemma res_fiber_from_projection_store_source
    (m mfib : WfWorld) (X : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  (m : World) τ.
Proof.
  intros [_ Hfib] Hτ.
  destruct mfib as [wmfib Hwfib].
  cbn [raw_world raw_worldA world_stores] in Hτ, Hfib.
  change (wmfib = rawA_fiber (m : World) σ) in Hfib.
  change (wmfib τ) in Hτ.
  rewrite Hfib in Hτ.
  exact (proj1 Hτ).
Qed.



(** * Concrete resource key action and order interface lemmas *)




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

Lemma res_fiber_from_projection_transport_on
    (m n nfib : WfWorld) (σ : StoreT) (D X : aset) :
  D ⊆ X →
  D ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X →
  res_fiber_from_projection n D σ nfib →
  ∃ mfib,
    res_fiber_from_projection m D σ mfib ∧
    res_restrict mfib X = res_restrict nfib X.
Proof. apply resA_fiber_from_projection_transport_on. Qed.

Lemma world_compat_le_r (w m n : WfWorld) :
  m ⊑ n →
  world_compat w n →
  world_compat w m.
Proof. apply worldA_compat_le_r. Qed.

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

Lemma res_pullback_subset_projection_subset (n p : WfWorld) Hsub :
  res_subset (res_pullback_subset_projection n p Hsub) n.
Proof. apply resA_pullback_subset_projection_subset. Qed.

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

Lemma res_product_le_l (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w1 ⊑ res_product w1 w2 Hc.
Proof. apply resA_le_product_l. Qed.

Lemma res_product_le_r (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w2 ⊑ res_product w1 w2 Hc.
Proof. apply resA_le_product_r. Qed.

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



(** * Concrete resource extension interface lemmas *)




Local Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).

Lemma res_extend_by_restrict_base (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  res_restrict n (world_dom m) = m.
Proof. apply resA_extend_by_restrict_base. Qed.

Lemma res_extend_by_dom (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  world_dom (n : World) = world_dom (m : World) ∪ extA_out F.
Proof. apply resA_extend_by_dom. Qed.

Lemma res_extend_by_le (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  m ⊑ n.
Proof. apply resA_extend_by_le. Qed.

Lemma res_extend_by_applicable (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  extension_applicable F m.
Proof. apply resA_extend_by_applicable. Qed.

Lemma res_extend_by_input_dom (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  extA_in F ⊆ world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_in _ _ Happ).
Qed.

Lemma res_extend_by_output_fresh (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  extA_out F ## world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_out _ _ Happ).
Qed.

Lemma res_extend_by_exists (m : WfWorld) (F : fiber_extension) :
  extension_applicable F m →
  ∃ n, m #> F ~~> n.
Proof. apply resA_extend_by_exists. Qed.

Lemma res_extend_by_projection_eq
    (m n : WfWorld) (F : fiber_extension) (my ny : WfWorld) :
  res_restrict m (extA_in F) = res_restrict n (extA_in F) →
  m #> F ~~> my →
  n #> F ~~> ny →
  res_restrict my (extA_in F ∪ extA_out F) =
  res_restrict ny (extA_in F ∪ extA_out F).
Proof. apply resA_extend_by_projection_eq. Qed.

Lemma res_extend_by_product_frame_r
    (m1 m1x m2 : WfWorld) (F : fiber_extension)
    (Hc : world_compat m1 m2) :
  m1 #> F ~~> m1x ->
  extA_out F ## world_dom (m2 : World) ->
  exists Hcx : world_compat m1x m2,
    res_product m1 m2 Hc #> F ~~>
      res_product m1x m2 Hcx.
Proof. apply resA_extend_by_product_frame_r. Qed.

Lemma res_extend_by_product_frame_l
    (m1 m1x m2 : WfWorld) (F : fiber_extension)
    (Hc : world_compat m2 m1) :
  m1 #> F ~~> m1x ->
  extA_out F ## world_dom (m2 : World) ->
  exists Hcx : world_compat m2 m1x,
    res_product m2 m1 Hc #> F ~~>
      res_product m2 m1x Hcx.
Proof. apply resA_extend_by_product_frame_l. Qed.

End ResourceInterface.
