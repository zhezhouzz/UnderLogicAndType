From ChoicePrelude Require Import Prelude Store.
From ChoiceAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
  ResourceAlgebra ResourceExtension ResourceExtensionDerived.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Atom-keyed resource interface *)

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Definition World : Type := @WorldA atom _ _ V.
Definition WfWorld : Type := @WfWorldA atom _ _ V.
Definition LWorld : Type := @WorldA logic_var _ _ V.
Definition LWfWorld : Type := @WfWorldA logic_var _ _ V.

Definition world_dom (m : World) : aset := worldA_dom m.
Definition lworld_dom (m : LWorld) : lvset := worldA_dom m.
Definition world_stores (m : World) : Store → Prop := worldA_stores m.
Definition wf_world (m : World) : Prop := wf_worldA m.
Definition raw_world (w : WfWorld) : World := proj1_sig w.
Definition lraw_world (w : LWfWorld) : LWorld := proj1_sig w.
Definition world_wf (w : WfWorld) : wf_world (raw_world w) := proj2_sig w.

Coercion world_stores : World >-> Funclass.
Coercion raw_world : WfWorld >-> World.
Coercion lraw_world : LWfWorld >-> LWorld.

Definition raw_unit : World := rawA_unit.
Definition raw_restrict (m : World) (X : aset) : World := rawA_restrict m X.
Definition raw_fiber (m : World) (σ : Store) : World := rawA_fiber m σ.
Definition raw_swap (x y : atom) (m : World) : World := rawA_swap x y m.
Definition raw_shift (k : nat) (m : World) : World := rawA_shift k m.
Definition raw_le (m1 m2 : World) : Prop := rawA_le m1 m2.

Definition res_unit : WfWorld := resA_unit.
Definition res_restrict (w : WfWorld) (X : aset) : WfWorld := resA_restrict w X.
Definition res_fiber (w : WfWorld) (σ : Store)
    (Hne : ∃ σ0, (w : World) σ0 ∧ store_restrict σ0 (dom σ) = σ) : WfWorld :=
  resA_fiber w σ Hne.
Definition res_swap (x y : atom) (w : WfWorld) : WfWorld := resA_swap x y w.
Definition res_shift (k : nat) (w : WfWorld) : WfWorld := resA_shift k w.
Definition lres_swap (x y : logic_var) (w : LWfWorld) : LWfWorld := resA_swap x y w.

Lemma lworld_dom_lres_swap (x y : logic_var) (w : LWfWorld) :
  lworld_dom (lres_swap x y w : LWorld) =
  gset_swap x y (lworld_dom (lraw_world w)).
Proof. reflexivity. Qed.

(** Atom worlds can be viewed as locally-nameless worlds whose keys are all
    free logic variables.  The implementation lives at the concrete interface
    because it relates the two public key instances [atom] and [logic_var]. *)
Definition lstore_lift_free
    (σ : @StoreA V atom _ _) : @StoreA V logic_var _ _ :=
  kmap LVFree σ.

Lemma dom_lstore_lift_free (σ : @StoreA V atom _ _) :
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

Lemma lstore_lift_free_lookup_free (σ : @StoreA V atom _ _) x :
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

Lemma lstore_lift_free_lookup_bound (σ : @StoreA V atom _ _) k :
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
      ∃ σ : @StoreA V atom _ _, (w : World) σ ∧ τ = lstore_lift_free σ
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

Definition world_compat (m1 m2 : World) : Prop := worldA_compat m1 m2.
Definition raw_product (m1 m2 : World) : World := rawA_product m1 m2.
Definition raw_sum (m1 m2 : World) : World := rawA_sum m1 m2.
Definition raw_sum_defined (m1 m2 : World) : Prop := rawA_sum_defined m1 m2.
Definition res_product (w1 w2 : WfWorld) (Hc : world_compat (w1 : World) (w2 : World)) : WfWorld :=
  resA_product w1 w2 Hc.
Definition res_sum (w1 w2 : WfWorld) (Hdef : raw_sum_defined (w1 : World) (w2 : World)) : WfWorld :=
  resA_sum w1 w2 Hdef.
Definition res_le (w1 w2 : WfWorld) : Prop := resA_le w1 w2.
Definition res_subset (w1 w2 : WfWorld) : Prop := resA_subset w1 w2.

Definition singleton_world (σ : Store) : World := singleton_worldA σ.
Definition raw_slice_restrict (n : WfWorld) (X : aset) (p : WfWorld) : World :=
  rawA_slice_restrict n X p.
Definition res_slice_restrict
    (n : WfWorld) (X : aset) (p : WfWorld)
    (Hsub : res_subset p (res_restrict n X)) : WfWorld :=
  resA_slice_restrict n X p Hsub.
Definition raw_pullback_projection (n p : WfWorld) : World :=
  rawA_pullback_projection n p.
Definition res_pullback_projection (n p : WfWorld) (Hle : p ⊑ n) : WfWorld :=
  resA_pullback_projection n p Hle.

Definition fiber_extension : Type := @fiber_extensionA atom _ _ V.
Definition extension_applicable (F : fiber_extension) (m : WfWorld) : Prop :=
  extension_applicableA F m.
Definition res_extend_by (m : WfWorld) (F : fiber_extension) (n : WfWorld) : Prop :=
  resA_extend_by m F n.
Definition fiber_extension_functional_on (m : WfWorld) (F : fiber_extension) : Prop :=
  fiber_extensionA_functional_on m F.
Definition fiber_extension_equiv_on (m : WfWorld) (F G : fiber_extension) : Prop :=
  fiber_extensionA_equiv_on m F G.
Definition res_fiber_from_projection
    (w : WfWorld) (X : aset) (σ : Store) (wfib : WfWorld) : Prop :=
  resA_fiber_from_projection w X σ wfib.
Definition res_fiber_of_projection
    (w : WfWorld) (X : aset) (σ : Store) (wfib : WfWorld) : Prop :=
  res_fiber_from_projection w X σ wfib.
Definition res_fiber_member (w : WfWorld) (X : aset) (wfib : WfWorld) : Prop :=
  resA_fiber_member w X wfib.

Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).
Notation "wfib ∈ᶠ Fiber( w , X )" :=
  (res_fiber_member w X wfib) (at level 70).

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
Proof.
  apply resA_sum_swap.
Qed.

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

Lemma res_extend_by_restrict_base m F n :
  m #> F ~~> n →
  res_restrict n (world_dom m) = m.
Proof. apply resA_extend_by_restrict_base. Qed.

Lemma res_extend_by_dom m F n :
  m #> F ~~> n →
  world_dom (n : World) = world_dom (m : World) ∪ extA_out F.
Proof. apply resA_extend_by_dom. Qed.

Lemma res_extend_by_le m F n :
  m #> F ~~> n →
  m ⊑ n.
Proof. apply resA_extend_by_le. Qed.

Lemma res_extend_by_applicable m F n :
  m #> F ~~> n →
  extension_applicable F m.
Proof. apply resA_extend_by_applicable. Qed.

Lemma res_extend_by_input_dom m F n :
  m #> F ~~> n →
  extA_in F ⊆ world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_in _ _ Happ).
Qed.

Lemma res_extend_by_output_fresh m F n :
  m #> F ~~> n →
  extA_out F ## world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_out _ _ Happ).
Qed.

Lemma res_extend_by_base_le m n F my ny :
  m ⊑ n →
  m #> F ~~> my →
  n #> F ~~> ny →
  my ⊑ ny.
Proof. apply resA_extend_by_base_le. Qed.

Lemma res_extend_by_exists m F :
  extension_applicable F m →
  ∃ n, m #> F ~~> n.
Proof. apply resA_extend_by_exists. Qed.

Lemma res_extend_by_unique m F n1 n2 :
  m #> F ~~> n1 →
  m #> F ~~> n2 →
  n1 = n2.
Proof. apply resA_extend_by_unique. Qed.

Lemma res_extend_by_projection_eq m n F my ny :
  res_restrict m (extA_in F) = res_restrict n (extA_in F) →
  m #> F ~~> my →
  n #> F ~~> ny →
  res_restrict my (extA_in F ∪ extA_out F) =
  res_restrict ny (extA_in F ∪ extA_out F).
Proof. apply resA_extend_by_projection_eq. Qed.

Lemma res_extend_by_fiber_equiv_on m F G n :
  extA_in F = extA_in G →
  m #> F ~~> n →
  m #> G ~~> n →
  fiber_extension_equiv_on m F G.
Proof. apply resA_extend_by_fiber_equiv_on. Qed.

Lemma res_extend_by_commute m F G mF mG mFG mGF :
  m #> F ~~> mF →
  m #> G ~~> mG →
  mF #> G ~~> mFG →
  mG #> F ~~> mGF →
  mFG = mGF.
Proof. apply resA_extend_by_commute. Qed.

Lemma res_extend_by_sum_pullback
    (m : WfWorld) F (n n1 n2 : WfWorld)
    (Hdef : raw_sum_defined (n1 : World) (n2 : World)) :
  m #> F ~~> n →
  fiber_extension_functional_on m F →
  world_dom (m : World) ⊆ world_dom (n1 : World) →
  world_dom (m : World) ⊆ world_dom (n2 : World) →
  res_sum n1 n2 Hdef ⊑ n →
  ∃ (m1 m2 : WfWorld) (Hdefm : raw_sum_defined m1 m2)
    (n1' n2' : WfWorld),
    world_dom (m1 : World) = world_dom (m : World) ∧
    world_dom (m2 : World) = world_dom (m : World) ∧
    res_subset m1 m ∧
    res_subset m2 m ∧
    res_sum m1 m2 Hdefm ⊑ m ∧
    m1 #> F ~~> n1' ∧
    n1 ⊑ n1' ∧
    m2 #> F ~~> n2' ∧
    n2 ⊑ n2'.
Proof. apply resA_extend_by_sum_pullback. Qed.

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
Proof. apply resA_one_point_extension_pushout. Qed.

End ResourceInterface.
