From ContextBase Require Import Prelude LogicVarInterface.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
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
Definition raw_le (m1 m2 : World) : Prop := rawA_le m1 m2.

Definition res_unit : WfWorld := resA_unit.
Definition res_restrict (w : WfWorld) (X : aset) : WfWorld := resA_restrict w X.
Definition lres_swap (x y : logic_var) (w : LWfWorld) : LWfWorld := resA_swap x y w.

Lemma lworld_dom_lres_swap (x y : logic_var) (w : LWfWorld) :
  lworld_dom (lres_swap x y w : LWorld) =
  gset_swap x y (lworld_dom (lraw_world w)).
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
  rewrite !key_swap_fresh by congruence.
  reflexivity.
Qed.

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
  rewrite lvars_open_unfold, gset_swap_involutive. reflexivity.
Defined.

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

Definition singleton_world (σ : Store) : World := singleton_worldA σ.

Definition fiber_extension : Type := @fiber_extensionA atom _ _ V.
Definition extension_applicable (F : fiber_extension) (m : WfWorld) : Prop :=
  extension_applicableA F m.
Definition res_extend_by (m : WfWorld) (F : fiber_extension) (n : WfWorld) : Prop :=
  resA_extend_by m F n.
Definition fiber_extension_functional_on (m : WfWorld) (F : fiber_extension) : Prop :=
  fiber_extensionA_functional_on m F.
Definition res_fiber_from_projection
    (w : WfWorld) (X : aset) (σ : Store) (wfib : WfWorld) : Prop :=
  resA_fiber_from_projection w X σ wfib.
Definition res_fiber_member (w : WfWorld) (X : aset) (wfib : WfWorld) : Prop :=
  resA_fiber_member w X wfib.

Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).
Notation "wfib ∈ᶠ Fiber( w , X )" :=
  (res_fiber_member w X wfib) (at level 70).

End ResourceInterface.
