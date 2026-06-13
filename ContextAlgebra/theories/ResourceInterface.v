From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra ResourceExtension.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Atom-keyed resource interface *)

Declare Scope resource_scope.
Delimit Scope resource_scope with res.

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).

Definition World : Type := @WorldA atom _ _ V.
Definition WfWorld : Type := @WfWorldA atom _ _ V.
Definition LWorld : Type := @WorldA logic_var _ _ V.
Definition LWfWorld : Type := @WfWorldA logic_var _ _ V.

Bind Scope resource_scope with World.
Bind Scope resource_scope with WfWorld.
Bind Scope resource_scope with LWorld.
Bind Scope resource_scope with LWfWorld.

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

#[global] Instance dom_world_inst : Dom World aset := world_dom.
#[global] Instance dom_wfworld_inst : Dom WfWorld aset :=
  fun w => world_dom (w : World).
#[global] Instance dom_lworld_inst : Dom LWorld lvset := lworld_dom.
#[global] Instance dom_lwfworld_inst : Dom LWfWorld lvset :=
  fun w => lworld_dom (w : LWorld).
Arguments dom_world_inst /.
Arguments dom_wfworld_inst /.
Arguments dom_lworld_inst /.
Arguments dom_lwfworld_inst /.

Definition raw_unit : World := rawA_unit.
Definition raw_restrict (m : World) (X : aset) : World := rawA_restrict m X.
Definition raw_fiber (m : World) (σ : StoreT) : World := rawA_fiber m σ.
Definition raw_le (m1 m2 : World) : Prop := rawA_le m1 m2.

Definition res_unit : WfWorld := resA_unit.
Definition res_restrict (w : WfWorld) (X : aset) : WfWorld := resA_restrict w X.
Definition res_atom_swap (x y : atom) (w : WfWorld) : WfWorld := resA_swap x y w.
Definition lres_swap (x y : logic_var) (w : LWfWorld) : LWfWorld := resA_swap x y w.

Notation "'𝟙'" := res_unit : resource_scope.
Notation "'Dom' r" := (world_dom r)
  (at level 10, format "Dom  r") : resource_scope.
Notation "r '↾' X" := (res_restrict r X)
  (at level 20, no associativity,
   format "r  ↾  X") : resource_scope.
Notation "m1 '⊑ᵣ' m2" := (raw_le m1 m2)
  (at level 70, no associativity,
   format "m1  ⊑ᵣ  m2") : resource_scope.
Lemma world_dom_res_atom_swap (x y : atom) (w : WfWorld) :
  world_dom (res_atom_swap x y w : World) =
  set_swap x y (world_dom (w : World)).
Proof. reflexivity. Qed.

Lemma res_restrict_atom_swap (x y : atom) (w : WfWorld) (X : aset) :
  res_restrict (res_atom_swap x y w) (set_swap x y X) =
  res_atom_swap x y (res_restrict w X).
Proof. apply resA_restrict_swap. Qed.

Lemma res_atom_swap_fresh (x y : atom) (w : WfWorld) :
  x ∉ world_dom (w : World) ->
  y ∉ world_dom (w : World) ->
  res_atom_swap x y w = w.
Proof.
  intros Hx Hy.
  apply wfworldA_ext. apply worldA_ext.
  - rewrite world_dom_res_atom_swap.
    apply set_swap_fresh; assumption.
  - intros σ. simpl. split.
    + intros [σ0 [Hσ0 Hσ]]. rewrite <- Hσ.
      change (worldA_stores (w : World) (storeA_swap x y σ0)).
      rewrite storeA_swap_fresh; [exact Hσ0 | |];
        rewrite (wfworldA_store_dom w σ0 Hσ0); assumption.
    + intros Hσ.
      exists σ. split; [exact Hσ |].
      apply storeA_swap_fresh; rewrite (wfworldA_store_dom w σ Hσ); assumption.
Qed.

Lemma lworld_dom_lres_swap (x y : logic_var) (w : LWfWorld) :
  lworld_dom (lres_swap x y w : LWorld) =
  set_swap x y (lworld_dom (lraw_world w)).
Proof. reflexivity. Qed.

Lemma lres_restrict_swap (x y : logic_var) (w : LWfWorld) (X : lvset) :
  @resA_restrict logic_var _ _ V (lres_swap x y w) (set_swap x y X) =
  lres_swap x y (@resA_restrict logic_var _ _ V w X).
Proof. apply resA_restrict_swap. Qed.

Lemma lres_swap_involutive (x y : logic_var) (w : LWfWorld) :
  lres_swap x y (lres_swap x y w) = w.
Proof. apply resA_swap_involutive. Qed.

Lemma lres_swap_fresh (x y : logic_var) (w : LWfWorld) :
  x ∉ lworld_dom (w : LWorld) ->
  y ∉ lworld_dom (w : LWorld) ->
  lres_swap x y w = w.
Proof.
  intros Hx Hy.
  apply wfworldA_ext. apply worldA_ext.
  - rewrite lworld_dom_lres_swap.
    apply set_swap_fresh; assumption.
  - intros σ. simpl. split.
    + intros [σ0 [Hσ0 Hσ]]. rewrite <- Hσ.
      change (worldA_stores (w : LWorld) (storeA_swap x y σ0)).
      rewrite storeA_swap_fresh; [exact Hσ0 | |];
        rewrite (wfworldA_store_dom w σ0 Hσ0); assumption.
    + intros Hσ.
      exists σ. split; [exact Hσ |].
      apply storeA_swap_fresh; rewrite (wfworldA_store_dom w σ Hσ); assumption.
Qed.

Lemma lworld_compat_swap (x y : logic_var) (w1 w2 : LWfWorld) :
  worldA_compat (w1 : LWorld) (w2 : LWorld) ->
  worldA_compat (lres_swap x y w1 : LWorld)
    (lres_swap x y w2 : LWorld).
Proof.
  intros Hc σ1 σ2 [σ1' [Hσ1' Hσ1eq]] [σ2' [Hσ2' Hσ2eq]].
  subst σ1 σ2.
  apply (proj2 (storeA_compat_swap x y σ1' σ2')).
  eapply Hc; eauto.
Qed.

Lemma lres_product_swap_eq x y
    (w1 w2 : LWfWorld)
    (Hc : worldA_compat (w1 : LWorld) (w2 : LWorld))
    (Hc_sw : worldA_compat (lres_swap x y w1 : LWorld)
      (lres_swap x y w2 : LWorld)) :
  resA_product (lres_swap x y w1) (lres_swap x y w2) Hc_sw =
  lres_swap x y (resA_product w1 w2 Hc).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - change (set_swap x y (lworld_dom (w1 : LWorld)) ∪
      set_swap x y (lworld_dom (w2 : LWorld)) =
      set_swap x y (lworld_dom (w1 : LWorld) ∪ lworld_dom (w2 : LWorld))).
    rewrite set_swap_union. reflexivity.
  - intros σ. split.
    + intros [σ1 [σ2 [[σ1' [Hσ1' Hσ1eq]]
        [[σ2' [Hσ2' Hσ2eq]] [Hcompat Hσeq]]]]].
      subst σ1 σ2 σ.
      exists (σ1' ∪ σ2'). split.
      * exists σ1', σ2'. repeat split; eauto.
      * exact (storeA_swap_union x y σ1' σ2').
    + intros [σ0 [[σ1 [σ2 [Hσ1 [Hσ2 [Hcompat Hσ0eq]]]]] Hσeq]].
      subst σ0 σ.
      exists (storeA_swap x y σ1), (storeA_swap x y σ2).
      repeat split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * exists σ2. split; [exact Hσ2 | reflexivity].
      * apply (proj2 (storeA_compat_swap x y σ1 σ2)). exact Hcompat.
      * apply storeA_swap_union.
Qed.

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

Lemma lstore_lift_free_union (σ1 σ2 : gmap atom V) :
  lstore_lift_free (σ1 ∪ σ2) =
  (lstore_lift_free σ1 ∪ lstore_lift_free σ2 : gmap logic_var V).
Proof.
  unfold lstore_lift_free.
  apply atom_store_to_lvar_store_union.
Qed.

Lemma lstore_lift_free_swap (x y : atom) (σ : gmap atom V) :
  lstore_lift_free (storeA_swap x y σ) =
  lvar_store_swap x y (lstore_lift_free σ).
Proof.
  apply storeA_map_eq. intros v.
  destruct v as [k|z].
  - rewrite lstore_lift_free_lookup_bound.
    rewrite lvar_store_swap_lookup_inv.
    symmetry. apply lstore_lift_free_lookup_bound.
  - rewrite lvar_store_swap_lookup_inv.
    rewrite !lstore_lift_free_lookup_free.
    apply storeA_swap_lookup_inv.
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

Lemma res_lift_free_atom_swap (x y : atom) (w : WfWorld) :
  res_lift_free (res_atom_swap x y w) =
  lres_swap (LVFree x) (LVFree y) (res_lift_free w).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - simpl.
    change (lvars_of_atoms (set_swap x y (world_dom (w : World))) =
      lvars_swap x y (lvars_of_atoms (world_dom (w : World)))).
    apply lvars_of_atoms_swap.
  - intros τ. simpl. split.
    + intros [σ [[σ0 [Hσ0 Hswap]] ->]]. subst σ.
      exists (lstore_lift_free σ0). split.
      * exists σ0. split; [exact Hσ0 | reflexivity].
      * symmetry. apply lstore_lift_free_swap.
    + intros [τ0 [[σ0 [Hσ0 ->]] Hswap]]. subst τ.
      exists (storeA_swap x y σ0). split.
      * exists σ0. split; [exact Hσ0 | reflexivity].
      * symmetry. apply lstore_lift_free_swap.
Qed.

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

Definition lworld_on_atom_swap_back
    (x y : atom) (D : lvset)
    (w : LWorldOn (lvars_swap x y D)) : LWorldOn D.
Proof.
  refine {| lw := lres_swap (LVFree x) (LVFree y) (lw w) |}.
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

Lemma lworld_on_lift_atom_swap_back
    (x y : atom) (D : lvset) (m : WfWorld)
    (Hlc_sw : lc_lvars (lvars_swap x y D))
    (Hsub_sw : lvars_fv (lvars_swap x y D) ⊆
      world_dom (res_atom_swap x y m : World))
    (Hlc : lc_lvars D)
    (Hsub : lvars_fv D ⊆ world_dom (m : World)) :
  lworld_on_atom_swap_back x y D
    (lworld_on_lift (lvars_swap x y D)
      (res_atom_swap x y m) Hlc_sw Hsub_sw) =
  lworld_on_lift D m Hlc Hsub.
Proof.
  apply lworld_on_ext.
  unfold lworld_on_atom_swap_back, lworld_on_lift.
  cbn [lw].
  rewrite lvars_fv_swap.
  rewrite res_restrict_atom_swap.
  rewrite res_lift_free_atom_swap.
  change (lres_swap (LVFree x) (LVFree y)
    (@resA_restrict logic_var _ _ V
      (lres_swap (LVFree x) (LVFree y)
        (res_lift_free (res_restrict m (lvars_fv D))))
      (lvars_swap x y D)) =
    @resA_restrict logic_var _ _ V
      (res_lift_free (res_restrict m (lvars_fv D))) D).
  change (lres_swap (LVFree x) (LVFree y)
    (@resA_restrict logic_var _ _ V
      (lres_swap (LVFree x) (LVFree y)
        (res_lift_free (res_restrict m (lvars_fv D))))
      (set_swap (LVFree x) (LVFree y) D)) =
    @resA_restrict logic_var _ _ V
      (res_lift_free (res_restrict m (lvars_fv D))) D).
  rewrite lres_restrict_swap.
  rewrite lres_swap_involutive.
  reflexivity.
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

Notation "m1 '##ᵣ' m2" := (world_compat m1 m2)
  (at level 70, no associativity,
   format "m1  ##ᵣ  m2") : resource_scope.
Notation "m1 '×[' Hc ']' m2" := (res_product m1 m2 Hc)
  (at level 40, Hc at level 200, left associativity,
   format "m1  ×[ Hc ]  m2") : resource_scope.
Notation "m1 '+[' Hdef ']' m2" := (res_sum m1 m2 Hdef)
  (at level 50, Hdef at level 200, left associativity,
   format "m1  +[ Hdef ]  m2") : resource_scope.
Lemma res_atom_swap_involutive x y (w : WfWorld) :
  res_atom_swap x y (res_atom_swap x y w) = w.
Proof. apply resA_swap_involutive. Qed.

Lemma raw_le_atom_swap x y (w1 w2 : WfWorld) :
  w1 ⊑ w2 ->
  res_atom_swap x y w1 ⊑ res_atom_swap x y w2.
Proof.
  intros Hle.
  unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in *.
  apply worldA_ext.
  - simpl.
    pose proof (rawA_le_dom (w1 : World) (w2 : World) Hle) as Hdom.
    set_solver.
  - intros σ. simpl. split.
    + intros [σ1 [Hσ1 Hσeq]]. subst σ.
      rewrite Hle in Hσ1.
      destruct Hσ1 as [σ2 [Hσ2 Hrestrict]].
      exists (storeA_swap x y σ2). split.
      * exists σ2. split; [exact Hσ2 | reflexivity].
      * rewrite <- Hrestrict.
        apply storeA_restrict_swap.
    + intros [σ2sw [[σ2 [Hσ2 Hσ2eq]] Hrestrict_sw]]. subst σ2sw.
      exists (storeA_restrict σ2 (world_dom (w1 : World))). split.
      * rewrite Hle. exists σ2. split; [exact Hσ2 | reflexivity].
      * rewrite <- Hrestrict_sw.
        symmetry. apply storeA_restrict_swap.
Qed.

Lemma res_subset_atom_swap x y (w1 w2 : WfWorld) :
  res_subset w1 w2 ->
  res_subset (res_atom_swap x y w1) (res_atom_swap x y w2).
Proof.
  intros [Hdom Hsub]. split.
  - rewrite !world_dom_res_atom_swap. f_equal. exact Hdom.
  - intros σ [σ0 [Hσ0 Hσeq]]. subst σ.
    exists σ0. split; [auto | reflexivity].
Qed.

Lemma world_compat_atom_swap x y (w1 w2 : WfWorld) :
  world_compat (w1 : World) (w2 : World) ->
  world_compat (res_atom_swap x y w1 : World)
    (res_atom_swap x y w2 : World).
Proof.
  intros Hc σ1 σ2 [σ1' [Hσ1' Hσ1eq]] [σ2' [Hσ2' Hσ2eq]].
  subst σ1 σ2.
  apply (proj2 (storeA_compat_swap x y σ1' σ2')).
  eapply Hc; eauto.
Qed.

Lemma raw_sum_defined_atom_swap x y (w1 w2 : WfWorld) :
  raw_sum_defined (w1 : World) (w2 : World) ->
  raw_sum_defined (res_atom_swap x y w1 : World)
    (res_atom_swap x y w2 : World).
Proof.
  intros Hdef.
  unfold raw_sum_defined, rawA_sum_defined in *.
  rewrite !world_dom_res_atom_swap. f_equal. exact Hdef.
Qed.

Lemma res_product_r_eq
    (w1 w2 w2' : WfWorld)
    (Hc : world_compat (w1 : World) (w2 : World))
    (Hc' : world_compat (w1 : World) (w2' : World)) :
  w2 = w2' ->
  res_product w1 w2 Hc = res_product w1 w2' Hc'.
Proof.
  intros ->. unfold res_product. f_equal. apply proof_irrelevance.
Qed.

Lemma res_product_l_eq
    (w1 w1' w2 : WfWorld)
    (Hc : world_compat (w1 : World) (w2 : World))
    (Hc' : world_compat (w1' : World) (w2 : World)) :
  w1 = w1' ->
  res_product w1 w2 Hc = res_product w1' w2 Hc'.
Proof.
  intros ->. unfold res_product. f_equal. apply proof_irrelevance.
Qed.

Lemma res_product_atom_swap_eq x y
    (w1 w2 : WfWorld)
    (Hc : world_compat (w1 : World) (w2 : World))
    (Hc_sw : world_compat (res_atom_swap x y w1 : World)
      (res_atom_swap x y w2 : World)) :
  res_product (res_atom_swap x y w1) (res_atom_swap x y w2) Hc_sw =
  res_atom_swap x y (res_product w1 w2 Hc).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - change (set_swap x y (world_dom (w1 : World)) ∪
      set_swap x y (world_dom (w2 : World)) =
      set_swap x y (world_dom (w1 : World) ∪ world_dom (w2 : World))).
    rewrite set_swap_union. reflexivity.
  - intros σ. split.
    + intros [σ1 [σ2 [[σ1' [Hσ1' Hσ1eq]]
        [[σ2' [Hσ2' Hσ2eq]] [Hcompat Hσeq]]]]].
      subst σ1 σ2 σ.
      exists (@union (gmap atom V) _ σ1' σ2'). split.
      * exists σ1', σ2'. repeat split; eauto.
      * exact (storeA_swap_union x y σ1' σ2').
    + intros [σ0 [[σ1 [σ2 [Hσ1 [Hσ2 [Hcompat Hσ0eq]]]]] Hσeq]].
      subst σ0 σ.
      exists (storeA_swap x y σ1), (storeA_swap x y σ2).
      repeat split.
      * exists σ1. split; [exact Hσ1 | reflexivity].
      * exists σ2. split; [exact Hσ2 | reflexivity].
      * apply (proj2 (storeA_compat_swap x y σ1 σ2)). exact Hcompat.
      * apply storeA_swap_union.
Qed.

Lemma res_sum_atom_swap_eq x y
    (w1 w2 : WfWorld)
    (Hdef : raw_sum_defined (w1 : World) (w2 : World))
    (Hdef_sw : raw_sum_defined (res_atom_swap x y w1 : World)
      (res_atom_swap x y w2 : World)) :
  res_sum (res_atom_swap x y w1) (res_atom_swap x y w2) Hdef_sw =
  res_atom_swap x y (res_sum w1 w2 Hdef).
Proof.
  apply wfworldA_ext. apply worldA_ext.
  - change (set_swap x y (world_dom (w1 : World)) =
      set_swap x y (world_dom (w1 : World))).
    reflexivity.
  - intros σ. split.
    + intros [[σ0 [Hσ0 Hσeq]] | [σ0 [Hσ0 Hσeq]]]; subst σ.
      * exists σ0. split; [left; exact Hσ0 | reflexivity].
      * exists σ0. split; [right; exact Hσ0 | reflexivity].
    + intros [σ0 [[Hσ0 | Hσ0] Hσeq]]; subst σ.
      * left. exists σ0. split; [exact Hσ0 | reflexivity].
      * right. exists σ0. split; [exact Hσ0 | reflexivity].
Qed.

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

Lemma res_fiber_from_projection_store_dom_subset
    (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  dom (σ : StoreT) ⊆ X.
Proof.
  intros [Hproj _] a Ha.
  pose proof (wfworld_store_dom (res_restrict m X) σ Hproj) as Hdom.
  change (dom (σ : StoreT) = world_dom (res_restrict m X : World)) in Hdom.
  rewrite Hdom in Ha. simpl in Ha.
  set_solver.
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

Lemma res_fiber_from_projection_store_restrict
    (m mfib : WfWorld) (X : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  store_restrict τ (dom (σ : StoreT)) = σ.
Proof.
  intros [Hproj Hfib] Hτ.
  destruct mfib as [wmfib Hwfib].
  cbn [raw_world raw_worldA world_stores] in Hτ, Hfib.
  change (wmfib = rawA_fiber (m : World) σ) in Hfib.
  change (wmfib τ) in Hτ.
  rewrite Hfib in Hτ.
  destruct Hτ as [_ Hτ].
  exact Hτ.
Qed.

Lemma res_fiber_from_projection_store_restrict_substore
    (m mfib : WfWorld) (X Y : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  store_restrict τ (dom (store_restrict σ Y : StoreT)) =
    store_restrict σ Y.
Proof.
  intros Hproj Hτ.
  pose proof (res_fiber_from_projection_store_restrict
    m mfib X σ τ Hproj Hτ) as Hfixed.
  apply storeA_map_eq. intros a.
  rewrite !storeA_restrict_lookup.
  destruct (decide (a ∈ dom (store_restrict σ Y : StoreT))) as [Ha|Ha].
  - apply elem_of_dom in Ha as [v Hv].
    apply storeA_restrict_lookup_some in Hv as [HaY Hσa].
    assert (Hτa : τ !! a = Some v).
    {
      assert (Hτrestrict :
        (store_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
        Some v).
      { rewrite Hfixed. exact Hσa. }
      apply storeA_restrict_lookup_some in Hτrestrict as [_ Hτa].
      exact Hτa.
    }
    rewrite decide_True by exact HaY.
    rewrite Hσa. exact Hτa.
  - destruct (decide (a ∈ Y)) as [HaY|HaY]; [|reflexivity].
    destruct (σ !! a) as [v|] eqn:Hσa; [|reflexivity].
    exfalso. apply Ha. apply elem_of_dom. exists v.
    apply storeA_restrict_lookup_some_2; [exact Hσa|exact HaY].
Qed.

Lemma res_fiber_from_projection_drop_fixed_domain
    (m mfib : WfWorld) (Y : aset) (σ σfix : StoreT) :
  (forall τ, (m : World) τ ->
    store_restrict τ (dom (σfix : StoreT)) = σfix) ->
  res_fiber_from_projection m Y σ mfib ->
  res_fiber_from_projection m
    (Y ∖ dom (σfix : StoreT))
    (store_restrict σ (Y ∖ dom (σfix : StoreT))) mfib.
Proof.
  intros Hfixed [Hproj Hfib].
  destruct Hproj as [τ0 [Hτ0 Hτ0Y]].
  split.
  - exists τ0. split; [exact Hτ0|].
    rewrite <- Hτ0Y.
    rewrite storeA_restrict_restrict.
    replace (Y ∩ (Y ∖ dom (σfix : StoreT)))
      with (Y ∖ dom (σfix : StoreT)) by set_solver.
    reflexivity.
  - destruct mfib as [wmfib Hwfib].
    cbn [proj1_sig] in Hfib |- *.
    change (wmfib = rawA_fiber (m : World) σ) in Hfib.
    change (wmfib =
      rawA_fiber (m : World)
        (store_restrict σ (Y ∖ dom (σfix : StoreT)))).
    rewrite Hfib.
    apply world_ext.
    + reflexivity.
    + intros τ. cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores].
      split.
      * intros [Hτ HτY]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        rewrite !storeA_restrict_lookup.
        destruct (decide
          (a ∈ dom (storeA_restrict σ (Y ∖ dom (σfix : StoreT)) :
            gmap atom V)))
          as [Haσres|Haσres].
        -- destruct (decide (a ∈ Y ∖ dom (σfix : StoreT))) as [HaYfix|Hbad].
           2:{
             exfalso. apply Hbad.
             pose proof Haσres as Haσres_dom.
             rewrite storeA_restrict_dom in Haσres_dom.
             set_solver.
           }
           pose proof Haσres as Haσres_dom.
           rewrite storeA_restrict_dom in Haσres_dom.
           assert (Haσ : a ∈ dom (σ : StoreT)) by set_solver.
           destruct (σ !! a) as [va|] eqn:Hσa.
           2:{ apply not_elem_of_dom in Hσa. contradiction. }
           assert (Hτa : τ !! a = Some va).
           {
             assert ((storeA_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
               Some va) as Hrt.
             { rewrite HτY. exact Hσa. }
             apply storeA_restrict_lookup_some in Hrt as [_ Hrt].
             exact Hrt.
           }
           exact Hτa.
        -- destruct (decide (a ∈ Y ∖ dom (σfix : StoreT))) as [HaYfix|_];
             [|reflexivity].
           assert (Haσnone : σ !! a = None).
           {
             apply not_elem_of_dom.
             intros Haσ.
             apply Haσres.
             rewrite storeA_restrict_dom.
             set_solver.
           }
           symmetry. exact Haσnone.
      * intros [Hτ Hτres]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        destruct (decide (a ∈ dom (σ : StoreT))) as [Haσ|Haσ].
        2:{
          rewrite storeA_restrict_lookup_none_r by exact Haσ.
          apply not_elem_of_dom in Haσ. symmetry. exact Haσ.
        }
        rewrite storeA_restrict_lookup.
        destruct (decide (a ∈ dom (σ : StoreT))) as [_|Hbad];
          [|contradiction].
        pose proof (wfworld_store_dom m τ0 Hτ0) as Hdomτ0.
        change (dom (τ0 : StoreT) = world_dom (m : World)) in Hdomτ0.
        assert (HaY : a ∈ Y).
        {
          rewrite <- Hτ0Y in Haσ.
          rewrite storeA_restrict_dom, Hdomτ0 in Haσ.
          set_solver.
        }
        destruct (decide (a ∈ dom (σfix : StoreT))) as [Hafix|Hafix].
        -- assert (Hτfix : τ !! a = σfix !! a).
           {
             rewrite <- (Hfixed τ Hτ).
             symmetry.
             change ((storeA_restrict τ (dom (σfix : StoreT)) : StoreT) !! a =
               τ !! a).
             destruct (τ !! a) as [va|] eqn:Hτa.
             - apply storeA_restrict_lookup_some_2; [exact Hτa|exact Hafix].
             - apply storeA_restrict_lookup_none_l. exact Hτa.
           }
           assert (Hτ0fix : τ0 !! a = σfix !! a).
           {
             rewrite <- (Hfixed τ0 Hτ0).
             symmetry.
             change ((storeA_restrict τ0 (dom (σfix : StoreT)) : StoreT) !! a =
               τ0 !! a).
             destruct (τ0 !! a) as [va|] eqn:Hτ0a.
             - apply storeA_restrict_lookup_some_2; [exact Hτ0a|exact Hafix].
             - apply storeA_restrict_lookup_none_l. exact Hτ0a.
           }
           transitivity (σfix !! a); [exact Hτfix|].
           transitivity (τ0 !! a); [symmetry; exact Hτ0fix|].
           rewrite <- Hτ0Y.
           rewrite storeA_restrict_lookup.
           destruct (decide (a ∈ Y)) as [_|Hbad]; [reflexivity|contradiction].
        -- assert (HaYfix : a ∈ Y ∖ dom (σfix : StoreT)) by set_solver.
           assert (Haσres :
             a ∈ dom (storeA_restrict σ (Y ∖ dom (σfix : StoreT)) :
               gmap atom V)).
           { rewrite storeA_restrict_dom. set_solver. }
           transitivity
             ((storeA_restrict τ
               (dom (storeA_restrict σ (Y ∖ dom (σfix : StoreT)) :
                 gmap atom V)) : StoreT) !! a).
           ++ symmetry.
              destruct (τ !! a) as [va|] eqn:Hτa.
              ** apply storeA_restrict_lookup_some_2; [exact Hτa|exact Haσres].
              ** apply storeA_restrict_lookup_none_l. exact Hτa.
           ++ rewrite Hτres.
              destruct (σ !! a) as [va|] eqn:Hσa.
              ** apply storeA_restrict_lookup_some_2; [exact Hσa|exact HaYfix].
              ** apply storeA_restrict_lookup_none_l. exact Hσa.
Qed.

Lemma res_fiber_from_projection_add_fixed_domain
    (m mfib : WfWorld) (Y : aset) (σres σfix : StoreT) :
  (forall τ, (m : World) τ ->
    store_restrict τ (dom (σfix : StoreT)) = σfix) ->
  res_fiber_from_projection m
    (Y ∖ dom (σfix : StoreT)) σres mfib ->
  res_fiber_from_projection m Y
    (store_restrict σfix Y ∪ σres) mfib.
Proof.
  intros Hfixed Hres.
  pose proof (res_fiber_from_projection_store_dom_subset
    m mfib (Y ∖ dom (σfix : StoreT)) σres Hres) as Hres_dom.
  destruct Hres as [[τ0 [Hτ0 Hτ0res]] Hfib].
  split.
  - exists τ0. split; [exact Hτ0|].
    apply storeA_map_eq. intros a.
    rewrite storeA_restrict_lookup.
    destruct (decide (a ∈ Y)) as [HaY|HaY].
    + destruct (decide (a ∈ dom (σfix : StoreT))) as [Hafix|Hafix].
      * assert (Hτ0fix_a : τ0 !! a = σfix !! a).
        {
          apply elem_of_dom in Hafix as [va Hva].
          assert (Hlook :
              (store_restrict τ0 (dom (σfix : StoreT)) : StoreT) !! a =
              Some va).
          { rewrite Hfixed by exact Hτ0. exact Hva. }
          apply storeA_restrict_lookup_some in Hlook as [_ Hτ0a].
          change ((τ0 : gmap atom V) !! a =
            (σfix : gmap atom V) !! a).
          exact (eq_trans Hτ0a (eq_sym Hva)).
        }
        assert (Hafix_dom : a ∈ dom (σfix : StoreT)) by exact Hafix.
        apply elem_of_dom in Hafix as [va Hva].
        transitivity (Some va).
        -- change ((τ0 : gmap atom V) !! a = Some va).
           rewrite Hτ0fix_a. exact Hva.
        -- symmetry.
	           transitivity ((store_restrict σfix Y : StoreT) !! a).
		           ++ apply lookup_union_l.
		              apply not_elem_of_dom.
		              intros Hares.
		              pose proof (Hres_dom a Hares) as HaresYfix.
		              apply elem_of_difference in HaresYfix as [_ Hanotfix].
		              exact (Hanotfix Hafix_dom).
	           ++ assert (HfixY :
	                (store_restrict σfix Y : StoreT) !! a = Some va).
	              { eapply storeA_restrict_lookup_some_2; [exact Hva|exact HaY]. }
	              exact HfixY.
      * assert (Hτ0res_a : τ0 !! a = σres !! a).
        {
          destruct (σres !! a) as [va|] eqn:Hresa.
          - assert (Hlook :
                (store_restrict τ0 (Y ∖ dom (σfix : StoreT)) : StoreT) !! a =
                Some va).
	            { rewrite Hτ0res. exact Hresa. }
	            apply storeA_restrict_lookup_some in Hlook as [_ Hτ0a].
	            exact Hτ0a.
	          - assert (Hlook :
	                (store_restrict τ0 (Y ∖ dom (σfix : StoreT)) : StoreT) !! a =
	                None).
	            { rewrite Hτ0res. exact Hresa. }
	            destruct (τ0 !! a) as [va|] eqn:Hτ0a; [|reflexivity].
	            exfalso.
	            assert (Hsome :
	                (store_restrict τ0 (Y ∖ dom (σfix : StoreT)) : StoreT)
                  !! a = Some va).
	            {
	              eapply storeA_restrict_lookup_some_2;
	                [exact Hτ0a|set_solver].
	            }
	            rewrite Hlook in Hsome. discriminate.
        }
	        transitivity (σres !! a); [exact Hτ0res_a|].
	        symmetry.
	        apply lookup_union_r.
	        apply storeA_restrict_lookup_none_l.
	        apply not_elem_of_dom. exact Hafix.
    + symmetry.
      apply map_lookup_union_None. split.
      * apply storeA_restrict_lookup_none_r. exact HaY.
      * apply not_elem_of_dom.
        intros Hares. apply Hres_dom in Hares. set_solver.
  - destruct mfib as [wmfib Hwfib].
    cbn [proj1_sig] in Hfib |- *.
    change (wmfib = rawA_fiber (m : World) σres) in Hfib.
    change (wmfib =
      rawA_fiber (m : World) (store_restrict σfix Y ∪ σres)).
    rewrite Hfib.
    apply world_ext.
    + reflexivity.
    + intros τ. cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores].
      split.
      * intros [Hτ Hτres]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        destruct (decide
          (a ∈ dom (store_restrict σfix Y ∪ σres : StoreT))) as [Hafull|Hafull].
	        -- rewrite storeA_restrict_lookup.
	           destruct (decide (a ∈ dom (store_restrict σfix Y ∪ σres : StoreT)))
	             as [_|Hbad]; [|contradiction].
	           destruct ((store_restrict σfix Y : StoreT) !! a) as [vfix|] eqn:Hfixlook.
	           ++ pose proof Hfixlook as Hfixlook_some.
	              apply storeA_restrict_lookup_some in Hfixlook_some
	                as [HaYfix Hσfixa].
	              assert (Hτfix_a : τ !! a = Some vfix).
	              {
	                assert (Hlook :
	                    (store_restrict τ (dom (σfix : StoreT)) : StoreT) !! a =
	                    Some vfix).
	                { rewrite Hfixed by exact Hτ. exact Hσfixa. }
	                apply storeA_restrict_lookup_some in Hlook as [_ Hτa].
	                exact Hτa.
	              }
	              transitivity (Some vfix); [exact Hτfix_a|].
	              symmetry.
	              transitivity ((store_restrict σfix Y : StoreT) !! a).
	              ** apply lookup_union_l.
	                 apply not_elem_of_dom.
	                 intros Hares.
	                 pose proof (Hres_dom a Hares) as HaresYfix.
	                 apply elem_of_difference in HaresYfix as [_ Hanotfix].
	                 apply Hanotfix. eapply elem_of_dom_2. exact Hσfixa.
	              ** exact Hfixlook.
	           ++ pose proof Hafull as Hafull_dom.
	              assert (Hares : a ∈ dom (σres : StoreT)).
	              {
	                destruct (σres !! a) as [vres|] eqn:Hreslook.
	                - eapply elem_of_dom_2. exact Hreslook.
	                - exfalso.
	                  assert (Hunion_none :
	                    (store_restrict σfix Y ∪ σres : StoreT) !! a = None).
	                  {
	                    apply map_lookup_union_None. split; assumption.
	                  }
	                  apply not_elem_of_dom in Hunion_none.
	                  exact (Hunion_none Hafull_dom).
	              }
	              assert (Hτres_a : τ !! a = σres !! a).
	              {
	                destruct (σres !! a) as [vres|] eqn:Hreslook.
	                - assert (Hlook :
	                    (store_restrict τ (dom (σres : StoreT)) : StoreT) !! a =
	                    Some vres).
	                  { rewrite Hτres. exact Hreslook. }
	                  apply storeA_restrict_lookup_some in Hlook as [_ Hτa].
	                  exact Hτa.
	                - exfalso. apply not_elem_of_dom in Hreslook.
	                  contradiction.
	              }
	              transitivity (σres !! a); [exact Hτres_a|].
	              symmetry.
	              apply lookup_union_r.
	              exact Hfixlook.
        -- rewrite storeA_restrict_lookup_none_r by exact Hafull.
           apply not_elem_of_dom in Hafull. symmetry. exact Hafull.
      * intros [Hτ Hτfull]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        destruct (decide (a ∈ dom (σres : StoreT))) as [Hares|Hares].
        -- rewrite storeA_restrict_lookup.
           destruct (decide (a ∈ dom (σres : StoreT))) as [_|Hbad];
             [|contradiction].
	           pose proof Hares as HaresY.
	           apply Hres_dom in HaresY.
	           assert (Hanotfix : a ∉ dom (σfix : StoreT)) by set_solver.
	           apply elem_of_dom in Hares as [vres Hreslook].
	           assert (Hleft_none : (store_restrict σfix Y : StoreT) !! a = None).
	           {
	             apply storeA_restrict_lookup_none_l.
	             apply not_elem_of_dom. exact Hanotfix.
	           }
	           assert (Hfull_lookup :
	             (store_restrict σfix Y ∪ σres : StoreT) !! a = Some vres).
	           {
	             transitivity (σres !! a).
	             - apply lookup_union_r. exact Hleft_none.
	             - exact Hreslook.
	           }
	           assert (Hτa : τ !! a = Some vres).
	           {
	             assert (Hrestrict :
	               (store_restrict τ
	                 (dom (store_restrict σfix Y ∪ σres : StoreT)) : StoreT)
	               !! a = Some vres).
	             { rewrite Hτfull. exact Hfull_lookup. }
	             apply storeA_restrict_lookup_some in Hrestrict as [_ Hτa].
	             exact Hτa.
	           }
	           change ((τ : gmap atom V) !! a = (σres : gmap atom V) !! a).
	           rewrite Hτa, Hreslook. reflexivity.
        -- rewrite storeA_restrict_lookup_none_r by exact Hares.
           apply not_elem_of_dom in Hares. symmetry. exact Hares.
Qed.

Lemma res_subset_fiber_source
    (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  res_subset mfib m.
Proof.
  intros Hfib.
  split.
  - destruct Hfib as [_ Hfib_eq].
    change ((mfib : World) = raw_fiber (m : World) σ) in Hfib_eq.
    pose proof (f_equal world_dom Hfib_eq) as Hdom.
    change (world_dom (mfib : World) = world_dom (m : World)) in Hdom.
    exact Hdom.
  - intros τ Hτ.
    eapply res_fiber_from_projection_store_source; eauto.
Qed.

Lemma res_fiber_from_projection_of_store
    (m : WfWorld) (X : aset) (σ : StoreT) :
  X ⊆ world_dom (m : World) ->
  (m : World) σ ->
  exists mfib,
    res_fiber_from_projection m X (store_restrict σ X) mfib /\
    (mfib : World) σ.
Proof.
  intros HX Hσ.
  set (σX := store_restrict σ X).
  assert (HdomσX : dom (σX : StoreT) = X).
  {
    subst σX.
    change (dom (storeA_restrict σ X : gmap atom V) = X).
    rewrite (storeA_restrict_dom σ X).
    rewrite (wfworld_store_dom m σ Hσ).
    apply set_eq. intros a. split.
    - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    - intros Ha. apply elem_of_intersection. split; [apply HX|]; exact Ha.
  }
  assert (Hne :
      exists σ0,
        (m : World) σ0 /\
        storeA_restrict σ0 (dom (σX : StoreT)) = σX).
  {
    exists σ. split; [exact Hσ|].
    rewrite HdomσX. reflexivity.
  }
  exists (resA_fiber m σX Hne).
  split.
  - split.
    + exists σ. split; [exact Hσ|reflexivity].
    + reflexivity.
  - cbn [raw_world raw_worldA world_stores rawA_fiber].
    split; [exact Hσ|].
    change (storeA_restrict σ (dom (σX : StoreT)) = σX).
    rewrite HdomσX.
    subst σX. reflexivity.
Qed.

Lemma res_fiber_from_projection_atom_swap
    x y (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  res_fiber_from_projection
    (res_atom_swap x y m) (set_swap x y X)
    (storeA_swap x y σ) (res_atom_swap x y mfib).
Proof.
  intros [Hproj Hfib]. split.
  - destruct Hproj as [σ0 [Hσ0 Hrestrict]]. subst σ.
    exists (storeA_swap x y σ0). split.
    + exists σ0. split; [exact Hσ0 | reflexivity].
    + apply storeA_restrict_swap.
  - apply world_ext.
    + pose proof (f_equal world_dom Hfib) as Hdomfib.
      simpl in Hdomfib.
      change (world_dom (mfib : World) = world_dom (m : World)) in Hdomfib.
      change (set_swap x y (world_dom (mfib : World)) =
        set_swap x y (world_dom (m : World))).
      rewrite Hdomfib. reflexivity.
    + intros τ. simpl. split.
      * intros [τ0 [Hmfib Hτ]].
        subst τ.
        rewrite Hfib in Hmfib.
        destruct Hmfib as [Hm Hrestrict].
        split.
        -- exists τ0. split; [exact Hm | reflexivity].
        -- rewrite storeA_swap_dom.
           change (storeA_restrict (storeA_swap x y τ0)
             (set_swap x y (dom σ)) = storeA_swap x y σ).
           rewrite storeA_restrict_swap.
           rewrite Hrestrict. reflexivity.
      * intros [[τ0 [Hm Hτ]] Hrestrict].
        subst τ.
        exists τ0. split.
        -- rewrite Hfib. split; [exact Hm |].
           rewrite storeA_swap_dom in Hrestrict.
           change (storeA_restrict (storeA_swap x y τ0)
             (set_swap x y (dom σ)) = storeA_swap x y σ) in Hrestrict.
           rewrite storeA_restrict_swap in Hrestrict.
           apply (f_equal (storeA_swap x y)) in Hrestrict.
           rewrite !storeA_swap_involutive in Hrestrict.
           exact Hrestrict.
        -- reflexivity.
Qed.



(** * Concrete resource key action and order interface lemmas *)




Lemma res_restrict_restrict_eq (w : WfWorld) (X Y : aset) :
  res_restrict (res_restrict w X) Y =
  res_restrict w (X ∩ Y).
Proof. apply resA_restrict_restrict_eq. Qed.

Lemma res_restrict_dom (w : WfWorld) (X : aset) :
  world_dom (res_restrict w X : World) = world_dom (w : World) ∩ X.
Proof. reflexivity. Qed.

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

Lemma res_le_of_restrict_eq (m n p : WfWorld) :
  m ⊑ n ->
  res_restrict p (world_dom (n : World)) = n ->
  m ⊑ p.
Proof.
  intros Hmn Hnp.
  assert (Hn_p : n ⊑ p).
  {
    rewrite <- Hnp. apply res_restrict_le.
  }
  etransitivity; eauto.
Qed.

Lemma res_le_of_projection_eq (m p : WfWorld) :
  res_restrict p (world_dom (m : World)) = m ->
  m ⊑ p.
Proof.
  intros Hproj.
  eapply res_le_of_restrict_eq; [apply raw_le_refl|exact Hproj].
Qed.

Lemma res_le_store_lift
    (m n : WfWorld) (σ : StoreT) :
  m ⊑ n ->
  (m : World) σ ->
  exists σn,
    (n : World) σn /\
    store_restrict σn (world_dom (m : World)) = σ.
Proof.
  intros Hle Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert (Hσrestrict :
      (res_restrict n (world_dom (m : World)) : World) σ).
  { rewrite Hrestrict. exact Hσ. }
  cbn [res_restrict raw_world raw_worldA world_stores] in Hσrestrict.
  destruct Hσrestrict as [σn [Hσn Hσn_restrict]].
  exists σn. split; [exact Hσn|exact Hσn_restrict].
Qed.

Lemma res_restrict_self_dom (m : WfWorld) (X : aset) :
  res_restrict m (world_dom (res_restrict m X : World)) =
  res_restrict m X.
Proof.
  apply res_restrict_eq_of_le. apply res_restrict_le.
Qed.

Lemma res_restrict_delete_notin (m : WfWorld) x :
  x ∉ world_dom
    (res_restrict m (world_dom (m : World) ∖ {[x]}) : World).
Proof.
  rewrite res_restrict_dom. better_set_solver.
Qed.

Lemma res_restrict_delete_insert_dom (m : WfWorld) x :
  x ∈ world_dom (m : World) ->
  world_dom (m : World) =
    world_dom
      (res_restrict m (world_dom (m : World) ∖ {[x]}) : World) ∪ {[x]}.
Proof.
  intros Hx.
  rewrite res_restrict_dom.
  replace (world_dom (m : World) ∩
    (world_dom (m : World) ∖ {[x]}))
    with (world_dom (m : World) ∖ {[x]}) by better_set_solver.
  apply set_eq. intros z. split.
  - intros Hz.
    destruct (decide (z = x)) as [->|Hzx].
    + apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    + apply elem_of_union_l. apply elem_of_difference. split; [exact Hz|].
      intros Hzsingle. apply elem_of_singleton in Hzsingle. congruence.
  - intros Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_difference in Hz as [Hz _]. exact Hz.
    + apply elem_of_singleton in Hz. subst z. exact Hx.
Qed.

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

Lemma world_compat_of_disjoint_dom (m n : WfWorld) :
  world_dom (m : World) ## world_dom (n : World) →
  world_compat m n.
Proof.
  intros Hdisj.
  apply disj_dom_worldA_compat.
  set_solver.
Qed.

Lemma world_compat_restrict_overlap
    (n m : WfWorld) (X Y S : aset) :
  X ∩ Y ⊆ S ->
  world_compat n (res_restrict m S) ->
  world_compat (res_restrict n X) (res_restrict m Y).
Proof. apply worldA_compat_restrict_overlap. Qed.

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

Lemma res_product_dom (w1 w2 : WfWorld)
    (Hc : world_compat w1 w2) :
  world_dom (res_product w1 w2 Hc : World) =
  world_dom (w1 : World) ∪ world_dom (w2 : World).
Proof. reflexivity. Qed.

Lemma res_product_restrict_singleton_delete_dom
    (marg mframe : WfWorld) x
    (Hc : world_compat (res_restrict marg ({[x]} : aset))
      (res_restrict mframe (world_dom (mframe : World) ∖ {[x]}))) :
  x ∈ world_dom (marg : World) ->
  world_dom
    (res_product (res_restrict marg ({[x]} : aset))
      (res_restrict mframe (world_dom (mframe : World) ∖ {[x]})) Hc
      : World) =
    world_dom
      (res_restrict mframe (world_dom (mframe : World) ∖ {[x]}) : World) ∪
      {[x]}.
Proof.
  intros Hx.
  rewrite !res_restrict_dom.
  change ((world_dom (marg : World) ∩ {[x]}) ∪
    (world_dom (mframe : World) ∩ (world_dom (mframe : World) ∖ {[x]})) =
    (world_dom (mframe : World) ∩ (world_dom (mframe : World) ∖ {[x]})) ∪
      {[x]}).
  assert (Hsingle :
      world_dom (marg : World) ∩ ({[x]} : aset) = ({[x]} : aset)).
  {
    apply set_eq. intros z. split.
    - intros Hz. apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
    - intros Hz. apply elem_of_intersection. split; [|exact Hz].
      apply elem_of_singleton in Hz. subst z. exact Hx.
  }
  rewrite Hsingle.
  apply set_eq. intros z. split.
  - intros Hz. apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_union_r. exact Hz.
    + apply elem_of_union_l. exact Hz.
  - intros Hz. apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_union_r. exact Hz.
    + apply elem_of_union_l. exact Hz.
Qed.

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

Lemma res_product_restrict_frame_common_eq
    (n m : WfWorld) (X S C Y : aset)
    (Hc_common : world_compat (res_restrict n X) (res_restrict m C))
    (Hc_tgt : world_compat n (res_restrict m S)) :
  S ⊆ C ->
  Y ⊆ (X ∩ world_dom (n : World)) ∪
        (S ∩ world_dom (m : World)) ->
  res_restrict
    (res_product (res_restrict n X) (res_restrict m C) Hc_common)
    Y =
    res_restrict (res_product n (res_restrict m S) Hc_tgt) Y.
Proof. apply resA_product_restrict_frame_common_eq. Qed.

Lemma res_product_restrict_frame_r_eq
    (n m : WfWorld) (S Y : aset)
    (Hc : world_compat n m)
    (HcS : world_compat n (res_restrict m S)) :
  S ⊆ world_dom (m : World) ->
  Y ⊆ world_dom (n : World) ∪ S ->
  res_restrict (res_product n (res_restrict m S) HcS) Y =
  res_restrict (res_product n m Hc) Y.
Proof.
  intros HSm HY.
  set (X := world_dom (n : World)).
  set (C := world_dom (m : World)).
  assert (Hn_full : res_restrict n X = n).
  { subst X. apply res_restrict_eq_of_le. apply raw_le_refl. }
  assert (Hm_full : res_restrict m C = m).
  { subst C. apply res_restrict_eq_of_le. apply raw_le_refl. }
  assert (Hc_common :
      world_compat (res_restrict n X) (res_restrict m C)).
  { rewrite Hn_full, Hm_full. exact Hc. }
  pose proof (res_product_restrict_frame_common_eq
    n m X S C Y Hc_common HcS ltac:(subst C; exact HSm))
    as Heq.
  assert (HY' : Y ⊆ (X ∩ world_dom (n : World)) ∪
                  (S ∩ world_dom (m : World))).
  {
    subst X. intros z Hz.
	    pose proof (HY z Hz) as HzNS.
	    apply elem_of_union in HzNS as [HzN|HzS].
	    - apply elem_of_union_l. set_solver.
	    - apply elem_of_union_r. apply elem_of_intersection.
	      split; [exact HzS|apply HSm; exact HzS].
	  }
	  specialize (Heq HY').
	  assert (Hcommon_full :
	      res_product (res_restrict n X) (res_restrict m C) Hc_common =
	      res_product n m Hc).
	  {
	    assert (Hc_nC : world_compat n (res_restrict m C)).
	    { eapply world_compat_le_r; [apply res_restrict_le|exact Hc]. }
	    transitivity (res_product n (res_restrict m C) Hc_nC).
	    - eapply res_product_l_eq. exact Hn_full.
	    - eapply res_product_r_eq. exact Hm_full.
	  }
  rewrite Hcommon_full in Heq.
  symmetry. exact Heq.
Qed.

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

Lemma res_product_restrict_binder_arg_compat_dom
    (m n marg : WfWorld) (C X A : aset)
    (Hc_tgt : world_compat marg n) :
  res_restrict m C = res_restrict n C ->
  C ⊆ world_dom (m : World) ->
  A ## world_dom (m : World) ->
  A ## world_dom (n : World) ->
  world_dom (res_product marg n Hc_tgt : World) =
    world_dom (n : World) ∪ A ->
  X ⊆ C ∪ A ->
  A ⊆ X ->
  exists Hc_src : world_compat (res_restrict marg X) m,
    world_dom (res_product (res_restrict marg X) m Hc_src : World) =
      world_dom (m : World) ∪ A.
Proof.
  intros Hmn HCm HAm HAn Hdom_tgt HXC HAX.
  assert (HA_marg : A ⊆ world_dom (marg : World)).
  {
    intros a Ha.
    assert (Ha_prod : a ∈ world_dom (res_product marg n Hc_tgt : World)).
    { rewrite Hdom_tgt. set_solver. }
    change (a ∈ world_dom (marg : World) ∪ world_dom (n : World))
      in Ha_prod.
    set_solver.
  }
  assert (Hc_marg_nC : world_compat marg (res_restrict n C)).
  { eapply world_compat_le_r; [apply res_restrict_le|exact Hc_tgt]. }
  assert (Hc_marg_mC : world_compat marg (res_restrict m C)).
  { rewrite <- (eq_sym Hmn). exact Hc_marg_nC. }
  assert (Hc_src : world_compat (res_restrict marg X) m).
  {
    assert (Hc_tmp :
        world_compat (res_restrict marg X)
          (res_restrict m (world_dom (m : World)))).
    {
      eapply world_compat_restrict_overlap
        with (S := C) (n := marg) (m := m).
      - intros z Hz.
        apply elem_of_intersection in Hz as [HzX Hzm].
        assert (HzCA : z ∈ C ∪ A) by set_solver.
        apply elem_of_union in HzCA as [HzC|HzA]; [exact HzC|].
        exfalso.
        eapply elem_of_disjoint; [exact HAm|exact HzA|exact Hzm].
      - exact Hc_marg_mC.
    }
    rewrite (res_restrict_eq_of_le m m (raw_le_refl m)) in Hc_tmp.
    exact Hc_tmp.
  }
  exists Hc_src.
  apply set_eq. intros z. split; intros Hz.
  - change (z ∈ world_dom (res_restrict marg X : World) ∪
      world_dom (m : World)) in Hz.
    apply elem_of_union in Hz as [Hz|Hz]; [|set_solver].
    change (z ∈ world_dom (marg : World) ∩ X) in Hz.
    apply elem_of_intersection in Hz as [_ HzX].
	    assert (HzCA : z ∈ C ∪ A) by set_solver.
	    apply elem_of_union in HzCA as [HzC|HzA].
	    + apply elem_of_union_l. apply HCm. exact HzC.
	    + apply elem_of_union_r. exact HzA.
  - change (z ∈ world_dom (res_restrict marg X : World) ∪
      world_dom (m : World)).
	    apply elem_of_union in Hz as [Hzm|HzA].
	    + apply elem_of_union_r. exact Hzm.
	    + apply elem_of_union_l. change (z ∈ world_dom (marg : World) ∩ X).
      apply elem_of_intersection. split.
      * apply HA_marg. exact HzA.
      * apply HAX. exact HzA.
Qed.

Lemma res_product_restrict_binder_arg_projection
    (m n marg : WfWorld) (C X A Y : aset)
    (Hc_tgt : world_compat marg n) :
  res_restrict m C = res_restrict n C ->
  C ⊆ world_dom (m : World) ->
  A ## world_dom (m : World) ->
  A ## world_dom (n : World) ->
  world_dom (res_product marg n Hc_tgt : World) =
    world_dom (n : World) ∪ A ->
  X ⊆ C ∪ A ->
  A ⊆ X ->
  Y ⊆ C ∪ A ->
  exists Hc_src : world_compat (res_restrict marg X) m,
    world_dom (res_product (res_restrict marg X) m Hc_src : World) =
      world_dom (m : World) ∪ A /\
    res_restrict (res_product (res_restrict marg X) m Hc_src) Y =
    res_restrict (res_product marg n Hc_tgt) Y.
Proof.
  intros Hmn HCm HAm HAn Hdom_tgt HXC HAX HYC.
  destruct (res_product_restrict_binder_arg_compat_dom
    m n marg C X A Hc_tgt Hmn HCm HAm HAn Hdom_tgt HXC HAX)
    as [Hc_src Hdom_src].
  exists Hc_src. split; [exact Hdom_src|].
  assert (HA_marg : A ⊆ world_dom (marg : World)).
  {
    intros a Ha.
    assert (Ha_prod : a ∈ world_dom (res_product marg n Hc_tgt : World)).
    { rewrite Hdom_tgt. set_solver. }
    change (a ∈ world_dom (marg : World) ∪ world_dom (n : World))
      in Ha_prod.
    set_solver.
  }
  assert (HCn : C ⊆ world_dom (n : World)).
  {
    pose proof (f_equal (fun w : WfWorld => world_dom (w : World)) Hmn)
      as HdomC.
    cbn [world_dom raw_world raw_worldA res_restrict] in HdomC.
    set_solver.
  }
  assert (Hc_marg_nC : world_compat marg (res_restrict n C)).
  { eapply world_compat_le_r; [apply res_restrict_le|exact Hc_tgt]. }
  assert (Hc_marg_mC : world_compat marg (res_restrict m C)).
  { rewrite Hmn. exact Hc_marg_nC. }
  assert (Hc_common_m :
      world_compat (res_restrict marg X) (res_restrict m C)).
  {
    eapply world_compat_restrict_overlap
      with (S := C) (n := marg) (m := m).
    - set_solver.
    - exact Hc_marg_mC.
  }
	  assert (Hsrc_to_common :
	      res_restrict (res_product (res_restrict marg X) m Hc_src) Y =
	      res_restrict
	        (res_product (res_restrict marg X) (res_restrict m C)
	          Hc_common_m) Y).
	  {
    symmetry.
	    eapply res_product_restrict_frame_r_eq.
    - exact HCm.
    - intros z HzY.
      assert (HzCA : z ∈ C ∪ A) by set_solver.
      apply elem_of_union in HzCA as [HzC|HzA].
      + apply elem_of_union_r. exact HzC.
      + apply elem_of_union_l.
        change (z ∈ world_dom (marg : World) ∩ X).
        apply elem_of_intersection. split.
        * apply HA_marg. exact HzA.
        * apply HAX. exact HzA.
  }
	  assert (Hcommon_eq :
	      res_restrict
	        (res_product (res_restrict marg X) (res_restrict m C)
	          Hc_common_m) Y =
	      res_restrict (res_product marg (res_restrict n C) Hc_marg_nC) Y).
	  {
    assert (Hc_common_n :
        world_compat (res_restrict marg X) (res_restrict n C)).
    {
      eapply world_compat_restrict_overlap
        with (S := C) (n := marg) (m := n).
      - set_solver.
      - exact Hc_marg_nC.
    }
    assert (Hmn_prod :
        res_product (res_restrict marg X) (res_restrict m C)
          Hc_common_m =
        res_product (res_restrict marg X) (res_restrict n C)
          Hc_common_n).
    { eapply res_product_r_eq. exact Hmn. }
    rewrite Hmn_prod.
    eapply res_product_restrict_frame_common_eq
      with (S := C) (C := C).
    - set_solver.
    - intros z HzY.
      assert (HzCA : z ∈ C ∪ A) by set_solver.
      apply elem_of_union in HzCA as [HzC|HzA].
      + apply elem_of_union_r. apply elem_of_intersection.
        split; [exact HzC|apply HCn; exact HzC].
	      + apply elem_of_union_l. apply elem_of_intersection.
	        split.
	        * apply HAX. exact HzA.
	        * apply HA_marg. exact HzA.
	  }
  assert (Htgt_common_to_full :
      res_restrict (res_product marg (res_restrict n C) Hc_marg_nC) Y =
      res_restrict (res_product marg n Hc_tgt) Y).
  {
    eapply res_product_restrict_frame_r_eq.
    - exact HCn.
    - intros z HzY.
      assert (HzCA : z ∈ C ∪ A) by set_solver.
      apply elem_of_union in HzCA as [HzC|HzA].
      + apply elem_of_union_r. exact HzC.
      + apply elem_of_union_l. apply HA_marg. exact HzA.
  }
  rewrite Hsrc_to_common, Hcommon_eq, Htgt_common_to_full.
  reflexivity.
Qed.



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

Lemma res_extend_by_le_mono
    (m n mx nx : WfWorld) (F : fiber_extension) :
  m ⊑ n ->
  m #> F ~~> mx ->
  n #> F ~~> nx ->
  mx ⊑ nx.
Proof. apply resA_extend_by_le_mono. Qed.

Lemma res_extend_by_sum
    (m1 m2 m1x m2x : WfWorld) (F : fiber_extension)
    (Hdef : raw_sum_defined (m1 : World) (m2 : World)) :
  m1 #> F ~~> m1x ->
  m2 #> F ~~> m2x ->
  exists Hdefx : raw_sum_defined (m1x : World) (m2x : World),
    res_sum m1 m2 Hdef #> F ~~>
      res_sum m1x m2x Hdefx.
Proof. apply resA_extend_by_sum. Qed.

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

Notation "r '↾ᵣ' X" := (res_restrict r X)
  (at level 20, no associativity,
   format "r  ↾ᵣ  X", only printing).
Notation "m1 '⊑ᵣ' m2" := (raw_le m1 m2)
  (at level 70, no associativity,
   format "m1  ⊑ᵣ  m2", only printing).
Notation "m1 '##ᵣ' m2" := (world_compat m1 m2)
  (at level 70, no associativity,
   format "m1  ##ᵣ  m2", only printing).
Notation "m1 '×ᵣ[' Hc ']' m2" := (res_product m1 m2 Hc)
  (at level 40, Hc at level 200, left associativity,
   format "m1  ×ᵣ[ Hc ]  m2", only printing).
Notation "m1 '+ᵣ[' Hdef ']' m2" := (res_sum m1 m2 Hdef)
  (at level 50, Hdef at level 200, left associativity,
   format "m1  +ᵣ[ Hdef ]  m2", only printing).
