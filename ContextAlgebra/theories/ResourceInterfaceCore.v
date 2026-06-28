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





End ResourceInterface.
