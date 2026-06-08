From ContextAlgebra Require Export ResourceInterface ResourceCompat.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From ContextBase Require Export Prelude LogicVar.
From ContextBase Require Import BaseTactics.
From ContextStore Require Export Store.
From ContextQualifier Require Export Qualifier.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Formula atoms

    Formula atoms use the unified store-level [qualifier].  A world satisfies
    [FAtom q] exactly when its projection to [qual_vars q] contains precisely
    the stores accepted by [q].  This file keeps the world/resource support for
    that exact atom semantics; pure qualifier syntax lives in
    [ContextQualifier]. *)

Section FormulaAtom.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (Store (V := V)) (only parsing).
Local Notation LStoreT := (gmap logic_var V) (only parsing).
Local Notation LWorldOnT := (LWorldOn (V := V)) (only parsing).

Definition lstore_in_lworld_on
    {D : lvset} (s : LStoreOn (V := V) D) (w : LWorldOnT D) : Prop :=
  worldA_stores (@lw V _ w : LWorld) (lso_store s).

Definition lstore_on_lift_store
    (D : lvset) (σ : Store (V := V))
    (Hlc : lc_lvars D)
    (Hsub : lvars_fv D ⊆ dom (σ : Store (V := V))) :
    LStoreOn (V := V) D.
Proof.
  refine {| storeAO_store :=
    storeA_restrict (lstore_lift_free σ : LStore (V := V)) D |}.
  rewrite storeA_restrict_dom, dom_lstore_lift_free.
  apply set_eq. intros v. split.
  - intros Hv. apply elem_of_intersection in Hv as [_ Hv]. exact Hv.
  - intros Hv. apply elem_of_intersection. split; [|exact Hv].
    unfold lvars_of_atoms.
    destruct v as [k | x].
    + exfalso. exact (Hlc (LVBound k) Hv).
    + apply elem_of_map. exists x. split; [reflexivity|].
      apply Hsub. apply lvars_fv_elem. exact Hv.
Defined.

Definition qualifier_holds_store
    (q : qualifier (V := V)) (σ : Store (V := V)) : Prop :=
  match q with
  | tqual D P =>
      exists (Hlc : lc_lvars D)
        (Hsub : lvars_fv D ⊆ dom (σ : Store (V := V))),
        P (lstore_on_lift_store D σ Hlc Hsub)
  end.

Lemma lstore_in_lworld_on_atom_swap_front x y D
    (s : LStoreOn (V := V) D)
    (w : LWorldOnT (lvars_swap x y D)) :
  lstore_in_lworld_on (lstore_on_atom_swap_front x y D s) w <->
  lstore_in_lworld_on s (lworld_on_atom_swap_back x y D w).
Proof.
  unfold lstore_in_lworld_on, lstore_on_atom_swap_front,
    lworld_on_atom_swap_back.
  cbn [lso_store storeAO_store lw lraw_world raw_worldA worldA_stores].
  split.
  - intros Hs.
    exists (lstore_swap (LVFree x) (LVFree y) (lso_store s)).
    split; [exact Hs|].
    unfold lstore_swap, lstore_rekey.
    apply storeA_swap_involutive.
  - intros [σ0 [Hσ0 Hswap]].
    change (storeA_swap (LVFree x) (LVFree y) σ0 = lso_store s) in Hswap.
    assert (σ0 = lstore_swap (LVFree x) (LVFree y) (lso_store s)) as ->.
    {
      rewrite <- (storeA_swap_involutive (LVFree x) (LVFree y) σ0).
      rewrite Hswap.
      unfold lstore_swap, lstore_rekey. reflexivity.
    }
    exact Hσ0.
Qed.

Definition qualifier_exact_denote
    (q : qualifier (V := V)) (m : WfWorldT) : Prop :=
  match q with
  | tqual D P =>
      ∃ (Hlc : lc_lvars D)
        (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)),
        forall s : LStoreOn (V := V) D,
          P s <-> lstore_in_lworld_on s (lworld_on_lift D m Hlc Hsub)
  end.

Lemma qualifier_exact_denote_atom_swap
    (x y : atom) (q : qualifier (V := V)) (m : WfWorldT) :
  qualifier_exact_denote (qual_atom_swap x y q) (res_atom_swap x y m) <->
  qualifier_exact_denote q m.
Proof.
  destruct q as [D P]. cbn [qual_atom_swap qualifier_exact_denote].
  split.
  - intros [Hlc_sw [Hsub_sw Hholds_sw]].
    assert (Hlc : lc_lvars D).
    {
      apply lc_lvars_no_bv.
      pose proof (proj1 (lc_lvars_no_bv _) Hlc_sw) as Hbv_sw.
      rewrite lvars_bv_swap in Hbv_sw. exact Hbv_sw.
    }
    assert (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)).
    {
      pose proof Hsub_sw as Hsub_sw_proj.
      rewrite lvars_fv_swap in Hsub_sw_proj.
      rewrite world_dom_res_atom_swap in Hsub_sw_proj.
      intros z Hz.
      assert (Hzsw :
          swap x y z ∈ set_swap x y (world_dom (m : WorldT))).
      {
        apply Hsub_sw_proj.
        rewrite set_swap_elem, swap_involutive. exact Hz.
      }
      rewrite set_swap_elem, swap_involutive in Hzsw. exact Hzsw.
    }
    exists Hlc, Hsub. intros s.
    pose proof (Hholds_sw (lstore_on_atom_swap_front x y D s)) as Hsw.
    rewrite lstore_on_atom_swap_back_front in Hsw.
    rewrite lstore_in_lworld_on_atom_swap_front in Hsw.
    rewrite (lworld_on_lift_atom_swap_back
      x y D m Hlc_sw Hsub_sw Hlc Hsub) in Hsw.
    exact Hsw.
  - intros [Hlc [Hsub Hholds]].
    assert (Hlc_sw : lc_lvars (lvars_swap x y D)).
    {
      apply lc_lvars_no_bv.
      rewrite lvars_bv_swap.
      exact (proj1 (lc_lvars_no_bv _) Hlc).
    }
    assert (Hsub_sw : lvars_fv (lvars_swap x y D) ⊆
      world_dom (res_atom_swap x y m : WorldT)).
    {
      rewrite lvars_fv_swap.
      rewrite world_dom_res_atom_swap.
      intros z Hz.
      rewrite set_swap_elem in Hz |- *.
      apply Hsub. exact Hz.
    }
    exists Hlc_sw, Hsub_sw. intros s.
    specialize (Hholds (lstore_on_atom_swap_back x y D s)) as Horig.
    rewrite <- (lworld_on_lift_atom_swap_back
      x y D m Hlc_sw Hsub_sw Hlc Hsub) in Horig.
    rewrite <- lstore_in_lworld_on_atom_swap_front in Horig.
    rewrite lstore_on_atom_swap_front_back in Horig.
    exact Horig.
Qed.

Definition lworld_on_mlsubst_back
    (D : lvset) (ρ : LStoreT)
    (w : LWorldOnT (D ∖ dom (ρ : gmap logic_var V))) : LWorldOnT D.
Proof.
  set (ρD := storeA_restrict ρ D).
  set (wρ := (exist _ (singleton_worldA ρD) (wf_singleton_worldA ρD)
    : LWfWorld)).
  assert (Hc : worldA_compat (@lw V _ w : LWorld) (wρ : LWorld)).
  {
    apply disj_dom_worldA_compat.
    change (lworld_dom (@lw V _ w : LWorld) ∩ lworld_dom (wρ : LWorld) = ∅).
    rewrite (@lw_dom V _ w).
    unfold wρ.
    unfold lworld_dom, lraw_world.
    cbn [proj1_sig singleton_worldA worldA_dom].
    change (dom ρD) with (dom (storeA_restrict ρ D)).
    better_store_solver.
  }
  refine {| lw := resA_product (@lw V _ w) wρ Hc |}.
  change (lworld_dom (resA_product (@lw V _ w) wρ Hc : LWorld) = D).
  unfold wρ.
  unfold lworld_dom, lraw_world, resA_product.
  change (worldA_dom (rawA_product (@lw V _ w : LWorld) (singleton_worldA ρD)) = D).
  cbn [rawA_product singleton_worldA worldA_dom].
  change (lworld_dom (@lw V _ w : LWorld) ∪ dom ρD = D).
  rewrite (@lw_dom V _ w).
  change (dom ρD) with (dom (storeA_restrict ρ D)).
  store_normalize.
  apply set_eq. intros z.
  rewrite elem_of_union, elem_of_difference, elem_of_intersection.
  split.
  - intros [[HzD _] | [_ HzD]]; exact HzD.
  - intros HzD.
    destruct (decide (z ∈ dom (ρ : gmap logic_var V))) as [Hzρ | Hzρ].
    + right. split; assumption.
    + left. split; assumption.
Defined.

Lemma lstore_lift_free_restrict_fv_lvars_eq
    (σ : Store (V := V)) (D : lvset) :
  storeA_restrict
    (lstore_lift_free (store_restrict σ (lvars_fv D)) : LStoreT) D =
  storeA_restrict (lstore_lift_free σ : LStoreT) D.
Proof.
  apply storeA_map_eq. intros z.
  destruct (decide (z ∈ D)) as [HzD|HzD].
  2:{
    transitivity (@None V).
    - apply storeA_restrict_lookup_none_r. exact HzD.
    - symmetry. apply storeA_restrict_lookup_none_r. exact HzD.
  }
  destruct z as [k|x].
  - transitivity (@None V).
    + apply storeA_restrict_lookup_none_l.
      rewrite lstore_lift_free_lookup_bound. reflexivity.
    + symmetry. apply storeA_restrict_lookup_none_l.
      rewrite lstore_lift_free_lookup_bound. reflexivity.
  - assert (HxD : x ∈ lvars_fv D) by (apply lvars_fv_elem; exact HzD).
    destruct ((σ : gmap atom V) !! x) as [v|] eqn:Hσx.
    + transitivity (Some v).
      * apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free.
        apply storeA_restrict_lookup_some_2; [exact Hσx|exact HxD].
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free. exact Hσx.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free.
        apply storeA_restrict_lookup_none_l. exact Hσx.
      * symmetry. apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free. exact Hσx.
Qed.

Lemma lstore_in_lworld_on_lift_store_of_world
    (D : lvset) (m : WfWorldT)
    (Hlc : lc_lvars D)
    (Hsub : lvars_fv D ⊆ world_dom (m : WorldT))
    (σ : Store (V := V))
    (Hsubσ : lvars_fv D ⊆ dom (σ : Store (V := V))) :
  (m : WorldT) σ ->
  lstore_in_lworld_on (lstore_on_lift_store D σ Hlc Hsubσ)
    (lworld_on_lift D m Hlc Hsub).
Proof.
  intros Hσ.
  unfold lstore_in_lworld_on, lstore_on_lift_store, lworld_on_lift.
  cbn [lw lso_store lraw_world raw_worldA worldA_stores storeAO_store].
  exists (lstore_lift_free (store_restrict σ (lvars_fv D))).
  split.
  - exists (store_restrict σ (lvars_fv D)).
    split.
    + exists σ. split; [exact Hσ | reflexivity].
    + reflexivity.
  - apply lstore_lift_free_restrict_fv_lvars_eq.
Qed.

Lemma res_fiber_from_projection_lookup
    (m mfib : WfWorldT) (X : aset) (σx σ : StoreT) x :
  res_fiber_from_projection m X σx mfib ->
  (mfib : WorldT) σ ->
  x ∈ X ->
  σ !! x = σx !! x.
Proof.
  intros Hfiber Hσ Hx.
  destruct Hfiber as [Hproj Hfib].
  destruct mfib as [wmfib Hwfib].
  cbn [raw_world raw_worldA world_stores] in Hσ, Hfib.
  change (wmfib = rawA_fiber (m : WorldT) σx) in Hfib.
  change (wmfib σ) in Hσ.
  rewrite Hfib in Hσ.
  destruct Hσ as [Hsource Hrestrict].
  change (storeA_restrict σ (dom (σx : StoreT)) = σx) in Hrestrict.
  pose proof (wfworld_store_dom (res_restrict m X) σx Hproj)
    as Hdomσx.
  change (dom (σx : StoreT) = world_dom (res_restrict m X : WorldT))
    in Hdomσx.
  cbn in Hdomσx.
  destruct (decide (x ∈ dom (σx : StoreT))) as [Hxσx|Hxσx].
  - change (x ∈ dom (σx : gmap atom V)) in Hxσx.
    apply elem_of_dom in Hxσx as [vx Hσxx].
    assert (Hlook :
        ((storeA_restrict σ (dom (σx : StoreT)) : StoreT) !! x) =
        Some vx).
    { rewrite Hrestrict. exact Hσxx. }
    apply storeA_restrict_lookup_some in Hlook as [_ Hσx].
    change ((σ : gmap atom V) !! x =
      (σx : gmap atom V) !! x).
    exact (eq_trans Hσx (eq_sym Hσxx)).
  - change (x ∉ dom (σx : gmap atom V)) in Hxσx.
    rewrite not_elem_of_dom in Hxσx.
    change ((σ : gmap atom V) !! x =
      (σx : gmap atom V) !! x).
    rewrite Hxσx.
    apply not_elem_of_dom.
    pose proof (wfworld_store_dom m σ Hsource) as Hdomσ.
    rewrite Hdomσ.
    intros Hxm.
    assert (Hxσx_dom : x ∈ dom (σx : StoreT)).
    {
      rewrite Hdomσx.
      cbn.
      apply elem_of_intersection. split; assumption.
    }
    change (x ∈ dom (σx : gmap atom V)) in Hxσx_dom.
    apply elem_of_dom in Hxσx_dom as [vx Hlook].
    rewrite Hxσx in Hlook. discriminate.
Qed.

Lemma lstore_lift_restrict_singleton_free_eq
    y D (s : LStoreOn (V := V) D) (σ : StoreT) v :
  D = ({[LVFree y]} : lvset) ->
  σ !! y = Some v ->
  (lso_store s : LStoreT) !! LVFree y = Some v ->
  storeA_restrict
    (lstore_lift_free (store_restrict σ (lvars_fv D)) : LStoreT) D =
  lso_store s.
Proof.
  intros HD Hσy Hsy.
  subst D.
  destruct s as [s Hsdom].
  cbn [lso_store storeAO_store] in *.
  apply storeA_map_eq. intros k.
  rewrite storeA_restrict_lookup.
  destruct (decide (k ∈ ({[LVFree y]} : lvset))) as [Hk|Hk].
  - apply elem_of_singleton in Hk as ->.
    rewrite lstore_lift_free_lookup_free.
    replace ((store_restrict σ (lvars_fv ({[LVFree y]} : lvset)) : StoreT)
        !! y)
      with (Some v).
    2:{
      symmetry.
      change ((storeA_restrict σ (lvars_fv ({[LVFree y]} : lvset))
        : gmap atom V) !! y = Some v).
      apply storeA_restrict_lookup_some_2; [exact Hσy|].
      rewrite lvars_fv_singleton_free. apply elem_of_singleton.
      reflexivity.
    }
    replace (s !! LVFree y) with (Some v).
    { reflexivity. }
  - symmetry. apply not_elem_of_dom_1.
    rewrite Hsdom. exact Hk.
Qed.

Lemma lstore_in_lworld_on_singleton_free_lookup
    y D (m : WfWorldT)
    (Hlc : lc_lvars D)
    (Hsub : lvars_fv D ⊆ world_dom (m : WorldT))
    (s : LStoreOn (V := V) D) :
  D = ({[LVFree y]} : lvset) ->
  lstore_in_lworld_on s (lworld_on_lift D m Hlc Hsub) ->
  exists σ,
    (m : WorldT) σ /\
    (lso_store s : LStoreT) !! LVFree y = σ !! y.
Proof.
  intros HD Hmem.
  subst D.
  unfold lstore_in_lworld_on, lworld_on_lift in Hmem.
  cbn [lw lraw_world raw_worldA worldA_stores] in Hmem.
  destruct Hmem as [σl [[τ [Hτres ->]] Hrestrict_l]].
  destruct Hτres as [σ [Hσ Hrestrict_τ]].
  exists σ. split; [exact Hσ|].
  pose proof (f_equal (fun st => (st : LStoreT) !! LVFree y) Hrestrict_l)
    as Hyl.
  cbn [lso_store storeAO_store] in Hyl.
  change ((storeA_restrict (lstore_lift_free τ : LStoreT)
    ({[LVFree y]} : lvset) : LStoreT) !! LVFree y =
    (lso_store s : LStoreT) !! LVFree y) in Hyl.
  replace ((storeA_restrict (lstore_lift_free τ : LStoreT)
      ({[LVFree y]} : lvset) : LStoreT) !! LVFree y)
    with ((τ : gmap atom V) !! y) in Hyl.
  2:{
    symmetry.
    rewrite (storeA_restrict_lookup
      (K := logic_var) (V := V)
      (lstore_lift_free τ : LStoreT) ({[LVFree y]} : lvset) (LVFree y)).
    destruct (decide (LVFree y ∈ ({[LVFree y]} : lvset))) as [_|Hbad].
    - rewrite lstore_lift_free_lookup_free. reflexivity.
    - exfalso. apply Hbad. apply elem_of_singleton. reflexivity.
  }
  pose proof (f_equal (fun st => (st : StoreT) !! y) Hrestrict_τ)
    as Hyτ.
  change ((storeA_restrict σ (lvars_fv ({[LVFree y]} : lvset))
    : StoreT) !! y = τ !! y) in Hyτ.
  rewrite (storeA_restrict_lookup
    (K := atom) (V := V)
    (σ : gmap atom V) (lvars_fv ({[LVFree y]} : lvset)) y) in Hyτ.
  destruct (decide (y ∈ lvars_fv ({[LVFree y]} : lvset))) as [_|Hbad].
  2:{ exfalso. apply Hbad.
      rewrite lvars_fv_singleton_free. apply elem_of_singleton.
      reflexivity. }
  rewrite <- Hyτ in Hyl. symmetry. exact Hyl.
Qed.

Lemma lvars_closed_difference_atom_store_to_lvar_store_empty
    (D : lvset) (σ : Store (V := V)) :
  lc_lvars D ->
  dom (σ : Store (V := V)) = lvars_fv D ->
  D ∖ dom (atom_store_to_lvar_store σ : LStore (V := V)) = ∅.
Proof.
  intros Hlc Hdom.
  change (D ∖ dom (atom_store_to_lvar_store (σ : gmap atom V) : gmap logic_var V) = ∅).
  apply set_eq. intros v.
  rewrite elem_of_difference, elem_of_empty, atom_store_to_lvar_store_dom.
  split; [|tauto].
  intros [HvD Hvnot].
  exfalso. apply Hvnot.
  pose proof (lvars_bv_empty_subset_of_atoms_fv D
    (proj1 (lc_lvars_no_bv _) Hlc) v HvD) as HvAtoms.
  unfold lvars_of_atoms in *.
  apply elem_of_map in HvAtoms as [x [Hv Hx]].
  apply elem_of_map. exists x. split; [exact Hv|].
  change (x ∈ dom (σ : Store (V := V))).
  rewrite Hdom. exact Hx.
Qed.

Lemma lstore_on_mlsubst_back_full_lift
    (D : lvset) (ρ : LStore (V := V)) (σ : Store (V := V))
    (s : LStoreOn (V := V) (D ∖ dom (ρ : gmap logic_var V)))
    (Hlc : lc_lvars D)
    (Hsub : lvars_fv D ⊆ dom (σ : Store (V := V))) :
  storeA_restrict ρ D =
    storeA_restrict (lstore_lift_free σ : LStore (V := V)) D ->
  D ∖ dom (ρ : gmap logic_var V) = ∅ ->
  lstore_on_mlsubst_back D ρ s =
    lstore_on_lift_store D σ Hlc Hsub.
Proof.
  intros Hρ HDempty.
  apply lstore_on_ext.
  unfold lstore_on_mlsubst_back, lstore_on_lift_store.
  cbn [lso_store storeAO_store].
  rewrite Hρ.
  apply storeA_map_eq. intros v.
  destruct (decide (v ∈ D)) as [HvD|HvD].
  - rewrite lookup_union_r.
    + reflexivity.
    + apply not_elem_of_dom.
      change (v ∉ dom (lso_store s : LStore (V := V))).
      rewrite (lso_dom s), HDempty. better_set_solver.
  - rewrite storeA_restrict_lookup_none_r by exact HvD.
    rewrite map_lookup_union_None. split.
    + apply not_elem_of_dom.
      change (v ∉ dom (lso_store s : LStore (V := V))).
      rewrite (lso_dom s), HDempty. better_set_solver.
    + apply storeA_restrict_lookup_none_r. exact HvD.
Qed.

Lemma lstore_on_mlsubst_back_lift_store
    (D : lvset) (ρ : LStore (V := V)) (σ : Store (V := V))
    (HlcD : lc_lvars D)
    (HsubD : lvars_fv D ⊆ dom (σ : Store (V := V)))
    (HlcR : lc_lvars (D ∖ dom (ρ : gmap logic_var V)))
    (HsubR :
      lvars_fv (D ∖ dom (ρ : gmap logic_var V)) ⊆
        dom (σ : Store (V := V))) :
  storeA_restrict ρ D =
    storeA_restrict (lstore_lift_free σ : LStore (V := V))
      (D ∩ dom (ρ : gmap logic_var V)) ->
  lstore_on_mlsubst_back D ρ
    (lstore_on_lift_store (D ∖ dom (ρ : gmap logic_var V)) σ
      HlcR HsubR) =
  lstore_on_lift_store D σ HlcD HsubD.
Proof.
  intros Hρ.
  apply lstore_on_ext.
  unfold lstore_on_mlsubst_back, lstore_on_lift_store.
  cbn [lso_store storeAO_store].
  rewrite Hρ.
  rewrite <- (storeA_restrict_union_partition
    (storeA_restrict (lstore_lift_free σ : LStore (V := V)) D
      : gmap logic_var V)
    (D ∖ dom (ρ : gmap logic_var V))
    (D ∩ dom (ρ : gmap logic_var V))).
  - f_equal.
    + symmetry. apply storeA_restrict_twice_subset. better_set_solver.
    + symmetry. apply storeA_restrict_twice_subset. better_set_solver.
  - rewrite storeA_restrict_dom.
    intros v Hv.
    apply elem_of_intersection in Hv as [_ HvD].
    apply elem_of_union.
    destruct (decide (v ∈ dom (ρ : gmap logic_var V))) as [Hvρ|Hvρ].
    + right. apply elem_of_intersection. split; assumption.
    + left. apply elem_of_difference. split; assumption.
  - apply set_eq. intros v.
    rewrite elem_of_intersection.
    split.
    + intros [Hvrem Hvcovered].
      apply elem_of_difference in Hvrem as [_ Hnot].
      apply elem_of_intersection in Hvcovered as [_ Hin].
      contradiction.
    + intros Hv. set_solver.
Qed.

Lemma qualifier_exact_denote_restrict q w X :
  qual_dom q ⊆ X →
  qualifier_exact_denote q (res_restrict w X) ↔
  qualifier_exact_denote q w.
Proof.
  destruct q as [D P]. cbn [qualifier_exact_denote qual_dom qual_lvars].
  intros HfvX. split.
  - intros [Hlc [Hsub Hholds]].
    assert (Hsubw : lvars_fv D ⊆ world_dom (w : WorldT)).
    {
      intros x Hx.
      pose proof (Hsub x Hx) as Hx_restrict.
      simpl in Hx_restrict.
      apply elem_of_intersection in Hx_restrict as [Hxw _].
      exact Hxw.
    }
    exists Hlc, Hsubw. intros s.
    enough (lworld_on_lift D (res_restrict w X) Hlc Hsub =
            lworld_on_lift D w Hlc Hsubw) as Heq.
    { rewrite <- Heq. apply Hholds. }
    apply lworld_on_ext. unfold lworld_on_lift. simpl.
    rewrite res_restrict_restrict_eq.
    replace (X ∩ lvars_fv D) with (lvars_fv D) by set_solver.
    reflexivity.
  - intros [Hlc [Hsub Hholds]].
    assert (Hsubr : lvars_fv D ⊆ world_dom (res_restrict w X : WorldT)).
    {
      simpl. set_solver.
    }
    exists Hlc, Hsubr. intros s.
    enough (lworld_on_lift D w Hlc Hsub =
            lworld_on_lift D (res_restrict w X) Hlc Hsubr) as Heq.
    { rewrite <- Heq. apply Hholds. }
    apply lworld_on_ext. unfold lworld_on_lift. simpl.
    rewrite res_restrict_restrict_eq.
    replace (X ∩ lvars_fv D) with (lvars_fv D) by set_solver.
    reflexivity.
Qed.

End FormulaAtom.
