From ContextAlgebra Require Export ResourceInterface ResourceCompat.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From ContextBase Require Export Prelude LogicVar.
From ContextBase Require Import BaseTactics.
From ContextStore Require Export Store.
From ContextQualifier Require Export Qualifier.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.

(** * Logic qualifiers

    A logic qualifier is a predicate over a locally-nameless resource whose
    domain is exactly the qualifier domain.  At denotation time an atom-keyed
    world is lifted to the free-lvar view, restricted to the qualifier domain,
    and then passed to the predicate.

    Opening is just key swapping: the domain swaps [LVBound k] with [LVFree x],
    and the predicate swaps the incoming lworld back before interpreting it. *)

Section LogicQualifier.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation LStoreT := (gmap logic_var V) (only parsing).
Local Notation LWorldT := (LWorld (V := V)) (only parsing).
Local Notation LWorldOnT := (LWorldOn (V := V)) (only parsing).

Record logic_qualifier : Type := lqual {
  lqual_dom : lvset;
  lqual_prop : LWorldOnT lqual_dom → Prop;
}.

Definition lqual_lvars (q : logic_qualifier) : lvset :=
  lqual_dom q.

Definition lqual_fv (q : logic_qualifier) : aset :=
  lvars_fv (lqual_dom q).

Definition logic_qualifier_denote
    (q : logic_qualifier) (m : WfWorldT) : Prop :=
  match q with
  | lqual D P =>
      ∃ (Hlc : lc_lvars D)
        (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)),
        P (lworld_on_lift D m Hlc Hsub)
  end.

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

Definition lqual_fvars
    (d : aset) (prop : LWorldOnT (lvars_of_atoms d) → Prop)
    : logic_qualifier :=
  lqual (lvars_of_atoms d) prop.

Definition lqual_open
    (k : nat) (x : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual D P =>
		      lqual (lvars_open k x D)
		        (λ w, P (lworld_on_open_back k x D w))
		  end.

Definition lqual_atom_swap
    (x y : atom) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual D P =>
      lqual (lvars_swap x y D)
        (λ w, P (lworld_on_atom_swap_back x y D w))
  end.

Lemma logic_qualifier_denote_atom_swap
    (x y : atom) (q : logic_qualifier) (m : WfWorldT) :
  logic_qualifier_denote (lqual_atom_swap x y q) (res_atom_swap x y m) <->
  logic_qualifier_denote q m.
Proof.
  destruct q as [D P]. cbn [lqual_atom_swap logic_qualifier_denote].
  split.
  - intros [Hlc_sw [Hsub_sw HP]].
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
    exists Hlc, Hsub.
    rewrite <- (lworld_on_lift_atom_swap_back
      x y D m Hlc_sw Hsub_sw Hlc Hsub).
    exact HP.
  - intros [Hlc [Hsub HP]].
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
    exists Hlc_sw, Hsub_sw.
    rewrite (lworld_on_lift_atom_swap_back
      x y D m Hlc_sw Hsub_sw Hlc Hsub).
    exact HP.
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

Definition lqual_mlsubst
    (ρ : LStoreT) (q : logic_qualifier) : logic_qualifier :=
  match q with
  | lqual D P =>
      lqual (D ∖ dom (ρ : gmap logic_var V))
        (fun w => P (lworld_on_mlsubst_back D ρ w))
  end.

Definition lqual_msubst_store
    (σ : Store (V := V)) (q : logic_qualifier) : logic_qualifier :=
  lqual_mlsubst (lstore_lift_free σ) q.

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

Lemma logic_qualifier_ext (q1 q2 : logic_qualifier) :
  lqual_dom q1 = lqual_dom q2 ->
  (forall (w1 : LWorldOnT (lqual_dom q1))
          (w2 : LWorldOnT (lqual_dom q2)),
      @lw V (lqual_dom q1) w1 = @lw V (lqual_dom q2) w2 ->
      lqual_prop q1 w1 <-> lqual_prop q2 w2) ->
  q1 = q2.
Proof.
  destruct q1 as [D1 P1], q2 as [D2 P2]. simpl.
  intros HD HP. subst D2.
  f_equal.
  apply functional_extensionality. intros w.
  apply propositional_extensionality.
  apply HP. reflexivity.
Qed.

Lemma lqual_atom_swap_involutive x y (q : logic_qualifier) :
  lqual_atom_swap x y (lqual_atom_swap x y q) = q.
Proof.
  destruct q as [D P]. cbn [lqual_atom_swap].
  apply logic_qualifier_ext.
  - apply set_swap_involutive.
  - intros w1 w2 Hlw. cbn [lqual_prop lqual_dom].
    enough (lworld_on_atom_swap_back x y D
      (lworld_on_atom_swap_back x y (lvars_swap x y D) w1) = w2) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    cbn [lworld_on_atom_swap_back].
    change (lres_swap (LVFree x) (LVFree y)
      (lres_swap (LVFree x) (LVFree y) (@lw V _ w1)) =
      @lw V _ w2).
    rewrite Hlw.
    apply lres_swap_involutive.
Qed.

Lemma lqual_atom_swap_fresh_id x y (q : logic_qualifier) :
  x ∉ lqual_fv q ->
  y ∉ lqual_fv q ->
  lqual_atom_swap x y q = q.
Proof.
  destruct q as [D P]. cbn [lqual_atom_swap lqual_fv lqual_dom].
  intros Hx Hy.
  apply logic_qualifier_ext.
  - apply lvars_swap_fresh; assumption.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    enough (lworld_on_atom_swap_back x y D w1 = w2) as -> by reflexivity.
    apply lworld_on_ext.
    cbn [lworld_on_atom_swap_back lw].
    change (lres_swap (LVFree x) (LVFree y) (@lw V _ w1) =
      @lw V _ w2).
    rewrite Hlw.
    apply lres_swap_fresh.
    + rewrite (@lw_dom V (lqual_dom {| lqual_dom := D; lqual_prop := P |}) w2).
      cbn [lqual_dom].
      intros Hbad. apply Hx. apply lvars_fv_elem. exact Hbad.
    + rewrite (@lw_dom V (lqual_dom {| lqual_dom := D; lqual_prop := P |}) w2).
      cbn [lqual_dom].
      intros Hbad. apply Hy. apply lvars_fv_elem. exact Hbad.
Qed.

Lemma lqual_atom_swap_open_conjugate k x y z q :
  lqual_atom_swap x y (lqual_open k (swap x y z) q) =
  lqual_open k z (lqual_atom_swap x y q).
Proof.
  destruct q as [D P]. cbn [lqual_atom_swap lqual_open].
  apply logic_qualifier_ext.
  - apply lvars_swap_open_conjugate.
  - intros w1 w2 Hlw. cbn [lqual_prop lqual_dom].
    enough
      (lworld_on_open_back k (swap x y z) D
        (lworld_on_atom_swap_back x y (lvars_open k (swap x y z) D) w1) =
       lworld_on_atom_swap_back x y D
        (lworld_on_open_back k z (lvars_swap x y D) w2)) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    cbn [lworld_on_open_back lworld_on_atom_swap_back].
    change (lres_swap (LVBound k) (LVFree (swap x y z))
      (lres_swap (LVFree x) (LVFree y) (@lw V _ w1)) =
      lres_swap (LVFree x) (LVFree y)
        (lres_swap (LVBound k) (LVFree z) (@lw V _ w2))).
    rewrite Hlw.
    unfold lres_swap.
    rewrite (resA_swap_conjugate
      (LVFree x) (LVFree y) (LVBound k) (LVFree z)).
    replace (swap (LVFree x) (LVFree y) (LVBound k)) with (LVBound k)
      by (unfold swap; repeat destruct decide; congruence).
    replace (swap (LVFree x) (LVFree y) (LVFree z))
      with (LVFree (swap x y z))
      by (unfold swap; repeat destruct decide; congruence).
    reflexivity.
Qed.

Lemma lqual_atom_swap_mlsubst x y (ρ : LStoreT) q :
  lqual_atom_swap x y (lqual_mlsubst ρ q) =
  lqual_mlsubst (lvar_store_swap x y ρ) (lqual_atom_swap x y q).
Proof.
  destruct q as [D P]. cbn [lqual_atom_swap lqual_mlsubst].
  apply logic_qualifier_ext.
  - transitivity (set_swap (LVFree x) (LVFree y) D ∖
      set_swap (LVFree x) (LVFree y) (dom (ρ : LStoreT))).
    + apply set_swap_difference.
    + apply (f_equal (fun R =>
        set_swap (LVFree x) (LVFree y) D ∖ R)).
      symmetry. apply lvar_store_swap_dom.
  - intros w1 w2 Hlw. cbn [lqual_prop lqual_dom].
    enough (lworld_on_mlsubst_back D ρ
      (lworld_on_atom_swap_back x y (D ∖ dom (ρ : LStoreT)) w1) =
      lworld_on_atom_swap_back x y D
        (lworld_on_mlsubst_back (lvars_swap x y D)
          (lvar_store_swap x y ρ) w2)) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    apply wfworldA_ext. apply worldA_ext.
    + change (lworld_dom
        (@lw V D (lworld_on_mlsubst_back D ρ
          (lworld_on_atom_swap_back x y (D ∖ dom (ρ : LStoreT)) w1))
          : LWorld) =
        lworld_dom
        (@lw V D (lworld_on_atom_swap_back x y D
          (lworld_on_mlsubst_back (lvars_swap x y D)
            (lvar_store_swap x y ρ) w2)) : LWorld)).
      rewrite !lw_dom. reflexivity.
    + intros τ.
      cbn [lworld_on_mlsubst_back lworld_on_atom_swap_back lw].
      unfold lres_swap.
      split.
      * intros Hτ.
        destruct Hτ as [τ1 [τ2 [Hτ1 [Hτ2 [Hcompat Hτeq]]]]].
        destruct Hτ1 as [τ1₀ [Hτ1₀ Hτ1eq]].
        subst τ1 τ.
        set (s := storeA_restrict ρ D : LStoreT) in *.
        set (ssw := storeA_restrict (lvar_store_swap x y ρ)
          (lvars_swap x y D) : LStoreT).
        assert (Hssw : ssw = lvar_store_swap x y s).
        {
          subst s ssw.
          change (storeA_restrict (lvar_store_swap x y ρ)
            (lvars_swap x y D) =
            lvar_store_swap x y (storeA_restrict ρ D)).
          apply storeA_restrict_swap.
        }
        subst ssw.
        assert (Hτ2eq : τ2 = s).
        {
          change ((singleton_worldA s : LWorld) τ2) in Hτ2.
          unfold singleton_worldA in Hτ2.
          cbn [worldA_stores] in Hτ2.
          exact Hτ2.
        }
        subst τ2.
        exists (τ1₀ ∪ lvar_store_swap x y s). split.
        -- exists τ1₀, (lvar_store_swap x y s). repeat split.
           ++ exact (eq_rect _ (fun w : LWfWorld => (w : LWorld) τ1₀)
                Hτ1₀ _ Hlw).
           ++ symmetry. exact Hssw.
           ++ apply (proj1 (storeA_compat_swap (LVFree x) (LVFree y) τ1₀
                (lvar_store_swap x y s))).
              change (storeA_compat (storeA_swap (LVFree x) (LVFree y) τ1₀)
                (storeA_swap (LVFree x) (LVFree y)
                  (storeA_swap (LVFree x) (LVFree y) s))).
              rewrite storeA_swap_involutive.
              exact Hcompat.
        -- change (storeA_swap (LVFree x) (LVFree y)
             (τ1₀ ∪ storeA_swap (LVFree x) (LVFree y) s) =
             storeA_swap (LVFree x) (LVFree y) τ1₀ ∪ s).
           rewrite storeA_swap_union.
           rewrite storeA_swap_involutive.
           reflexivity.
      * intros Hτ.
        destruct Hτ as [τ0 [Hprod Hτeq]].
        destruct Hprod as [α [β [Hα [Hβ [Hcompat Hτ0eq]]]]].
        subst τ0 τ.
        set (s := storeA_restrict ρ D : LStoreT) in *.
        set (ssw := storeA_restrict (lvar_store_swap x y ρ)
          (lvars_swap x y D) : LStoreT).
        assert (Hssw : ssw = lvar_store_swap x y s).
        {
          subst s ssw.
          change (storeA_restrict (lvar_store_swap x y ρ)
            (lvars_swap x y D) =
            lvar_store_swap x y (storeA_restrict ρ D)).
          apply storeA_restrict_swap.
        }
        subst ssw.
        assert (Hβeq : β = lvar_store_swap x y s).
        {
          change ((singleton_worldA
            (storeA_restrict (lvar_store_swap x y ρ)
              (lvars_swap x y D)) : LWorld) β) in Hβ.
          unfold singleton_worldA in Hβ.
          cbn [worldA_stores] in Hβ.
          rewrite Hβ. exact Hssw.
        }
        subst β.
        exists (storeA_swap (LVFree x) (LVFree y) α), s.
        split.
        -- exists α. split.
           ++ exact (eq_rect _ (fun w : LWfWorld => (w : LWorld) α)
                Hα _ (eq_sym Hlw)).
           ++ reflexivity.
        -- split.
           ++ unfold singleton_worldA. cbn [worldA_stores]. reflexivity.
           ++ split.
              ** rewrite <- (storeA_swap_involutive (LVFree x) (LVFree y) s).
                 apply (proj2 (storeA_compat_swap (LVFree x) (LVFree y) α
                   (lvar_store_swap x y s))).
                 exact Hcompat.
              ** change (storeA_swap (LVFree x) (LVFree y)
                   (α ∪ storeA_swap (LVFree x) (LVFree y) s) =
                   storeA_swap (LVFree x) (LVFree y) α ∪ s).
                 rewrite storeA_swap_union.
                 rewrite storeA_swap_involutive.
                 reflexivity.
Qed.

Lemma lqual_mlsubst_empty (q : logic_qualifier) :
  lqual_mlsubst (∅ : LStoreT) q = q.
Proof.
  destruct q as [D P].
  cbn [lqual_mlsubst].
  apply logic_qualifier_ext.
  - change (D ∖ (∅ : lvset) = D).
    apply difference_empty_L.
  - intros w1 w2 Hlw. cbn [lqual_prop lqual_dom] in *.
    enough (lworld_on_mlsubst_back D (∅ : LStoreT) w1 = w2) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    unfold lworld_on_mlsubst_back.
    cbn [lw].
    transitivity (@lw V (D ∖ dom (∅ : LStoreT)) w1).
    + apply wfworldA_ext. apply worldA_ext.
      * simpl.
        unfold storeA_restrict.
        replace (map_restrict V (∅ : LStoreT) D) with (∅ : LStoreT)
          by (symmetry; apply map_restrict_idemp;
              rewrite dom_empty_L; apply empty_subseteq).
        change (dom (∅ : LStoreT)) with (∅ : lvset).
        apply set_eq. intros z.
        rewrite elem_of_union, elem_of_empty. tauto.
      * intros σ. simpl.
        unfold storeA_restrict.
        replace (map_restrict V (∅ : LStoreT) D) with (∅ : LStoreT)
          by (symmetry; apply map_restrict_idemp;
              rewrite dom_empty_L; apply empty_subseteq).
        split.
        -- intros (σ1 & σ2 & Hσ1 & -> & _ & ->).
           replace (σ1 ∪ ∅) with σ1 by (symmetry; apply map_union_empty).
           exact Hσ1.
        -- intros Hσ.
           exists σ, (∅ : LStoreT). repeat split; try exact Hσ; try reflexivity.
           ++ exact (ResourceAlgebra.rawA_compat_unit_r
                (@lw V _ w1 : LWorldT) σ (∅ : LStoreT) Hσ eq_refl).
           ++ symmetry. apply map_union_empty.
    + exact Hlw.
Qed.

Lemma lqual_open_commute_fresh i j x y q :
  i <> j ->
  x <> y ->
  lqual_open i x (lqual_open j y q) =
  lqual_open j y (lqual_open i x q).
Proof.
  intros Hij Hxy.
  destruct q as [D P].
  cbn [lqual_open].
  apply logic_qualifier_ext.
  - apply lvars_open_commute_fresh; assumption.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    enough
      (lworld_on_open_back j y D
        (lworld_on_open_back i x (lvars_open j y D) w1) =
       lworld_on_open_back i x D
        (lworld_on_open_back j y (lvars_open i x D) w2)) as ->.
    { reflexivity. }
    apply lworld_on_ext.
    eapply lworld_on_open_back_commute_fresh; eauto.
Qed.

Lemma logic_qualifier_denote_restrict q w X :
  lqual_fv q ⊆ X →
  logic_qualifier_denote q (res_restrict w X) ↔
  logic_qualifier_denote q w.
Proof.
  destruct q as [D P]. simpl. intros HfvX. split.
  - intros [Hlc [Hsub HP]].
    exists Hlc.
    assert (Hsubw : lvars_fv D ⊆ world_dom (w : WorldT)).
    {
      intros x Hx.
      pose proof (Hsub x Hx) as Hx_restrict.
      simpl in Hx_restrict.
      apply elem_of_intersection in Hx_restrict as [Hxw _].
      exact Hxw.
    }
    exists Hsubw.
    enough (lworld_on_lift D (res_restrict w X) Hlc Hsub =
            lworld_on_lift D w Hlc Hsubw) as Heq.
    { rewrite <- Heq. exact HP. }
    apply lworld_on_ext. unfold lworld_on_lift. simpl.
    rewrite res_restrict_restrict_eq.
    replace (X ∩ lvars_fv D) with (lvars_fv D) by set_solver.
    reflexivity.
  - intros [Hlc [Hsub HP]].
    exists Hlc.
    assert (Hsubr : lvars_fv D ⊆ world_dom (res_restrict w X : WorldT)).
    {
      simpl. set_solver.
    }
    exists Hsubr.
    enough (lworld_on_lift D w Hlc Hsub =
            lworld_on_lift D (res_restrict w X) Hlc Hsubr) as Heq.
    { rewrite <- Heq. exact HP. }
    apply lworld_on_ext. unfold lworld_on_lift. simpl.
    rewrite res_restrict_restrict_eq.
    replace (X ∩ lvars_fv D) with (lvars_fv D) by set_solver.
    reflexivity.
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

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_fv.
Arguments stale_logic_qualifier /.

End LogicQualifier.
