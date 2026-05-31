From ContextAlgebra Require Export ResourceInterface ResourceCompat.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From ContextBase Require Export Prelude LogicVar.
From ContextStore Require Export Store.
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

Lemma lworld_on_mlsubst_back_union
    (D : lvset) (ρ1 ρ2 : LStoreT)
    (w1 : LWorldOnT ((D ∖ dom (ρ1 : gmap logic_var V))
      ∖ dom (ρ2 : gmap logic_var V)))
    (w2 : LWorldOnT (D ∖ dom (ρ1 ∪ ρ2 : gmap logic_var V))) :
  storeA_compat ρ1 ρ2 ->
  @lw V _ w1 = @lw V _ w2 ->
  lworld_on_mlsubst_back D ρ1
    (lworld_on_mlsubst_back (D ∖ dom (ρ1 : gmap logic_var V)) ρ2 w1) =
  lworld_on_mlsubst_back D (ρ1 ∪ ρ2) w2.
Proof.
  intros Hcompat Hlw.
  assert (Hwiff : forall σ,
      (@lw V _ w1 : LWorld) σ <-> (@lw V _ w2 : LWorld) σ).
  { intros σ. rewrite Hlw. reflexivity. }
  apply lworld_on_ext.
  apply wfworldA_ext. apply worldA_ext.
  - set (wl := lworld_on_mlsubst_back D ρ1
        (lworld_on_mlsubst_back (D ∖ dom (ρ1 : gmap logic_var V)) ρ2 w1)).
    set (wr := lworld_on_mlsubst_back D
        (@union (gmap logic_var V) _ ρ1 ρ2) w2).
    change (lworld_dom (lraw_world (lw D wl)) =
      lworld_dom (lraw_world (lw D wr))).
    rewrite (lw_dom D wl), (lw_dom D wr).
    reflexivity.
  - unfold lworld_on_mlsubst_back.
    intros σ. cbn [lw resA_product rawA_product singleton_worldA worldA_stores
      proj1_sig].
    split.
    + intros (σ12 & σ1 & Hσ12 & -> & Hc12_1 & ->).
      destruct Hσ12 as (σ0 & σ2' & Hσ0 & -> & Hc0_2 & ->).
      exists σ0, (storeA_restrict (ρ1 ∪ ρ2) D). repeat split; auto.
      * apply Hwiff. exact Hσ0.
      * rewrite <- storeA_restrict_union_residual_l by exact Hcompat.
        apply storeA_compat_union_intro_r.
        -- exact Hc0_2.
        -- eapply storeA_compat_union_inv_l. exact Hc12_1.
      * rewrite <- map_union_assoc.
        rewrite storeA_restrict_union_residual_l by exact Hcompat.
        reflexivity.
    + intros (σ0 & σ12 & Hσ0 & -> & Hc0_12 & ->).
      assert (Hc0_12' : storeA_compat σ0
          (@union (gmap logic_var V) _
            (storeA_restrict ρ2 (D ∖ dom (ρ1 : gmap logic_var V)))
            (storeA_restrict ρ1 D))).
      {
        rewrite storeA_restrict_union_residual_l by exact Hcompat.
        exact Hc0_12.
      }
      assert (Hc0_res : storeA_compat σ0
          (storeA_restrict ρ2 (D ∖ dom (ρ1 : gmap logic_var V)))).
      { eapply storeA_compat_union_r_inv_l. exact Hc0_12'. }
      assert (Hres_1 : storeA_compat
          (storeA_restrict ρ2 (D ∖ dom (ρ1 : gmap logic_var V)))
          (storeA_restrict ρ1 D)).
      {
        apply storeA_compat_sym.
        apply storeA_compat_restrict_r.
        eapply (storeA_compat_restrict_l_full_r
          (storeA_restrict ρ1 D) ρ2 D).
        - rewrite storeA_restrict_dom. better_set_solver.
        - apply storeA_compat_restrict. exact Hcompat.
      }
      assert (Hc0_1 : storeA_compat σ0 (storeA_restrict ρ1 D)).
      { eapply storeA_compat_union_r_inv_r; [exact Hres_1 | exact Hc0_12']. }
      exists (@union (gmap logic_var V) _
          σ0 (storeA_restrict ρ2 (D ∖ dom (ρ1 : gmap logic_var V)))).
      exists (storeA_restrict ρ1 D).
      split.
      * exists σ0, (storeA_restrict ρ2 (D ∖ dom (ρ1 : gmap logic_var V))).
        split.
        -- apply (proj2 (Hwiff σ0)). exact Hσ0.
        -- split.
           ++ reflexivity.
           ++ split.
              ** exact Hc0_res.
              ** reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ apply storeA_compat_union_intro_l; assumption.
           ++ rewrite <- map_union_assoc.
              rewrite storeA_restrict_union_residual_l by exact Hcompat.
              reflexivity.
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

Lemma lqual_mlsubst_union
    (ρ1 ρ2 : LStoreT) (q : logic_qualifier) :
  storeA_compat ρ1 ρ2 ->
  lqual_mlsubst ρ2 (lqual_mlsubst ρ1 q) =
  lqual_mlsubst (ρ1 ∪ ρ2) q.
Proof.
  intros Hcompat.
  destruct q as [D P]. cbn [lqual_mlsubst lqual_dom lqual_prop].
  eapply logic_qualifier_ext.
  - change ((D ∖ dom (ρ1 : gmap logic_var V)) ∖
      dom (ρ2 : gmap logic_var V) =
      D ∖ dom (ρ1 ∪ ρ2 : gmap logic_var V)).
    apply set_eq. intros v.
    rewrite !elem_of_difference, dom_union_L, elem_of_union.
    tauto.
  - intros w1 w2 Hlw. cbn [lqual_prop lqual_dom] in *.
    pose proof (lworld_on_mlsubst_back_union D ρ1 ρ2 w1 w2 Hcompat Hlw)
      as Hback.
    rewrite Hback. reflexivity.
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

Lemma logic_qualifier_denote_mono
    (q : logic_qualifier) (m0 m : WfWorldT) :
  logic_qualifier_denote q m0 →
  lqual_fv q ⊆ world_dom (m0 : WorldT) →
  m0 ⊑ m →
  logic_qualifier_denote q m.
Proof.
  destruct q as [D P]. simpl. intros [Hlc [Hsub0 HP]] _ Hle.
  exists Hlc.
  assert (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    pose proof (raw_le_dom _ _ Hle) as Hdom.
    set_solver.
  }
  exists Hsub.
  enough (lworld_on_lift D m0 Hlc Hsub0 =
          lworld_on_lift D m Hlc Hsub) as Heq.
  { rewrite <- Heq. exact HP. }
  apply lworld_on_ext. unfold lworld_on_lift. simpl.
  rewrite (res_restrict_le_eq m0 m (lvars_fv D) Hle Hsub0).
  reflexivity.
Qed.

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_fv.
Arguments stale_logic_qualifier /.

End LogicQualifier.
