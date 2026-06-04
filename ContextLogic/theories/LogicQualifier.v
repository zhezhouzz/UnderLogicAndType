From ContextAlgebra Require Export ResourceInterface ResourceCompat.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra.
From ContextBase Require Export Prelude LogicVar.
From ContextBase Require Import BaseTactics.
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

Lemma lstore_lift_free_restrict_lvars_subset_eq
    (σ : Store (V := V)) (D : lvset) (X : aset) :
  lvars_fv D ⊆ X ->
  storeA_restrict
    (lstore_lift_free (store_restrict σ X) : LStoreT) D =
  storeA_restrict (lstore_lift_free σ : LStoreT) D.
Proof.
  intros HDX.
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
  - assert (HxX : x ∈ X).
    { apply HDX. apply lvars_fv_elem. exact HzD. }
    destruct ((σ : gmap atom V) !! x) as [v|] eqn:Hσx.
    + transitivity (Some v).
      * apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free.
        apply storeA_restrict_lookup_some_2; [exact Hσx|exact HxX].
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free. exact Hσx.
    + transitivity (@None V).
      * apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free.
        apply storeA_restrict_lookup_none_l. exact Hσx.
      * symmetry. apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free. exact Hσx.
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

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_fv.
Arguments stale_logic_qualifier /.

End LogicQualifier.
