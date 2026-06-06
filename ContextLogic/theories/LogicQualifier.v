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

#[global] Instance stale_logic_qualifier : Stale logic_qualifier := lqual_fv.
Arguments stale_logic_qualifier /.

End LogicQualifier.
