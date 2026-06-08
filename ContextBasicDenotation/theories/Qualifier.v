(** * BasicDenotation.Qualifier

    Interpreting type qualifiers as exact logic-qualifier worlds. *)

From ContextBasicDenotation Require Import Notation TermOpen.
From ContextAlgebra Require Import ResourceAlgebra.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Section QualifierDenotation.

Definition lstore_in_lworld_on
    {D : lvset} (s : LStoreOn D) (w : LWorldOn D) : Prop :=
  worldA_stores (@lw value _ w : LWorld) (lso_store s).

Definition type_qualifier_holds_lworld
    (q : type_qualifier) (w : LWorldOn (qual_vars q)) : Prop :=
  forall s : LStoreOn (qual_vars q),
    qual_prop q s <-> lstore_in_lworld_on s w.

Lemma lstore_in_lworld_on_open_back k x D
    (s : LStoreOn (lvars_open k x D))
    (w : LWorldOn (lvars_open k x D)) :
  lstore_in_lworld_on (lstore_on_open_back k x D s)
    (lworld_on_open_back k x D w) <->
  lstore_in_lworld_on s w.
Proof.
  unfold lstore_in_lworld_on, lstore_on_open_back, lworld_on_open_back.
  cbn [lw lso_store lraw_world raw_worldA worldA_stores].
  split.
  - intros [σ0 [Hσ0 Hswap]].
    change (storeA_swap (LVBound k) (LVFree x) σ0 =
      lstore_swap (LVBound k) (LVFree x) (lso_store s)) in Hswap.
    assert (σ0 = lso_store s) as ->.
    {
      rewrite <- (storeA_swap_involutive (LVBound k) (LVFree x) σ0).
      rewrite Hswap.
      change (storeA_swap (LVBound k) (LVFree x)
        (lstore_swap (LVBound k) (LVFree x) (lso_store s)) = lso_store s).
      unfold lstore_swap, lstore_rekey.
      apply storeA_swap_involutive.
    }
    exact Hσ0.
  - intros Hs.
    exists (lso_store s). split; [exact Hs|].
    unfold lstore_swap, lstore_rekey. reflexivity.
Qed.

Lemma lstore_in_lworld_on_open_front k x D
    (s : LStoreOn D) (w : LWorldOn (lvars_open k x D)) :
  lstore_in_lworld_on s (lworld_on_open_back k x D w) <->
  lstore_in_lworld_on (lstore_on_open_front k x s) w.
Proof.
  unfold lstore_in_lworld_on, lstore_on_open_front, lworld_on_open_back.
  cbn [lw lso_store lraw_world raw_worldA worldA_stores].
  split.
  - intros [σ0 [Hσ0 Hswap]].
    change (storeA_swap (LVBound k) (LVFree x) σ0 =
      lso_store s) in Hswap.
    assert (σ0 = lstore_swap (LVBound k) (LVFree x) (lso_store s)) as ->.
    {
      rewrite <- (storeA_swap_involutive (LVBound k) (LVFree x) σ0).
      rewrite Hswap.
      unfold lstore_swap, lstore_rekey. reflexivity.
    }
    exact Hσ0.
  - intros Hs.
    exists (lstore_swap (LVBound k) (LVFree x) (lso_store s)).
    split; [exact Hs|].
    unfold lstore_swap, lstore_rekey.
    apply storeA_swap_involutive.
Qed.

Lemma res_models_atom_exact_iff q (m : WfWorldT) :
  res_models m (FAtom q) <->
  qualifier_exact_denote q m.
Proof.
  unfold res_models.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden]. exact Hden.
  - intros Hden. split; [|exact Hden].
    destruct q as [D P]. cbn [qualifier_exact_denote] in Hden.
    destruct Hden as [_ [Hsub _]].
    unfold formula_scoped_in_world.
    rewrite formula_fv_atom.
    cbn [qual_dom qual_vars qual_lvars].
    exact Hsub.
Qed.

Lemma lt_qual_open_vars b x y :
  x <> y ->
  qual_vars
    (qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y))) =
  ({[LVFree x; LVFree y]} : lvset).
Proof.
  intros Hxy.
  rewrite qual_open_atom_vars.
  unfold mk_q_lt_base, qual_vars.
  cbn [qual_lvars lvar_value_keys].
  rewrite set_swap_union, !set_swap_singleton.
  base_swap_normalize.
  better_set_solver.
Qed.

Lemma lt_qual_open_fibvars_set b z y :
  z <> y ->
  set_swap (LVBound 0) (LVFree z)
    (qual_vars (mk_q_lt_base b (vbvar 0) (vfvar y)) ∖ {[LVBound 0]}) =
  qual_vars (qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y))) ∖
    {[LVFree z]}.
Proof.
  intros Hzy.
  replace
    (qual_vars (mk_q_lt_base b (vbvar 0) (vfvar y)) ∖ {[LVBound 0]})
    with ({[LVFree y]} : lvset).
  2:{
    unfold mk_q_lt_base, qual_vars.
    cbn [qual_lvars lvar_value_keys].
    better_set_solver.
  }
  rewrite set_swap_singleton.
  base_swap_normalize.
  rewrite lt_qual_open_vars by exact Hzy.
  better_set_solver.
Qed.

Lemma lt_qual_open_prop_iff b x y
    (Hxy : x <> y)
    (s : LStoreOnT
      (qual_vars
        (qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y))))) :
  qual_prop
    (qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y))) s <->
  exists cx cy,
    (lso_store s : LStoreT) !! LVFree x = Some (vconst cx) /\
    (lso_store s : LStoreT) !! LVFree y = Some (vconst cy) /\
    constant_lt_for_base b cx cy.
Proof.
  unfold qual_open_atom, mk_q_lt_base.
  cbn [qual_prop qual_lvars lvar_value_keys denote_lvar_value
    lstore_on_open_back lso_store].
  unfold lstore_on_open_back.
  cbn [lso_store storeAO_store].
  rewrite !lstore_swap_lookup_inv_value.
  base_swap_normalize.
  tauto.
Qed.

Lemma lt_type_qualifier_open_lookup b x y
    (Hxy : x <> y) (m : WfWorldT) σ :
  res_models m (FAtom
      (qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y)))) ->
  (m : WorldT) σ ->
  exists cx cy,
    σ !! x = Some (vconst cx) /\
    σ !! y = Some (vconst cy) /\
    constant_lt_for_base b cx cy.
Proof.
  intros Hqual Hσ.
  apply res_models_atom_exact_iff in Hqual.
  destruct Hqual as [Hlc [Hscope Hholds]].
  set (q := qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y))).
  set (D := qual_vars q).
  set (s_store := storeA_restrict (lstore_lift_free σ : LStoreT) D).
  assert (Hx_dom : x ∈ dom (σ : StoreT)).
  {
    change (x ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ).
    apply Hscope. subst D q.
    change (x ∈ lvars_fv
      (qual_vars (qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y))))).
    rewrite lt_qual_open_vars by exact Hxy.
    rewrite lvars_fv_union, !lvars_fv_singleton_free. better_set_solver.
  }
  assert (Hy_dom : y ∈ dom (σ : StoreT)).
  {
    change (y ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ).
    apply Hscope. subst D q.
    change (y ∈ lvars_fv
      (qual_vars (qual_open_atom 0 x (mk_q_lt_base b (vbvar 0) (vfvar y))))).
    rewrite lt_qual_open_vars by exact Hxy.
    rewrite lvars_fv_union, !lvars_fv_singleton_free. better_set_solver.
  }
  assert (Hs_dom : dom (s_store : gmap logic_var value) = D).
  {
    subst s_store D q.
    rewrite storeA_restrict_dom, dom_lstore_lift_free.
    rewrite lt_qual_open_vars by exact Hxy.
    apply set_eq. intros v. split.
    - intros Hv.
      apply elem_of_intersection in Hv as [_ Hv].
      exact Hv.
    - intros Hv.
      apply elem_of_intersection. split; [|exact Hv].
      unfold lvars_of_atoms.
      apply elem_of_union in Hv as [Hv|Hv].
      + apply elem_of_singleton in Hv. subst v.
        apply elem_of_map. eexists. split; [reflexivity|exact Hx_dom].
      + apply elem_of_singleton in Hv. subst v.
        apply elem_of_map. eexists. split; [reflexivity|exact Hy_dom].
  }
  pose (s :=
    ({| storeAO_store := s_store; storeAO_dom := Hs_dom |}
      : StoreAOn (K := logic_var) (V := value) D)).
  assert (Hmem : lstore_in_lworld_on s (lworld_on_lift D m Hlc Hscope)).
  {
    unfold s, lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lso_store lraw_world raw_worldA worldA_stores storeAO_store].
    exists (lstore_lift_free (store_restrict σ (lvars_fv D))).
    split.
    - exists (store_restrict σ (lvars_fv D)).
      split.
      + exists σ. split; [exact Hσ|reflexivity].
      + reflexivity.
    - apply lstore_lift_free_restrict_fv_lvars_eq.
  }
  pose proof (proj2 (Hholds s) Hmem) as Hprop.
  apply lt_qual_open_prop_iff in Hprop.
  2:{ exact Hxy. }
  destruct Hprop as [cx [cy [Hx [Hy Hlt]]]].
  exists cx, cy.
  split; [|split].
  - change ((s_store : LStoreT) !! LVFree x = Some (vconst cx)) in Hx.
    subst s_store.
    change (((storeA_restrict (lstore_lift_free σ : LStoreT) D
        : gmap logic_var value) !! LVFree x) =
      Some (vconst cx)) in Hx.
    unfold storeA_restrict, map_restrict in Hx.
    apply map_lookup_filter_Some in Hx as [Hx _].
    rewrite lstore_lift_free_lookup_free in Hx.
    exact Hx.
  - change ((s_store : LStoreT) !! LVFree y = Some (vconst cy)) in Hy.
    subst s_store.
    change (((storeA_restrict (lstore_lift_free σ : LStoreT) D
        : gmap logic_var value) !! LVFree y) =
      Some (vconst cy)) in Hy.
    unfold storeA_restrict, map_restrict in Hy.
    apply map_lookup_filter_Some in Hy as [Hy _].
    rewrite lstore_lift_free_lookup_free in Hy.
    exact Hy.
  - exact Hlt.
Qed.

Lemma lstore_in_lworld_on_mlsubst_back_self
    (D : lvset) (ρ : LStoreT)
    (w : LWorldOn (D ∖ dom (ρ : gmap logic_var value)))
    (s : LStoreOnT (D ∖ dom (ρ : gmap logic_var value))) :
  lstore_in_lworld_on s w ->
  lstore_in_lworld_on
    (lstore_on_mlsubst_back D ρ s)
    (lworld_on_mlsubst_back D ρ w).
Proof.
  intros Hs.
  unfold lstore_in_lworld_on, lstore_on_mlsubst_back,
    lworld_on_mlsubst_back in *.
  cbn [lw lso_store lraw_world raw_worldA worldA_stores storeAO_store].
  set (ρD := storeA_restrict ρ D).
  exists (lso_store s), ρD.
  split; [exact Hs|].
  split; [unfold ρD; reflexivity|].
  split.
  - apply storeA_disj_dom_compat.
    change (dom (lso_store s : LStoreT) ∩ dom (ρD : LStoreT) = ∅).
    assert (HρDdom : dom (ρD : LStoreT) = dom (ρ : LStoreT) ∩ D).
    { subst ρD. apply storeA_restrict_dom. }
    rewrite (lso_dom s).
    rewrite HρDdom.
    better_set_solver.
  - reflexivity.
Qed.

Lemma lt_type_qualifier_open_msubst_lookup b z y
    (Hzy : z <> y) (σy : StoreT) (m : WfWorldT) σ :
  dom (σy : StoreT) = {[y]} ->
  res_models m (formula_msubst_store σy
      (FAtom
        (qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y))))) ->
  (m : WorldT) σ ->
  exists cz cy,
    σ !! z = Some (vconst cz) /\
    σy !! y = Some (vconst cy) /\
    constant_lt_for_base b cz cy.
Proof.
  intros Hσy_dom Hqual Hσ.
  formula_msubst_syntax_norm_in Hqual.
  unfold res_models in Hqual.
  cbn [formula_measure res_models_fuel] in Hqual.
  destruct Hqual as [_ Hqual].
  cbn [qualifier_exact_denote qual_msubst_store qual_mlsubst] in Hqual.
  set (q := qual_open_atom 0 z (mk_q_lt_base b (vbvar 0) (vfvar y))).
  set (D := qual_vars q).
  set (ρ := lstore_lift_free σy : LStoreT).
  destruct Hqual as [Hlc [Hscope Hholds]].
  set (D' := D ∖ dom (ρ : LStoreT)).
  set (s_store := storeA_restrict (lstore_lift_free σ : LStoreT) D').
  assert (HD : D = ({[LVFree z; LVFree y]} : lvset)).
  { subst D q. rewrite lt_qual_open_vars by exact Hzy. reflexivity. }
  assert (Hρ_dom : dom (ρ : LStoreT) = {[LVFree y]}).
  {
    subst ρ.
    rewrite dom_lstore_lift_free.
    change (lvars_of_atoms (dom (σy : StoreT)) = {[LVFree y]}).
    rewrite Hσy_dom.
    unfold lvars_of_atoms. rewrite set_map_singleton_L. reflexivity.
  }
  assert (HD' : D' = ({[LVFree z]} : lvset)).
  {
    subst D'. rewrite HD, Hρ_dom.
    better_set_solver.
  }
  assert (Hz_dom : z ∈ dom (σ : StoreT)).
  {
    change (z ∈ dom (σ : gmap atom value)).
    rewrite (wfworld_store_dom m σ Hσ).
    apply Hscope.
    change (z ∈ lvars_fv D').
    rewrite HD'. rewrite lvars_fv_singleton_free. better_set_solver.
  }
  assert (Hs_dom : dom (s_store : gmap logic_var value) = D').
  {
    subst s_store.
    rewrite storeA_restrict_dom, dom_lstore_lift_free.
    apply set_eq. intros v. split.
    - intros Hv. apply elem_of_intersection in Hv as [_ Hv]. exact Hv.
    - intros Hv. apply elem_of_intersection. split; [|exact Hv].
      unfold lvars_of_atoms.
      rewrite HD' in Hv.
      apply elem_of_singleton in Hv. subst v.
      apply elem_of_map. eexists. split; [reflexivity|exact Hz_dom].
  }
  pose (s' :=
    ({| storeAO_store := s_store; storeAO_dom := Hs_dom |}
      : StoreAOn (K := logic_var) (V := value) D')).
  assert (Hmem' : lstore_in_lworld_on s' (lworld_on_lift D' m Hlc Hscope)).
  {
    unfold s', lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lso_store lraw_world raw_worldA worldA_stores storeAO_store].
    exists (lstore_lift_free (store_restrict σ (lvars_fv D'))).
    split.
    - exists (store_restrict σ (lvars_fv D')).
      split.
      + exists σ. split; [exact Hσ|reflexivity].
      + reflexivity.
    - apply lstore_lift_free_restrict_fv_lvars_eq.
  }
  specialize (Hholds s').
  pose proof (proj2 Hholds Hmem') as Hprop.
  change (qual_prop q (lstore_on_mlsubst_back D ρ s')) in Hprop.
  subst q.
  apply lt_qual_open_prop_iff in Hprop; [|exact Hzy].
  destruct Hprop as [cz [cy [Hz [Hy Hlt]]]].
  exists cz, cy.
  split; [|split].
  - unfold lstore_on_mlsubst_back in Hz.
    cbn [lso_store storeAO_store] in Hz.
    unfold s_store in Hz.
    apply map_lookup_union_Some_raw in Hz as [Hz | [_ Hz]].
    + unfold storeA_restrict, map_restrict in Hz.
      apply map_lookup_filter_Some in Hz as [Hz _].
      rewrite lstore_lift_free_lookup_free in Hz.
      exact Hz.
    + unfold storeA_restrict, map_restrict in Hz.
      apply map_lookup_filter_Some in Hz as [Hz _].
      assert (Hρz : (ρ : LStoreT) !! LVFree z = σy !! z).
      { subst ρ. apply lstore_lift_free_lookup_free. }
      replace ((ρ : LStoreT) !! LVFree z) with (σy !! z) in Hz
        by (symmetry; exact Hρz).
      assert (Hznone : σy !! z = None).
      {
        change ((σy : gmap atom value) !! z = None).
        apply not_elem_of_dom_1.
        change (z ∉ dom (σy : gmap atom value)).
        change (dom (σy : gmap atom value) = {[y]}) in Hσy_dom.
        rewrite Hσy_dom. better_set_solver.
      }
      rewrite Hznone in Hz. discriminate.
  - unfold lstore_on_mlsubst_back in Hy.
    cbn [lso_store storeAO_store] in Hy.
    apply map_lookup_union_Some_raw in Hy as [Hy | [_ Hy]].
    + unfold s_store in Hy.
      apply storeA_restrict_lookup_some in Hy as [HyD _].
      change (LVFree y ∈ D') in HyD.
      rewrite HD' in HyD. better_set_solver.
    + unfold storeA_restrict, map_restrict in Hy.
      apply map_lookup_filter_Some in Hy as [Hy _].
      assert (Hρy : (ρ : LStoreT) !! LVFree y = σy !! y).
      { subst ρ. apply lstore_lift_free_lookup_free. }
      replace ((ρ : LStoreT) !! LVFree y) with (σy !! y) in Hy
        by (symmetry; exact Hρy).
      exact Hy.
  - exact Hlt.
Qed.

End QualifierDenotation.
