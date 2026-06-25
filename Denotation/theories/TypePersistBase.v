(** * Denotation.TypePersist

    Semantic support lemmas for the type-level persistency modality. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivCore TypeEquivFiberBase TypeEquivBody TypeEquiv.
From ContextAlgebra Require Import ResourceAlgebra.

Section TypePersist.

Definition over_open_body (φ : type_qualifier) (z : atom) : FormulaT :=
  FFibVars
    (qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]})
    (FOver (FAtom (qual_open_atom 0 z φ))).

Definition under_open_body (φ : type_qualifier) (z : atom) : FormulaT :=
  FFibVars
    (qual_vars (qual_open_atom 0 z φ) ∖ {[LVFree z]})
    (FUnder (FAtom (qual_open_atom 0 z φ))).

Local Lemma singleton_fvar_in_insert_env_dom z T :
  lvars_of_atoms ({[z]} : aset) ⊆
  dom (<[LVFree z := T]> (∅ : lty_env)).
Proof.
  intros v Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [a [-> Ha]].
  apply elem_of_singleton in Ha. subst a.
  apply elem_of_dom. exists T.
  rewrite lookup_insert.
  destruct decide as [_|Hbad]; [reflexivity|contradiction].
Qed.

Local Lemma notin_union4_l (a : atom) (A B C D : aset) :
  a ∉ (((A ∪ B) ∪ C) ∪ D) ->
  a ∉ A.
Proof.
  intros Hnot Ha. apply Hnot.
  apply elem_of_union_l. apply elem_of_union_l. apply elem_of_union_l.
  exact Ha.
Qed.

Local Lemma notin_union4_r1 (a : atom) (A B C D : aset) :
  a ∉ (((A ∪ B) ∪ C) ∪ D) ->
  a ∉ B.
Proof.
  intros Hnot Ha. apply Hnot.
  apply elem_of_union_l. apply elem_of_union_l. apply elem_of_union_r.
  exact Ha.
Qed.

Local Lemma notin_union4_r2 (a : atom) (A B C D : aset) :
  a ∉ (((A ∪ B) ∪ C) ∪ D) ->
  a ∉ C.
Proof.
  intros Hnot Ha. apply Hnot.
  apply elem_of_union_l. apply elem_of_union_r.
  exact Ha.
Qed.

Local Lemma notin_union4_r3 (a : atom) (A B C D : aset) :
  a ∉ (((A ∪ B) ∪ C) ∪ D) ->
  a ∉ D.
Proof.
  intros Hnot Ha. apply Hnot.
  apply elem_of_union_r. exact Ha.
Qed.

Local Lemma fvar_in_singleton_restrict_dom
    (m my : WfWorldT) (σ : StoreT) x y :
  x ∈ world_dom (m : WorldT) ->
  (my : WorldT) σ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value).
Proof.
  intros Hxm Hσ Hdom.
  rewrite storeA_restrict_dom.
  rewrite (wfworld_store_dom my σ Hσ), Hdom.
  apply elem_of_intersection. split.
  - apply elem_of_union_l. exact Hxm.
  - apply elem_of_singleton. reflexivity.
Qed.

Local Lemma elem_union_singleton_not_eq_left (A : aset) a y :
  a ∈ A ∪ {[y]} ->
  a <> y ->
  a ∈ A.
Proof.
  intros Ha Hay.
  apply elem_of_union in Ha as [HaA|Hay'].
  - exact HaA.
  - apply elem_of_singleton in Hay'. contradiction.
Qed.

Local Lemma notin_union_singleton_of_notin_world
    (A : aset) x y (m : WfWorldT) :
  y ∉ A ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  y ∉ A ∪ {[x]}.
Proof.
  intros HyA Hxm Hym HyAx.
  apply elem_of_union in HyAx as [HyA'|Hyx].
  - exact (HyA HyA').
  - apply elem_of_singleton in Hyx. subst y. exact (Hym Hxm).
Qed.

Local Lemma notin_union_singleton_swap_ne (A : aset) a x y :
  a ∉ A ∪ {[y]} ->
  a <> x ->
  a ∉ A ∪ {[x]}.
Proof.
  intros Ha Hax HaAx.
  apply elem_of_union in HaAx as [HaA|Hax'].
  - apply Ha. apply elem_of_union_l. exact HaA.
  - apply elem_of_singleton in Hax'. subst a. contradiction.
Qed.

Local Lemma swap_opened_singleton_domain (M A : aset) x y :
  x ∈ M ->
  y ∉ M ->
  x ∉ A ->
  y ∉ A ->
  (M ∪ {[y]}) ∩ (A ∪ {[y]}) =
    set_swap x y (M ∩ (A ∪ {[x]})).
Proof.
  intros HxM HyM HxA HyA.
  assert (Hxy : x <> y).
  { intros ->. exact (HyM HxM). }
  apply set_eq. intros a.
  rewrite set_swap_elem.
  destruct (decide (a = x)) as [->|Hax].
  - replace (swap x y x) with y
      by (unfold swap; repeat destruct decide; congruence).
    split.
    + intros Hleft. exfalso.
      apply elem_of_intersection in Hleft as [_ HxAy].
      apply elem_of_union in HxAy as [HxA'|Hxy'].
      * exact (HxA HxA').
      * apply elem_of_singleton in Hxy'. contradiction.
    + intros Hright. exfalso.
      apply elem_of_intersection in Hright as [HyM' _].
      exact (HyM HyM').
  - destruct (decide (a = y)) as [->|Hay].
    + replace (swap x y y) with x
        by (unfold swap; repeat destruct decide; congruence).
      split.
      * intros _. apply elem_of_intersection. split.
        -- exact HxM.
        -- apply elem_of_union_r. apply elem_of_singleton. reflexivity.
      * intros _. apply elem_of_intersection. split.
        -- apply elem_of_union_r. apply elem_of_singleton. reflexivity.
        -- apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    + replace (swap x y a) with a
        by (unfold swap; repeat destruct decide; congruence).
      split.
      * intros Hleft.
        apply elem_of_intersection in Hleft as [HaMy HaAy].
        apply elem_of_intersection. split.
        -- apply elem_of_union in HaMy as [HaM|Hay']; [exact HaM|].
           apply elem_of_singleton in Hay'. contradiction.
        -- apply elem_of_union_l.
           apply elem_of_union in HaAy as [HaA|Hay']; [exact HaA|].
           apply elem_of_singleton in Hay'. contradiction.
      * intros Hright.
        apply elem_of_intersection in Hright as [HaM HaAx].
        apply elem_of_intersection. split.
        -- apply elem_of_union_l. exact HaM.
        -- apply elem_of_union_l.
        apply elem_of_union in HaAx as [HaA|Hax']; [exact HaA|].
           apply elem_of_singleton in Hax'. contradiction.
Qed.

Local Lemma singleton_subset_world_dom (m : WfWorldT) z :
  z ∈ world_dom (m : WorldT) ->
  ({[z]} : aset) ⊆ world_dom (m : WorldT).
Proof.
  intros Hzm a Ha. apply elem_of_singleton in Ha. subst a. exact Hzm.
Qed.

Local Lemma wfworld_closed_on_open_world_from_base
    (m my : WfWorldT) X :
  X ⊆ world_dom (m : WorldT) ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  wfworld_closed_on X m ->
  wfworld_closed_on X my.
Proof.
  intros HX Hbase Hclosed σ Hσ.
  assert (Hσm :
      (m : WorldT) (store_restrict σ (world_dom (m : WorldT)))).
  {
    assert (Hσres :
        (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ (world_dom (m : WorldT)))).
    { exists σ. split; [exact Hσ|reflexivity]. }
    rewrite Hbase in Hσres.
    exact Hσres.
  }
  specialize (Hclosed _ Hσm).
  rewrite (storeA_restrict_twice_subset σ
    (world_dom (m : WorldT)) X HX) in Hclosed.
  exact Hclosed.
Qed.

Definition over_ret_fvar_env (Σ : lty_env) b (φ : type_qualifier) z : lty_env :=
  <[LVFree z := TBase b]>
    (lty_env_restrict_lvars Σ (lvars_at_depth 1 (qual_vars φ))).

Lemma relevant_env_persist_eq Σ τ e :
  relevant_env Σ (CTPersist τ) e =
  relevant_env Σ τ e.
Proof.
  unfold relevant_env, relevant_lvars.
  cbn [context_ty_lvars context_ty_lvars_at].
  reflexivity.
Qed.

Local Lemma lvfree_notin_lvars_at_depth1_qual_vars (φ : type_qualifier) z :
  z ∉ qual_dom φ ->
  LVFree z ∉ lvars_at_depth 1 (qual_vars φ).
Proof.
  unfold qual_dom.
  intros Hz HzD.
  apply Hz.
  rewrite lvars_at_depth_elem in HzD.
  destruct HzD as [v [Hv Hat]].
  destruct v as [n|a].
  - cbn [logic_var_at_depth] in Hat.
    destruct decide; discriminate.
  - cbn [logic_var_at_depth] in Hat.
    inversion Hat. subst a.
    apply lvars_fv_elem. exact Hv.
Qed.

Lemma over_ret_fvar_env_restrict_eq Σ b φ z :
  z ∉ qual_dom φ ->
  lty_env_restrict_lvars (<[LVFree z := TBase b]> Σ)
    (relevant_lvars (CTOver b φ) (tret (vfvar z))) =
  lty_env_restrict_lvars (over_ret_fvar_env Σ b φ z)
    (relevant_lvars (CTOver b φ) (tret (vfvar z))).
Proof.
  intros Hz.
  unfold over_ret_fvar_env.
  relevant_lvars_norm.
  apply lty_env_restrict_lvars_insert_restrict_current.
  apply lvfree_notin_lvars_at_depth1_qual_vars.
  exact Hz.
Qed.

Lemma over_ret_fvar_relevant_env_restrict_eq Σ b φ z y :
  y ∉ qual_dom φ ∪ {[z]} ->
  z ∉ qual_dom φ ->
  lty_env_restrict_lvars
    (<[LVFree y := TBase b]>
      (relevant_env Σ (CTOver b φ) (tret (vfvar z))))
    (relevant_lvars (CTOver b φ) (tret (vfvar y))) =
  lty_env_restrict_lvars (over_ret_fvar_env Σ b φ y)
    (relevant_lvars (CTOver b φ) (tret (vfvar y))).
Proof.
  intros Hy Hzφ.
  unfold over_ret_fvar_env.
  relevant_lvars_norm.
  rewrite lty_env_restrict_lvars_insert_restrict_current.
  2:{
    apply lvfree_notin_lvars_at_depth1_qual_vars.
    clear -Hy. set_solver.
  }
  rewrite (relevant_env_restrict_subset Σ (CTOver b φ) (tret (vfvar z))
    (lvars_at_depth 1 (qual_vars φ))).
  - reflexivity.
  - relevant_lvars_norm. set_solver.
Qed.

Lemma insert_relevant_env_ret_fvar_restrict_eq Σ τ z y :
  y ∉ lvars_fv (dom Σ) ∪ fv_cty τ ∪ {[z]} ->
  z ∉ fv_cty τ ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τ]>
      (relevant_env Σ τ (tret (vfvar z))))
    (relevant_lvars τ (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τ]> Σ)
    (relevant_lvars τ (tret (vfvar y))).
Proof.
  intros Hy Hzτ.
  unfold relevant_env, relevant_lvars, lty_env_restrict_lvars.
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ context_ty_lvars τ ∪ tm_lvars (tret (vfvar y))))
    as [Hvrel|Hvrel]; [|reflexivity].
  destruct (decide (v = LVFree y)) as [->|Hvy].
  - rewrite !lookup_insert.
    destruct decide as [_|Hbad]; [reflexivity|contradiction].
  - rewrite !lookup_insert_ne by congruence.
    rewrite storeA_restrict_lookup.
    destruct (decide (v ∈ context_ty_lvars τ ∪ tm_lvars (tret (vfvar z))))
      as [Hvsrc|Hvsrc]; [reflexivity|].
    exfalso.
    apply elem_of_union in Hvrel as [Hvτ|Hvy_lvars].
    + apply Hvsrc. apply elem_of_union_l. exact Hvτ.
    + cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hvy_lvars.
      apply elem_of_singleton in Hvy_lvars. subst v.
      contradiction.
Qed.

Lemma formula_open_over_self_body_normalize φ z :
  LVFree z ∉ qual_vars φ ->
  formula_open 0 z
    (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ))) =
  over_open_body φ z.
Proof.
  intros Hzφ.
  unfold over_open_body.
  rewrite formula_open_fibvars, formula_open_over, formula_open_atom.
  rewrite qual_open_atom_vars.
  rewrite lvars_open0_difference_bound0_normalize by exact Hzφ.
  reflexivity.
Qed.

Lemma formula_open_under_self_body_normalize φ z :
  LVFree z ∉ qual_vars φ ->
  formula_open 0 z
    (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ))) =
  under_open_body φ z.
Proof.
  intros Hzφ.
  unfold under_open_body.
  rewrite formula_open_fibvars, formula_open_under, formula_open_atom.
  rewrite qual_open_atom_vars.
  rewrite lvars_open0_difference_bound0_normalize by exact Hzφ.
  reflexivity.
Qed.

Lemma formula_atom_swap_over_open_body φ x y :
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  formula_atom_swap x y (over_open_body φ x) =
  over_open_body φ y.
Proof.
  intros Hx Hy.
  set (P := FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ))).
  assert (Hxvars : LVFree x ∉ qual_vars φ).
  {
    intros Hbad. apply Hx.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyvars : LVFree y ∉ qual_vars φ).
  {
    intros Hbad. apply Hy.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hxfv : x ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hx Hbad)].
    apply Hx. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  assert (Hyfv : y ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hy Hbad)].
    apply Hy. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  rewrite <- (formula_open_over_self_body_normalize φ x Hxvars).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv || exact Hyfv).
  rewrite formula_open_over_self_body_normalize by exact Hyvars.
  reflexivity.
Qed.

Lemma formula_atom_swap_under_open_body φ x y :
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  formula_atom_swap x y (under_open_body φ x) =
  under_open_body φ y.
Proof.
  intros Hx Hy.
  set (P := FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ))).
  assert (Hxvars : LVFree x ∉ qual_vars φ).
  {
    intros Hbad. apply Hx.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyvars : LVFree y ∉ qual_vars φ).
  {
    intros Hbad. apply Hy.
    unfold qual_dom. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hxfv : x ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hx Hbad)].
    apply Hx. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  assert (Hyfv : y ∉ formula_fv P).
  {
    subst P. rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad]; [|exact (Hy Hbad)].
    apply Hy. unfold qual_dom.
    eapply lvars_fv_mono; [|exact Hbad].
    set_solver.
  }
  rewrite <- (formula_open_under_self_body_normalize φ x Hxvars).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv || exact Hyfv).
  rewrite formula_open_under_self_body_normalize by exact Hyvars.
  reflexivity.
Qed.

Lemma formula_fv_over_open_body_subset φ z :
  formula_fv (over_open_body φ z) ⊆ qual_dom φ ∪ {[z]}.
Proof.
  unfold over_open_body.
  rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply lvars_fv_elem in Ha.
    apply elem_of_difference in Ha as [Ha _].
    rewrite qual_open_atom_vars in Ha.
    pose proof (lvars_fv_open_subset 0 z (qual_vars φ)) as Hsub.
    assert (Ha_fv : a ∈ lvars_fv (lvars_open 0 z (qual_vars φ))).
    { apply lvars_fv_elem. exact Ha. }
    apply Hsub in Ha_fv.
    unfold qual_dom. set_solver.
  - pose proof (qual_open_atom_dom_subset 0 z φ) as Hsub.
    unfold qual_dom in Ha.
    apply Hsub in Ha. set_solver.
Qed.

Lemma basic_over_empty_fv b φ :
  basic_context_ty ∅ (CTOver b φ) ->
  fv_cty (CTOver b φ) = ∅.
Proof.
  intros Hbasic.
  apply set_eq. intros x.
  split.
  - intros Hx.
    pose proof (basic_context_ty_fv_subset ∅ (CTOver b φ) Hbasic x Hx)
      as Hempty.
    set_solver.
  - intros Hx. set_solver.
Qed.

Lemma over_open_body_closed_arg_fv b φ y :
  basic_context_ty ∅ (CTOver b φ) ->
  formula_fv (over_open_body φ y) ⊆ {[y]}.
Proof.
  intros Hbasic.
  pose proof (formula_fv_over_open_body_subset φ y) as Hfv.
  assert (Hφfv : qual_dom φ ⊆ fv_cty (CTOver b φ)).
  {
    unfold qual_dom, fv_cty, context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    reflexivity.
  }
  pose proof (basic_context_ty_fv_subset ∅ (CTOver b φ) Hbasic) as Hclosed.
  intros x Hx.
  apply Hfv in Hx.
  apply elem_of_union in Hx as [Hxφ|Hxy].
  - pose proof (Hclosed x (Hφfv x Hxφ)) as Hempty.
    set_solver.
  - exact Hxy.
Qed.

Lemma fiberwise_joinable_on_over_open_body X φ z :
  z ∉ X ->
  fiberwise_joinable_on X (over_open_body φ z).
Proof.
  intros HzX.
  unfold over_open_body.
  eapply fiberwise_joinable_on_fibvars.
  - rewrite formula_fv_over, formula_fv_atom.
    intros a Ha.
    apply elem_of_intersection in Ha as [HaX Ha].
    apply lvars_fv_elem.
    apply elem_of_difference. split.
    + apply lvars_fv_elem. exact Ha.
    + intros Haz. apply elem_of_singleton in Haz.
      inversion Haz. subst a.
    apply HzX.
      exact HaX.
  - intros σ.
    cbn [formula_msubst_store].
    apply fiberwise_joinable_on_over_atom.
Qed.

Lemma fiberwise_stable_on_over_open_body X φ z :
  formula_fv (over_open_body φ z) ⊆ X ->
  fiberwise_stable_on X (over_open_body φ z).
Proof.
  unfold over_open_body.
  apply fiberwise_stable_on_fibvars_over_atom.
Qed.

Lemma formula_fv_under_open_body_subset φ z :
  formula_fv (under_open_body φ z) ⊆ qual_dom φ ∪ {[z]}.
Proof.
  unfold under_open_body.
  rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply lvars_fv_elem in Ha.
    apply elem_of_difference in Ha as [Ha _].
    rewrite qual_open_atom_vars in Ha.
    pose proof (lvars_fv_open_subset 0 z (qual_vars φ)) as Hsub.
    assert (Ha_fv : a ∈ lvars_fv (lvars_open 0 z (qual_vars φ))).
    { apply lvars_fv_elem. exact Ha. }
    apply Hsub in Ha_fv.
    unfold qual_dom. set_solver.
  - pose proof (qual_open_atom_dom_subset 0 z φ) as Hsub.
    unfold qual_dom in Ha.
    apply Hsub in Ha. set_solver.
Qed.

Lemma under_open_body_closed_arg_fv b φ y :
  basic_context_ty ∅ (CTOver b φ) ->
  formula_fv (under_open_body φ y) ⊆ {[y]}.
Proof.
  intros Hbasic.
  pose proof (formula_fv_under_open_body_subset φ y) as Hfv.
  assert (Hφfv : qual_dom φ ⊆ fv_cty (CTOver b φ)).
  {
    unfold qual_dom, fv_cty, context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    reflexivity.
  }
  pose proof (basic_context_ty_fv_subset ∅ (CTOver b φ) Hbasic) as Hclosed.
  intros x Hx.
  apply Hfv in Hx.
  apply elem_of_union in Hx as [Hxφ|Hxy].
  - pose proof (Hclosed x (Hφfv x Hxφ)) as Hempty.
    set_solver.
  - exact Hxy.
Qed.

Lemma fiberwise_joinable_on_under_open_body X φ z :
  z ∉ X ->
  fiberwise_joinable_on X (under_open_body φ z).
Proof.
  intros HzX.
  unfold under_open_body.
  eapply fiberwise_joinable_on_fibvars.
  - rewrite formula_fv_under, formula_fv_atom.
    intros a Ha.
    apply elem_of_intersection in Ha as [HaX Ha].
    apply lvars_fv_elem.
    apply elem_of_difference. split.
    + apply lvars_fv_elem. exact Ha.
    + intros Haz. apply elem_of_singleton in Haz.
      inversion Haz. subst a. exact (HzX HaX).
  - intros σ.
    cbn [formula_msubst_store].
    apply fiberwise_joinable_on_under_any.
Qed.

Lemma ty_denote_gas_persist_open_result
    gas (Σ : lty_env) τ e y (m my : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm e ->
  y ∉ fv_tm e ->
  y ∉ lvars_fv (dom (relevant_env Σ (CTPersist τ) e)) ->
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) e ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ expr_result_formula_at
    (dom (relevant_env Σ (CTPersist τ) e)) e (LVFree y) ->
  my ⊨ formula_open 0 y
    (FPersist
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTPersist τ) e)
          (erase_ty (CTPersist τ)))
        (cty_shift 0 τ) (tret (vbvar 0)))).
Proof.
  intros HΣclosed Hlce Hye HyΣ Hden Hy Hdom Hrestrict Hresult.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hbody].
  pose proof (res_models_forall_open_named_fresh
    m my y _ Hbody Hy Hdom Hrestrict) as Hopen.
  cbn [formula_open] in Hopen.
  denotation_result_first_open_norm_in Hopen.
  eapply res_models_impl_elim; eauto.
Qed.

Lemma expr_result_formula_at_ret_fvar_lookup_eq
    D x y (m : WfWorldT) σ :
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  store_closed (store_restrict σ ({[x]} : aset)) ->
  x ∈ dom (store_restrict σ ({[x]} : aset) : StoreT) ->
  m ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  (m : WorldT) σ ->
  σ !! y = σ !! x.
Proof.
  intros HD HyD Hclosed Hxdom Hres Hσ.
  pose proof (expr_result_formula_at_models_elim
    D (tret (vfvar x)) y m HD HyD Hres σ Hσ) as Hstore.
  destruct Hstore as [_ [v [Hy Heval]]].
  assert (Heval_restrict :
      tm_eval_in_store (store_restrict σ ({[x]} : aset))
        (tret (vfvar x)) v).
  {
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tret (vfvar x)) v ({[x]} : aset)
      ltac:(cbn [fv_tm fv_value]; set_solver))).
    exact Heval.
  }
  pose proof (tm_eval_in_store_ret_fvar_inv
    (store_restrict σ ({[x]} : aset)) x v Hclosed Hxdom Heval_restrict)
    as Hx.
  rewrite lstore_lift_free_lookup_free in Hy.
  apply storeA_restrict_lookup_some in Hx as [_ Hx].
  transitivity (Some v); [exact Hy|symmetry; exact Hx].
Qed.

Lemma expr_result_formula_at_ret_fvar_flip
    Dsrc Dtgt x y (m : WfWorldT) :
  tm_lvars (tret (vfvar x)) ⊆ Dsrc ->
  LVFree y ∉ Dsrc ->
  lc_lvars Dtgt ->
  tm_lvars (tret (vfvar y)) ⊆ Dtgt ->
  LVFree x ∉ Dtgt ->
  lvars_fv Dtgt ∪ {[x; y]} ⊆ world_dom (m : WorldT) ->
  wfworld_closed_on ({[x]} : aset) m ->
  wfworld_closed_on ({[y]} : aset) m ->
  m ⊨ expr_result_formula_at Dsrc (tret (vfvar x)) (LVFree y) ->
  m ⊨ expr_result_formula_at Dtgt (tret (vfvar y)) (LVFree x).
Proof.
  intros HsrcD HyD HlcDtgt HtgtD HxD Hscope_dom Hclosed_x Hclosed_y Hres.
  eapply expr_result_formula_at_intro.
  - exact HlcDtgt.
  - exact HtgtD.
  - exact HxD.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula_at.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    rewrite lvars_fv_union, !lvars_fv_singleton_free.
    intros a Ha. apply Hscope_dom.
    set_solver.
  - intros σ Hσ.
    pose proof (expr_result_formula_at_ret_fvar_lookup_eq
      Dsrc x y m σ HsrcD HyD (Hclosed_x σ Hσ) ltac:(
        change (x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value));
        rewrite storeA_restrict_dom;
        rewrite (wfworld_store_dom m σ Hσ);
        set_solver) Hres Hσ) as Hxy.
    unfold expr_result_at_store.
    split.
    + intros Hbad. apply HxD. apply HtgtD.
      exact Hbad.
    + destruct (σ !! y) as [v|] eqn:Hylookup.
      * exists v. split.
        -- rewrite lstore_lift_free_lookup_free.
           rewrite <- Hxy. reflexivity.
        -- apply (proj1 (tm_eval_in_store_restrict_fv_subset
             σ (tret (vfvar y)) v ({[y]} : aset)
             ltac:(cbn [fv_tm fv_value]; set_solver))).
           apply tm_eval_in_store_ret_fvar_lookup.
           ++ exact (Hclosed_y σ Hσ).
           ++ change ((storeA_restrict σ ({[y]} : aset) : gmap atom value)
                !! y = Some v).
              apply storeA_restrict_lookup_some_2; [exact Hylookup|set_solver].
      * exfalso.
        apply not_elem_of_dom in Hylookup.
        apply Hylookup.
        rewrite (wfworld_store_dom m σ Hσ).
        set_solver.
  - intros σ v Hσ Heval.
    exists σ. split; [exact Hσ|]. split; [reflexivity|].
    pose proof (expr_result_formula_at_ret_fvar_lookup_eq
      Dsrc x y m σ HsrcD HyD (Hclosed_x σ Hσ) ltac:(
        change (x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value));
        rewrite storeA_restrict_dom;
        rewrite (wfworld_store_dom m σ Hσ);
        set_solver) Hres Hσ) as Hxy.
    pose proof (tm_eval_in_store_ret_fvar_inv
      (store_restrict σ ({[y]} : aset)) y v) as Hinv.
    assert (Hclosed_yσ : store_closed (store_restrict σ ({[y]} : aset))).
    { exact (Hclosed_y σ Hσ). }
    assert (Hydom :
        y ∈ dom (store_restrict σ ({[y]} : aset) : StoreT)).
    {
      change (y ∈ dom (storeA_restrict σ ({[y]} : aset) : gmap atom value)).
      rewrite storeA_restrict_dom.
      rewrite (wfworld_store_dom m σ Hσ).
      set_solver.
    }
    change (tm_eval_in_store (store_restrict σ ({[y]} : aset))
      (tret (vfvar y)) v) in Heval.
    specialize (Hinv Hclosed_yσ Hydom Heval).
    apply storeA_restrict_lookup_some in Hinv as [_ Hlookup_y].
    rewrite <- Hxy. exact Hlookup_y.
Qed.

Lemma res_restrict_ret_fvar_result_swap_projection
    A D x y (m my : WfWorldT) :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ A ->
  y ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict my (A ∪ {[y]}) =
    res_atom_swap x y (res_restrict m (A ∪ {[x]})).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom, world_dom_res_atom_swap, res_restrict_dom.
    rewrite Hdom_my.
    apply swap_opened_singleton_domain; assumption.
  - intros σ. split.
    + intros [σmy [Hσmy Hσeq]]. subst σ.
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        rewrite <- Hbase.
        subst σm. exists σmy. split; [exact Hσmy|reflexivity].
      }
      exists (store_restrict σm (A ∪ {[x]}) : StoreT). split.
      * exists σm. split; [exact Hσm|reflexivity].
      * apply storeA_map_eq. intros a.
        cbn.
        rewrite !storeA_restrict_lookup.
        destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
        -- destruct (decide (a = y)) as [->|Hay].
           ++ assert (Hxy : σmy !! y = σmy !! x).
              {
                eapply (expr_result_formula_at_ret_fvar_lookup_eq
                  D x y my σmy);
	                  [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
                eapply fvar_in_singleton_restrict_dom; eauto.
              }
              subst σm.
              change ((storeA_swap x y
                (store_restrict (store_restrict σmy (world_dom (m : WorldT)))
                  (A ∪ {[x]}) : StoreT) : gmap atom value) !! y =
                σmy !! y).
              replace y with (swap x y x) by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              replace (swap x y x) with (swap x (swap x y x) x) at 1 by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              rewrite (storeA_swap_lookup x (swap x y x)
                (store_restrict (store_restrict σmy (world_dom (m : WorldT)))
                  (A ∪ {[x]}) : StoreT) x).
              replace (swap x y x) with y by
                (unfold swap; repeat destruct decide; try congruence;
                 exfalso; apply Hym; subst; exact Hxm).
              rewrite storeA_restrict_lookup.
              rewrite decide_True by (apply elem_of_union_r; apply elem_of_singleton; reflexivity).
              rewrite storeA_restrict_lookup.
              rewrite decide_True by exact Hxm.
              symmetry. exact Hxy.
           ++ assert (HaA : a ∈ A)
                by (eapply elem_union_singleton_not_eq_left; eauto).
              change ((storeA_swap x y
                (store_restrict σm (A ∪ {[x]}) : StoreT)
                : gmap atom value) !! a = σmy !! a).
              replace a with (swap x y a) at 1 by
                (unfold swap; repeat destruct decide; set_solver).
              rewrite (storeA_swap_lookup x y
                (store_restrict σm (A ∪ {[x]}) : StoreT) a).
              rewrite storeA_restrict_lookup.
              rewrite decide_True by (apply elem_of_union_l; exact HaA).
              subst σm.
              rewrite storeA_restrict_lookup.
              rewrite decide_True by (apply HAm; exact HaA).
              unfold swap. repeat destruct decide; try congruence.
              reflexivity.
        -- change ((storeA_swap x y
              (store_restrict σm (A ∪ {[x]}) : StoreT)
              : gmap atom value) !! a = None).
           destruct (decide (a = x)) as [->|Hax].
	           ++ replace x with (swap x y y) at 1 by
	                (unfold swap; repeat destruct decide; try congruence;
	                 exfalso; apply Hym; subst; exact Hxm).
	              rewrite (storeA_swap_lookup x y
	                (store_restrict σm (A ∪ {[x]}) : StoreT) y).
	              apply storeA_restrict_lookup_none_r.
	              eapply notin_union_singleton_of_notin_world; eauto.
	           ++ replace a with (swap x y a) at 1 by
	                (unfold swap; repeat destruct decide; set_solver).
	              rewrite (storeA_swap_lookup x y
	                (store_restrict σm (A ∪ {[x]}) : StoreT) a).
	              apply storeA_restrict_lookup_none_r.
	              eapply notin_union_singleton_swap_ne; eauto.
    + intros [σr [[σm [Hσm Hσm_eq]] Hσswap]]. subst σr σ.
      assert (Hσm_proj : (res_restrict my (world_dom (m : WorldT)) : WorldT) σm).
      { rewrite Hbase. exact Hσm. }
      destruct Hσm_proj as [σmy [Hσmy Hσmy_base]].
      exists σmy. split; [exact Hσmy|].
      apply storeA_map_eq. intros a.
      cbn.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
      * destruct (decide (a = y)) as [->|Hay].
        -- assert (Hxy : σmy !! y = σmy !! x).
           {
             eapply (expr_result_formula_at_ret_fvar_lookup_eq
               D x y my σmy);
		               [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
		             eapply fvar_in_singleton_restrict_dom; eauto.
		           }
	           change (σmy !! y = (storeA_swap x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT)
	             : gmap atom value) !! y).
	           replace y with (swap x y x) at 2 by
	             (unfold swap; repeat destruct decide; try congruence;
	              exfalso; apply Hym; subst; exact Hxm).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) x).
	           rewrite storeA_restrict_lookup.
	           rewrite decide_True by set_solver.
	           assert (Hxbase : σm !! x = σmy !! x).
	           {
	             symmetry.
	             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσmy_base.
           }
	           transitivity (σmy !! x); [exact Hxy|].
	           symmetry. exact Hxbase.
        -- assert (HaA : a ∈ A)
             by (eapply elem_union_singleton_not_eq_left; eauto).
	           change (σmy !! a = (storeA_swap x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT)
	             : gmap atom value) !! a).
	           replace a with (swap x y a) at 2 by
	             (unfold swap; repeat destruct decide; set_solver).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) a).
	           rewrite storeA_restrict_lookup.
	           rewrite decide_True by (apply elem_of_union_l; exact HaA).
	           assert (Habase : σm !! a = σmy !! a).
	           {
	             symmetry.
	             eapply store_lookup_eq_of_restrict_eq_full.
	             - apply HAm. exact HaA.
	             - exact Hσmy_base.
	           }
	           symmetry. exact Habase.
	      * change (None = (storeA_swap x y
	            (store_restrict σm (A ∪ {[x]}) : StoreT)
	            : gmap atom value) !! a).
	        destruct (decide (a = x)) as [->|Hax].
	        -- replace x with (swap x y y) at 1 by
	             (unfold swap; repeat destruct decide; try congruence;
	              exfalso; apply Hym; subst; exact Hxm).
		           rewrite (storeA_swap_lookup x y
		             (store_restrict σm (A ∪ {[x]}) : StoreT) y).
		           symmetry. apply storeA_restrict_lookup_none_r.
               eapply notin_union_singleton_of_notin_world; eauto.
	        -- replace a with (swap x y a) at 1 by
	             (unfold swap; repeat destruct decide; set_solver).
		           rewrite (storeA_swap_lookup x y
		             (store_restrict σm (A ∪ {[x]}) : StoreT) a).
		           symmetry. apply storeA_restrict_lookup_none_r.
               eapply notin_union_singleton_swap_ne; eauto.
Qed.

Lemma over_open_body_transport_ret_fvar_result
    D φ x y (m my : WfWorldT) :
  qual_dom φ ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ over_open_body φ y ->
  m ⊨ over_open_body φ x.
Proof.
  intros Hφm Hxm Hym Hxφ Hyφ HD HyD Hres Hclosed_x Hdom_my Hbase Hbody_y.
  pose proof (res_restrict_ret_fvar_result_swap_projection
    (qual_dom φ) D x y m my Hφm Hxm Hym Hxφ Hyφ HD HyD Hres
    Hclosed_x Hdom_my Hbase) as Hproj.
  set (Sy := qual_dom φ ∪ {[y]}).
  set (Sx := qual_dom φ ∪ {[x]}).
  assert (Hbody_y_restrict : res_restrict my Sy ⊨ over_open_body φ y).
  {
    pose proof (res_models_minimal_on Sy my (over_open_body φ y)
      ltac:(subst Sy; apply formula_fv_over_open_body_subset)) as Hmin.
    exact (proj1 Hmin Hbody_y).
  }
  change Sy with (qual_dom φ ∪ {[y]}) in Hbody_y_restrict.
  rewrite Hproj in Hbody_y_restrict.
  assert (Hsw :
      res_atom_swap x y (res_restrict m Sx) ⊨
      formula_atom_swap x y (over_open_body φ x)).
  {
    rewrite formula_atom_swap_over_open_body by assumption.
    subst Sx. exact Hbody_y_restrict.
  }
  pose proof (proj1 (res_models_atom_swap (res_restrict m Sx)
    (over_open_body φ x) x y) Hsw) as Hbody_x_restrict.
  pose proof (res_models_minimal_on Sx m (over_open_body φ x)
    ltac:(subst Sx; apply formula_fv_over_open_body_subset)) as Hmin_x.
  exact (proj2 Hmin_x Hbody_x_restrict).
Qed.

Lemma under_open_body_transport_ret_fvar_result
    D φ x y (m my : WfWorldT) :
  qual_dom φ ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ under_open_body φ y ->
  m ⊨ under_open_body φ x.
Proof.
  intros Hφm Hxm Hym Hxφ Hyφ HD HyD Hres Hclosed_x Hdom_my Hbase Hbody_y.
  pose proof (res_restrict_ret_fvar_result_swap_projection
    (qual_dom φ) D x y m my Hφm Hxm Hym Hxφ Hyφ HD HyD Hres
    Hclosed_x Hdom_my Hbase) as Hproj.
  set (Sy := qual_dom φ ∪ {[y]}).
  set (Sx := qual_dom φ ∪ {[x]}).
  assert (Hbody_y_restrict : res_restrict my Sy ⊨ under_open_body φ y).
  {
    pose proof (res_models_minimal_on Sy my (under_open_body φ y)
      ltac:(subst Sy; apply formula_fv_under_open_body_subset)) as Hmin.
    exact (proj1 Hmin Hbody_y).
  }
  change Sy with (qual_dom φ ∪ {[y]}) in Hbody_y_restrict.
  rewrite Hproj in Hbody_y_restrict.
  assert (Hsw :
      res_atom_swap x y (res_restrict m Sx) ⊨
      formula_atom_swap x y (under_open_body φ x)).
  {
    rewrite formula_atom_swap_under_open_body by assumption.
    subst Sx. exact Hbody_y_restrict.
  }
  pose proof (proj1 (res_models_atom_swap (res_restrict m Sx)
    (under_open_body φ x) x y) Hsw) as Hbody_x_restrict.
  pose proof (res_models_minimal_on Sx m (under_open_body φ x)
    ltac:(subst Sx; apply formula_fv_under_open_body_subset)) as Hmin_x.
  exact (proj2 Hmin_x Hbody_x_restrict).
Qed.

Lemma over_open_body_push_ret_fvar_result
    D φ x y (m my : WfWorldT) :
  qual_dom φ ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  m ⊨ over_open_body φ x ->
  my ⊨ over_open_body φ y.
Proof.
  intros Hφm Hxm Hym Hxφ Hyφ HD HyD Hres Hclosed_x Hdom_my Hbase Hbody_x.
  pose proof (res_restrict_ret_fvar_result_swap_projection
    (qual_dom φ) D x y m my Hφm Hxm Hym Hxφ Hyφ HD HyD Hres
    Hclosed_x Hdom_my Hbase) as Hproj.
  set (Sy := qual_dom φ ∪ {[y]}).
  set (Sx := qual_dom φ ∪ {[x]}).
  assert (Hbody_x_restrict : res_restrict m Sx ⊨ over_open_body φ x).
  {
    pose proof (res_models_minimal_on Sx m (over_open_body φ x)
      ltac:(subst Sx; apply formula_fv_over_open_body_subset)) as Hmin.
    exact (proj1 Hmin Hbody_x).
  }
  assert (Hsw :
      res_atom_swap x y (res_restrict m Sx) ⊨
      formula_atom_swap x y (over_open_body φ x)).
  {
    apply (proj2 (res_models_atom_swap (res_restrict m Sx)
      (over_open_body φ x) x y)).
    exact Hbody_x_restrict.
  }
  rewrite formula_atom_swap_over_open_body in Hsw by assumption.
  subst Sx.
  change Sy with (qual_dom φ ∪ {[y]}).
  rewrite <- Hproj in Hsw.
  pose proof (res_models_minimal_on Sy my (over_open_body φ y)
    ltac:(subst Sy; apply formula_fv_over_open_body_subset)) as Hmin_y.
  exact (proj2 Hmin_y Hsw).
Qed.

Lemma under_open_body_push_ret_fvar_result
    D φ x y (m my : WfWorldT) :
  qual_dom φ ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ qual_dom φ ->
  y ∉ qual_dom φ ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  m ⊨ under_open_body φ x ->
  my ⊨ under_open_body φ y.
Proof.
  intros Hφm Hxm Hym Hxφ Hyφ HD HyD Hres Hclosed_x Hdom_my Hbase Hbody_x.
  pose proof (res_restrict_ret_fvar_result_swap_projection
    (qual_dom φ) D x y m my Hφm Hxm Hym Hxφ Hyφ HD HyD Hres
    Hclosed_x Hdom_my Hbase) as Hproj.
  set (Sy := qual_dom φ ∪ {[y]}).
  set (Sx := qual_dom φ ∪ {[x]}).
  assert (Hbody_x_restrict : res_restrict m Sx ⊨ under_open_body φ x).
  {
    pose proof (res_models_minimal_on Sx m (under_open_body φ x)
      ltac:(subst Sx; apply formula_fv_under_open_body_subset)) as Hmin.
    exact (proj1 Hmin Hbody_x).
  }
  assert (Hsw :
      res_atom_swap x y (res_restrict m Sx) ⊨
      formula_atom_swap x y (under_open_body φ x)).
  {
    apply (proj2 (res_models_atom_swap (res_restrict m Sx)
      (under_open_body φ x) x y)).
    exact Hbody_x_restrict.
  }
  rewrite formula_atom_swap_under_open_body in Hsw by assumption.
  subst Sx.
  change Sy with (qual_dom φ ∪ {[y]}).
  rewrite <- Hproj in Hsw.
  pose proof (res_models_minimal_on Sy my (under_open_body φ y)
    ltac:(subst Sy; apply formula_fv_under_open_body_subset)) as Hmin_y.
  exact (proj2 Hmin_y Hsw).
Qed.

Lemma ty_denote_gas_over_ret_fvar_self_body
    gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) (tret (vfvar z)) ->
  m ⊨ over_open_body φ z.
Proof.
  intros HΣclosed Hzφ Hden.
  pose proof (ty_denote_gas_guard (S gas) Σ (CTOver b φ)
    (tret (vfvar z)) m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (ty_denote_gas_ret_fvar_world_dom
    (S gas) Σ (CTOver b φ) z m Hden) as Hzm.
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [HlcD [_ Hty]].
  apply basic_world_formula_models_iff in Hworld as [_ [Hrel_dom _]].
  assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
  {
    destruct Hbasicτ as [Hvars _].
    intros a Ha.
    apply Hrel_dom.
    apply lvars_fv_elem.
    apply Hvars.
    unfold context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_at_depth_elem.
    exists (LVFree a). split.
    - rewrite <- lvars_fv_elem. exact Ha.
    - reflexivity.
  }
  set (Dres := dom (relevant_env Σ (CTOver b φ) (tret (vfvar z)))).
  assert (Hlc_D : lc_lvars Dres).
  { subst Dres. apply relevant_env_closed. exact HΣclosed. }
  assert (Htm_D : tm_lvars (tret (vfvar z)) ⊆ Dres).
  {
    intros v Hv.
    pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hty) as Hlc_tm.
    pose proof (tm_lvars_lc_subset_atoms_fv _ (tm_lvars_lc _ Hlc_tm)
      v Hv) as Hvfv.
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hfv.
    exact (Hfv v Hvfv).
  }
  set (y := fresh_for
    (world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]})).
  assert (Hyfresh :
      y ∉ world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]}).
  { subst y. apply fresh_for_not_in. }
  assert (Hym : y ∉ world_dom (m : WorldT))
    by (eapply notin_union4_l; exact Hyfresh).
  assert (Hyφ : y ∉ qual_dom φ)
    by (eapply notin_union4_r1; exact Hyfresh).
  assert (HyD : LVFree y ∉ Dres).
  {
    intros HyD.
    assert (HyDfv : y ∈ lvars_fv Dres).
    { apply lvars_fv_elem. exact HyD. }
    eapply notin_union4_r2; [exact Hyfresh|exact HyDfv].
  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar z)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
    rewrite tm_lvars_fv. exact Ha.
  - intros HyD_atoms. apply HyD. apply lvars_fv_elem. exact HyD_atoms.
  - destruct (res_extend_by_exists m Fx) as [my Hext].
    {
      constructor.
      - change (ext_in Fx ⊆ world_dom (m : WorldT)).
        destruct HFx as [_ _ [Hin _] _].
        rewrite Hin. exact Hrel_dom.
      - change (ext_out Fx ## world_dom (m : WorldT)).
        destruct HFx as [_ _ [_ Hout] _].
        rewrite Hout.
        intros a Haout Ham.
        apply elem_of_singleton in Haout. subst a. exact (Hym Ham).
    }
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    pose proof (res_extend_by_singleton_output_open_world
      m my Fx y Hext Hout_Fx) as [Hdom_my' Hbase_my].
    assert (Hres_at :
        my ⊨ expr_result_formula_at Dres (tret (vfvar z)) (LVFree y)).
    {
      eapply expr_result_formula_at_of_result_extends_on.
      - exact Hlc_D.
      - exact Htm_D.
      - exact HyD.
      - exact Hrel_dom.
      - constructor.
        + intros a Ha. apply lvars_fv_elem. apply Htm_D.
          apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
          rewrite tm_lvars_fv. exact Ha.
        + intros HyD_atoms. apply HyD. apply lvars_fv_elem. exact HyD_atoms.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    pose proof Hden as Hden_full.
    cbn [ty_denote_gas] in Hden.
    rewrite res_models_and_iff in Hden.
    destruct Hden as [_ Hforall].
    pose proof (res_models_forall_open_named_fresh
      m my y _ Hforall Hym Hdom_my' Hbase_my) as Hbody_impl.
    denotation_result_first_open_norm_in Hbody_impl.
    pose proof (res_models_impl_elim _ _ _ Hbody_impl Hres_at)
      as Hbody_open.
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      (S gas) Σ (CTOver b φ) z m Hden_full) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTOver b φ)]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(apply singleton_fvar_in_insert_env_dom) Hbasic_z) as Hclosed_z_m.
    assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
    {
      eapply wfworld_closed_on_open_world_from_base.
      - apply singleton_subset_world_dom. exact Hzm.
      - exact Hbase_my.
      - exact Hclosed_z_m.
    }
    eapply over_open_body_transport_ret_fvar_result.
    + exact Hφm.
    + exact Hzm.
    + exact Hym.
    + exact Hzφ.
    + exact Hyφ.
    + exact Htm_D.
    + exact HyD.
    + exact Hres_at.
    + exact Hclosed_z_my.
    + exact Hdom_my'.
    + exact Hbase_my.
	    + exact Hbody_open.
Qed.

Lemma ty_denote_gas_under_ret_fvar_self_body
    gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) (tret (vfvar z)) ->
  m ⊨ under_open_body φ z.
Proof.
  intros HΣclosed Hzφ Hden.
  pose proof (ty_denote_gas_guard (S gas) Σ (CTUnder b φ)
    (tret (vfvar z)) m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (ty_denote_gas_ret_fvar_world_dom
    (S gas) Σ (CTUnder b φ) z m Hden) as Hzm.
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [HlcD [_ Hty]].
  apply basic_world_formula_models_iff in Hworld as [_ [Hrel_dom _]].
  assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
  {
    destruct Hbasicτ as [Hvars _].
    intros a Ha.
    apply Hrel_dom.
    apply lvars_fv_elem.
    apply Hvars.
    unfold context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_at_depth_elem.
    exists (LVFree a). split.
    - rewrite <- lvars_fv_elem. exact Ha.
    - reflexivity.
  }
  set (Dres := dom (relevant_env Σ (CTUnder b φ) (tret (vfvar z)))).
  assert (Hlc_D : lc_lvars Dres).
  { subst Dres. apply relevant_env_closed. exact HΣclosed. }
  assert (Htm_D : tm_lvars (tret (vfvar z)) ⊆ Dres).
  {
    intros v Hv.
    pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hty) as Hlc_tm.
    pose proof (tm_lvars_lc_subset_atoms_fv _ (tm_lvars_lc _ Hlc_tm)
      v Hv) as Hvfv.
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hfv.
    exact (Hfv v Hvfv).
  }
  set (y := fresh_for
    (world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]})).
  assert (Hyfresh :
      y ∉ world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]}).
  { subst y. apply fresh_for_not_in. }
  assert (Hym : y ∉ world_dom (m : WorldT))
    by (eapply notin_union4_l; exact Hyfresh).
  assert (Hyφ : y ∉ qual_dom φ)
    by (eapply notin_union4_r1; exact Hyfresh).
  assert (HyD : LVFree y ∉ Dres).
  {
    intros HyD.
    assert (HyDfv : y ∈ lvars_fv Dres).
    { apply lvars_fv_elem. exact HyD. }
    eapply notin_union4_r2; [exact Hyfresh|exact HyDfv].
  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar z)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
    rewrite tm_lvars_fv. exact Ha.
  - intros HyD_atoms. apply HyD. apply lvars_fv_elem. exact HyD_atoms.
  - destruct (res_extend_by_exists m Fx) as [my Hext].
    {
      constructor.
      - change (ext_in Fx ⊆ world_dom (m : WorldT)).
        destruct HFx as [_ _ [Hin _] _].
        rewrite Hin. exact Hrel_dom.
      - change (ext_out Fx ## world_dom (m : WorldT)).
        destruct HFx as [_ _ [_ Hout] _].
        rewrite Hout.
        intros a Haout Ham.
        apply elem_of_singleton in Haout. subst a. exact (Hym Ham).
    }
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    pose proof (res_extend_by_singleton_output_open_world
      m my Fx y Hext Hout_Fx) as [Hdom_my' Hbase_my].
    assert (Hres_at :
        my ⊨ expr_result_formula_at Dres (tret (vfvar z)) (LVFree y)).
    {
      eapply expr_result_formula_at_of_result_extends_on.
      - exact Hlc_D.
      - exact Htm_D.
      - exact HyD.
      - exact Hrel_dom.
      - constructor.
        + intros a Ha. apply lvars_fv_elem. apply Htm_D.
          apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
          rewrite tm_lvars_fv. exact Ha.
        + intros HyD_atoms. apply HyD. apply lvars_fv_elem. exact HyD_atoms.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    pose proof Hden as Hden_full.
    cbn [ty_denote_gas] in Hden.
    rewrite res_models_and_iff in Hden.
    destruct Hden as [_ Hforall].
    pose proof (res_models_forall_open_named_fresh
      m my y _ Hforall Hym Hdom_my' Hbase_my) as Hbody_impl.
    denotation_result_first_open_norm_in Hbody_impl.
    pose proof (res_models_impl_elim _ _ _ Hbody_impl Hres_at)
      as Hbody_open.
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      (S gas) Σ (CTUnder b φ) z m Hden_full) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTUnder b φ)]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(apply singleton_fvar_in_insert_env_dom)
      Hbasic_z) as Hclosed_z_m.
    assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
    {
      eapply wfworld_closed_on_open_world_from_base.
      - apply singleton_subset_world_dom. exact Hzm.
      - exact Hbase_my.
      - exact Hclosed_z_m.
    }
    eapply under_open_body_transport_ret_fvar_result.
    + exact Hφm.
    + exact Hzm.
    + exact Hym.
    + exact Hzφ.
    + exact Hyφ.
    + exact Htm_D.
    + exact HyD.
    + exact Hres_at.
    + exact Hclosed_z_my.
    + exact Hdom_my'.
    + exact Hbase_my.
    + exact Hbody_open.
Qed.

Lemma ty_denote_gas_over_ret_fvar_self_body_iff
    gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTOver b φ) (tret (vfvar z)) <->
  m ⊨ ty_denote_gas 0 Σ (CTOver b φ) (tret (vfvar z)) /\
  m ⊨ over_open_body φ z.
Proof.
  intros HΣclosed Hzφ.
  split.
  - intros Hden. split.
    + apply ty_denote_gas_zero_of_guard.
      eapply ty_denote_gas_guard. exact Hden.
    + eapply ty_denote_gas_over_ret_fvar_self_body; eauto.
  - intros [Hzero Hbody_z].
    pose proof (ty_denote_gas_guard_of_zero
      Σ (CTOver b φ) (tret (vfvar z)) m Hzero) as Hguard.
    pose proof (ty_denote_gas_ret_fvar_world_dom
      0 Σ (CTOver b φ) z m Hzero) as Hzm.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
    apply expr_basic_typing_formula_models_iff in Hbasic as [HlcD [_ Hty]].
    apply basic_world_formula_models_iff in Hworld as [_ [Hrel_dom _]].
    assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
    {
      destruct Hbasicτ as [Hvars _].
      intros a Ha.
      apply Hrel_dom.
      apply lvars_fv_elem.
      apply Hvars.
      unfold context_ty_lvars.
      cbn [context_ty_lvars_at].
      rewrite lvars_at_depth_elem.
      exists (LVFree a). split.
      - rewrite <- lvars_fv_elem. exact Ha.
      - reflexivity.
    }
    set (Dres := dom (relevant_env Σ (CTOver b φ) (tret (vfvar z)))).
    assert (Hlc_D : lc_lvars Dres).
    { subst Dres. apply relevant_env_closed. exact HΣclosed. }
    assert (Htm_D : tm_lvars (tret (vfvar z)) ⊆ Dres).
    {
      intros v Hv.
      pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hty) as Hlc_tm.
      pose proof (tm_lvars_lc_subset_atoms_fv _ (tm_lvars_lc _ Hlc_tm)
        v Hv) as Hvfv.
      pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hfv.
      exact (Hfv v Hvfv).
    }
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      0 Σ (CTOver b φ) z m Hzero) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTOver b φ)]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(apply singleton_fvar_in_insert_env_dom) Hbasic_z) as Hclosed_z_m.
    cbn [ty_denote_gas].
    rewrite res_models_and_iff. split.
    + exact (ty_denote_gas_guard_of_zero Σ (CTOver b φ)
        (tret (vfvar z)) m Hzero).
    + assert (Hscope_full : formula_scoped_in_world m
          (ty_denote_gas (S gas) Σ (CTOver b φ) (tret (vfvar z)))).
      {
        unfold formula_scoped_in_world.
        eapply ty_denote_gas_scope_of_guard.
        - reflexivity.
        - exact (ty_denote_gas_guard_of_zero Σ (CTOver b φ)
            (tret (vfvar z)) m Hzero).
      }
      cbn [ty_denote_gas] in Hscope_full.
      pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
      eapply res_models_forall_rev_intro; [exact Hscope_forall|].
      exists (world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]}).
      intros y Hy my Hdom_my Hbase_my.
      assert (Hym : y ∉ world_dom (m : WorldT))
        by (eapply notin_union4_l; exact Hy).
      assert (Hy_my : y ∈ world_dom (my : WorldT)).
      { rewrite Hdom_my. set_solver. }
      assert (Hyφ : y ∉ qual_dom φ)
        by (eapply notin_union4_r1; exact Hy).
      assert (HyD : LVFree y ∉ Dres).
      {
        intros HyD.
        assert (HyDfv : y ∈ lvars_fv Dres).
        { apply lvars_fv_elem. exact HyD. }
        eapply notin_union4_r2; [exact Hy|exact HyDfv].
      }
      assert (Hle : m ⊑ my).
      { rewrite <- Hbase_my. apply res_restrict_le. }
      cbn [formula_open].
      denotation_result_first_open_norm.
      eapply res_models_impl_intro.
      * pose proof (formula_scoped_forall_open_res_le
          m my y
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0 Dres)
              (tm_shift 0 (tret (vfvar z))) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ))))
          Hscope_forall Hle Hy_my) as Hscope_open.
        cbn [formula_open] in Hscope_open.
        denotation_result_first_open_norm_in Hscope_open.
        exact Hscope_open.
      * intros Hres_at.
        assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
        {
          eapply wfworld_closed_on_open_world_from_base.
          - apply singleton_subset_world_dom. exact Hzm.
          - exact Hbase_my.
          - exact Hclosed_z_m.
        }
        assert (Hbody_y : my ⊨ over_open_body φ y).
        {
          eapply over_open_body_push_ret_fvar_result.
          + exact Hφm.
          + exact Hzm.
          + exact Hym.
          + exact Hzφ.
          + exact Hyφ.
          + exact Htm_D.
          + exact HyD.
          + exact Hres_at.
          + exact Hclosed_z_my.
          + exact Hdom_my.
          + exact Hbase_my.
          + exact Hbody_z.
        }
        rewrite <- formula_open_over_self_body_normalize in Hbody_y.
        -- cbn [formula_open] in Hbody_y.
           lvars_open_difference_bound0_norm_in Hbody_y.
           exact Hbody_y.
        -- intros Hyvars. apply Hyφ.
	           unfold qual_dom. apply lvars_fv_elem. exact Hyvars.
Qed.

Lemma ty_denote_gas_under_ret_fvar_self_body_iff
    gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ (CTUnder b φ) (tret (vfvar z)) <->
  m ⊨ ty_denote_gas 0 Σ (CTUnder b φ) (tret (vfvar z)) /\
  m ⊨ under_open_body φ z.
Proof.
  intros HΣclosed Hzφ.
  split.
  - intros Hden. split.
    + apply ty_denote_gas_zero_of_guard.
      eapply ty_denote_gas_guard. exact Hden.
    + eapply ty_denote_gas_under_ret_fvar_self_body; eauto.
  - intros [Hzero Hbody_z].
    pose proof (ty_denote_gas_guard_of_zero
      Σ (CTUnder b φ) (tret (vfvar z)) m Hzero) as Hguard.
    pose proof (ty_denote_gas_ret_fvar_world_dom
      0 Σ (CTUnder b φ) z m Hzero) as Hzm.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
    apply expr_basic_typing_formula_models_iff in Hbasic as [HlcD [_ Hty]].
    apply basic_world_formula_models_iff in Hworld as [_ [Hrel_dom _]].
    assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
    {
      destruct Hbasicτ as [Hvars _].
      intros a Ha.
      apply Hrel_dom.
      apply lvars_fv_elem.
      apply Hvars.
      unfold context_ty_lvars.
      cbn [context_ty_lvars_at].
      rewrite lvars_at_depth_elem.
      exists (LVFree a). split.
      - rewrite <- lvars_fv_elem. exact Ha.
      - reflexivity.
    }
    set (Dres := dom (relevant_env Σ (CTUnder b φ) (tret (vfvar z)))).
    assert (Hlc_D : lc_lvars Dres).
    { subst Dres. apply relevant_env_closed. exact HΣclosed. }
    assert (Htm_D : tm_lvars (tret (vfvar z)) ⊆ Dres).
    {
      intros v Hv.
      pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hty) as Hlc_tm.
      pose proof (tm_lvars_lc_subset_atoms_fv _ (tm_lvars_lc _ Hlc_tm)
        v Hv) as Hvfv.
      pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hfv.
      exact (Hfv v Hvfv).
    }
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      0 Σ (CTUnder b φ) z m Hzero) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTUnder b φ)]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(apply singleton_fvar_in_insert_env_dom) Hbasic_z) as Hclosed_z_m.
    cbn [ty_denote_gas].
    rewrite res_models_and_iff. split.
    + exact (ty_denote_gas_guard_of_zero Σ (CTUnder b φ)
        (tret (vfvar z)) m Hzero).
    + assert (Hscope_full : formula_scoped_in_world m
          (ty_denote_gas (S gas) Σ (CTUnder b φ) (tret (vfvar z)))).
      {
        unfold formula_scoped_in_world.
        eapply ty_denote_gas_scope_of_guard.
        - reflexivity.
        - exact (ty_denote_gas_guard_of_zero Σ (CTUnder b φ)
            (tret (vfvar z)) m Hzero).
      }
      cbn [ty_denote_gas] in Hscope_full.
      pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
      eapply res_models_forall_rev_intro; [exact Hscope_forall|].
      exists (world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]}).
      intros y Hy my Hdom_my Hbase_my.
      assert (Hym : y ∉ world_dom (m : WorldT))
        by (eapply notin_union4_l; exact Hy).
      assert (Hy_my : y ∈ world_dom (my : WorldT)).
      { rewrite Hdom_my. apply elem_of_union_r. apply elem_of_singleton. reflexivity. }
      assert (Hyφ : y ∉ qual_dom φ)
        by (eapply notin_union4_r1; exact Hy).
      assert (HyD : LVFree y ∉ Dres).
      {
        intros HyD.
        assert (HyDfv : y ∈ lvars_fv Dres).
        { apply lvars_fv_elem. exact HyD. }
        eapply notin_union4_r2; [exact Hy|exact HyDfv].
      }
      assert (Hle : m ⊑ my).
      { rewrite <- Hbase_my. apply res_restrict_le. }
      cbn [formula_open].
      denotation_result_first_open_norm.
      eapply res_models_impl_intro.
      * pose proof (formula_scoped_forall_open_res_le
          m my y
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0 Dres)
              (tm_shift 0 (tret (vfvar z))) (LVBound 0))
          (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ))))
          Hscope_forall Hle Hy_my) as Hscope_open.
        cbn [formula_open] in Hscope_open.
        denotation_result_first_open_norm_in Hscope_open.
        exact Hscope_open.
      * intros Hres_at.
        assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
        {
          eapply wfworld_closed_on_open_world_from_base.
          - apply singleton_subset_world_dom. exact Hzm.
          - exact Hbase_my.
          - exact Hclosed_z_m.
        }
        assert (Hbody_y : my ⊨ under_open_body φ y).
        {
          eapply under_open_body_push_ret_fvar_result.
          + exact Hφm.
          + exact Hzm.
          + exact Hym.
          + exact Hzφ.
          + exact Hyφ.
          + exact Htm_D.
          + exact HyD.
          + exact Hres_at.
          + exact Hclosed_z_my.
          + exact Hdom_my.
          + exact Hbase_my.
          + exact Hbody_z.
        }
        rewrite <- formula_open_under_self_body_normalize in Hbody_y.
        -- cbn [formula_open] in Hbody_y.
           lvars_open_difference_bound0_norm_in Hbody_y.
           exact Hbody_y.
        -- intros Hyvars. apply Hyφ.
	           unfold qual_dom. apply lvars_fv_elem. exact Hyvars.
Qed.

Lemma ty_denote_gas_persist_over_ret_fvar_self_body
    gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S (S gas)) Σ
    (CTPersist (CTOver b φ)) (tret (vfvar z)) ->
  m ⊨ over_open_body φ z.
Proof.
  intros HΣclosed Hzφ Hden.
  pose proof (ty_denote_gas_guard (S (S gas)) Σ
    (CTPersist (CTOver b φ)) (tret (vfvar z)) m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof (ty_denote_gas_ret_fvar_world_dom
    (S (S gas)) Σ (CTPersist (CTOver b φ)) z m Hden) as Hzm.
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [HlcD [_ Hty]].
  apply basic_world_formula_models_iff in Hworld as [_ [Hrel_dom _]].
  assert (Hφm : qual_dom φ ⊆ world_dom (m : WorldT)).
  {
    destruct Hbasicτ as [Hvars _].
    intros a Ha.
    apply Hrel_dom.
    apply lvars_fv_elem.
    apply Hvars.
    unfold context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_at_depth_elem.
    exists (LVFree a). split.
    - rewrite <- lvars_fv_elem. exact Ha.
    - reflexivity.
  }
  set (τp := CTPersist (CTOver b φ)).
  set (Dres := dom (relevant_env Σ τp (tret (vfvar z)))).
  assert (Hlc_D : lc_lvars Dres).
  { subst Dres τp. apply relevant_env_closed. exact HΣclosed. }
  assert (Htm_D : tm_lvars (tret (vfvar z)) ⊆ Dres).
  {
    intros v Hv.
    pose proof (basic_tm_has_ltype_lc _ _ _ HlcD Hty) as Hlc_tm.
    pose proof (tm_lvars_lc_subset_atoms_fv _ (tm_lvars_lc _ Hlc_tm)
      v Hv) as Hvfv.
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hfv.
    exact (Hfv v Hvfv).
  }
  set (y := fresh_for
    (world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]})).
  assert (Hyfresh :
      y ∉ world_dom (m : WorldT) ∪ qual_dom φ ∪ lvars_fv Dres ∪ {[z]}).
  { subst y. apply fresh_for_not_in. }
  assert (Hym : y ∉ world_dom (m : WorldT))
    by (eapply notin_union4_l; exact Hyfresh).
  assert (Hyφ : y ∉ qual_dom φ)
    by (eapply notin_union4_r1; exact Hyfresh).
  assert (HyD : LVFree y ∉ Dres).
  {
    intros HyD.
    assert (HyDfv : y ∈ lvars_fv Dres).
    { apply lvars_fv_elem. exact HyD. }
    eapply notin_union4_r2; [exact Hyfresh|exact HyDfv].
  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar z)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
    rewrite tm_lvars_fv. exact Ha.
  - intros HyD_atoms. apply HyD. apply lvars_fv_elem. exact HyD_atoms.
  - destruct (res_extend_by_exists m Fx) as [my Hext].
    {
      constructor.
      - change (ext_in Fx ⊆ world_dom (m : WorldT)).
        destruct HFx as [_ _ [Hin _] _].
        rewrite Hin. exact Hrel_dom.
      - change (ext_out Fx ## world_dom (m : WorldT)).
        destruct HFx as [_ _ [_ Hout] _].
        rewrite Hout.
        intros a Haout Ham.
        apply elem_of_singleton in Haout. subst a. exact (Hym Ham).
    }
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    pose proof (res_extend_by_singleton_output_open_world
      m my Fx y Hext Hout_Fx) as [Hdom_my' Hbase_my].
    assert (Hres_at :
        my ⊨ expr_result_formula_at Dres (tret (vfvar z)) (LVFree y)).
    {
      eapply expr_result_formula_at_of_result_extends_on.
      - exact Hlc_D.
      - exact Htm_D.
      - exact HyD.
      - exact Hrel_dom.
      - constructor.
        + intros a Ha. apply lvars_fv_elem. apply Htm_D.
          apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
          rewrite tm_lvars_fv. exact Ha.
	        + intros HyD_atoms. apply HyD. apply lvars_fv_elem. exact HyD_atoms.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    pose proof (ty_denote_gas_persist_open_result
      (S gas) Σ (CTOver b φ) (tret (vfvar z)) y m my
      HΣclosed
      ltac:(constructor; constructor)
      ltac:(cbn [fv_tm fv_value]; eapply notin_union4_r3; exact Hyfresh)
      ltac:(subst Dres τp; intros Hyrel; apply HyD;
        apply lvars_fv_elem; exact Hyrel)
      Hden Hym Hdom_my' Hbase_my Hres_at) as Hpersist_open.
    rewrite formula_open_persist in Hpersist_open.
    rewrite formula_open_ty_denote_gas_singleton in Hpersist_open.
    2:{
      rewrite typed_lty_env_bind_lvars_fv_dom.
      subst Dres τp. intros Hyrel.
      apply HyD. apply lvars_fv_elem. exact Hyrel.
    }
    2:{
      cbn [fv_tm fv_value].
      intros Hyempty.
      exact (not_elem_of_empty y Hyempty).
    }
    2:{
      rewrite cty_shift_fv.
      intros Hyτ. apply Hyφ.
      unfold fv_cty, context_ty_lvars in Hyτ.
      cbn [context_ty_lvars_at] in Hyτ.
      rewrite lvars_fv_lvars_at_depth in Hyτ.
      exact Hyτ.
    }
    rewrite (cty_open_shift_from_lc_fresh 0 y (CTOver b φ)) in Hpersist_open.
    2:{
      pose proof (basic_context_ty_lvars_lc _ _ HlcD Hbasicτ) as Hlcτp.
      cbn [lc_context_ty cty_lc_at] in Hlcτp.
      exact Hlcτp.
    }
    2:{
      intros Hyτ. apply Hyφ.
      unfold fv_cty, context_ty_lvars in Hyτ.
      cbn [context_ty_lvars_at] in Hyτ.
      rewrite lvars_fv_lvars_at_depth in Hyτ.
      exact Hyτ.
    }
    apply res_models_persist_elim in Hpersist_open.
    rewrite (typed_lty_env_bind_open_current y
      (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)))
      (erase_ty (CTPersist (CTOver b φ)))) in Hpersist_open.
    2:{ subst Dres τp. exact HyD. }
    2:{ apply relevant_env_closed. exact HΣclosed. }
    set (Σy :=
      <[LVFree y := erase_ty (CTPersist (CTOver b φ))]>
        (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)))) in *.
    change (my ⊨ ty_denote_gas (S gas) Σy
      (CTOver b φ) (tret (vfvar y))) in Hpersist_open.
    assert (HΣy_closed : lty_env_closed Σy).
    {
      subst Σy.
      apply lty_env_closed_insert_free.
      apply relevant_env_closed. exact HΣclosed.
    }
    pose proof (ty_denote_gas_over_ret_fvar_self_body
      gas Σy b φ y my HΣy_closed Hyφ Hpersist_open) as Hbody_y.
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      (S (S gas)) Σ (CTPersist (CTOver b φ)) z m Hden) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTPersist (CTOver b φ))]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(apply singleton_fvar_in_insert_env_dom) Hbasic_z) as Hclosed_z_m.
    assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
    {
      eapply wfworld_closed_on_open_world_from_base.
      - apply singleton_subset_world_dom. exact Hzm.
      - exact Hbase_my.
      - exact Hclosed_z_m.
    }
    eapply over_open_body_transport_ret_fvar_result.
    + exact Hφm.
    + exact Hzm.
    + exact Hym.
    + exact Hzφ.
    + exact Hyφ.
    + exact Htm_D.
    + exact HyD.
    + exact Hres_at.
    + exact Hclosed_z_my.
    + exact Hdom_my'.
    + exact Hbase_my.
    + exact Hbody_y.
Qed.

Lemma ty_guard_persist_over_to_over
    Σ b φ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (CTPersist (CTOver b φ)) e)
    (CTPersist (CTOver b φ)) e ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTOver b φ) e)
    (CTOver b φ) e.
Proof.
  intros Hguard.
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  rewrite res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom Hbasicτ]].
    split; [exact Hlc|]. split.
    + exact Hdom.
    + destruct Hbasicτ as [Hvars Hshape].
      split; [exact Hvars|exact Hshape].
  - rewrite res_models_and_iff. split.
    + exact Hworld.
    + rewrite res_models_and_iff. split.
      * exact Hbasic.
      * exact Htotal.
Qed.

Lemma ty_guard_over_to_persist_over
    Σ b φ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ (CTOver b φ) e)
    (CTOver b φ) e ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTPersist (CTOver b φ)) e)
    (CTPersist (CTOver b φ)) e.
Proof.
  intros Hguard.
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  rewrite res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom Hbasicτ]].
    split; [exact Hlc|]. split.
    + exact Hdom.
    + exact Hbasicτ.
  - rewrite res_models_and_iff. split.
    + exact Hworld.
    + rewrite res_models_and_iff. split.
      * exact Hbasic.
      * exact Htotal.
Qed.

Lemma ty_guard_to_persist
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula (relevant_env Σ τ e) τ e ->
  m ⊨ ty_guard_formula (relevant_env Σ (CTPersist τ) e)
    (CTPersist τ) e.
Proof.
  intros Hguard.
  rewrite relevant_env_persist_eq.
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  rewrite res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom Hbasicτ]].
    split; [exact Hlc|]. split.
    + exact Hdom.
    + exact Hbasicτ.
  - rewrite res_models_and_iff. split.
    + exact Hworld.
    + rewrite res_models_and_iff. split.
      * exact Hbasic.
      * exact Htotal.
Qed.

Lemma res_models_persist_intro_from_singleton_superset
    (m : WfWorldT) (φ : FormulaT) X σ :
  formula_fv φ ⊆ X ->
  dom (σ : StoreT) = X ->
  res_restrict m X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ φ ->
  m ⊨ FPersist φ.
Proof.
  intros Hfv Hdomσ Hsingle Hφ.
  change (dom (σ : gmap atom value) = X) in Hdomσ.
  eapply res_models_persist_intro
    with (σ := store_restrict σ (formula_fv φ)).
  - change (dom (storeA_restrict σ (formula_fv φ) : gmap atom value) =
      formula_fv φ).
    rewrite storeA_restrict_dom, Hdomσ.
    apply set_eq. intros a. set_solver.
  - transitivity (res_restrict (res_restrict m X) (formula_fv φ)).
    + rewrite res_restrict_restrict_eq.
      replace (X ∩ formula_fv φ) with (formula_fv φ) by set_solver.
      reflexivity.
    + rewrite Hsingle. apply res_restrict_singleton_world.
  - pose proof (res_models_minimal_on X m φ Hfv) as Hmin.
    rewrite Hsingle in Hmin.
    pose proof (proj1 Hmin Hφ) as Hsingleton_big.
    change ((exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT)
      ⊨ φ) in Hsingleton_big.
    pose proof (res_models_minimal_on (formula_fv φ)
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT)
      φ ltac:(reflexivity)) as Hmin_small.
    rewrite res_restrict_singleton_world in Hmin_small.
    exact (proj1 Hmin_small Hsingleton_big).
Qed.

Lemma ty_denote_gas_over_ret_fvar_result_alias_open
    gas Σ b φ y z D (m my : WfWorldT) :
  lty_env_closed Σ ->
  lc_lvars D ->
  z ∉ lvars_fv (dom Σ) ->
  z ∉ qual_dom φ ->
  z <> y ->
  tm_lvars (tret (vfvar y)) ⊆ D ->
  context_ty_lvars (CTOver b φ) ⊆ D ->
  LVFree z ∉ D ->
  lvars_fv D ⊆ world_dom (my : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ expr_result_formula_at D (tret (vfvar y)) (LVFree z) ->
  m ⊨ ty_denote_gas gas Σ (CTOver b φ) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree z := erase_ty (CTOver b φ)]> Σ)
    (CTOver b φ) (tret (vfvar z)).
Proof.
  intros HΣclosed HlcD HzΣ Hzφ Hzy HtmD HτD HzD HDmy Hdom_my Hbase_my
    Hres Hden.
  assert (HzΣlv : LVFree z ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HzΣ. apply lvars_fv_elem. exact Hbad.
  }
  assert (Hsource_my :
      my ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty (CTOver b φ)]> Σ)
        (CTOver b φ) (tret (vfvar y))).
  {
    rewrite (ty_denote_gas_insert_fresh_lty_env_eq
      gas Σ (CTOver b φ) (tret (vfvar y)) z (erase_ty (CTOver b φ))).
    2: exact HzΣlv.
    2:{
      intros Hzτ.
      apply Hzφ.
      unfold qual_dom.
      cbn [context_ty_lvars context_ty_lvars_at] in Hzτ.
      rewrite lvars_at_depth_elem in Hzτ.
      destruct Hzτ as [v [Hv Hdepth]].
      destruct v as [n|a].
      - cbn [logic_var_at_depth] in Hdepth.
        destruct decide; discriminate.
      - cbn [logic_var_at_depth] in Hdepth.
        inversion Hdepth. subst a.
        apply lvars_fv_elem. exact Hv.
    }
    2:{
      cbn [fv_tm fv_value].
      intros Hzy'.
      apply elem_of_singleton in Hzy'. subst z.
      exact (Hzy eq_refl).
    }
    eapply (res_models_kripke m my).
    - rewrite <- Hbase_my. apply res_restrict_le.
    - exact Hden.
  }
  eapply (ty_denote_gas_result_alias_at
    gas (<[LVFree z := erase_ty (CTOver b φ)]> Σ)
    (CTOver b φ) (tret (vfvar y)) z D my).
  - apply lty_env_closed_insert_free. exact HΣclosed.
  - exact HlcD.
  - exact HtmD.
  - exact HτD.
  - exact HzD.
  - exact HDmy.
  - apply map_lookup_insert.
  - exact Hres.
  - exact Hsource_my.
Qed.

Lemma over_ret_fvar_insert_env_to_normal_env
    gas Σ b φ z (m : WfWorldT) :
  z ∉ lvars_fv (dom Σ) ∪ qual_dom φ ->
  m ⊨ ty_denote_gas gas
    (<[LVFree z := TBase b]> Σ)
    (CTOver b φ) (tret (vfvar z)) ->
  m ⊨ ty_denote_gas gas
    (over_ret_fvar_env Σ b φ z)
    (CTOver b φ) (tret (vfvar z)).
Proof.
  intros Hz Hden.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - apply over_ret_fvar_env_restrict_eq. clear -Hz. set_solver.
  - exact Hden.
Qed.

Lemma ty_denote_gas_ret_fvar_persist_body_intro_singleton
    gas Σ τ z σ (m : WfWorldT) :
  dom (σ : StoreT) = fv_cty τ ∪ {[z]} ->
  res_restrict m (fv_cty τ ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar z)) ->
  m ⊨ FPersist
    (ty_denote_gas gas Σ τ (tret (vfvar z))).
Proof.
  intros Hdomσ Hsingle Hden.
  eapply (res_models_persist_intro_from_singleton_superset
    m
    (ty_denote_gas gas Σ τ (tret (vfvar z)))
    (fv_cty τ ∪ {[z]}) σ).
  - etransitivity; [apply ty_denote_gas_fv_subset|].
    cbn [fv_tm fv_value]. set_solver.
  - exact Hdomσ.
  - exact Hsingle.
  - exact Hden.
Qed.

Lemma ty_denote_gas_over_ret_fvar_persist_body_intro_singleton
    gas Σ b φ z σ (m : WfWorldT) :
  dom (σ : StoreT) = fv_cty (CTOver b φ) ∪ {[z]} ->
  res_restrict m (fv_cty (CTOver b φ) ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas (over_ret_fvar_env Σ b φ z)
    (CTOver b φ) (tret (vfvar z)) ->
  m ⊨ FPersist
    (ty_denote_gas gas (over_ret_fvar_env Σ b φ z)
      (CTOver b φ) (tret (vfvar z))).
Proof.
  apply ty_denote_gas_ret_fvar_persist_body_intro_singleton.
Qed.

Lemma ty_denote_gas_persist_over_ret_fvar_elim
    gas Σ b φ z (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote_gas (S gas) Σ
    (CTPersist (CTOver b φ)) (tret (vfvar z)) ->
  m ⊨ ty_denote_gas gas Σ (CTOver b φ) (tret (vfvar z)).
Proof.
  intros HΣclosed Hzφ Hden.
  destruct gas as [|gas].
  - apply ty_denote_gas_zero_of_guard_formula.
    apply ty_guard_persist_over_to_over.
    eapply ty_denote_gas_guard_formula. exact Hden.
  - apply ty_denote_gas_over_ret_fvar_self_body_iff; [exact HΣclosed|exact Hzφ|].
    split.
    + apply ty_denote_gas_zero_of_guard_formula.
      apply ty_guard_persist_over_to_over.
      eapply ty_denote_gas_guard_formula. exact Hden.
    + eapply ty_denote_gas_persist_over_ret_fvar_self_body; eauto.
Qed.

Lemma ty_denote_persist_over_ret_fvar_elim
    Δ b φ z (m : WfWorldT) :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  z ∉ qual_dom φ ->
  m ⊨ ty_denote Δ (CTPersist (CTOver b φ)) (tret (vfvar z)) ->
  m ⊨ ty_denote Δ (CTOver b φ) (tret (vfvar z)).
Proof.
  intros HΔclosed Hzφ Hden.
  unfold ty_denote in *.
  cbn [cty_depth] in Hden |- *.
  eapply ty_denote_gas_persist_over_ret_fvar_elim; eauto.
Qed.


End TypePersist.
