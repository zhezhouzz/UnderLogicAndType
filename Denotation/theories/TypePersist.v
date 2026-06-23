(** * Denotation.TypePersist

    Semantic support lemmas for the type-level persistency modality. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivCore TypeEquivFiberBase TypeEquiv.
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

Definition over_ret_fvar_env (Σ : lty_env) b (φ : type_qualifier) z : lty_env :=
  <[LVFree z := TBase b]>
    (lty_env_restrict_lvars Σ (lvars_at_depth 1 (qual_vars φ))).

Lemma relevant_env_persist_over_ret_fvar_eq Σ b φ z :
  relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)) =
  relevant_env Σ (CTOver b φ) (tret (vfvar z)).
Proof.
  unfold relevant_env, relevant_lvars.
  cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
    value_lvars_at lvar_value_keys].
  reflexivity.
Qed.

Lemma relevant_env_persist_eq Σ τ e :
  relevant_env Σ (CTPersist τ) e =
  relevant_env Σ τ e.
Proof.
  unfold relevant_env, relevant_lvars.
  cbn [context_ty_lvars context_ty_lvars_at].
  reflexivity.
Qed.

Lemma over_ret_fvar_env_restrict_eq Σ b φ z :
  z ∉ lvars_fv (dom Σ) ∪ qual_dom φ ->
  lty_env_restrict_lvars (<[LVFree z := TBase b]> Σ)
    (relevant_lvars (CTOver b φ) (tret (vfvar z))) =
  lty_env_restrict_lvars (over_ret_fvar_env Σ b φ z)
    (relevant_lvars (CTOver b φ) (tret (vfvar z))).
Proof.
  intros Hz.
  unfold over_ret_fvar_env.
  unfold relevant_lvars, lty_env_restrict_lvars.
  cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
    value_lvars_at lvar_value_keys].
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ lvars_at_depth 1 (qual_vars φ) ∪ {[LVFree z]}))
    as [Hvrel|Hvrel].
  2:{ reflexivity. }
  destruct (decide (v = LVFree z)) as [->|Hvz_ne].
  - rewrite !lookup_insert.
    destruct decide as [_|Hbad].
    2:{
      exfalso. apply Hbad. reflexivity.
    }
    reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    destruct (decide (v ∈ lvars_at_depth 1 (qual_vars φ))) as [Hvφ|Hvφ].
    + rewrite storeA_restrict_lookup.
      destruct decide as [_|Hbad]; [reflexivity|contradiction].
    + exfalso.
      apply elem_of_union in Hvrel as [Hvφ'|Hvz].
      * exact (Hvφ Hvφ').
      * apply elem_of_singleton in Hvz. exact (Hvz_ne Hvz).
Qed.

Lemma over_ret_fvar_relevant_env_restrict_eq Σ b φ z y :
  y ∉ lvars_fv (dom Σ) ∪ qual_dom φ ∪ {[z]} ->
  z ∉ qual_dom φ ->
  lty_env_restrict_lvars
    (<[LVFree y := TBase b]>
      (relevant_env Σ (CTOver b φ) (tret (vfvar z))))
    (relevant_lvars (CTOver b φ) (tret (vfvar y))) =
  lty_env_restrict_lvars (over_ret_fvar_env Σ b φ y)
    (relevant_lvars (CTOver b φ) (tret (vfvar y))).
Proof.
  intros Hy Hzφ.
  unfold over_ret_fvar_env, relevant_env, relevant_lvars,
    lty_env_restrict_lvars.
  cbn [context_ty_lvars context_ty_lvars_at tm_lvars tm_lvars_at
    value_lvars_at lvar_value_keys].
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ lvars_at_depth 1 (qual_vars φ) ∪ {[LVFree y]}))
    as [Hvrel|Hvrel].
  2:{ reflexivity. }
  destruct (decide (v = LVFree y)) as [->|Hvy_ne].
  - rewrite !lookup_insert.
    destruct decide as [_|Hbad].
    2:{ exfalso. apply Hbad. reflexivity. }
    reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    destruct (decide (v ∈ lvars_at_depth 1 (qual_vars φ))) as [Hvφ|Hvφ].
    + rewrite storeA_restrict_lookup.
      destruct decide as [_|Hbad].
      2:{ exfalso. apply Hbad. apply elem_of_union_l. exact Hvφ. }
      rewrite storeA_restrict_lookup.
      destruct decide as [_|Hbad].
      2:{ exfalso. apply Hbad. exact Hvφ. }
      reflexivity.
    + exfalso.
      apply elem_of_union in Hvrel as [Hvφ'|Hvy].
      * exact (Hvφ Hvφ').
      * apply elem_of_singleton in Hvy. exact (Hvy_ne Hvy).
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

Lemma lvars_open0_difference_bound0_normalize D z :
  LVFree z ∉ D ->
  lvars_open 0 z (D ∖ {[LVBound 0]}) =
  lvars_open 0 z D ∖ {[LVFree z]}.
Proof.
  intros HzD.
  apply set_eq. intros a.
  rewrite elem_of_difference.
  split.
  - intros Ha.
    split.
    + change (a ∈ set_swap (LVBound 0) (LVFree z) D).
      change (a ∈ set_swap (LVBound 0) (LVFree z)
        (D ∖ {[LVBound 0]})) in Ha.
      rewrite elem_of_set_swap in Ha.
      rewrite elem_of_set_swap.
      set_solver.
    + intros Haz.
      apply elem_of_singleton in Haz. subst a.
      change (LVFree z ∈ set_swap (LVBound 0) (LVFree z)
        (D ∖ {[LVBound 0]})) in Ha.
      rewrite elem_of_set_swap in Ha.
      apply elem_of_difference in Ha as [_ Hnot].
      apply Hnot. apply elem_of_singleton.
      unfold swap. rewrite decide_False by discriminate.
      rewrite decide_True by reflexivity. reflexivity.
  - intros [Ha Haz].
    change (a ∈ set_swap (LVBound 0) (LVFree z) D) in Ha.
    change (a ∈ set_swap (LVBound 0) (LVFree z)
      (D ∖ {[LVBound 0]})).
    rewrite elem_of_set_swap in Ha.
    rewrite elem_of_set_swap.
    apply elem_of_difference. split; [exact Ha|].
    intros Hbound.
    apply Haz. apply elem_of_singleton.
    apply elem_of_singleton in Hbound.
    unfold swap in Hbound.
    repeat destruct decide; congruence.
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

Lemma ty_denote_gas_persist_open_result
    gas (Σ : lty_env) τ e y (m my : WfWorldT) :
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) e ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTPersist τ) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  my ⊨ formula_open 0 y
    (FPersist
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTPersist τ) e)
          (erase_ty (CTPersist τ)))
        (cty_shift 0 τ) (tret (vbvar 0)))).
Proof.
  intros Hden Hy Hdom Hrestrict Hresult.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hbody].
  eapply result_first_forall_impl_open_elim; eauto.
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
    apply set_eq. intros a.
    rewrite elem_of_intersection, elem_of_union.
    rewrite set_swap_elem, elem_of_intersection, elem_of_union.
    unfold swap. repeat destruct decide; set_solver.
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
                change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
                rewrite storeA_restrict_dom.
                rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
                set_solver.
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
              rewrite decide_True by set_solver.
              rewrite storeA_restrict_lookup.
              rewrite decide_True by exact Hxm.
              symmetry. exact Hxy.
           ++ assert (HaA : a ∈ A) by set_solver.
              change ((storeA_swap x y
                (store_restrict σm (A ∪ {[x]}) : StoreT)
                : gmap atom value) !! a = σmy !! a).
              replace a with (swap x y a) at 1 by
                (unfold swap; repeat destruct decide; set_solver).
              rewrite (storeA_swap_lookup x y
                (store_restrict σm (A ∪ {[x]}) : StoreT) a).
              rewrite storeA_restrict_lookup.
              rewrite decide_True by set_solver.
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
              apply storeA_restrict_lookup_none_r. set_solver.
           ++ replace a with (swap x y a) at 1 by
                (unfold swap; repeat destruct decide; set_solver).
              rewrite (storeA_swap_lookup x y
                (store_restrict σm (A ∪ {[x]}) : StoreT) a).
              apply storeA_restrict_lookup_none_r. set_solver.
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
	             change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
	             rewrite storeA_restrict_dom.
	             rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
	             set_solver.
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
	        -- assert (HaA : a ∈ A) by set_solver.
	           change (σmy !! a = (storeA_swap x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT)
	             : gmap atom value) !! a).
	           replace a with (swap x y a) at 2 by
	             (unfold swap; repeat destruct decide; set_solver).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) a).
	           rewrite storeA_restrict_lookup.
	           rewrite decide_True by set_solver.
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
	           symmetry. apply storeA_restrict_lookup_none_r. set_solver.
	        -- replace a with (swap x y a) at 1 by
	             (unfold swap; repeat destruct decide; set_solver).
	           rewrite (storeA_swap_lookup x y
	             (store_restrict σm (A ∪ {[x]}) : StoreT) a).
	           symmetry. apply storeA_restrict_lookup_none_r. set_solver.
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
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (HyD : LVFree y ∉ Dres).
  {
    intros HyD.
    assert (HyDfv : y ∈ lvars_fv Dres).
    { apply lvars_fv_elem. exact HyD. }
    apply Hyfresh.
    set_solver.
  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar z)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
    rewrite tm_lvars_fv. exact Ha.
  - intros HyD_atoms. set_solver.
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
    pose proof (res_extend_by_dom m Fx my Hext) as Hdom_my.
    pose proof (res_extend_by_restrict_base m Fx my Hext) as Hbase_my.
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    assert (Hdom_my' :
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
    {
      rewrite Hdom_my.
      change (extA_out Fx) with (ext_out Fx).
      rewrite Hout_Fx. reflexivity.
    }
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
        + intros HyD_atoms. set_solver.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    assert (Hres_open :
        my ⊨ formula_open 0 y
          (expr_result_formula_at
            (lvars_shift_from 0 Dres)
            (tm_shift 0 (tret (vfvar z))) (LVBound 0))).
    {
      subst Dres.
      eapply result_first_outer_result_ret_value_at_open.
      - exact HΣclosed.
      - constructor.
      - cbn [fv_value]. set_solver.
      - intros Hyrel. apply HyD. apply lvars_fv_elem. exact Hyrel.
      - exact Hres_at.
    }
    pose proof Hden as Hden_full.
    cbn [ty_denote_gas] in Hden.
    rewrite res_models_and_iff in Hden.
    destruct Hden as [_ Hforall].
    pose proof (result_first_forall_impl_open_elim m my y
      (expr_result_formula_at
        (lvars_shift_from 0 Dres)
        (tm_shift 0 (tret (vfvar z))) (LVBound 0))
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ)))
      Hforall Hym Hdom_my' Hbase_my Hres_open) as Hbody_open.
    rewrite formula_open_over_self_body_normalize in Hbody_open.
    2:{
      intros Hyvars. apply Hyφ.
      unfold qual_dom. apply lvars_fv_elem. exact Hyvars.
    }
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      (S gas) Σ (CTOver b φ) z m Hden_full) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTOver b φ)]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(set_solver) Hbasic_z) as Hclosed_z_m.
    assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
    {
      intros σ Hσ.
      assert (Hσm :
          (m : WorldT)
            (store_restrict σ (world_dom (m : WorldT)))).
      {
        assert (Hσres :
            (res_restrict my (world_dom (m : WorldT)) : WorldT)
              (store_restrict σ (world_dom (m : WorldT)))).
        { exists σ. split; [exact Hσ|reflexivity]. }
        rewrite Hbase_my in Hσres.
        exact Hσres.
      }
      specialize (Hclosed_z_m _ Hσm).
      assert (Hzsub : ({[z]} : aset) ⊆ world_dom (m : WorldT))
        by set_solver.
      rewrite (storeA_restrict_twice_subset σ
        (world_dom (m : WorldT)) ({[z]} : aset) Hzsub) in Hclosed_z_m.
      exact Hclosed_z_m.
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
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (HyD : LVFree y ∉ Dres).
  {
    intros HyD.
    assert (HyDfv : y ∈ lvars_fv Dres).
    { apply lvars_fv_elem. exact HyD. }
    apply Hyfresh.
    set_solver.
  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar z)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
    rewrite tm_lvars_fv. exact Ha.
  - intros HyD_atoms. set_solver.
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
    pose proof (res_extend_by_dom m Fx my Hext) as Hdom_my.
    pose proof (res_extend_by_restrict_base m Fx my Hext) as Hbase_my.
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    assert (Hdom_my' :
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
    {
      rewrite Hdom_my.
      change (extA_out Fx) with (ext_out Fx).
      rewrite Hout_Fx. reflexivity.
    }
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
        + intros HyD_atoms. set_solver.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    assert (Hres_open :
        my ⊨ formula_open 0 y
          (expr_result_formula_at
            (lvars_shift_from 0 Dres)
            (tm_shift 0 (tret (vfvar z))) (LVBound 0))).
    {
      subst Dres.
      eapply result_first_outer_result_ret_value_at_open.
      - exact HΣclosed.
      - constructor.
      - cbn [fv_value]. set_solver.
      - intros Hyrel. apply HyD. apply lvars_fv_elem. exact Hyrel.
      - exact Hres_at.
    }
    pose proof Hden as Hden_full.
    cbn [ty_denote_gas] in Hden.
    rewrite res_models_and_iff in Hden.
    destruct Hden as [_ Hforall].
    pose proof (result_first_forall_impl_open_elim m my y
      (expr_result_formula_at
        (lvars_shift_from 0 Dres)
        (tm_shift 0 (tret (vfvar z))) (LVBound 0))
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ)))
      Hforall Hym Hdom_my' Hbase_my Hres_open) as Hbody_open.
    rewrite formula_open_under_self_body_normalize in Hbody_open.
    2:{
      intros Hyvars. apply Hyφ.
      unfold qual_dom. apply lvars_fv_elem. exact Hyvars.
    }
    pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
      (S gas) Σ (CTUnder b φ) z m Hden_full) as Hbasic_z.
    pose proof (basic_world_formula_wfworld_closed_on_atoms
      (<[LVFree z := erase_ty (CTUnder b φ)]> (∅ : lty_env))
      ({[z]} : aset) m ltac:(set_solver) Hbasic_z) as Hclosed_z_m.
    assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
    {
      intros σ Hσ.
      assert (Hσm :
          (m : WorldT)
            (store_restrict σ (world_dom (m : WorldT)))).
      {
        assert (Hσres :
            (res_restrict my (world_dom (m : WorldT)) : WorldT)
              (store_restrict σ (world_dom (m : WorldT)))).
        { exists σ. split; [exact Hσ|reflexivity]. }
        rewrite Hbase_my in Hσres.
        exact Hσres.
      }
      specialize (Hclosed_z_m _ Hσm).
      assert (Hzsub : ({[z]} : aset) ⊆ world_dom (m : WorldT))
        by set_solver.
      rewrite (storeA_restrict_twice_subset σ
        (world_dom (m : WorldT)) ({[z]} : aset) Hzsub) in Hclosed_z_m.
      exact Hclosed_z_m.
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
      ({[z]} : aset) m ltac:(set_solver) Hbasic_z) as Hclosed_z_m.
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
      assert (Hym : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
      assert (Hy_my : y ∈ world_dom (my : WorldT)).
      { rewrite Hdom_my. set_solver. }
      assert (Hyφ : y ∉ qual_dom φ) by (clear -Hy; set_solver).
      assert (HyD : LVFree y ∉ Dres).
      {
        intros HyD.
        assert (HyDfv : y ∈ lvars_fv Dres).
        { apply lvars_fv_elem. exact HyD. }
        clear -Hy HyDfv. set_solver.
      }
      assert (Hle : m ⊑ my).
      { rewrite <- Hbase_my. apply res_restrict_le. }
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
        exact Hscope_open.
      * intros Hres_open.
        assert (Hres_at :
            my ⊨ expr_result_formula_at Dres (tret (vfvar z)) (LVFree y)).
        {
          subst Dres.
          eapply result_first_outer_result_ret_value_at.
          - exact HΣclosed.
          - constructor.
          - cbn [fv_value]. set_solver.
          - intros Hyrel. apply HyD. apply lvars_fv_elem. exact Hyrel.
          - exact Hres_open.
        }
        assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
        {
          intros σ Hσ.
          assert (Hσm :
              (m : WorldT)
                (store_restrict σ (world_dom (m : WorldT)))).
          {
            assert (Hσres :
                (res_restrict my (world_dom (m : WorldT)) : WorldT)
                  (store_restrict σ (world_dom (m : WorldT)))).
            { exists σ. split; [exact Hσ|reflexivity]. }
            rewrite Hbase_my in Hσres.
            exact Hσres.
          }
          specialize (Hclosed_z_m _ Hσm).
          assert (Hzsub : ({[z]} : aset) ⊆ world_dom (m : WorldT))
            by set_solver.
          rewrite (storeA_restrict_twice_subset σ
            (world_dom (m : WorldT)) ({[z]} : aset) Hzsub) in Hclosed_z_m.
          exact Hclosed_z_m.
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
        -- cbn [formula_open] in Hbody_y. exact Hbody_y.
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
      ({[z]} : aset) m ltac:(set_solver) Hbasic_z) as Hclosed_z_m.
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
      assert (Hym : y ∉ world_dom (m : WorldT)) by (clear -Hy; set_solver).
      assert (Hy_my : y ∈ world_dom (my : WorldT)).
      { rewrite Hdom_my. set_solver. }
      assert (Hyφ : y ∉ qual_dom φ) by (clear -Hy; set_solver).
      assert (HyD : LVFree y ∉ Dres).
      {
        intros HyD.
        assert (HyDfv : y ∈ lvars_fv Dres).
        { apply lvars_fv_elem. exact HyD. }
        clear -Hy HyDfv. set_solver.
      }
      assert (Hle : m ⊑ my).
      { rewrite <- Hbase_my. apply res_restrict_le. }
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
        exact Hscope_open.
      * intros Hres_open.
        assert (Hres_at :
            my ⊨ expr_result_formula_at Dres (tret (vfvar z)) (LVFree y)).
        {
          subst Dres.
          eapply result_first_outer_result_ret_value_at.
          - exact HΣclosed.
          - constructor.
          - cbn [fv_value]. set_solver.
          - intros Hyrel. apply HyD. apply lvars_fv_elem. exact Hyrel.
          - exact Hres_open.
        }
        assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
        {
          intros σ Hσ.
          assert (Hσm :
              (m : WorldT)
                (store_restrict σ (world_dom (m : WorldT)))).
          {
            assert (Hσres :
                (res_restrict my (world_dom (m : WorldT)) : WorldT)
                  (store_restrict σ (world_dom (m : WorldT)))).
            { exists σ. split; [exact Hσ|reflexivity]. }
            rewrite Hbase_my in Hσres.
            exact Hσres.
          }
          specialize (Hclosed_z_m _ Hσm).
          assert (Hzsub : ({[z]} : aset) ⊆ world_dom (m : WorldT))
            by set_solver.
          rewrite (storeA_restrict_twice_subset σ
            (world_dom (m : WorldT)) ({[z]} : aset) Hzsub) in Hclosed_z_m.
          exact Hclosed_z_m.
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
        -- cbn [formula_open] in Hbody_y. exact Hbody_y.
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
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hyφ : y ∉ qual_dom φ) by set_solver.
  assert (HyD : LVFree y ∉ Dres).
  {
    intros HyD.
    assert (HyDfv : y ∈ lvars_fv Dres).
    { apply lvars_fv_elem. exact HyD. }
    apply Hyfresh. set_solver.
  }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dres) (tret (vfvar z)) y) as [Fx HFx].
  - intros a Ha.
    apply lvars_fv_elem.
    apply Htm_D.
    apply (proj1 (lvars_fv_elem (tm_lvars (tret (vfvar z))) a)).
    rewrite tm_lvars_fv. exact Ha.
  - intros HyD_atoms. set_solver.
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
    pose proof (res_extend_by_dom m Fx my Hext) as Hdom_my.
    pose proof (res_extend_by_restrict_base m Fx my Hext) as Hbase_my.
    destruct HFx as [_ _ [Hin_Fx Hout_Fx] Hrel_Fx].
    assert (Hdom_my' :
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
    {
      rewrite Hdom_my.
      change (extA_out Fx) with (ext_out Fx).
      rewrite Hout_Fx. reflexivity.
    }
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
        + intros HyD_atoms. set_solver.
        + split; [exact Hin_Fx|exact Hout_Fx].
        + exact Hrel_Fx.
      - exact Hext.
      - apply expr_total_formula_to_atom_world. exact Htotal.
    }
    assert (Hres_open :
        my ⊨ formula_open 0 y
          (expr_result_formula_at
            (lvars_shift_from 0 Dres)
            (tm_shift 0 (tret (vfvar z))) (LVBound 0))).
    {
      subst Dres τp.
      eapply result_first_outer_result_ret_value_at_open.
      - exact HΣclosed.
      - constructor.
      - cbn [fv_value]. set_solver.
      - intros Hyrel. apply HyD. apply lvars_fv_elem. exact Hyrel.
      - exact Hres_at.
    }
    pose proof (ty_denote_gas_persist_open_result
      (S gas) Σ (CTOver b φ) (tret (vfvar z)) y m my Hden
      Hym Hdom_my' Hbase_my Hres_open) as Hpersist_open.
    rewrite formula_open_persist in Hpersist_open.
    rewrite formula_open_ty_denote_gas_singleton in Hpersist_open.
    2:{
      rewrite typed_lty_env_bind_lvars_fv_dom.
      subst Dres τp. intros Hyrel.
      apply HyD. apply lvars_fv_elem. exact Hyrel.
    }
    2:{ cbn [fv_tm fv_value]. set_solver. }
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
      ({[z]} : aset) m ltac:(set_solver) Hbasic_z) as Hclosed_z_m.
    assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
    {
      intros σ Hσ.
      assert (Hσm :
          (m : WorldT)
            (store_restrict σ (world_dom (m : WorldT)))).
      {
        assert (Hσres :
            (res_restrict my (world_dom (m : WorldT)) : WorldT)
              (store_restrict σ (world_dom (m : WorldT)))).
        { exists σ. split; [exact Hσ|reflexivity]. }
        rewrite Hbase_my in Hσres.
        exact Hσres.
      }
      specialize (Hclosed_z_m _ Hσm).
      assert (Hzsub : ({[z]} : aset) ⊆ world_dom (m : WorldT))
        by set_solver.
      rewrite (storeA_restrict_twice_subset σ
        (world_dom (m : WorldT)) ({[z]} : aset) Hzsub) in Hclosed_z_m.
      exact Hclosed_z_m.
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
  - apply over_ret_fvar_env_restrict_eq. exact Hz.
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

Lemma arrow_value_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr ef (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  lc_context_ty (cty_shift 0 (CTOver bx φx)) ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world m
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (cty_shift 0 (CTPersist (CTOver bx φx))) τr ef) ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_src Σ
    (cty_shift 0 (CTOver bx φx)) τr ef ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (cty_shift 0 (CTPersist (CTOver bx φx))) τr ef.
Proof.
  intros HΣclosed Hlc_over Hlc_shift_over
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue.
  cbn [arrow_value_denote_gas_with] in Hvalue |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  destruct gas_tgt' as [|gas_tgt'']; [lia|].
  destruct (res_models_forall_rev _ _ Hvalue) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro.
  { exact Hscope_tgt. }
	  exists (Lsrc ∪ lvars_fv (dom Σ) ∪ qual_dom φx ∪
	    fv_cty τr ∪ fv_tm ef).
  intros y Hy my Hdom Hrestrict.
  cbn [formula_open].
  eapply res_models_impl_intro.
  {
    pose proof (formula_scoped_forall_open_res_le m my y
      (FImpl
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ
            (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx)))))
          (cty_shift 0 (cty_shift 0 (CTPersist (CTOver bx φx))))
          (tret (vbvar 0)))
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ
            (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx)))))
          τr (tapp_tm (tm_shift 0 ef) (vbvar 0))))
      Hscope_tgt
      ltac:(rewrite <- Hrestrict; apply res_restrict_le)
      ltac:(rewrite Hdom; apply elem_of_union_r; apply elem_of_singleton;
        reflexivity)) as Hopened_scope.
    cbn [formula_open] in Hopened_scope.
    exact Hopened_scope.
  }
  intros Harg_persist.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by (clear -Hy; set_solver).
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
	  assert (Hyφ : y ∉ qual_dom φx) by (clear -Hy; set_solver).
	  assert (Hyτr : y ∉ fv_cty τr) by (clear -Hy; set_solver).
	  assert (Hyef : y ∉ fv_tm ef) by (clear -Hy; set_solver).
  assert (Harg_over :
      my ⊨ formula_open 0 y
        (ty_denote_gas (S gas_src')
          (typed_lty_env_bind Σ (erase_ty (cty_shift 0 (CTOver bx φx))))
          (cty_shift 0 (cty_shift 0 (CTOver bx φx))) (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2: {
      rewrite typed_lty_env_bind_lvars_fv_dom.
      exact HyΣ.
    }
    2:{
      cbn [fv_tm fv_value]. intros Hin.
      rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      rewrite !cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2: exact Hlc_shift_over.
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
	    replace (lvar_store_open_one 0 y
	      (typed_lty_env_bind Σ (erase_ty (cty_shift 0 (CTOver bx φx)))))
	      with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
	    2:{
	      rewrite cty_shift_preserves_erasure.
	      symmetry.
	      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	    }
	    assert (Harg_over_base :
	        my ⊨ ty_denote_gas (S gas_tgt'')
	          (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	          (cty_shift 0 (CTOver bx φx)) (tret (vfvar y))).
	    {
	      rewrite formula_open_ty_denote_gas_singleton in Harg_persist.
      2: {
        rewrite typed_lty_env_bind_lvars_fv_dom.
        exact HyΣ.
      }
      2:{
        cbn [fv_tm fv_value]. intros Hin.
        rewrite elem_of_empty in Hin. contradiction.
      }
      2:{
        rewrite !cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφ.
      }
	      replace (lvar_store_open_one 0 y
	        (typed_lty_env_bind Σ
	          (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx))))))
	        with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	        in Harg_persist.
	      2:{
	        rewrite cty_shift_preserves_erasure.
	        symmetry.
	        apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	      }
	      replace (cty_open 0 y
	        (cty_shift 0 (cty_shift 0 (CTPersist (CTOver bx φx)))))
	        with (cty_shift 0 (CTPersist (CTOver bx φx))) in Harg_persist.
	      2:{
	        symmetry. apply cty_open_shift_from_lc_fresh.
	        - cbn [lc_context_ty cty_lc_at]. exact Hlc_shift_over.
	        - rewrite cty_shift_fv.
	          unfold fv_cty, qual_dom in *.
	          cbn [context_ty_lvars context_ty_lvars_at] in *.
	          rewrite lvars_fv_lvars_at_depth.
	          exact Hyφ.
	      }
	      cbn [open_tm open_value] in Harg_persist.
	      change (cty_shift 0 (CTPersist (CTOver bx φx)))
	        with (CTPersist (CTOver bx (qual_shift_from 1 φx))) in Harg_persist.
	      change (cty_shift 0 (CTOver bx φx))
	        with (CTOver bx (qual_shift_from 1 φx)).
	      eapply (ty_denote_gas_persist_over_ret_fvar_elim
	        (S gas_tgt'')
	        (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	        bx (qual_shift_from 1 φx) y).
	      - apply lty_env_closed_insert_free. exact HΣclosed.
	      - unfold qual_dom.
	        change (qual_lvars (qual_shift_from 1 φx)) with
	          (qual_vars (qual_shift_from 1 φx)).
	        rewrite qual_shift_from_vars.
	        rewrite lvars_shift_from_fv.
	        exact Hyφ.
	      - exact Harg_persist.
	    }
	    rewrite (ty_denote_gas_saturate (S gas_src')
	      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	      (cty_shift 0 (CTOver bx φx)) (tret (vfvar y)))
	      by (rewrite cty_shift_preserves_depth; cbn [cty_depth]; lia).
	    rewrite (ty_denote_gas_saturate (S gas_tgt'')
	      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	      (cty_shift 0 (CTOver bx φx)) (tret (vfvar y))) in Harg_over_base
	      by (rewrite cty_shift_preserves_depth; cbn [cty_depth]; lia).
	    exact Harg_over_base.
	  }
  assert (HyLsrc : y ∉ Lsrc) by (clear -Hy; set_solver).
  pose proof (Hsrc y HyLsrc my Hdom Hrestrict)
    as Hopened_src.
  cbn [formula_open] in Hopened_src.
	  pose proof (res_models_impl_elim _ _ _ Hopened_src Harg_over) as Hres.
	  rewrite formula_open_ty_denote_gas_singleton in Hres.
	  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
	  2:{
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_tm fv_value].
	    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
	    - exact (Hyef Hin).
	    - rewrite elem_of_empty in Hin. contradiction.
	  }
	  2:{ exact Hyτr. }
	  rewrite formula_open_ty_denote_gas_singleton.
	  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
	  2:{
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_tm fv_value].
	    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
	    - exact (Hyef Hin).
	    - rewrite elem_of_empty in Hin. contradiction.
	  }
	  2:{ exact Hyτr. }
	  replace (lvar_store_open_one 0 y
	    (typed_lty_env_bind Σ (erase_ty (cty_shift 0 (CTOver bx φx)))))
	    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ) in Hres.
	  2:{
	    rewrite cty_shift_preserves_erasure.
	    symmetry.
	    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	  }
	  replace (lvar_store_open_one 0 y
	    (typed_lty_env_bind Σ
	      (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx))))))
	    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
	  2:{
	    rewrite cty_shift_preserves_erasure.
	    symmetry.
	    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	  }
	  rewrite (ty_denote_gas_saturate (S gas_src')
	    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	    (cty_open 0 y τr)
	    (open_tm 0 (vfvar y)
	      (tapp_tm (tm_shift 0 ef) (vbvar 0)))) in Hres
	    by (rewrite cty_open_preserves_depth; lia).
	  rewrite (ty_denote_gas_saturate (S (S gas_tgt''))
	    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	    (cty_open 0 y τr)
	    (open_tm 0 (vfvar y)
	      (tapp_tm (tm_shift 0 ef) (vbvar 0))))
	    by (rewrite cty_open_preserves_depth; lia).
	  exact Hres.
Qed.

Lemma ty_guard_arrow_over_arg_to_persist_over_arg
    Σ bx φx τr e (m : WfWorldT) :
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
      (CTArrow (CTOver bx φx) τr) e ->
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
      (CTArrow (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros Hguard.
  change (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
    with (relevant_env Σ (CTArrow (CTOver bx φx) τr) e).
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hdom Hbasic_ty]].
    split; [exact Hlc|]. split; [exact Hdom|].
    destruct Hbasic_ty as [Hvars Hshape].
    split.
    + cbn [context_ty_lvars context_ty_lvars_at] in Hvars |- *.
      exact Hvars.
    + cbn [context_ty_shape_ok] in Hshape |- *.
      exact Hshape.
  - split; [exact Hworld|split; [exact Hbasic|exact Htotal]].
Qed.

Lemma cty_lc_at_shift_at d τ :
  cty_lc_at d τ ->
  cty_lc_at d (cty_shift d τ).
Proof.
  induction τ in d |- *; cbn [cty_lc_at cty_shift]; intros Hlc;
    try tauto.
  - rewrite qual_shift_from_vars.
    rewrite lvars_shift_from_lc_at_id by exact Hlc.
    exact Hlc.
  - rewrite qual_shift_from_vars.
    rewrite lvars_shift_from_lc_at_id by exact Hlc.
    exact Hlc.
  - destruct Hlc as [H1 H2]. split; [apply IHτ1|apply IHτ2]; assumption.
  - destruct Hlc as [H1 H2]. split; [apply IHτ1|apply IHτ2]; assumption.
  - destruct Hlc as [H1 H2]. split; [apply IHτ1|apply IHτ2]; assumption.
  - destruct Hlc as [H1 H2]. split.
    + apply IHτ1. exact H1.
    + apply IHτ2. exact H2.
  - destruct Hlc as [H1 H2]. split.
    + apply IHτ1. exact H1.
    + apply IHτ2. exact H2.
  - apply IHτ. exact Hlc.
Qed.

Lemma formula_open_arrow_value_ret_bvar0
    gas (Σ : lty_env) τx τr f :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ->
  f ∉ fv_cty τr ->
  formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas Σ τx τr
      (tret (vbvar 0))) =
  arrow_value_denote_gas_with ty_denote_gas gas Σ τx τr
    (tret (vfvar f)).
Proof.
  intros HΣclosed HfΣ Hlcτx Hlcτr Hfτx Hfτr.
  unfold arrow_value_denote_gas_with.
  cbn [formula_open].
  rewrite (formula_open_ty_denote_gas_singleton 1 f gas
    (typed_lty_env_bind Σ (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))).
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom.
      intros Hbad. apply HfΣ. apply lvars_fv_elem. exact Hbad. }
  2:{ cbn [fv_tm fv_value]. intros Hbad.
      rewrite elem_of_empty in Hbad. contradiction. }
  2:{ rewrite cty_shift_fv. exact Hfτx. }
  rewrite (formula_open_ty_denote_gas_singleton 1 f gas
    (typed_lty_env_bind Σ (erase_ty τx))
    τr (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))).
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom.
      intros Hbad. apply HfΣ. apply lvars_fv_elem. exact Hbad. }
  2:{ rewrite fv_tapp_tm, tm_shift_fv.
      cbn [fv_tm fv_value].
      intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad];
        rewrite elem_of_empty in Hbad; contradiction. }
  2:{ exact Hfτr. }
  cbn [open_tm open_value value_shift].
	  repeat (destruct (decide (0 = 0)) as [_|Hbad]; [|lia]).
	  rewrite lvar_store_bind_open_under.
	  2: exact HfΣ.
	  rewrite lvar_store_open_one_fresh_noop.
	  2:{
	    intros Hbound.
	    unfold lvar_store_closed in HΣclosed.
	    exact (HΣclosed (LVBound 0) Hbound).
	  }
	  2: exact HfΣ.
	  rewrite cty_open_shift_under_gen by lia.
	  change (cty_shift 0 (open_one 0 f τx)) with
	    (cty_shift 0 (cty_open 0 f τx)).
	  rewrite (cty_open_above_lc_fresh 0 0 f τx)
	    by (try lia; try exact Hlcτx; exact Hfτx).
	  rewrite (cty_open_above_lc_fresh 1 1 f τr)
	    by (try lia; try exact Hlcτr; exact Hfτr).
	  cbn [open_tm open_value value_shift].
	  repeat (destruct decide; try lia; try congruence).
	  reflexivity.
Qed.

Lemma formula_open_result_first_arrow_value_ret_bvar0
    gas (Σ : lty_env) τx τr Tf f :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ->
  f ∉ fv_cty τr ->
  formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))) =
  arrow_value_denote_gas_with ty_denote_gas gas
    (<[LVFree f := Tf]> Σ) τx τr (tret (vfvar f)).
Proof.
  intros HΣclosed HfΣ Hlcτx Hlcτr Hfτx Hfτr.
  unfold arrow_value_denote_gas_with.
  cbn [formula_open].
  rewrite (formula_open_ty_denote_gas_singleton 1 f gas
    (typed_lty_env_bind (typed_lty_env_bind Σ Tf)
      (erase_ty (cty_shift 0 τx)))
    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))).
  2:{
    rewrite !typed_lty_env_bind_lvars_fv_dom.
    intros Hbad. apply HfΣ. apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  2:{ rewrite !cty_shift_fv. exact Hfτx. }
  rewrite (formula_open_ty_denote_gas_singleton 1 f gas
    (typed_lty_env_bind (typed_lty_env_bind Σ Tf)
      (erase_ty (cty_shift 0 τx)))
    (cty_shift 1 τr)
    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))).
  2:{
    rewrite !typed_lty_env_bind_lvars_fv_dom.
    intros Hbad. apply HfΣ. apply lvars_fv_elem. exact Hbad.
  }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value]. set_solver.
  }
  2:{ rewrite cty_shift_fv. exact Hfτr. }
  cbn [open_tm open_value value_shift].
  repeat (destruct (decide (1 = 1)) as [_|Hbad]; [|lia]).
  repeat (destruct (decide (1 = 0)) as [Hbad|_]; [lia|]).
  change (open_tm 1 (vfvar f)
    (tapp_tm (tret (vbvar 1)) (vbvar 0)))
    with (tapp_tm (tret (vfvar f)) (vbvar 0)).
  rewrite lvar_store_bind_open_under.
  2:{
    rewrite typed_lty_env_bind_dom.
    intros Hbad.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply HfΣ.
      unfold lvars_shift_from in Hbad.
      apply elem_of_map in Hbad as [v [Hv HvIn]].
      destruct v; inversion Hv; subst.
      exact HvIn.
    - apply elem_of_singleton in Hbad. discriminate.
  }
  rewrite (typed_lty_env_bind_open_current f Σ Tf HfΣ HΣclosed).
  rewrite cty_shift_preserves_erasure.
  rewrite cty_open_shift_under_gen by lia.
  change (@open_one atom context_ty open_cty_atom_inst 0 f
    (cty_shift 0 τx)) with (cty_open 0 f (cty_shift 0 τx)).
  rewrite (cty_open_shift_from_lc_fresh 0 f τx Hlcτx Hfτx).
  rewrite (cty_open_shift_from_lc_fresh 1 f τr Hlcτr Hfτr).
  reflexivity.
Qed.

Lemma arrow_open_value_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr f (mf : WfWorldT) :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty (CTOver bx φx) ->
  lc_context_ty (cty_shift 0 (CTOver bx φx)) ->
  cty_lc_at 1 τr ->
  f ∉ qual_dom φx ->
  f ∉ fv_cty τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world mf
    (formula_open 0 f
      (arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
        (cty_shift 0 (CTPersist (CTOver bx φx))) τr
        (tret (vbvar 0)))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas_src Σ
      (cty_shift 0 (CTOver bx φx)) τr
      (tret (vbvar 0))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (cty_shift 0 (CTPersist (CTOver bx φx))) τr
      (tret (vbvar 0))).
Proof.
  intros HΣclosed HfΣ Hlc_over Hlc_shift_over Hlcτr Hfφ Hfτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue_src.
	  rewrite (formula_open_arrow_value_ret_bvar0
	    gas_tgt Σ
    (cty_shift 0 (CTPersist (CTOver bx φx))) τr f) in Hscope_tgt.
  2: exact HΣclosed.
  2: exact HfΣ.
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_shift_over. }
  2: exact Hlcτr.
	  2:{
	    rewrite cty_shift_fv.
	    unfold fv_cty, qual_dom in *.
	    cbn [context_ty_lvars context_ty_lvars_at] in *.
	    rewrite lvars_fv_lvars_at_depth.
	    exact Hfφ.
	  }
  2: exact Hfτr.
	  rewrite (formula_open_arrow_value_ret_bvar0
	    gas_src Σ (cty_shift 0 (CTOver bx φx)) τr f) in Hvalue_src.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: exact Hlc_shift_over.
  2: exact Hlcτr.
	  2:{
	    rewrite cty_shift_fv.
	    unfold fv_cty, qual_dom in *.
	    cbn [context_ty_lvars context_ty_lvars_at] in *.
	    rewrite lvars_fv_lvars_at_depth.
	    exact Hfφ.
	  }
  2: exact Hfτr.
	  rewrite (formula_open_arrow_value_ret_bvar0
	    gas_tgt Σ
    (cty_shift 0 (CTPersist (CTOver bx φx))) τr f).
  2: exact HΣclosed.
  2: exact HfΣ.
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_shift_over. }
  2: exact Hlcτr.
	  2:{
	    rewrite cty_shift_fv.
	    unfold fv_cty, qual_dom in *.
	    cbn [context_ty_lvars context_ty_lvars_at] in *.
	    rewrite lvars_fv_lvars_at_depth.
	    exact Hfφ.
	  }
  2: exact Hfτr.
  eapply arrow_value_over_arg_to_persist_over_arg.
  - exact HΣclosed.
  - exact Hlc_over.
  - exact Hlc_shift_over.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - exact Hscope_tgt.
  - exact Hvalue_src.
Qed.

Lemma arrow_value_over_arg_to_persist_over_arg_plain
    gas_src gas_tgt (Σ : lty_env) bx φx τr ef (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world m
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (CTPersist (CTOver bx φx)) τr ef) ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_src Σ
    (CTOver bx φx) τr ef ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (CTPersist (CTOver bx φx)) τr ef.
Proof.
  intros HΣclosed Hlc_over Hlcτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue.
  cbn [arrow_value_denote_gas_with] in Hvalue |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  destruct gas_tgt' as [|gas_tgt'']; [lia|].
  destruct (res_models_forall_rev _ _ Hvalue) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro.
  { exact Hscope_tgt. }
  exists (Lsrc ∪ lvars_fv (dom Σ) ∪ qual_dom φx ∪
    fv_cty τr ∪ fv_tm ef).
  intros y Hy my Hdom Hrestrict.
  cbn [formula_open].
  eapply res_models_impl_intro.
  {
    pose proof (formula_scoped_forall_open_res_le m my y
      (FImpl
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx))))
          (cty_shift 0 (CTPersist (CTOver bx φx)))
          (tret (vbvar 0)))
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx))))
          τr (tapp_tm (tm_shift 0 ef) (vbvar 0))))
      Hscope_tgt
      ltac:(rewrite <- Hrestrict; apply res_restrict_le)
      ltac:(rewrite Hdom; apply elem_of_union_r; apply elem_of_singleton;
        reflexivity)) as Hopened_scope.
    cbn [formula_open] in Hopened_scope.
    exact Hopened_scope.
  }
  intros Harg_persist.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by (clear -Hy; set_solver).
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyφ : y ∉ qual_dom φx) by (clear -Hy; set_solver).
  assert (Hyτr : y ∉ fv_cty τr) by (clear -Hy; set_solver).
  assert (Hyef : y ∉ fv_tm ef) by (clear -Hy; set_solver).
  assert (Harg_over :
      my ⊨ formula_open 0 y
        (ty_denote_gas (S gas_src')
          (typed_lty_env_bind Σ (erase_ty (CTOver bx φx)))
          (cty_shift 0 (CTOver bx φx)) (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{
      cbn [fv_tm fv_value]. intros Hin.
      rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2: exact Hlc_over.
    2:{
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    replace (lvar_store_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
      with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
    2:{
      symmetry.
      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
    }
    assert (Harg_over_base :
        my ⊨ ty_denote_gas (S gas_tgt'')
          (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
          (CTOver bx φx) (tret (vfvar y))).
    {
      rewrite formula_open_ty_denote_gas_singleton in Harg_persist.
      2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
      2:{
        cbn [fv_tm fv_value]. intros Hin.
        rewrite elem_of_empty in Hin. contradiction.
      }
      2:{
        rewrite cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφ.
      }
      replace (lvar_store_open_one 0 y
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx)))))
        with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
        in Harg_persist.
      2:{
        symmetry.
        apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
      }
      replace (cty_open 0 y
        (cty_shift 0 (CTPersist (CTOver bx φx))))
        with (CTPersist (CTOver bx φx)) in Harg_persist.
      2:{
        symmetry. apply cty_open_shift_from_lc_fresh.
        - cbn [lc_context_ty cty_lc_at]. exact Hlc_over.
        - unfold fv_cty, qual_dom in *.
          cbn [context_ty_lvars context_ty_lvars_at] in *.
          rewrite lvars_fv_lvars_at_depth.
          exact Hyφ.
      }
      cbn [open_tm open_value] in Harg_persist.
      eapply (ty_denote_gas_persist_over_ret_fvar_elim
        (S gas_tgt'')
        (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
        bx φx y).
      - apply lty_env_closed_insert_free. exact HΣclosed.
      - exact Hyφ.
      - exact Harg_persist.
    }
    rewrite (ty_denote_gas_saturate (S gas_src')
      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
      (CTOver bx φx) (tret (vfvar y)))
      by (cbn [cty_depth]; lia).
    rewrite (ty_denote_gas_saturate (S gas_tgt'')
      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
      (CTOver bx φx) (tret (vfvar y))) in Harg_over_base
      by (cbn [cty_depth]; lia).
    exact Harg_over_base.
  }
  assert (HyLsrc : y ∉ Lsrc) by (clear -Hy; set_solver).
  pose proof (Hsrc y HyLsrc my Hdom Hrestrict)
    as Hopened_src.
  cbn [formula_open] in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Harg_over) as Hres.
  rewrite formula_open_ty_denote_gas_singleton in Hres.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{ exact Hyτr. }
  rewrite formula_open_ty_denote_gas_singleton.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{ exact Hyτr. }
  replace (lvar_store_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ) in Hres.
  2:{
    symmetry.
    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
  }
  replace (lvar_store_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx)))))
    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
  2:{
    symmetry.
    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
  }
  rewrite (ty_denote_gas_saturate (S gas_src')
    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
    (cty_open 0 y τr)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 ef) (vbvar 0)))) in Hres
    by (rewrite cty_open_preserves_depth; lia).
  rewrite (ty_denote_gas_saturate (S (S gas_tgt''))
    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
    (cty_open 0 y τr)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 ef) (vbvar 0))))
    by (rewrite cty_open_preserves_depth; lia).
  exact Hres.
Qed.

Lemma arrow_result_first_open_value_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr Tf f (mf : WfWorldT) :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty (CTOver bx φx) ->
  lc_context_ty (cty_shift 0 (CTOver bx φx)) ->
  cty_lc_at 1 τr ->
  f ∉ qual_dom φx ->
  f ∉ fv_cty τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world mf
    (formula_open 0 f
      (arrow_value_denote_gas_with ty_denote_gas gas_tgt
        (typed_lty_env_bind Σ Tf)
        (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
        (tret (vbvar 0)))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas_src
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
      (tret (vbvar 0))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
      (tret (vbvar 0))).
Proof.
  intros HΣclosed HfΣ Hlc_over Hlc_shift_over Hlcτr Hfφ Hfτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue_src.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas_tgt Σ (CTPersist (CTOver bx φx)) τr Tf f) in Hscope_tgt.
  2: exact HΣclosed.
  2: exact HfΣ.
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2: exact Hlcτr.
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2: exact Hfτr.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas_src Σ (CTOver bx φx) τr Tf f) in Hvalue_src.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: exact Hlc_over.
  2: exact Hlcτr.
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2: exact Hfτr.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas_tgt Σ (CTPersist (CTOver bx φx)) τr Tf f).
  2: exact HΣclosed.
  2: exact HfΣ.
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2: exact Hlcτr.
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2: exact Hfτr.
  eapply arrow_value_over_arg_to_persist_over_arg_plain.
  - apply lty_env_closed_insert_free; assumption.
  - exact Hlc_over.
  - exact Hlcτr.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - exact Hscope_tgt.
  - exact Hvalue_src.
Qed.

Lemma ty_denote_gas_arrow_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr e (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  m ⊨ ty_denote_gas (S gas_src) Σ
    (CTArrow (CTOver bx φx) τr) e ->
  m ⊨ ty_denote_gas (S gas_tgt) Σ
    (CTArrow (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros HΣclosed Hlc_over Hlcτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hden.
  pose proof (ty_denote_gas_guard (S gas_src) Σ
    (CTArrow (CTOver bx φx) τr) e m Hden) as Hguard_src.
  change (m ⊨ ty_guard_formula
    (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
    (CTArrow (CTOver bx φx) τr) e) in Hguard_src.
  assert (Hbody_src :
      m ⊨ FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)))
            (tm_shift 0 e) (LVBound 0))
          (arrow_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
              (erase_ty (CTArrow (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0))))).
  {
    change (m ⊨ FAnd
      (ty_guard_formula
        (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
        (CTArrow (CTOver bx φx) τr) e)
      (FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)))
            (tm_shift 0 e) (LVBound 0))
          (arrow_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
              (erase_ty (CTArrow (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0)))))) in Hden.
    eapply res_models_and_elim_r. exact Hden.
  }
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
        (CTArrow (CTPersist (CTOver bx φx)) τr) e).
  { apply ty_guard_arrow_over_arg_to_persist_over_arg. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hlc_shift_over : lc_context_ty (cty_shift 0 (CTOver bx φx))).
  { apply cty_lc_at_shift_at. exact Hlc_over. }
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas_tgt) Σ
          (CTArrow (CTPersist (CTOver bx φx)) τr) e)).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  destruct (res_models_forall_rev _ _ Hbody_src) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (Σg := relevant_env Σ (CTArrow (CTOver bx φx) τr) e).
  exists (Lsrc ∪ lvars_fv (dom Σg) ∪ qual_dom φx ∪
    fv_cty τr ∪ fv_tm e).
  intros f Hf mf Hdom Hrestrict.
  assert (Hscope_open :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ
                  (CTArrow (CTPersist (CTOver bx φx)) τr) e)))
              (tm_shift 0 e) (LVBound 0))
            (arrow_value_denote_gas_with ty_denote_gas gas_tgt
              (typed_lty_env_bind
                (relevant_env Σ
                  (CTArrow (CTPersist (CTOver bx φx)) τr) e)
                (erase_ty (CTArrow (CTPersist (CTOver bx φx)) τr)))
              (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
              (tret (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  cbn [formula_open].
  eapply res_models_impl_intro.
  { cbn [formula_open] in Hscope_open. exact Hscope_open. }
  intros Hresult_tgt.
  assert (HfΣg : LVFree f ∉ dom (Σg : lty_env)).
  {
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    clear -Hf Hbad. set_solver.
  }
  assert (Hfφ : f ∉ qual_dom φx).
  { clear -Hf. set_solver. }
  assert (Hfτr : f ∉ fv_cty τr).
  { clear -Hf. set_solver. }
  assert (Hfe : f ∉ fv_tm e).
  { clear -Hf. set_solver. }
  assert (Hopened_src :
      mf ⊨ formula_open 0 f
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0 (dom Σg))
            (tm_shift 0 e) (LVBound 0))
          (arrow_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind Σg
              (erase_ty (CTArrow (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0))))).
  {
    subst Σg.
    apply Hsrc.
    - clear -Hf. set_solver.
    - exact Hdom.
    - exact Hrestrict.
  }
  cbn [formula_open] in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hresult_tgt)
    as Hvalue_src.
  assert (Hvalue_tgt_scope :
      formula_scoped_in_world mf
        (formula_open 0 f
          (arrow_value_denote_gas_with ty_denote_gas gas_tgt
            (typed_lty_env_bind Σg
              (erase_ty (CTArrow (CTPersist (CTOver bx φx)) τr)))
            (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
            (tret (vbvar 0))))).
  {
    cbn [formula_open] in Hscope_open.
    eapply formula_scoped_impl_r. exact Hscope_open.
  }
  eapply arrow_result_first_open_value_over_arg_to_persist_over_arg.
  - subst Σg. apply relevant_env_closed. exact HΣclosed.
  - exact HfΣg.
  - exact Hlc_over.
  - exact Hlc_shift_over.
  - exact Hlcτr.
  - exact Hfφ.
  - exact Hfτr.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - subst Σg.
    change (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
      with (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
      in Hvalue_tgt_scope.
    change (erase_ty (CTArrow (CTPersist (CTOver bx φx)) τr))
      with (erase_ty (CTArrow (CTOver bx φx) τr))
      in Hvalue_tgt_scope.
    exact Hvalue_tgt_scope.
  - subst Σg. exact Hvalue_src.
Qed.

Lemma ty_denote_arrow_over_arg_to_persist_over_arg
    Δ bx φx τr e (m : WfWorldT) :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  m ⊨ ty_denote Δ (CTArrow (CTOver bx φx) τr) e ->
  m ⊨ ty_denote Δ (CTArrow (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros HΔclosed Hlc_over Hlcτr Hden.
  unfold ty_denote in *.
  cbn [cty_depth].
  eapply ty_denote_gas_arrow_over_arg_to_persist_over_arg.
  - exact HΔclosed.
  - exact Hlc_over.
  - exact Hlcτr.
  - apply Nat.le_max_r.
  - apply Nat.le_max_r.
  - apply Nat.le_max_l.
  - apply Nat.le_max_l.
  - exact Hden.
Qed.

Theorem ty_denote_arrow_over_param_persist_over_result_forward
    Δ bx φx br φr e :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 (CTOver br φr) ->
  ty_denote Δ (CTArrow (CTOver bx φx) (CTOver br φr)) e ⊫
  ty_denote Δ
    (CTArrow (CTPersist (CTOver bx φx)) (CTOver br φr)) e.
Proof.
  unfold entails.
  intros HΔclosed Hlc_arg Hlc_res m Hden.
  eapply ty_denote_arrow_over_arg_to_persist_over_arg; eauto.
Qed.

Theorem ty_denote_arrow_over_param_persist_under_result_forward
    Δ bx φx br φr e :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 (CTUnder br φr) ->
  ty_denote Δ (CTArrow (CTOver bx φx) (CTUnder br φr)) e ⊫
  ty_denote Δ
    (CTArrow (CTPersist (CTOver bx φx)) (CTUnder br φr)) e.
Proof.
  unfold entails.
  intros HΔclosed Hlc_arg Hlc_res m Hden.
  eapply ty_denote_arrow_over_arg_to_persist_over_arg; eauto.
Qed.

Lemma res_restrict_singleton_pullback_ret_fvar_result
    A D x y (m my : WfWorldT) σy :
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
    (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT) ->
  exists σx : StoreT,
    dom (σx : StoreT) = A ∪ {[x]} /\
    res_restrict m (A ∪ {[x]}) =
      (exist _ (singleton_world σx) (wf_singleton_world σx) : WfWorldT).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase
    Hsingle_y.
  destruct (wfA_ne _ (worldA_wf m)) as [σ0 Hσ0].
  set (σx := store_restrict σ0 (A ∪ {[x]}) : StoreT).
  exists σx.
  assert (Hdomσx : dom (σx : StoreT) = A ∪ {[x]}).
  {
    subst σx.
    change (dom (storeA_restrict σ0 (A ∪ {[x]}) : gmap atom value) =
      A ∪ {[x]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m σ0 Hσ0).
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσx|].
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict m (A ∪ {[x]}) : WorldT) =
      dom (σx : StoreT)).
    rewrite res_restrict_dom, Hdomσx.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σm [Hσm Hσeq]]. subst σ.
      rewrite <- Hbase in Hσm.
      destruct Hσm as [σmy [Hσmy Hσmy_base]].
      assert (Hσ0proj : (res_restrict my (world_dom (m : WorldT)) : WorldT) σ0).
      { rewrite Hbase. exact Hσ0. }
      destruct Hσ0proj as [σ0my [Hσ0my Hσ0my_base]].
      pose proof (res_restrict_singleton_store_eq
        my (A ∪ {[y]}) σy σmy Hsingle_y Hσmy) as Hσmy_y.
      pose proof (res_restrict_singleton_store_eq
        my (A ∪ {[y]}) σy σ0my Hsingle_y Hσ0my) as Hσ0my_y.
      assert (Hxy_my : σmy !! y = σmy !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σmy);
          [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
        change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
        set_solver.
      }
      assert (Hxy_0 : σ0my !! y = σ0my !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0my);
          [exact HD|exact HyD|exact (Hclosed_x σ0my Hσ0my)| |exact Hres|exact Hσ0my].
        change (x ∈ dom (storeA_restrict σ0my ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σ0my Hσ0my), Hdom_my.
        set_solver.
      }
      subst σx.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[x]})) as [Ha|Ha].
      * destruct (decide (a = x)) as [->|Hax].
        -- assert (Hbase_my_x : σmy !! x = σm !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσmy_base.
           }
           assert (Hbase_0_x : σ0my !! x = σ0 !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσ0my_base.
           }
           assert (Hy_my : σmy !! y = σy !! y).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσmy_y.
           }
           assert (Hy_0 : σ0my !! y = σy !! y).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσ0my_y.
           }
           change (σm !! x = σ0 !! x).
           rewrite <- Hbase_my_x, <- Hbase_0_x.
           rewrite <- Hxy_my, <- Hxy_0.
           congruence.
        -- assert (HaA : a ∈ A) by set_solver.
           assert (HaDom : a ∈ world_dom (m : WorldT)) by set_solver.
           assert (Hbase_my_a : σmy !! a = σm !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσmy_base.
           }
           assert (Hbase_0_a : σ0my !! a = σ0 !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσ0my_base.
           }
           assert (Hy_my_a : σmy !! a = σy !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσmy_y.
           }
           assert (Hy_0_a : σ0my !! a = σy !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσ0my_y.
           }
           change (σm !! a = σ0 !! a).
           rewrite <- Hbase_my_a, <- Hbase_0_a.
           congruence.
      * reflexivity.
    + intros Hσ.
      unfold singleton_world in Hσ.
      cbn [raw_world raw_worldA] in Hσ.
      change (σ = store_restrict σ0 (A ∪ {[x]})) in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

Lemma res_restrict_singleton_push_ret_fvar_result
    A D x y (m my : WfWorldT) σx :
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
  res_restrict m (A ∪ {[x]}) =
    (exist _ (singleton_world σx) (wf_singleton_world σx) : WfWorldT) ->
  exists σy : StoreT,
    dom (σy : StoreT) = A ∪ {[y]} /\
    res_restrict my (A ∪ {[y]}) =
      (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase
    Hsingle_x.
  destruct (wfA_ne _ (worldA_wf my)) as [σ0 Hσ0].
  set (σy := store_restrict σ0 (A ∪ {[y]}) : StoreT).
  exists σy.
  assert (Hdomσy : dom (σy : StoreT) = A ∪ {[y]}).
  {
    subst σy.
    change (dom (storeA_restrict σ0 (A ∪ {[y]}) : gmap atom value) =
      A ∪ {[y]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσy|].
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict my (A ∪ {[y]}) : WorldT) =
      dom (σy : StoreT)).
    rewrite res_restrict_dom, Hdomσy.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σmy [Hσmy Hσeq]]. subst σ.
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        rewrite <- Hbase.
        subst σm. exists σmy. split; [exact Hσmy|reflexivity].
      }
      assert (Hσm_base : store_restrict σmy (world_dom (m : WorldT)) = σm)
        by (subst σm; reflexivity).
      assert (Hσ0_base : (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ0 (world_dom (m : WorldT)))).
      {
        exists σ0. split; [exact Hσ0|reflexivity].
      }
      rewrite Hbase in Hσ0_base.
      pose proof (res_restrict_singleton_store_eq
        m (A ∪ {[x]}) σx σm Hsingle_x Hσm) as Hσm_x.
      pose proof (res_restrict_singleton_store_eq
        m (A ∪ {[x]}) σx
        (store_restrict σ0 (world_dom (m : WorldT)))
        Hsingle_x Hσ0_base) as Hσ0_x.
      assert (Hxy_my : σmy !! y = σmy !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σmy);
          [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
        change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
        set_solver.
      }
      assert (Hxy_0 : σ0 !! y = σ0 !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0);
          [exact HD|exact HyD|exact (Hclosed_x σ0 Hσ0)| |exact Hres|exact Hσ0].
        change (x ∈ dom (storeA_restrict σ0 ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
        set_solver.
      }
      subst σy.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
      * destruct (decide (a = y)) as [->|Hay].
        -- assert (Hmy_x : σmy !! x = σm !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσm_base.
           }
           assert (H0_x :
               σ0 !! x = store_restrict σ0 (world_dom (m : WorldT)) !! x).
           {
             destruct (σ0 !! x) as [vx|] eqn:H0look.
             - symmetry.
               change (
                 (storeA_restrict σ0 (world_dom (m : WorldT))
                   : gmap atom value) !! x = Some vx).
               apply storeA_restrict_lookup_some_2; [exact H0look|exact Hxm].
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               set_solver.
           }
           assert (H0base_x :
               store_restrict σ0 (world_dom (m : WorldT)) !! x =
               σx !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσ0_x.
           }
           assert (Hm_x :
               σm !! x = σx !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσm_x.
           }
           change (σmy !! y = σ0 !! y).
           rewrite Hxy_my, Hxy_0.
           rewrite Hmy_x, H0_x, H0base_x, Hm_x.
           reflexivity.
        -- assert (HaA : a ∈ A) by set_solver.
           assert (HaDom : a ∈ world_dom (m : WorldT)) by set_solver.
           assert (Hmy_a : σmy !! a = σm !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσm_base.
           }
           assert (H0_a :
               σ0 !! a = store_restrict σ0 (world_dom (m : WorldT)) !! a).
           {
             destruct (σ0 !! a) as [va|] eqn:H0look.
             - symmetry.
               change (
                 (storeA_restrict σ0 (world_dom (m : WorldT))
                   : gmap atom value) !! a = Some va).
               apply storeA_restrict_lookup_some_2; [exact H0look|exact HaDom].
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               set_solver.
           }
           assert (H0base_a :
               store_restrict σ0 (world_dom (m : WorldT)) !! a =
               σx !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσ0_x.
           }
           assert (Hm_a : σm !! a = σx !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσm_x.
           }
           change (σmy !! a = σ0 !! a).
           rewrite Hmy_a, H0_a, H0base_a, Hm_a.
           reflexivity.
      * reflexivity.
    + intros Hσ.
      unfold singleton_world in Hσ.
      cbn [raw_world raw_worldA] in Hσ.
      change (σ = store_restrict σ0 (A ∪ {[y]})) in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

Lemma res_restrict_singleton_exact_dom_subset
    (m : WfWorldT) X σ :
  dom (σ : StoreT) = X ->
  res_restrict m X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  X ⊆ world_dom (m : WorldT).
Proof.
  intros Hdomσ Hsingle a Ha.
  assert (Hdom_eq :
      world_dom (res_restrict m X : WorldT) = dom (σ : StoreT)).
  { rewrite Hsingle. reflexivity. }
  rewrite res_restrict_dom, Hdomσ in Hdom_eq.
  set_solver.
Qed.

Local Lemma res_fiber_from_projection_world_dom
    (m mfib : WfWorldT) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  world_dom (mfib : WorldT) = world_dom (m : WorldT).
Proof.
  intros [_ Hfib].
  pose proof (f_equal world_dom Hfib) as Hdom.
  cbn [raw_fiber rawA_fiber world_dom worldA_dom] in Hdom.
  exact Hdom.
Qed.

Lemma res_fiber_from_projection_restrict_singleton
    (m mfib : WfWorldT) X σ :
  dom (σ : StoreT) = X ->
  res_fiber_from_projection m X σ mfib ->
  res_restrict mfib X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT).
Proof.
  intros Hdomσ Hproj.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom.
    rewrite (res_fiber_from_projection_world_dom m mfib X σ Hproj).
    destruct Hproj as [Hσproj _].
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσproj)
      as Hdom_proj.
    change (dom (σ : StoreT) = world_dom (res_restrict m X : WorldT))
      in Hdom_proj.
    rewrite res_restrict_dom in Hdom_proj.
    cbn [world_dom raw_world raw_worldA singleton_world singleton_worldA].
    symmetry. exact Hdom_proj.
  - intros τ. split.
    + intros [τ0 [Hτ0 Hτ]].
      pose proof (res_fiber_from_projection_store_restrict
        m mfib X σ τ0 Hproj Hτ0) as Hτ0σ.
      change (store_restrict τ0 (dom (σ : StoreT)) = σ) in Hτ0σ.
      rewrite Hdomσ in Hτ0σ.
      assert (τ = σ) as ->.
      { rewrite <- Hτ. exact Hτ0σ. }
      unfold singleton_world. cbn [raw_world raw_worldA singleton_worldA].
      reflexivity.
    + intros Hτ.
      unfold singleton_world in Hτ.
      cbn [raw_world raw_worldA singleton_worldA] in Hτ.
      rewrite Hτ.
      destruct Hproj as [[τ0 [Hτ0 Hτ0X]] Hfib].
      exists τ0. split.
      * destruct mfib as [wmfib Hwmfib].
        cbn [proj1_sig raw_world raw_worldA world_stores] in Hfib |- *.
        change (wmfib = rawA_fiber (m : WorldT) σ) in Hfib.
        rewrite Hfib. split; [exact Hτ0|].
        change (store_restrict τ0 (dom (σ : StoreT)) = σ).
        rewrite Hdomσ. exact Hτ0X.
      * exact Hτ0X.
Qed.

Lemma store_singleton_dom_value y (v : value) :
  dom ({[y := v]} : StoreT) = {[y]}.
Proof.
  change (dom ({[y := v]} : gmap atom value) = ({[y]} : aset)).
  apply dom_singleton_L.
Qed.

Lemma singleton_world_member_eq (σ τ : StoreT) :
  (singleton_world σ : WorldT) τ ->
  τ = σ.
Proof.
  unfold singleton_world.
  cbn [raw_world raw_worldA singleton_worldA].
  intros ->. reflexivity.
Qed.

Definition const_fresh_value_extension
    (X : aset) (y : atom) (v : value) (HyX : y ∉ X) : fiber_extension :=
  mk_fiber_extension X {[y]}
    (fun _ =>
      (exist _ (singleton_world ({[y := v]} : StoreT))
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorldT))
    ltac:(set_solver)
    ltac:(intros σ Hσ;
      cbn [world_dom raw_world raw_worldA singleton_world];
      apply store_singleton_dom_value)
    ltac:(intros σ Hσ; exists ({[y := v]} : StoreT);
      cbn [raw_world raw_worldA singleton_world];
      reflexivity).

Lemma res_extend_by_const_fresh_value
    (m : WfWorldT) y v :
  y ∉ world_dom (m : WorldT) ->
  exists F my,
    ext_in F = world_dom (m : WorldT) /\
    ext_out F = {[y]} /\
    res_extend_by m F my /\
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my (world_dom (m : WorldT)) = m /\
    forall σ, (my : WorldT) σ -> σ !! y = Some v.
Proof.
  intros Hy.
  set (F := const_fresh_value_extension (world_dom (m : WorldT)) y v Hy).
  assert (Happ : extension_applicable F m).
  {
    constructor.
    - subst F. cbn [const_fresh_value_extension extA_in].
      reflexivity.
    - subst F. cbn [const_fresh_value_extension extA_out].
      set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [my Hext].
  exists F, my.
  split; [subst F; reflexivity|].
  split; [subst F; reflexivity|].
  split; [exact Hext|].
  split.
  - rewrite (res_extend_by_dom m F my Hext).
    subst F. reflexivity.
  - split; [exact (res_extend_by_restrict_base m F my Hext)|].
    intros σ Hσ.
    pose proof (resA_extend_by_store_iff m F my σ Hext) as Hiff.
    destruct (proj1 Hiff Hσ) as [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
    subst F.
    change (we =
      (exist _ (singleton_world ({[y := v]} : StoreT))
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorldT)) in Hrel.
    rewrite Hrel in Hσe.
    apply singleton_world_member_eq in Hσe. subst σe.
    rewrite (lookup_union_r (M:=gmap atom) (A:=value)
      σm ({[y := v]} : gmap atom value) y).
    + apply map_lookup_insert.
    + apply not_elem_of_dom.
      rewrite (wfworld_store_dom m σm Hσm).
      exact Hy.
Qed.

Lemma ty_denote_gas_persist_ret_fvar_intro_singleton
    gas Σ τ z σ (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ fv_cty τ ->
  dom (σ : StoreT) = fv_cty τ ∪ {[z]} ->
  res_restrict m (fv_cty τ ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar z)) ->
  m ⊨ ty_denote_gas (S gas) Σ
    (CTPersist τ) (tret (vfvar z)).
Proof.
  intros HΣclosed Hzτ Hdomσ Hsingle Hden.
  pose proof (ty_denote_gas_guard_formula gas Σ τ
    (tret (vfvar z)) m Hden) as Hguard_src.
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTPersist τ) (tret (vfvar z)))
        (CTPersist τ) (tret (vfvar z))).
  { apply ty_guard_to_persist. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas) Σ (CTPersist τ) (tret (vfvar z)))).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (Dres := dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))).
  exists (world_dom (m : WorldT) ∪ lvars_fv (dom Σ) ∪
    lvars_fv Dres ∪ fv_cty τ ∪ {[z]}).
  intros y Hy my Hdom_my Hbase_my.
  rewrite formula_open_impl.
  eapply res_models_impl_intro.
  {
    rewrite <- formula_open_impl.
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - rewrite Hdom_my. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  intros Hres.
  cbn [formula_open] in Hres.
  subst Dres.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres.
  2:{ apply lvars_shift_from_lc. apply relevant_env_closed. exact HΣclosed. }
  2:{ rewrite lvars_shift_from_fv. clear -Hy. set_solver. }
  2:{ apply lc_ret_iff_value. constructor. }
  2:{ cbn [fv_tm fv_value]. clear -Hy. set_solver. }
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))))
    in Hres
    by (apply relevant_env_closed; exact HΣclosed).
  rewrite relevant_env_persist_eq in Hres.
  pose proof (res_models_and_elim_l _ _ _ Hguard_src) as Hwf_src.
  pose proof (res_models_and_elim_r _ _ _ Hguard_src) as Hguard_rest_src.
  pose proof (res_models_and_elim_l _ _ _ Hguard_rest_src) as Hworld_src.
  pose proof (res_models_and_elim_r _ _ _ Hguard_rest_src) as Hguard_tail_src.
  pose proof (res_models_and_elim_l _ _ _ Hguard_tail_src) as Hbasic_src.
  pose proof Hworld_src as Hworld_src_info.
  apply basic_world_formula_models_iff in Hworld_src_info
    as [_ [Hrel_world _]].
  pose proof Hwf_src as Hwf_src_info.
  apply context_ty_wf_formula_models_iff in Hwf_src_info
    as [HlcD_src [_ [HτD_src Hbasic_cty_src]]].
  assert (Hlcτ_src : lc_context_ty τ).
  {
    unfold lc_context_ty.
    eapply (context_ty_lvars_at_lc 0
      (dom (relevant_env Σ τ (tret (vfvar z)))) τ);
      eauto.
  }
  pose proof Hbasic_src as Hbasic_src_info.
  apply expr_basic_typing_formula_models_iff in Hbasic_src_info
    as [_ [_ Hbasic_lty_src]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_lty_src) as HtmD_src.
  assert (HtmD_ret_src :
      tm_lvars (tret (vfvar z)) ⊆ dom (relevant_env Σ τ (tret (vfvar z)))).
  {
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    intros lv Hlv.
    apply elem_of_singleton in Hlv. subst lv.
    apply HtmD_src.
    unfold lvars_of_atoms.
    apply elem_of_map.
    exists z. split; [reflexivity|].
    cbn [fv_tm fv_value]. apply elem_of_singleton. reflexivity.
  }
  assert (Hzdom : z ∈ world_dom (m : WorldT)).
  {
    assert (Hsub : fv_cty τ ∪ {[z]} ⊆ world_dom (m : WorldT)).
    {
      intros a Ha.
      assert (Hdom_eq :
          world_dom (res_restrict m (fv_cty τ ∪ {[z]}) : WorldT) =
          dom (σ : StoreT)).
      { rewrite Hsingle. reflexivity. }
      rewrite res_restrict_dom, Hdomσ in Hdom_eq.
      set_solver.
    }
    apply Hsub. set_solver.
  }
  assert (HA_sub : fv_cty τ ⊆ world_dom (m : WorldT)).
  {
    assert (Hsub : fv_cty τ ∪ {[z]} ⊆ world_dom (m : WorldT)).
    {
      intros a Ha.
      assert (Hdom_eq :
          world_dom (res_restrict m (fv_cty τ ∪ {[z]}) : WorldT) =
          dom (σ : StoreT)).
      { rewrite Hsingle. reflexivity. }
      rewrite res_restrict_dom, Hdomσ in Hdom_eq.
      set_solver.
    }
    intros a Ha. apply Hsub. set_solver.
  }
  assert (Hy_m : y ∉ world_dom (m : WorldT)).
  { clear -Hy. set_solver. }
  assert (Hyτ : y ∉ fv_cty τ).
  { clear -Hy. set_solver. }
  assert (Hclosed_z_m : wfworld_closed_on ({[z]} : aset) m).
  {
    change ({[z]} : aset) with (fv_tm (tret (vfvar z))).
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    exact Hguard_src.
  }
  assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply elem_of_singleton in Ha. subst a. exact Hzdom.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - exact Hclosed_z_m.
  }
  assert (HDmy : lvars_fv
      (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z))))
      ⊆ world_dom (my : WorldT)).
  {
    intros a Ha.
    rewrite relevant_env_persist_eq in Ha.
    rewrite Hdom_my.
    apply elem_of_union_l.
    apply Hrel_world. exact Ha.
  }
  assert (HtmD_result :
      tm_lvars (tret (vfvar z)) ⊆
        dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))).
  { rewrite relevant_env_persist_eq. exact HtmD_ret_src. }
  assert (HyD_result :
      LVFree y ∉ dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))).
  {
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_eq in HyD.
    exact HyD.
  }
  pose proof (res_restrict_singleton_push_ret_fvar_result
    (fv_cty τ)
    (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z))))
    z y m my σ
    HA_sub Hzdom Hy_m Hzτ Hyτ HtmD_result HyD_result Hres
    Hclosed_z_my Hdom_my Hbase_my Hsingle)
    as [σy [Hdomσy Hsingle_y]].
  assert (Hinner_insert :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τ]> Σ) τ (tret (vfvar y))).
  {
    eapply (ty_denote_gas_result_alias_at
      gas (<[LVFree y := erase_ty τ]> Σ) τ (tret (vfvar z)) y
      (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))) my).
    - apply lty_env_closed_insert_free. exact HΣclosed.
    - apply relevant_env_closed. exact HΣclosed.
    - rewrite relevant_env_persist_eq. exact HtmD_ret_src.
    - rewrite relevant_env_persist_eq. exact HτD_src.
    - exact HyD_result.
    - exact HDmy.
    - apply map_lookup_insert.
    - exact Hres.
    - rewrite (ty_denote_gas_insert_fresh_lty_env_eq
        gas Σ τ (tret (vfvar z)) y (erase_ty τ)).
      2:{
        intros HyΣ.
        assert (HyΣfv : y ∈ lvars_fv (dom Σ)).
        { apply lvars_fv_elem. exact HyΣ. }
        apply Hy.
        clear -HyΣfv. set_solver.
      }
      2:{
        intros Hy_lvar.
        apply Hyτ.
        rewrite <- context_ty_lvars_fv.
        apply lvars_fv_elem. exact Hy_lvar.
      }
      2:{ cbn [fv_tm fv_value]. clear -Hy. set_solver. }
      eapply (res_models_kripke m my).
      + rewrite <- Hbase_my. apply res_restrict_le.
      + exact Hden.
  }
  assert (Hinner_norm :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τ]>
          (relevant_env Σ τ (tret (vfvar z))))
        τ (tret (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on.
    - reflexivity.
    - symmetry. apply insert_relevant_env_ret_fvar_restrict_eq.
      + clear -Hy. set_solver.
      + exact Hzτ.
    - exact Hinner_insert.
  }
  rewrite formula_open_persist.
  rewrite formula_open_ty_denote_gas_singleton.
  2:{
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_eq in HyD.
    apply lvars_fv_elem in HyD.
    exact HyD.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  2:{
    rewrite cty_shift_fv.
    exact Hyτ.
  }
  rewrite cty_open_shift_from_lc_fresh.
  2:{ exact Hlcτ_src. }
  2:{ exact Hyτ. }
  rewrite typed_lty_env_bind_open_current.
  2:{ exact HyD_result. }
  2:{ apply relevant_env_closed. exact HΣclosed. }
  change (erase_ty (CTPersist τ)) with (erase_ty τ).
  rewrite relevant_env_persist_eq.
  eapply (ty_denote_gas_ret_fvar_persist_body_intro_singleton
    gas (<[LVFree y := erase_ty τ]>
      (relevant_env Σ τ (tret (vfvar z)))) τ y σy my).
  - exact Hdomσy.
  - exact Hsingle_y.
  - exact Hinner_norm.
Qed.


Lemma ty_denote_gas_persist_over_ret_fvar_intro_singleton
    gas Σ b φ z σ (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  dom (σ : StoreT) = fv_cty (CTOver b φ) ∪ {[z]} ->
  res_restrict m (fv_cty (CTOver b φ) ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas Σ (CTOver b φ) (tret (vfvar z)) ->
  m ⊨ ty_denote_gas (S gas) Σ
    (CTPersist (CTOver b φ)) (tret (vfvar z)).
Proof.
  intros HΣclosed Hzφ Hdomσ Hsingle Hden.
  pose proof (ty_denote_gas_guard_formula gas Σ
    (CTOver b φ) (tret (vfvar z)) m Hden) as Hguard_src.
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)))
        (CTPersist (CTOver b φ)) (tret (vfvar z))).
  { apply ty_guard_over_to_persist_over. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas) Σ
          (CTPersist (CTOver b φ)) (tret (vfvar z)))).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (τp := CTPersist (CTOver b φ)).
  set (Dres := dom (relevant_env Σ τp (tret (vfvar z)))).
  exists (world_dom (m : WorldT) ∪ lvars_fv (dom Σ) ∪
    lvars_fv Dres ∪ qual_dom φ ∪ {[z]}).
  intros y Hy my Hdom_my Hbase_my.
  rewrite formula_open_impl.
  eapply res_models_impl_intro.
  {
    rewrite <- formula_open_impl.
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - rewrite Hdom_my. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  intros Hres.
  cbn [formula_open] in Hres.
  subst Dres τp.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres.
  2:{ apply lvars_shift_from_lc. apply relevant_env_closed. exact HΣclosed. }
  2:{ rewrite lvars_shift_from_fv. clear -Hy. set_solver. }
  2:{ apply lc_ret_iff_value. constructor. }
  2:{ cbn [fv_tm fv_value]. clear -Hy. set_solver. }
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)))))
    in Hres
    by (apply relevant_env_closed; exact HΣclosed).
  rewrite relevant_env_persist_over_ret_fvar_eq in Hres.
  pose proof (res_models_and_elim_l _ _ _ Hguard_src) as Hwf_src.
  pose proof (res_models_and_elim_r _ _ _ Hguard_src) as Hguard_rest_src.
  pose proof (res_models_and_elim_l _ _ _ Hguard_rest_src) as Hworld_src.
  pose proof (res_models_and_elim_r _ _ _ Hguard_rest_src) as Hguard_tail_src.
  pose proof (res_models_and_elim_l _ _ _ Hguard_tail_src) as Hbasic_src.
  pose proof Hworld_src as Hworld_src_info.
  apply basic_world_formula_models_iff in Hworld_src_info
    as [_ [Hrel_world _]].
  pose proof Hwf_src as Hwf_src_info.
  apply context_ty_wf_formula_models_iff in Hwf_src_info
    as [_ [_ [HτD_src _]]].
  pose proof Hwf_src as Hwf_src_lc_info.
  apply context_ty_wf_formula_models_iff in Hwf_src_lc_info
    as [HlcD_src [_ Hbasic_cty_src]].
  pose proof (basic_context_ty_lvars_lc _ _ HlcD_src Hbasic_cty_src)
    as Hlc_over_src.
  pose proof Hbasic_src as Hbasic_src_info.
  apply expr_basic_typing_formula_models_iff in Hbasic_src_info
    as [_ [_ Hbasic_lty_src]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_lty_src) as HtmD_src.
  assert (HtmD_ret_src :
      tm_lvars (tret (vfvar z)) ⊆
        dom (relevant_env Σ (CTOver b φ) (tret (vfvar z)))).
  {
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    intros lv Hlv.
    apply elem_of_singleton in Hlv. subst lv.
    apply HtmD_src.
    unfold lvars_of_atoms.
    apply elem_of_map.
    exists z. split; [reflexivity|].
    cbn [fv_tm fv_value]. apply elem_of_singleton. reflexivity.
  }
  assert (Hzdom : z ∈ world_dom (m : WorldT)).
  {
    pose proof (res_restrict_singleton_exact_dom_subset
      m (fv_cty (CTOver b φ) ∪ {[z]}) σ Hdomσ Hsingle) as Hsub.
    apply Hsub. set_solver.
  }
  assert (HA_sub : fv_cty (CTOver b φ) ⊆ world_dom (m : WorldT)).
  {
    pose proof (res_restrict_singleton_exact_dom_subset
      m (fv_cty (CTOver b φ) ∪ {[z]}) σ Hdomσ Hsingle) as Hsub.
    intros a Ha. apply Hsub. set_solver.
  }
  assert (Hy_m : y ∉ world_dom (m : WorldT)).
  { clear -Hy. set_solver. }
  assert (HzA : z ∉ fv_cty (CTOver b φ)).
  {
    intros HzA.
    rewrite <- context_ty_lvars_fv, context_ty_lvars_over_fv in HzA.
    exact (Hzφ HzA).
  }
  assert (HyA : y ∉ fv_cty (CTOver b φ)).
  {
    intros HyA.
    rewrite <- context_ty_lvars_fv, context_ty_lvars_over_fv in HyA.
    clear -Hy HyA. set_solver.
  }
  assert (Hclosed_z_m : wfworld_closed_on ({[z]} : aset) m).
  {
    change ({[z]} : aset) with (fv_tm (tret (vfvar z))).
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    exact Hguard_src.
  }
  assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply elem_of_singleton in Ha. subst a. exact Hzdom.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - exact Hclosed_z_m.
  }
  assert (HDmy : lvars_fv
      (dom (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z))))
      ⊆ world_dom (my : WorldT)).
  {
    intros a Ha.
    rewrite relevant_env_persist_over_ret_fvar_eq in Ha.
    rewrite Hdom_my.
    apply elem_of_union_l.
    apply Hrel_world. exact Ha.
  }
  assert (HtmD_result :
      tm_lvars (tret (vfvar z)) ⊆
        dom (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)))).
  {
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    rewrite relevant_env_persist_over_ret_fvar_eq.
    exact HtmD_ret_src.
  }
  assert (HyD_result :
      LVFree y ∉
        dom (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z)))).
  {
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_over_ret_fvar_eq in HyD.
    exact HyD.
  }
  pose proof (res_restrict_singleton_push_ret_fvar_result
    (fv_cty (CTOver b φ))
    (dom (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z))))
    z y m my σ
    HA_sub Hzdom Hy_m HzA HyA HtmD_result HyD_result Hres
    Hclosed_z_my Hdom_my Hbase_my Hsingle)
    as [σy [Hdomσy Hsingle_y]].
  assert (Hinner_insert :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty (CTOver b φ)]> Σ)
        (CTOver b φ) (tret (vfvar y))).
  {
    eapply (ty_denote_gas_over_ret_fvar_result_alias_open
      gas Σ b φ z y
      (dom (relevant_env Σ (CTPersist (CTOver b φ)) (tret (vfvar z))))
      m my).
    - exact HΣclosed.
    - apply relevant_env_closed. exact HΣclosed.
    - clear -Hy. set_solver.
    - clear -Hy. set_solver.
    - clear -Hy. set_solver.
    - cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
      rewrite relevant_env_persist_over_ret_fvar_eq.
      exact HtmD_ret_src.
    - rewrite relevant_env_persist_over_ret_fvar_eq.
      exact HτD_src.
    - intros HyD.
      apply Hy_m.
      apply Hrel_world.
      apply lvars_fv_elem.
      rewrite relevant_env_persist_over_ret_fvar_eq in HyD.
      exact HyD.
    - exact HDmy.
    - exact Hdom_my.
    - exact Hbase_my.
    - exact Hres.
    - exact Hden.
  }
  assert (Hinner_norm :
      my ⊨ ty_denote_gas gas
        (over_ret_fvar_env Σ b φ y)
        (CTOver b φ) (tret (vfvar y))).
  {
    eapply over_ret_fvar_insert_env_to_normal_env.
    - clear -Hy. set_solver.
    - change (erase_ty (CTOver b φ)) with (TBase b) in Hinner_insert.
      exact Hinner_insert.
  }
  rewrite formula_open_persist.
  rewrite formula_open_ty_denote_gas_singleton.
  2:{
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_over_ret_fvar_eq in HyD.
    apply lvars_fv_elem in HyD.
    exact HyD.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  2:{
    rewrite cty_shift_fv.
    intros Hyτ.
    apply HyA.
    exact Hyτ.
  }
  rewrite cty_open_shift_from_lc_fresh.
  2:{ exact Hlc_over_src. }
  2:{ exact HyA. }
  rewrite typed_lty_env_bind_open_current.
  2:{ exact HyD_result. }
  2:{ apply relevant_env_closed. exact HΣclosed. }
  change (erase_ty (CTPersist (CTOver b φ))) with (TBase b).
  rewrite relevant_env_persist_over_ret_fvar_eq.
  eapply (res_models_persist_intro_from_singleton_superset
    my
    (ty_denote_gas gas
      (<[LVFree y := TBase b]>
        (relevant_env Σ (CTOver b φ) (tret (vfvar z))))
      (CTOver b φ) (tret (vfvar y)))
    (fv_cty (CTOver b φ) ∪ {[y]}) σy).
  - etransitivity; [apply ty_denote_gas_fv_subset|].
    cbn [fv_tm fv_value]. set_solver.
  - exact Hdomσy.
  - change (fv_cty (CTOver b φ) ∪ {[y]})
      with (fv_cty (CTOver b φ) ∪ {[y]}) in Hsingle_y.
    exact Hsingle_y.
  - eapply res_models_ty_denote_gas_env_agree_on.
    + reflexivity.
    + symmetry. apply over_ret_fvar_relevant_env_restrict_eq.
      * clear -Hy. set_solver.
      * exact Hzφ.
    + exact Hinner_norm.
Qed.

Lemma ty_denote_persist_ret_fvar_intro_singleton
    (Δ : gmap atom ty) τ z σ (m : WfWorldT) :
  z ∉ fv_cty τ ->
  dom (σ : StoreT) = fv_cty τ ∪ {[z]} ->
  res_restrict m (fv_cty τ ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote Δ τ (tret (vfvar z)) ->
  m ⊨ ty_denote Δ (CTPersist τ) (tret (vfvar z)).
Proof.
  intros Hzτ Hdomσ Hsingle Hden.
  unfold ty_denote in *.
  cbn [cty_depth].
  eapply ty_denote_gas_persist_ret_fvar_intro_singleton; eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

Lemma arrow_value_persist_over_arg_apply_singleton
    gas (Σ : lty_env) bx φx τr ef y σ
    (m my : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  y ∉ world_dom (m : WorldT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ qual_dom φx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm ef ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  dom (σ : StoreT) = fv_cty (CTOver bx φx) ∪ {[y]} ->
  res_restrict my (fv_cty (CTOver bx φx) ∪ {[y]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas (S gas) Σ
    (CTPersist (CTOver bx φx)) τr ef ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := TBase bx]> Σ)
    (CTOver bx φx) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (S gas)
    (<[LVFree y := TBase bx]> Σ)
    (cty_open 0 y τr)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 ef) (vbvar 0))).
Proof.
  intros HΣclosed Hlc_over Hlcτr Hym HyΣ Hyφ Hyτr Hyef
    Hdom Hrestrict Hdomσ Hsingle Hvalue Harg_over.
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros HyD. apply HyΣ. apply lvars_fv_elem. exact HyD.
  }
  assert (Harg_persist_norm :
      my ⊨ ty_denote_gas (S gas)
        (<[LVFree y := TBase bx]> Σ)
        (CTPersist (CTOver bx φx)) (tret (vfvar y))).
  {
    eapply ty_denote_gas_persist_over_ret_fvar_intro_singleton.
    - apply lty_env_closed_insert_free. exact HΣclosed.
    - exact Hyφ.
    - exact Hdomσ.
    - exact Hsingle.
    - exact Harg_over.
  }
  pose proof (res_models_forall_open_named_fresh
    m my y
    (FImpl
      (ty_denote_gas (S gas)
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        (cty_shift 0 (CTPersist (CTOver bx φx)))
        (tret (vbvar 0)))
      (ty_denote_gas (S gas)
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        τr
        (tapp_tm (tm_shift 0 ef) (vbvar 0))))
    Hvalue Hym Hdom Hrestrict) as Hopened.
  cbn [formula_open] in Hopened.
  assert (Harg_persist_open :
      my ⊨ formula_open 0 y
        (ty_denote_gas (S gas)
          (typed_lty_env_bind Σ
            (erase_ty (CTPersist (CTOver bx φx))))
          (cty_shift 0 (CTPersist (CTOver bx φx)))
          (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{
      cbn [fv_tm fv_value]. intros Hin.
      rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at].
      intros Hbad. apply Hyφ.
      unfold qual_dom.
      rewrite lvars_fv_lvars_at_depth in Hbad.
      exact Hbad.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
    2:{
      unfold fv_cty, context_ty_lvars.
      cbn [context_ty_lvars_at].
      intros Hbad. apply Hyφ.
      unfold qual_dom.
      rewrite lvars_fv_lvars_at_depth in Hbad.
      exact Hbad.
    }
    rewrite typed_lty_env_bind_open_current.
    2:{ exact HyΣlv. }
    2:{ exact HΣclosed. }
    change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx).
    exact Harg_persist_norm.
  }
  pose proof (res_models_impl_elim _ _ _ Hopened Harg_persist_open)
    as Hres_open.
  rewrite formula_open_ty_denote_gas_singleton in Hres_open.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{ exact Hyτr. }
  rewrite typed_lty_env_bind_open_current in Hres_open.
  2:{ exact HyΣlv. }
  2:{ exact HΣclosed. }
  change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx) in Hres_open.
  exact Hres_open.
Qed.

End TypePersist.
