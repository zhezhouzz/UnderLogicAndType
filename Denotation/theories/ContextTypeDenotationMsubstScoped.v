(** * Denotation.ContextTypeDenotationMsubstScoped

    Split from ContextTypeDenotationMsubst for incremental compilation. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationLvars
  ContextTypeDenotationMsubstCore
  ContextTypeDenotationMsubstGuard
  ContextTypeDenotationMsubstKeepDomain
  ContextTypeDenotationOpenModels.

Section ContextTypeDenotationMsubst.

Lemma fv_cty_subset_denot_relevant_env
    Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  fv_cty τ ⊆ lvars_fv (dom (denot_relevant_env Σ τ e)).
Proof.
  intros Hwf.
  pose proof (basic_context_ty_lvars_denot_relevant_env Σ τ e Hwf)
    as [Hvars _].
  rewrite <- context_ty_lvars_fv.
  apply lvars_fv_mono. exact Hvars.
Qed.

Lemma formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  fv_tm e ∪ fv_cty τ ⊆ formula_fv (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros Hwf.
  transitivity (lvars_fv (tm_lvars e ∪ context_ty_lvars τ)).
  - rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
    reflexivity.
  - apply lvars_fv_mono.
    pose proof (basic_context_ty_lvars_denot_relevant_env Σ τ e Hwf)
      as [Hτ _].
    destruct gas as [|gas]; destruct τ;
      cbn [denot_ty_lvar_gas formula_lvars context_ty_wf_formula
        context_ty_wf_lqual basic_world_formula basic_world_lqual
        expr_basic_typing_formula expr_basic_typing_lqual expr_total_formula
        expr_total_lqual lqual_lvars lqual_fv lqual_dom];
      better_set_solver.
Qed.

Lemma lstore_instantiate_tm_lift_free_restrict_denot_formula_fv
    gas σ Σ τ e :
  basic_context_ty_lvars (dom Σ) τ ->
  lstore_instantiate_tm
    (lstore_lift_free
      (store_restrict σ (formula_fv (denot_ty_lvar_gas gas Σ τ e)))) e =
  lstore_instantiate_tm (lstore_lift_free σ) e.
Proof.
  intros Hwf.
  eapply lstore_instantiate_tm_lift_free_agree_subset.
  - pose proof (formula_fv_denot_ty_lvar_gas_components_lower
      gas Σ τ e Hwf) as Hlower.
    set_solver.
  - pose proof (formula_fv_denot_ty_lvar_gas_components_lower
      gas Σ τ e Hwf) as Hlower.
    rewrite storeA_restrict_twice_subset; [reflexivity|set_solver].
Qed.

Lemma fv_tm_lstore_instantiate_lift_free_closed_restore
    (σ : StoreT) e :
  store_closed σ ->
  fv_tm e ⊆
    fv_tm (lstore_instantiate_tm (lstore_lift_free σ) e) ∪
    dom (σ : StoreT).
Proof.
  intros Hclosed x Hx.
  destruct (decide (x ∈ dom (σ : StoreT))) as [Hxσ|Hxσ].
  - apply elem_of_union_r. exact Hxσ.
  - apply elem_of_union_l.
    rewrite <- (tm_lvars_fv
      (lstore_instantiate_tm (lstore_lift_free σ) e)).
    rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
    rewrite lvars_fv_elem.
    apply elem_of_difference. split.
    + rewrite <- tm_lvars_fv in Hx.
      apply lvars_fv_elem in Hx. exact Hx.
    + rewrite dom_lstore_lift_free.
      unfold lvars_of_atoms. rewrite elem_of_map.
      intros (y & Heq & Hy). inversion Heq. subst. exact (Hxσ Hy).
Qed.

Lemma denot_ty_lvar_gas_msubst_store_target_scope_from_source
    gas σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hwf _ _ Hσty Hproj Hscope.
  eapply formula_scoped_in_world_from_formula_fv.
  unfold formula_scoped_in_world in Hscope.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hσworld.
  pose proof (formula_msubst_store_fv_restore σ
    (denot_ty_lvar_gas gas Σ τ e)) as Hrestore.
  pose proof (formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ e Hwf) as Hsrc_lower.
  pose proof (formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open
    gas Σ τ (lstore_instantiate_tm (lstore_lift_free σ) e))
    as Htgt_upper.
  pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset
    σ e Hclosed) as Htm.
  set_solver.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_source_scope_from_target
    gas σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)).
Proof.
  intros Hwf _ _ Hσty Hproj Hscope.
  eapply formula_scoped_in_world_from_formula_fv.
  unfold formula_scoped_in_world in Hscope.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hσworld.
  pose proof (formula_msubst_store_fv_subset σ
    (denot_ty_lvar_gas gas Σ τ e)) as Hmsubst_upper.
  pose proof (formula_fv_denot_ty_lvar_gas_subset_relevant_pre_open
    gas Σ τ e) as Hsrc_upper.
  pose proof (formula_fv_denot_ty_lvar_gas_components_lower
    gas Σ τ (lstore_instantiate_tm (lstore_lift_free σ) e) Hwf)
    as Htgt_lower.
  pose proof (fv_tm_lstore_instantiate_lift_free_closed_restore
    σ e Hclosed) as Htm.
  set_solver.
Qed.

Lemma denot_msubst_local_scoped_IH_forward
    gas σ Σ τ e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope Hsrc.
  set (p := denot_ty_lvar_gas gas Σ τ e).
  set (σp := store_restrict σ (formula_fv p)).
  assert (Hrel : dom (σp : StoreT) ⊆ formula_fv p).
  { unfold σp. apply storeA_restrict_dom_subset. }
  assert (Hσp_ty : atom_store_has_ltype Σ σp).
  { unfold σp. apply atom_store_has_ltype_restrict_store. exact Hσty. }
  assert (Hσp_proj : store_singleton_projection σp m).
  { unfold σp. apply store_singleton_projection_restrict_any. exact Hproj. }
  assert (Heq_inst :
    lstore_instantiate_tm (lstore_lift_free σp) e =
    lstore_instantiate_tm (lstore_lift_free σ) e).
  {
    unfold σp, p.
    apply lstore_instantiate_tm_lift_free_restrict_denot_formula_fv.
    exact Hwf.
  }
  change (m ⊨ formula_msubst_store σ p) in Hsrc.
  change (formula_scoped_in_world m (formula_msubst_store σ p)) in Hsrc_scope.
  rewrite (formula_msubst_store_restrict_fv σ p) in Hsrc.
  rewrite (formula_msubst_store_restrict_fv σ p) in Hsrc_scope.
  fold σp in Hsrc.
  fold σp in Hsrc_scope.
  rewrite <- Heq_inst in Htgt_scope.
  rewrite <- Heq_inst.
  exact (proj1 (IH σp Σ τ e m Hrel Hwf He Hlc Hσp_ty Hσp_proj
    Hsrc_scope Htgt_scope) Hsrc).
Qed.

Lemma denot_msubst_local_scoped_IH_backward
    gas σ Σ τ e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e) ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e).
Proof.
  intros IH Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope Htgt.
  set (p := denot_ty_lvar_gas gas Σ τ e).
  set (σp := store_restrict σ (formula_fv p)).
  assert (Hrel : dom (σp : StoreT) ⊆ formula_fv p).
  { unfold σp. apply storeA_restrict_dom_subset. }
  assert (Hσp_ty : atom_store_has_ltype Σ σp).
  { unfold σp. apply atom_store_has_ltype_restrict_store. exact Hσty. }
  assert (Hσp_proj : store_singleton_projection σp m).
  { unfold σp. apply store_singleton_projection_restrict_any. exact Hproj. }
  assert (Heq_inst :
    lstore_instantiate_tm (lstore_lift_free σp) e =
    lstore_instantiate_tm (lstore_lift_free σ) e).
  {
    unfold σp, p.
    apply lstore_instantiate_tm_lift_free_restrict_denot_formula_fv.
    exact Hwf.
  }
  change (formula_scoped_in_world m (formula_msubst_store σ p)) in Hsrc_scope.
  rewrite (formula_msubst_store_restrict_fv σ p) in Hsrc_scope.
  fold σp in Hsrc_scope.
  rewrite <- Heq_inst in Htgt_scope.
  rewrite <- Heq_inst in Htgt.
  pose proof (proj2 (IH σp Σ τ e m Hrel Hwf He Hlc Hσp_ty Hσp_proj
    Hsrc_scope Htgt_scope) Htgt) as Hsrc.
  unfold σp in Hsrc.
  change (m ⊨ formula_msubst_store (store_restrict σ (formula_fv p)) p) in Hsrc.
  change (m ⊨ formula_msubst_store σ p).
  rewrite (formula_msubst_store_restrict_fv σ p).
  exact Hsrc.
Qed.

Lemma denot_msubst_local_scoped_IH_forward_env_agree
    gas σ Σsrc Σmid Σtgt τ e (m : WfWorldT) Xsrc Xtgt :
  denot_msubst_local_scoped_induction_hyp gas ->
  denot_relevant_lvars τ e ⊆ Xsrc ->
  lty_env_restrict_lvars Σsrc Xsrc =
    lty_env_restrict_lvars Σmid Xsrc ->
  denot_relevant_lvars τ
    (lstore_instantiate_tm (lstore_lift_free σ) e) ⊆ Xtgt ->
  lty_env_restrict_lvars Σmid Xtgt =
    lty_env_restrict_lvars Σtgt Xtgt ->
  basic_context_ty_lvars (dom Σmid) τ ->
  tm_lvars e ⊆ dom Σmid ->
  lc_tm e ->
  atom_store_has_ltype Σmid σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σsrc τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σtgt τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σsrc τ e) ->
  m ⊨ denot_ty_lvar_gas gas Σtgt τ
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hsrc_sub Hsrc_eq Htgt_sub Htgt_eq Hwf He Hlc Hσty Hproj
    Hsrc_scope Htgt_scope Hsrc.
  pose proof (denot_ty_lvar_gas_env_agree_on
    gas Σsrc Σmid τ e Xsrc Hsrc_sub Hsrc_eq) as Hsrc_formula_eq.
  pose proof (denot_ty_lvar_gas_env_agree_on
    gas Σmid Σtgt τ (lstore_instantiate_tm (lstore_lift_free σ) e)
    Xtgt Htgt_sub Htgt_eq) as Htgt_formula_eq.
  rewrite Hsrc_formula_eq in Hsrc, Hsrc_scope.
  rewrite <- Htgt_formula_eq in Htgt_scope.
  pose proof (denot_msubst_local_scoped_IH_forward
    gas σ Σmid τ e m IH Hwf He Hlc Hσty Hproj
    Hsrc_scope Htgt_scope Hsrc) as Hmid.
  rewrite Htgt_formula_eq in Hmid.
  exact Hmid.
Qed.

Lemma denot_msubst_local_scoped_IH_backward_env_agree
    gas σ Σsrc Σmid Σtgt τ e (m : WfWorldT) Xsrc Xtgt :
  denot_msubst_local_scoped_induction_hyp gas ->
  denot_relevant_lvars τ e ⊆ Xsrc ->
  lty_env_restrict_lvars Σsrc Xsrc =
    lty_env_restrict_lvars Σmid Xsrc ->
  denot_relevant_lvars τ
    (lstore_instantiate_tm (lstore_lift_free σ) e) ⊆ Xtgt ->
  lty_env_restrict_lvars Σmid Xtgt =
    lty_env_restrict_lvars Σtgt Xtgt ->
  basic_context_ty_lvars (dom Σmid) τ ->
  tm_lvars e ⊆ dom Σmid ->
  lc_tm e ->
  atom_store_has_ltype Σmid σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σsrc τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σtgt τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ denot_ty_lvar_gas gas Σtgt τ
    (lstore_instantiate_tm (lstore_lift_free σ) e) ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σsrc τ e).
Proof.
  intros IH Hsrc_sub Hsrc_eq Htgt_sub Htgt_eq Hwf He Hlc Hσty Hproj
    Hsrc_scope Htgt_scope Htgt.
  pose proof (denot_ty_lvar_gas_env_agree_on
    gas Σsrc Σmid τ e Xsrc Hsrc_sub Hsrc_eq) as Hsrc_formula_eq.
  pose proof (denot_ty_lvar_gas_env_agree_on
    gas Σmid Σtgt τ (lstore_instantiate_tm (lstore_lift_free σ) e)
    Xtgt Htgt_sub Htgt_eq) as Htgt_formula_eq.
  rewrite Hsrc_formula_eq in Hsrc_scope.
  rewrite <- Htgt_formula_eq in Htgt, Htgt_scope.
  pose proof (denot_msubst_local_scoped_IH_backward
    gas σ Σmid τ e m IH Hwf He Hlc Hσty Hproj
    Hsrc_scope Htgt_scope Htgt) as Hmid.
  rewrite <- Hsrc_formula_eq in Hmid.
  exact Hmid.
Qed.

Lemma basic_world_formula_open_msubst_store_fresh_iff
    (σ : StoreT) y T (m : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := T]> ∅))) <->
  m ⊨ formula_open 0 y
      (basic_world_formula (<[LVBound 0 := T]> ∅)).
Proof.
  intros Hyσ. split; intros Hworld.
  - rewrite formula_open_msubst_store_fresh in Hworld by exact Hyσ.
    formula_open_syntax_norm_in Hworld.
    change (m ⊨ FAtom (lqual_msubst_store σ
      (lqual_open 0 y
        (basic_world_lqual (<[LVBound 0 := T]> ∅))))) in Hworld.
    rewrite lqual_msubst_store_fresh in Hworld by
      (unfold lqual_fv, lqual_open, basic_world_lqual;
       cbn [lqual_dom];
       eapply elem_of_disjoint; intros z Hzσ Hzopen;
       pose proof (lvars_fv_open_subset 0 y
         (dom (<[LVBound 0 := T]> ∅ : lty_env)) z Hzopen)
         as Hzopen';
       rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
         lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
       set_solver).
    exact Hworld.
  - change (m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := T]> ∅)))).
    rewrite formula_open_msubst_store_fresh by exact Hyσ.
    formula_open_syntax_norm.
    change (m ⊨ FAtom (lqual_msubst_store σ
      (lqual_open 0 y
        (basic_world_lqual (<[LVBound 0 := T]> ∅))))).
    rewrite lqual_msubst_store_fresh by
      (unfold lqual_fv, lqual_open, basic_world_lqual;
       cbn [lqual_dom];
       eapply elem_of_disjoint; intros z Hzσ Hzopen;
       pose proof (lvars_fv_open_subset 0 y
         (dom (<[LVBound 0 := T]> ∅ : lty_env)) z Hzopen)
         as Hzopen';
       rewrite dom_insert_L, dom_empty_L, lvars_fv_union,
         lvars_fv_singleton_bound, lvars_fv_empty in Hzopen';
       set_solver).
    exact Hworld.
Qed.

Lemma lstore_instantiate_tm_lift_free_tret_fvar_fresh
    (σ : StoreT) y :
  y ∉ dom (σ : StoreT) ->
  lstore_instantiate_tm (lstore_lift_free σ) (tret (vfvar y)) =
  tret (vfvar y).
Proof.
  intros Hy.
  unfold lstore_instantiate_tm, lstore_instantiate_tm_at.
  cbn [lstore_instantiate_tm_split_at lstore_instantiate_value_split_at].
  rewrite lstore_free_part_lift_free.
  destruct ((σ : StoreT) !! y) as [v|] eqn:Hlook; [|reflexivity].
  exfalso. apply Hy.
  change (y ∈ dom (σ : gmap atom value)).
  eapply elem_of_dom_2. exact Hlook.
Qed.

Lemma context_ty_shape_ok_shift k τ :
  context_ty_shape_ok (cty_shift k τ) <-> context_ty_shape_ok τ.
Proof.
  induction τ in k |- *; cbn [cty_shift context_ty_shape_ok];
    try tauto;
    try rewrite ?IHτ1, ?IHτ2, ?cty_shift_preserves_erasure;
    tauto.
Qed.

Lemma atom_store_has_ltype_lty_env_open_one_fresh
    (Σ : lty_env) (σ : StoreT) y :
  y ∉ dom (σ : StoreT) ->
  atom_store_has_ltype Σ σ ->
  atom_store_has_ltype (lty_env_open_one 0 y Σ) σ.
Proof.
  intros Hy Hty x v Hσx.
  destruct (Hty x v Hσx) as [T [HΣx Hv]].
  exists T. split; [|exact Hv].
  assert (Hxy : x <> y).
  {
    intros ->. apply Hy.
    change (y ∈ dom (σ : gmap atom value)).
    eapply elem_of_dom_2. exact Hσx.
  }
  unfold lty_env_open_one, lvar_store_open_one.
  change ((storeA_rekey (logic_var_open 0 y)
    (Σ : gmap logic_var ty) : gmap logic_var ty) !!
    LVFree x = Some T).
  destruct (storeA_rekey_lookup_Some_inj_on
    (V:=ty) (K:=logic_var) (logic_var_open 0 y)
    (Σ : gmap logic_var ty) (LVFree x) T
    ltac:(intros a b _ _ Hab; eapply swap_inj; exact Hab))
    as [_ Hlookup].
  apply Hlookup.
  exists (LVFree x). split; [|exact HΣx].
  unfold swap.
  repeat destruct decide; try lia; try reflexivity; congruence.
Qed.

Lemma basic_context_ty_lvars_wand_arg_open_one
    (Σ : lty_env) y τx τr :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_cty τx ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  basic_context_ty_lvars
    (dom (lty_env_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty τx))))
    (cty_open 0 y (cty_shift 0 τx)).
Proof.
  intros HyΣ Hyτx [Hvars Hshape].
  rewrite lty_env_open_one_dom.
  apply (proj2 (basic_context_ty_lvars_open 0 y
    (dom (typed_lty_env_bind Σ (erase_ty τx))) (cty_shift 0 τx))).
  split.
  - rewrite cty_shift_vars.
    unfold context_ty_shift_lvars.
    rewrite typed_lty_env_bind_dom.
    pose proof (lvars_shift_from_mono 0 (context_ty_lvars τx) (dom Σ))
      as Hmono.
    specialize (Hmono ltac:(
      cbn [context_ty_lvars context_ty_lvars_at] in Hvars; set_solver)).
    intros v Hv.
    set_solver.
  - cbn [context_ty_shape_ok] in Hshape.
    apply context_ty_shape_ok_shift.
    tauto.
Qed.

Lemma basic_context_ty_lvars_arrow_arg_open_one
    (Σ : lty_env) y τx τr :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_cty τx ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  basic_context_ty_lvars
    (dom (lty_env_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty τx))))
    (cty_open 0 y (cty_shift 0 τx)).
Proof.
  intros HyΣ Hyτx Hwf.
  eapply basic_context_ty_lvars_wand_arg_open_one; eauto.
Qed.

Lemma tm_lvars_wand_opened_arg_subset
    (Σ : lty_env) y T :
  tm_lvars (open_tm 0 (vfvar y) (tret (vbvar 0))) ⊆
  dom (lty_env_open_one 0 y (typed_lty_env_bind Σ T)).
Proof.
  cbn [open_tm open_value tm_lvars tm_lvars_at value_lvars_at].
  rewrite decide_True by lia.
  cbn [value_lvars_at].
  rewrite lty_env_open_one_dom, typed_lty_env_bind_dom.
  intros v Hv.
  apply elem_of_singleton in Hv. subst v.
  rewrite set_swap_elem, swap_r.
  apply elem_of_union_r. apply elem_of_singleton.
  all: try set_solver.
Qed.

Lemma basic_context_ty_lvars_wand_result_open_one
    (Σ : lty_env) y τx τr :
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  basic_context_ty_lvars
    (dom (lty_env_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty τx))))
    (cty_open 0 y τr).
Proof.
  intros [Hvars Hshape].
  rewrite lty_env_open_one_dom.
  apply (proj2 (basic_context_ty_lvars_open 0 y
    (dom (typed_lty_env_bind Σ (erase_ty τx))) τr)).
  split.
  - rewrite typed_lty_env_bind_dom.
    transitivity (lvars_shift_from 0 (context_ty_lvars_at 1 τr)
      ∪ {[LVBound 0]}).
    + apply context_ty_lvars_at_succ_body.
    + pose proof (lvars_shift_from_mono 0
        (context_ty_lvars_at 1 τr) (dom Σ)) as Hmono.
      specialize (Hmono ltac:(
        cbn [context_ty_lvars context_ty_lvars_at] in Hvars; set_solver)).
      set_solver.
	  - cbn [context_ty_shape_ok] in Hshape.
	    tauto.
Qed.

Lemma basic_context_ty_lvars_arrow_result_open_one
    (Σ : lty_env) y τx τr :
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  basic_context_ty_lvars
    (dom (lty_env_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty τx))))
    (cty_open 0 y τr).
Proof.
  intros Hwf.
  eapply basic_context_ty_lvars_wand_result_open_one.
  change (basic_context_ty_lvars (dom Σ) (CTWand τx τr)).
  exact Hwf.
Qed.

Lemma tm_lvars_wand_opened_result_subset
    (Σ : lty_env) y T e :
  y ∉ fv_tm e ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  tm_lvars (open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom (lty_env_open_one 0 y (typed_lty_env_bind Σ T)).
Proof.
  intros Hye He Hlc.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc.
  rewrite tm_lvars_tapp_tm_fvar.
  rewrite lty_env_open_one_dom, typed_lty_env_bind_dom.
  intros v Hv.
  apply elem_of_union in Hv as [Hv|Hv].
  - pose proof (He v Hv) as Hdom.
    rewrite (tm_lvars_lc_eq_atoms e Hlc) in Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    rewrite set_swap_elem.
    destruct (decide (a = y)) as [->|Hay].
    + exfalso. exact (Hye Ha).
    + rewrite swap_fresh by congruence.
      apply elem_of_union_l.
      unfold lvars_shift_from. apply elem_of_map.
      exists (LVFree a). split; [reflexivity|exact Hdom].
  - apply elem_of_singleton in Hv. subst v.
    rewrite set_swap_elem, swap_r.
    apply elem_of_union_r. apply elem_of_singleton.
  all: set_solver.
Qed.

Lemma lc_tm_wand_opened_result e y :
  lc_tm e ->
  lc_tm (open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))).
Proof.
  intros Hlc.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc.
  apply lc_tapp_tm; [exact Hlc|constructor].
Qed.

Lemma lstore_instantiate_tm_opened_wand_result
    (σ : StoreT) e y :
  store_closed σ ->
  y ∉ dom (σ : StoreT) ->
  y ∉ fv_tm e ->
  lc_tm e ->
  lstore_instantiate_tm (lstore_lift_free σ)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 e) (vbvar 0))) =
  open_tm 0 (vfvar y)
    (tapp_tm
      (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
      (vbvar 0)).
Proof.
  intros Hclosed Hyσ Hye Hlc.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc.
  rewrite open_tapp_tm_shift_bvar0_lc
    by (apply lstore_instantiate_tm_lift_free_lc; assumption).
  unfold lstore_instantiate_tm.
  rewrite !lstore_instantiate_tm_at_lc_lstore.
  - rewrite !lstore_free_part_lift_free.
    unfold tapp_tm.
    rewrite subst_map_lete, subst_map_tapp.
    rewrite subst_map_vbvar.
    cbn [value_shift].
    rewrite subst_map_value_fresh.
    + reflexivity.
    + change (dom (σ : gmap atom value) ∩ ({[y]} : aset) = ∅).
      set_solver.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma fv_tm_wand_opened_result_source_subset_formula
    gas (Σ : lty_env) τx τr e y :
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  lc_tm e ->
  fv_tm e ⊆
  formula_fv
    (denot_ty_lvar_gas gas
      (lty_env_open_one 0 y
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr) e)
          (erase_ty τx)))
      (cty_open 0 y τr)
      (open_tm 0 (vfvar y)
        (tapp_tm (tm_shift 0 e) (vbvar 0)))).
Proof.
  intros Hwf Hlc.
  pose proof (basic_context_ty_lvars_wand_result_open_one
    (denot_relevant_env Σ (CTWand τx τr) e) y τx τr
    (basic_context_ty_lvars_denot_relevant_env Σ (CTWand τx τr) e Hwf))
    as Hwf_res.
  pose proof (formula_fv_denot_ty_lvar_gas_components_lower gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e)
        (erase_ty τx)))
    (cty_open 0 y τr)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 e) (vbvar 0)))
    Hwf_res) as Hlower.
  rewrite open_tapp_tm_shift_bvar0_lc in Hlower by exact Hlc.
  rewrite fv_tapp_tm in Hlower.
  cbn [fv_value] in Hlower.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc.
  intros a Ha.
  apply Hlower.
  apply elem_of_union_l.
  apply elem_of_union_l.
  exact Ha.
Qed.

Lemma fv_tm_arrow_opened_result_source_subset_formula
    gas (Σ : lty_env) τx τr e y :
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  lc_tm e ->
  fv_tm e ⊆
  formula_fv
    (denot_ty_lvar_gas gas
      (lty_env_open_one 0 y
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr) e)
          (erase_ty τx)))
      (cty_open 0 y τr)
      (open_tm 0 (vfvar y)
        (tapp_tm (tm_shift 0 e) (vbvar 0)))).
Proof.
  intros Hwf Hlc.
  change (denot_relevant_env Σ (CTArrow τx τr) e)
    with (denot_relevant_env Σ (CTWand τx τr) e).
  apply fv_tm_wand_opened_result_source_subset_formula.
  - change (basic_context_ty_lvars (dom Σ) (CTWand τx τr)).
    exact Hwf.
  - exact Hlc.
Qed.

Lemma wand_typed_relevant_bind_fresh
    Σ τx τr e y T :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) T)).
Proof.
  intros HyΣ Hye Hyτx Hyτr.
  rewrite typed_lty_env_bind_dom, lvars_fv_union,
    lvars_shift_from_fv, lvars_fv_singleton_bound.
  intros Hybad.
  apply elem_of_union in Hybad as [Hyrel|Hyempty]; [|set_solver].
  pose proof (lty_env_restrict_lvars_fv_subset Σ
    (denot_relevant_lvars (CTWand τx τr) e) y Hyrel) as Hrel.
  unfold denot_relevant_lvars in Hrel.
  rewrite lvars_fv_union, tm_lvars_fv in Hrel.
  cbn [context_ty_lvars context_ty_lvars_at] in Hrel.
  repeat rewrite lvars_fv_union in Hrel.
  repeat rewrite context_ty_lvars_fv_at in Hrel.
  apply elem_of_union in Hrel as [Hcty|Htm]; [|exact (Hye Htm)].
  apply elem_of_union in Hcty as [Hτx|Hτr].
  - exact (Hyτx Hτx).
  - exact (Hyτr Hτr).
Qed.

Lemma wand_typed_relevant_bind_inst_fresh
    σ Σ τx τr e y T :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  atom_store_has_ltype Σ σ ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e)) T)).
Proof.
  intros HyΣ Hye Hyτx Hyτr Hσty.
  apply wand_typed_relevant_bind_fresh; try assumption.
  pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
  pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset
    σ e Hclosed) as Hfv.
  set_solver.
Qed.

Lemma arrow_typed_relevant_bind_fresh
    Σ τx τr e y T :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) T)).
Proof.
  intros HyΣ Hye Hyτx Hyτr.
  change (denot_relevant_env Σ (CTArrow τx τr) e)
    with (denot_relevant_env Σ (CTWand τx τr) e).
  apply wand_typed_relevant_bind_fresh; assumption.
Qed.

Lemma arrow_typed_relevant_bind_inst_fresh
    σ Σ τx τr e y T :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  atom_store_has_ltype Σ σ ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e)) T)).
Proof.
  intros HyΣ Hye Hyτx Hyτr Hσty.
  change (denot_relevant_env Σ (CTArrow τx τr)
    (lstore_instantiate_tm (lstore_lift_free σ) e))
    with (denot_relevant_env Σ (CTWand τx τr)
      (lstore_instantiate_tm (lstore_lift_free σ) e)).
  apply wand_typed_relevant_bind_inst_fresh; assumption.
Qed.

Lemma wand_arg_relevant_env_agree_open_one
    (Σsrc : lty_env) Ty y τx τr e_src :
  y ∉ fv_cty τx ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTWand τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hyτx.
  set (X := denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y))).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ denot_relevant_lvars (CTWand τx τr) e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union_l.
      apply elem_of_union_l.
      apply elem_of_union in HvX as [Hopen|Hret].
      2:{ set_solver. }
      rewrite set_swap_elem in Hopen.
      rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen
        by congruence.
      unfold lvars_shift_from in Hopen.
      apply elem_of_map in Hopen as [w [Hwshift Hw]].
      destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
        repeat destruct decide; inversion Hwshift; subst; try lia.
      exact Hw.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite swap_l in Hopen.
        apply Hyτx.
        change (y ∈ lvars_fv (context_ty_lvars τx)).
        rewrite <- (lvars_shift_from_fv 0 (context_ty_lvars τx)).
        apply lvars_fv_elem. exact Hopen. }
      { set_solver. }
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ denot_relevant_lvars (CTWand τx τr) e_src))
        as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [context_ty_lvars context_ty_lvars_at
        tm_lvars tm_lvars_at value_lvars_at] in *.
      rewrite cty_open_vars in HvX.
      unfold context_ty_open_lvars in HvX.
      rewrite cty_shift_vars in HvX.
      unfold context_ty_shift_lvars in HvX.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      apply elem_of_union in HvX as [Hopen|Hret].
      { rewrite set_swap_elem in Hopen.
        rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z)) in Hopen
          by congruence.
        unfold lvars_shift_from in Hopen.
        apply elem_of_map in Hopen as [w [Hwshift Hw]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift;
          repeat destruct decide; inversion Hwshift; subst; try lia.
        apply elem_of_union_l. apply elem_of_union_l. exact Hw. }
      { set_solver. }
Qed.

Lemma arrow_arg_relevant_env_agree_open_one
    (Σsrc : lty_env) Ty y τx τr e_src :
  y ∉ fv_cty τx ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTArrow τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y))).
Proof.
  intros Hyτx.
  change (denot_relevant_env Σsrc (CTArrow τx τr) e_src)
    with (denot_relevant_env Σsrc (CTWand τx τr) e_src).
  apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
Qed.

Lemma tm_lvars_wand_opened_result_without_y e y :
  lc_tm e ->
  tm_lvars (open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))) ∖ {[LVFree y]} ⊆
  tm_lvars e.
Proof.
  intros Hlc.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc.
  apply tm_lvars_tapp_tm_fvar_without_arg.
Qed.

Lemma wand_body_relevant_env_agree_open_one
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  y ∉ fv_cty τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ lvars_shift_from 0 (tm_lvars e_src) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTWand τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hyτr He.
  set (X := denot_relevant_lvars (cty_open 0 y τr) e_body).
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  unfold lty_env_open_one, lvar_store_open_one.
  replace v with (logic_var_open 0 y (logic_var_open 0 y v))
    by exact (logic_var_open_involutive 0 y v).
  rewrite !storeA_rekey_lookup by apply swap_inj.
  unfold typed_lty_env_bind, lvar_store_bind.
  set (u := logic_var_open 0 y v).
  fold u.
  destruct u as [k|z] eqn:Hu.
  - destruct k as [|k].
    + rewrite !lookup_insert_eq. reflexivity.
    + cbn [insert].
      rewrite !lookup_insert_ne by discriminate.
      assert (Hv_eq : v = LVBound (S k)).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVBound (S k))) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVBound (S k)) with (logic_var_shift_from 0 (LVBound k))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVBound k ∈ denot_relevant_lvars
        (CTWand τx τr) e_src)) as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * assert (Hbody : LVBound k ∈ context_ty_lvars_at 1 τr).
        {
          rewrite <- (context_ty_lvars_depth τr 1).
          apply lvars_at_depth_elem.
          exists (LVBound (S k)). split.
          - rewrite cty_open_vars in Hτopen.
            unfold context_ty_open_lvars in Hτopen.
            rewrite set_swap_elem in Hτopen.
            rewrite (swap_fresh (LVBound 0) (LVFree y) (LVBound (S k)))
              in Hτopen by congruence.
            exact Hτopen.
          - cbn [logic_var_at_depth].
            rewrite decide_True by lia.
            replace (S k - 1) with k by lia.
            reflexivity.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
      * assert (Hbody : LVBound k ∈ tm_lvars e_src).
        {
          assert (Hshift : LVBound (S k) ∈ lvars_shift_from 0 (tm_lvars e_src)).
          {
            apply He. apply elem_of_difference. split; [exact Hebody|].
            set_solver.
          }
          unfold lvars_shift_from in Hshift.
          apply elem_of_map in Hshift as [w [Hwshift Hw]].
          destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
          - destruct (decide (0 <= n)); [|lia].
            inversion Hwshift. subst n. exact Hw.
          - discriminate.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso.
      unfold u in Hu.
      assert (Hv_eq : v = LVBound 0).
      {
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree y)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * apply Hyτr.
        change (y ∈ lvars_fv (context_ty_lvars τr)).
        rewrite context_ty_lvars_fv.
        apply lvars_fv_elem.
        rewrite cty_open_vars in Hτopen.
        unfold context_ty_open_lvars in Hτopen.
        rewrite set_swap_elem in Hτopen.
        rewrite swap_l in Hτopen.
        exact Hτopen.
      * assert (Hshift : LVBound 0 ∈ lvars_shift_from 0 (tm_lvars e_src)).
        {
          apply He. apply elem_of_difference. split; [exact Hebody|].
          set_solver.
        }
        unfold lvars_shift_from in Hshift.
        apply elem_of_map in Hshift as [w [Hwshift _]].
        destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
        -- destruct (decide (0 <= n)); [|lia].
           inversion Hwshift.
        -- discriminate.
    + rewrite !lookup_insert_ne by congruence.
      assert (Hv_eq : v = LVFree z).
      {
        unfold u in Hu.
        pose proof (f_equal (logic_var_open 0 y) Hu) as Hopen.
        change (swap (LVBound 0) (LVFree y)
          (swap (LVBound 0) (LVFree y) v) =
          swap (LVBound 0) (LVFree y) (LVFree z)) in Hopen.
        rewrite swap_involutive in Hopen.
        unfold swap in Hopen.
        repeat destruct decide; try lia; try congruence.
      }
      subst v.
      unfold lty_env_shift, lvar_store_shift, lvar_store_shift_from.
      replace (LVFree z) with (logic_var_shift_from 0 (LVFree z))
        by reflexivity.
      rewrite !storeA_rekey_lookup by apply logic_var_shift_from_inj.
      unfold denot_relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide (LVFree z ∈ denot_relevant_lvars
        (CTWand τx τr) e_src)) as [Hrel|Hrel]; [reflexivity|].
      exfalso. apply Hrel.
      subst X.
      unfold denot_relevant_lvars in *.
      cbn [tm_lvars tm_lvars_at value_lvars_at] in *.
      apply elem_of_union in HvX as [Hτopen|Hebody].
      * assert (Hbody : LVFree z ∈ context_ty_lvars_at 1 τr).
        {
          rewrite <- (context_ty_lvars_depth τr 1).
          apply lvars_at_depth_elem.
          exists (LVFree z). split.
          - rewrite cty_open_vars in Hτopen.
            unfold context_ty_open_lvars in Hτopen.
            rewrite set_swap_elem in Hτopen.
            rewrite (swap_fresh (LVBound 0) (LVFree y) (LVFree z))
              in Hτopen by congruence.
            exact Hτopen.
          - reflexivity.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
      * assert (Hbody : LVFree z ∈ tm_lvars e_src).
        {
          assert (Hshift : LVFree z ∈ lvars_shift_from 0 (tm_lvars e_src)).
          {
            apply He. apply elem_of_difference. split; [exact Hebody|].
            set_solver.
          }
          unfold lvars_shift_from in Hshift.
          apply elem_of_map in Hshift as [w [Hwshift Hw]].
          destruct w as [n|a]; cbn [logic_var_shift_from] in Hwshift.
          - destruct (decide (0 <= n)); discriminate.
          - inversion Hwshift. subst a. exact Hw.
        }
        cbn [denot_relevant_lvars context_ty_lvars context_ty_lvars_at].
        set_solver.
Qed.

Lemma arrow_body_relevant_env_agree_open_one
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  y ∉ fv_cty τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ lvars_shift_from 0 (tm_lvars e_src) ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σsrc (CTArrow τx τr) e_src) Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σsrc Ty))
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hyτr He.
  change (denot_relevant_env Σsrc (CTArrow τx τr) e_src)
    with (denot_relevant_env Σsrc (CTWand τx τr) e_src).
  apply wand_body_relevant_env_agree_open_one; assumption.
Qed.

Lemma denot_msubst_wand_opened_arg_target_to_source
    gas σ Σ τx τr e y (n : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  formula_scoped_in_world n
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y (cty_shift 0 τx))
          (tret (vfvar y))))) n ->
  formula_scoped_in_world n
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) ->
		  n ⊨ formula_open 0 y
		      (denot_ty_lvar_gas gas
		        (typed_lty_env_bind
		          (denot_relevant_env Σ (CTWand τx τr)
		            (lstore_instantiate_tm (lstore_lift_free σ) e))
		          (erase_ty τx))
		        (cty_shift 0 τx) (tret (vbvar 0))) ->
		  n ⊨ formula_open 0 y
		      (formula_msubst_store σ
		        (denot_ty_lvar_gas gas
	          (typed_lty_env_bind
	            (denot_relevant_env Σ (CTWand τx τr) e)
	            (erase_ty τx))
	          (cty_shift 0 τx) (tret (vbvar 0)))).
Proof.
  intros IH Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
    Hsrc_scope Hsrc_proj Htgt_scope Htgt.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_fresh; eauto. }
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_inst_fresh; eauto. }
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_body_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  assert (Hwf_arg : basic_context_ty_lvars (dom Σmid) τa).
  {
    subst Σmid τa.
    eapply (basic_context_ty_lvars_wand_arg_open_one Σ y τx τr);
      assumption.
  }
  assert (Htm_arg : tm_lvars ea ⊆ dom Σmid).
  { subst Σmid ea. apply tm_lvars_wand_opened_arg_subset. }
  assert (Hlc_arg : lc_tm ea).
  { subst ea. constructor. constructor. }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite formula_open_msubst_store_fresh by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc_scope
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt_scope
    by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt
    by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea in *
    by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  fold Σsrc Σtgt τa in Hsrc_scope, Htgt_scope, Htgt |- *.
  set (p_src := denot_ty_lvar_gas gas Σsrc τa ea).
  set (σarg := store_restrict σ (formula_fv p_src)).
  change (formula_scoped_in_world n (formula_msubst_store σ p_src))
    in Hsrc_scope.
  rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
  fold σarg in Hsrc_scope.
  change (n ⊨ formula_msubst_store σ p_src).
  rewrite (formula_msubst_store_restrict_fv σ p_src).
  fold σarg.
  assert (Heq_ea :
    lstore_instantiate_tm (lstore_lift_free σarg) ea = ea).
  {
    subst ea σarg. apply lstore_instantiate_tm_lift_free_tret_fvar_fresh.
    change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
    rewrite storeA_restrict_dom. set_solver.
  }
  rewrite <- Heq_ea in Htgt.
  eapply denot_msubst_local_scoped_IH_backward_env_agree
    with (Σmid := Σmid)
         (Xsrc := denot_relevant_lvars τa ea)
         (Xtgt := denot_relevant_lvars τa
           (lstore_instantiate_tm (lstore_lift_free σarg) ea)).
  - exact IH.
  - set_solver.
  - subst Σsrc Σmid τa ea.
    apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  - set_solver.
  - subst Σmid Σtgt τa ea.
    rewrite Heq_ea.
    symmetry. apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  - exact Hwf_arg.
  - exact Htm_arg.
  - exact Hlc_arg.
  - subst Σmid σarg.
    apply atom_store_has_ltype_lty_env_open_one_fresh.
    + change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
      rewrite storeA_restrict_dom. set_solver.
    + apply atom_store_has_ltype_typed_lty_env_bind.
      apply atom_store_has_ltype_restrict_store. exact Hσty.
  - exact Hsrc_proj.
  - exact Hsrc_scope.
  - rewrite Heq_ea. exact Htgt_scope.
  - exact Htgt.
Qed.

Lemma denot_msubst_wand_opened_arg_source_scope_from_target
    gas σ Σ τx τr e y (n : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  formula_scoped_in_world n
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) ->
  formula_scoped_in_world n
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))).
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty Htgt_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_fresh; eauto. }
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_inst_fresh; eauto. }
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_body_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt_scope
    by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite formula_open_msubst_store_fresh by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea in *
    by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  fold Σsrc Σtgt τa in Htgt_scope |- *.
  assert (Hsrc_mid :
    denot_ty_lvar_gas gas Σsrc τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σsrc Σmid τa ea.
      apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Htgt_mid :
    denot_ty_lvar_gas gas Σtgt τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σtgt Σmid τa ea.
      apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  eapply formula_scoped_in_world_from_formula_fv.
  pose proof (formula_msubst_store_fv_subset σ
    (denot_ty_lvar_gas gas Σsrc τa ea)) as Hmsubst_fv.
  assert (Hsrc_scope :
    formula_scoped_in_world n (denot_ty_lvar_gas gas Σsrc τa ea)).
  {
    rewrite Hsrc_mid.
    rewrite <- Htgt_mid.
    exact Htgt_scope.
  }
  unfold formula_scoped_in_world in Hsrc_scope.
  set_solver.
Qed.

Lemma denot_msubst_wand_opened_arg_source_to_target
    gas σ Σ τx τr e y (n : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  formula_scoped_in_world n
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y (cty_shift 0 τx))
          (tret (vfvar y))))) n ->
  formula_scoped_in_world n
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) ->
  n ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))) ->
  n ⊨ formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros IH Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
    Hsrc_scope Hsrc_proj Htgt_scope Hsrc.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_fresh; eauto. }
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_inst_fresh; eauto. }
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_body_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  assert (Hwf_arg : basic_context_ty_lvars (dom Σmid) τa).
  {
    subst Σmid τa.
    eapply (basic_context_ty_lvars_wand_arg_open_one Σ y τx τr);
      assumption.
  }
  assert (Htm_arg : tm_lvars ea ⊆ dom Σmid).
  { subst Σmid ea. apply tm_lvars_wand_opened_arg_subset. }
  assert (Hlc_arg : lc_tm ea).
  { subst ea. constructor. constructor. }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite formula_open_msubst_store_fresh in Hsrc by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc_scope
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt_scope
    by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea in *
    by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  fold Σsrc Σtgt τa in Hsrc_scope, Hsrc, Htgt_scope |- *.
  set (p_src := denot_ty_lvar_gas gas Σsrc τa ea).
  set (σarg := store_restrict σ (formula_fv p_src)).
  change (formula_scoped_in_world n (formula_msubst_store σ p_src))
    in Hsrc_scope.
  rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
  fold σarg in Hsrc_scope.
  change (n ⊨ formula_msubst_store σ p_src) in Hsrc.
  rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc.
  fold σarg in Hsrc.
  assert (Heq_ea :
    lstore_instantiate_tm (lstore_lift_free σarg) ea = ea).
  {
    subst ea σarg. apply lstore_instantiate_tm_lift_free_tret_fvar_fresh.
    change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
    rewrite storeA_restrict_dom. set_solver.
  }
  rewrite <- Heq_ea.
  eapply denot_msubst_local_scoped_IH_forward_env_agree
    with (Σmid := Σmid)
         (Xsrc := denot_relevant_lvars τa ea)
         (Xtgt := denot_relevant_lvars τa
           (lstore_instantiate_tm (lstore_lift_free σarg) ea)).
  - exact IH.
  - set_solver.
  - subst Σsrc Σmid τa ea.
    apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  - set_solver.
  - subst Σmid Σtgt τa ea.
    rewrite Heq_ea.
    symmetry. apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  - exact Hwf_arg.
  - exact Htm_arg.
  - exact Hlc_arg.
  - subst Σmid σarg.
    apply atom_store_has_ltype_lty_env_open_one_fresh.
    + change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
      rewrite storeA_restrict_dom. set_solver.
    + apply atom_store_has_ltype_typed_lty_env_bind.
      apply atom_store_has_ltype_restrict_store. exact Hσty.
  - exact Hsrc_proj.
  - exact Hsrc_scope.
  - rewrite Heq_ea. exact Htgt_scope.
  - exact Hsrc.
Qed.

Lemma denot_msubst_wand_completed_arg_target_scope
    gas σ Σ τx τr e y (my nσ : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  world_compat nσ my ->
  store_singleton_projection σ my ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y (cty_shift 0 τx))
          (tret (vfvar y))))) nσ ->
  nσ ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))) ->
  formula_scoped_in_world nσ
      (formula_open 0 y
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))).
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty Hcompat Hproj
    Hsrc_proj Hsrc.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e)
      (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_fresh; eauto. }
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_inst_fresh; eauto. }
  assert (Hea_body_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  rewrite formula_open_msubst_store_fresh in Hsrc by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea in Hsrc
    by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  fold Σsrc τa ea in Hsrc.
  set (p_src := denot_ty_lvar_gas gas Σsrc τa ea).
  set (σarg := store_restrict σ (formula_fv p_src)).
  change (nσ ⊨ formula_msubst_store σ p_src) in Hsrc.
  rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc.
  fold σarg in Hsrc.
  change (store_singleton_projection σarg nσ) in Hsrc_proj.
  assert (Heq_ea :
    lstore_instantiate_tm (lstore_lift_free σarg) ea = ea).
  {
    subst ea σarg. apply lstore_instantiate_tm_lift_free_tret_fvar_fresh.
    change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
    rewrite storeA_restrict_dom. set_solver.
  }
  assert (Hwf_arg : basic_context_ty_lvars (dom Σmid) τa).
  {
    subst Σmid τa.
    eapply (basic_context_ty_lvars_wand_arg_open_one Σ y τx τr);
      eauto.
  }
  assert (Htm_arg : tm_lvars ea ⊆ dom Σmid).
  { subst Σmid ea. apply tm_lvars_wand_opened_arg_subset. }
  assert (Hlc_arg : lc_tm ea).
  { subst ea. constructor. constructor. }
  assert (Hσty_arg : atom_store_has_ltype Σmid σarg).
  {
    subst Σmid σarg.
    apply atom_store_has_ltype_lty_env_open_one_fresh.
    - change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
      rewrite storeA_restrict_dom. set_solver.
    - apply atom_store_has_ltype_typed_lty_env_bind.
      apply atom_store_has_ltype_restrict_store. exact Hσty.
  }
  assert (Hsrc_mid :
    denot_ty_lvar_gas gas Σsrc τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σsrc Σmid τa ea.
      apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Htgt_mid :
    denot_ty_lvar_gas gas Σtgt τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σtgt Σmid τa ea.
      apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Hsrc_scope_mid :
    formula_scoped_in_world nσ
      (formula_msubst_store σarg
        (denot_ty_lvar_gas gas Σmid τa ea))).
  {
    rewrite <- Hsrc_mid.
    exact (res_models_scoped _ _ Hsrc).
  }
  pose proof (denot_ty_lvar_gas_msubst_store_target_scope_from_source
    gas σarg Σmid τa ea nσ Hwf_arg Htm_arg Hlc_arg Hσty_arg
    Hsrc_proj Hsrc_scope_mid) as Hmid_scope.
  rewrite Heq_ea in Hmid_scope.
  rewrite <- Htgt_mid in Hmid_scope.
  assert (Htgt_open_eq :
    formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))) =
    denot_ty_lvar_gas gas Σtgt τa ea).
  {
    subst Σtgt τa ea.
    rewrite formula_open_denot_ty_lvar_gas_singleton;
      [reflexivity|exact Htgt_env_fresh|exact Hea_body_fresh|exact Hτa_fresh].
  }
  rewrite Htgt_open_eq.
  exact Hmid_scope.
Qed.

Definition wand_open_arg_src_formula
    gas Σ τx τr e y : FormulaT :=
  denot_ty_lvar_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)).

Definition wand_open_arg_tgt_formula
    gas (σ : StoreT) Σ τx τr e y : FormulaT :=
  denot_ty_lvar_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)).

Definition wand_open_res_src_msubst_formula
    gas (σ : StoreT) Σ τx τr e y : FormulaT :=
  formula_open 0 y
    (formula_msubst_store σ
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr) e)
          (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e) (vbvar 0)))).

Definition wand_arg_completion_set
    gas (σ : StoreT) Σ τx τr e y : aset :=
  formula_fv (wand_open_arg_src_formula gas Σ τx τr e y) ∪
  formula_fv (wand_open_arg_tgt_formula gas σ Σ τx τr e y).

Definition singleton_wf_world_of_store (σ : StoreT) : WfWorldT :=
  exist _ (singleton_world σ) (wf_singleton_world σ).

Definition wand_arg_completion_world
    gas (σ : StoreT) Σ τx τr e y : WfWorldT :=
  singleton_wf_world_of_store
    (store_restrict σ (wand_arg_completion_set gas σ Σ τx τr e y)).

Lemma res_product_singleton_frame_restrict_disjoint
    (n m : WfWorldT) (σfix : StoreT) (S : aset)
    (Hcfix : world_compat n (singleton_wf_world_of_store σfix))
    (Hcσ : world_compat
      (res_product n (singleton_wf_world_of_store σfix) Hcfix) m)
    (Hc : world_compat n m) :
  dom (σfix : StoreT) ## S ->
  res_restrict
    (res_product
      (res_product n (singleton_wf_world_of_store σfix) Hcfix)
      m Hcσ) S =
  res_restrict (res_product n m Hc) S.
Proof.
  intros Hdisj.
  apply wfworld_ext. apply world_ext.
  - cbn [res_restrict resA_restrict rawA_restrict res_product
      raw_product singleton_wf_world_of_store singleton_world
      world_dom worldA_dom proj1_sig].
    set_solver.
  - intros τ.
    cbn [res_restrict resA_restrict rawA_restrict res_product
      raw_product singleton_wf_world_of_store singleton_world
      world_stores worldA_stores proj1_sig].
    split.
    + intros (τ0 & Hτ0 & Hτ). subst τ.
      destruct Hτ0 as (σnf & σm & Hσnf & Hσm & Hc_nf_m & Hτ0).
      subst τ0.
      destruct Hσnf as (σn & σfix' & Hσn & Hσfix' & Hc_nfix & Hσnf).
      subst σnf.
      inversion Hσfix'. subst σfix'. clear Hσfix'.
      exists (σn ∪ σm).
      split.
      * exists σn, σm. repeat split; eauto.
      * apply storeA_map_eq. intros z.
        rewrite !storeA_restrict_lookup.
        destruct (decide (z ∈ S)) as [HzS|HzS]; [|reflexivity].
        assert ((σfix : gmap atom value) !! z = None) as Hfix_none.
        {
          apply (not_elem_of_dom_1 (D := aset)).
          change (z ∉ dom (σfix : gmap atom value)).
          set_solver.
        }
        destruct ((σn : gmap atom value) !! z) as [vn|] eqn:Hn.
        -- transitivity (Some vn).
           ++ exact (proj2
                (map_lookup_union_Some_raw σn σm z vn)
                (or_introl Hn)).
           ++ symmetry. exact (proj2
                (map_lookup_union_Some_raw (σn ∪ σfix) σm z vn)
                (or_introl (proj2
                  (map_lookup_union_Some_raw σn σfix z vn)
                  (or_introl Hn)))).
        -- destruct ((σm : gmap atom value) !! z) as [vm|] eqn:Hm.
           ++ assert (((σn ∪ σfix) : gmap atom value) !! z = None) as Hnf.
              { apply map_lookup_union_None. split; assumption. }
              transitivity (Some vm).
              ** exact (proj2
                   (map_lookup_union_Some_raw σn σm z vm)
                   (or_intror (conj Hn Hm))).
              ** symmetry. exact (proj2
                   (map_lookup_union_Some_raw (σn ∪ σfix) σm z vm)
                   (or_intror (conj Hnf Hm))).
           ++ assert (((σn ∪ σfix) : gmap atom value) !! z = None) as Hnf.
              { apply map_lookup_union_None. split; assumption. }
              transitivity (@None value).
              ** apply map_lookup_union_None. split; [exact Hn|exact Hm].
              ** symmetry. apply map_lookup_union_None. split; [exact Hnf|exact Hm].
    + intros (τ0 & Hτ0 & Hτ). subst τ.
      destruct Hτ0 as (σn & σm & Hσn & Hσm & Hc_nm & Hτ0).
      subst τ0.
      exists ((σn ∪ σfix) ∪ σm).
      split.
      * exists (σn ∪ σfix), σm.
        repeat split; eauto.
        -- exists σn, σfix. repeat split; eauto.
           exact (Hcfix σn σfix Hσn eq_refl).
        -- apply Hcσ.
           ++ exists σn, σfix. repeat split; eauto.
              exact (Hcfix σn σfix Hσn eq_refl).
           ++ exact Hσm.
      * apply storeA_map_eq. intros z.
        rewrite !storeA_restrict_lookup.
        destruct (decide (z ∈ S)) as [HzS|HzS]; [|reflexivity].
        assert ((σfix : gmap atom value) !! z = None) as Hfix_none.
        {
          apply (not_elem_of_dom_1 (D := aset)).
          change (z ∉ dom (σfix : gmap atom value)).
          set_solver.
        }
        destruct ((σn : gmap atom value) !! z) as [vn|] eqn:Hn.
        -- transitivity (Some vn).
           ++ exact (proj2
                (map_lookup_union_Some_raw (σn ∪ σfix) σm z vn)
                (or_introl (proj2
                  (map_lookup_union_Some_raw σn σfix z vn)
                  (or_introl Hn)))).
           ++ symmetry. exact (proj2
                (map_lookup_union_Some_raw σn σm z vn)
                (or_introl Hn)).
        -- destruct ((σm : gmap atom value) !! z) as [vm|] eqn:Hm.
           ++ assert (((σn ∪ σfix) : gmap atom value) !! z = None) as Hnf.
              { apply map_lookup_union_None. split; assumption. }
              transitivity (Some vm).
              ** exact (proj2
                   (map_lookup_union_Some_raw (σn ∪ σfix) σm z vm)
                   (or_intror (conj Hnf Hm))).
              ** symmetry. exact (proj2
                   (map_lookup_union_Some_raw σn σm z vm)
                   (or_intror (conj Hn Hm))).
           ++ assert (((σn ∪ σfix) : gmap atom value) !! z = None) as Hnf.
              { apply map_lookup_union_None. split; assumption. }
              transitivity (@None value).
              ** apply map_lookup_union_None. split; [exact Hnf|exact Hm].
              ** symmetry. apply map_lookup_union_None. split; [exact Hn|exact Hm].
Qed.

Lemma denot_msubst_wand_completed_frame_result_agree
    gas σ Σ τx τr e y (my n : WfWorldT)
    (Hc : world_compat n my)
    (Hcfix : world_compat n
      (wand_arg_completion_world gas σ Σ τx τr e y))
    (Hcσ : world_compat
      (res_product n
        (wand_arg_completion_world gas σ Σ τx τr e y) Hcfix) my) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  n ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))) ->
  res_restrict
    (res_product
      (res_product n
        (wand_arg_completion_world gas σ Σ τx τr e y) Hcfix)
      my Hcσ)
    (formula_fv
      (wand_open_res_src_msubst_formula gas σ Σ τx τr e y)) =
  res_restrict (res_product n my Hc)
    (formula_fv
      (wand_open_res_src_msubst_formula gas σ Σ τx τr e y)).
Proof.
  intros Hyσ _ _ _ _ _ _ _ _ _.
  unfold wand_arg_completion_world.
  eapply (res_product_singleton_frame_restrict_disjoint
    n my
    (store_restrict σ (wand_arg_completion_set gas σ Σ τx τr e y))
    (formula_fv (wand_open_res_src_msubst_formula gas σ Σ τx τr e y))
    Hcfix Hcσ Hc).
  change (dom (store_restrict σ
      (wand_arg_completion_set gas σ Σ τx τr e y) : StoreT) ##
    formula_fv (wand_open_res_src_msubst_formula gas σ Σ τx τr e y)).
  store_normalize.
  unfold wand_open_res_src_msubst_formula.
  pose proof (formula_open_fv_subset 0 y
    (formula_msubst_store σ
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr) e)
          (erase_ty τx))
        τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) as Hopen.
  pose proof (formula_msubst_store_fv_disjoint_dom σ
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e) (vbvar 0)))) as Hmsubst.
  apply elem_of_disjoint. intros a Ha HaS.
  pose proof (@storeA_restrict_dom value atom _ _ σ
    (wand_arg_completion_set gas σ Σ τx τr e y)) as Hdom_fix.
  change (dom (store_restrict σ
      (wand_arg_completion_set gas σ Σ τx τr e y) : StoreT) =
    dom (σ : StoreT) ∩
      wand_arg_completion_set gas σ Σ τx τr e y) in Hdom_fix.
  rewrite Hdom_fix in Ha.
  apply elem_of_intersection in Ha as [Haσ _].
  pose proof (Hopen a HaS) as HaOpen.
  apply elem_of_union in HaOpen as [HaM | Hay].
  - apply elem_of_disjoint in Hmsubst.
    eapply Hmsubst; [exact HaM | exact Haσ].
  - apply elem_of_singleton in Hay. subst.
    contradiction.
Qed.

Lemma denot_msubst_wand_completed_arg_frame
    gas σ Σ τx τr e y (my n : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  forall Hc : world_compat n my,
  store_singleton_projection σ my ->
  n ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))) ->
  exists (nσ : WfWorldT) (Hcσ : world_compat nσ my),
    nσ ⊨ formula_open 0 y
        (formula_msubst_store σ
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))) /\
    formula_scoped_in_world nσ
      (formula_open 0 y
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))) /\
    store_singleton_projection
      (store_restrict σ
        (formula_fv
          (denot_ty_lvar_gas gas
            (lty_env_open_one 0 y
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx)))
            (cty_open 0 y (cty_shift 0 τx))
            (tret (vfvar y))))) nσ /\
    res_restrict (res_product nσ my Hcσ)
      (formula_fv
        (wand_open_res_src_msubst_formula gas σ Σ τx τr e y)) =
    res_restrict (res_product n my Hc)
      (formula_fv
        (wand_open_res_src_msubst_formula gas σ Σ τx τr e y)).
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty Hc Hproj Hsrc.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  set (p_src := denot_ty_lvar_gas gas Σsrc τa ea).
  set (p_tgt := denot_ty_lvar_gas gas Σtgt τa ea).
  set (Xfix := wand_arg_completion_set gas σ Σ τx τr e y).
  set (nfix := wand_arg_completion_world gas σ Σ τx τr e y).
  assert (Hcfix : world_compat n nfix).
  {
    subst nfix.
    unfold wand_arg_completion_world, singleton_wf_world_of_store.
    eapply world_compat_singleton_restrict_from_projection; eauto.
  }
  set (nσ := res_product n nfix Hcfix).
  assert (Hcσ : world_compat nσ my).
  {
    subst nσ nfix.
    eapply world_compat_product_singleton_restrict_from_projection; eauto.
  }
  exists nσ, Hcσ.
  assert (Hsrc_lift :
    nσ ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))).
  {
    subst nσ.
    eapply res_models_kripke; [apply res_product_le_l | exact Hsrc].
  }
  split; [exact Hsrc_lift |].
  assert (Hsrc_proj : store_singleton_projection
      (store_restrict σ
        (formula_fv
          (denot_ty_lvar_gas gas
            (lty_env_open_one 0 y
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx)))
            (cty_open 0 y (cty_shift 0 τx))
            (tret (vfvar y))))) nσ).
  {
    subst nσ nfix Xfix p_src p_tgt.
    unfold wand_arg_completion_world, singleton_wf_world_of_store,
      wand_arg_completion_set, wand_open_arg_src_formula,
      wand_open_arg_tgt_formula.
    eapply store_singleton_projection_product_singleton_frame.
    set_solver.
  }
  assert (Htgt_scope :
    formula_scoped_in_world nσ
      (formula_open 0 y
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))).
  {
    eapply denot_msubst_wand_completed_arg_target_scope; eauto.
  }
  split; [exact Htgt_scope |].
  split; [exact Hsrc_proj |].
  subst nσ nfix.
  eapply denot_msubst_wand_completed_frame_result_agree; eauto.
Qed.

Lemma denot_msubst_wand_drop_completed_frame_result
    gas σ Σ τx τr e y (my n nσ : WfWorldT)
    (Hc : world_compat n my) (Hcσ : world_compat nσ my) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  n ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))) ->
  let φres :=
    formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0)))) in
  res_restrict (res_product nσ my Hcσ) (formula_fv φres) =
  res_restrict (res_product n my Hc) (formula_fv φres) ->
  res_product nσ my Hcσ ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0)))) ->
  res_product n my Hc ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0)))).
Proof.
  intros _ _ _ _ _ _ _ _ _ _ φres Hagree Hmodel.
  apply (proj2 (res_models_minimal_on (formula_fv φres)
    (res_product n my Hc) φres ltac:(set_solver))).
  rewrite <- Hagree.
  apply (proj1 (res_models_minimal_on (formula_fv φres)
    (res_product nσ my Hcσ) φres ltac:(set_solver))).
  exact Hmodel.
Qed.

Lemma denot_msubst_wand_opened_result_transport_iff
    gas σ Σ τx τr e y (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  formula_scoped_in_world m
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) ->
  formula_scoped_in_world m
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        τr
        (tapp_tm
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (vbvar 0)))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y τr)
          (open_tm 0 (vfvar y)
            (tapp_tm (tm_shift 0 e) (vbvar 0)))))) m ->
  m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0)))) <->
  m ⊨ formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        τr
        (tapp_tm
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (vbvar 0))).
Proof.
  intros IH Hyσ HyΣ Hye Hyτr Hwf He Hlc Hσty
    Hsrc_scope Htgt_scope Hsrc_proj.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τres := cty_open 0 y τr).
  set (esrc := open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))).
  set (etgt := open_tm 0 (vfvar y)
    (tapp_tm
      (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
      (vbvar 0))).
  assert (Hyτx : y ∉ fv_cty τx).
  {
    intros Hybad. apply HyΣ.
    destruct Hwf as [Hvars _].
    pose proof (lvars_fv_mono (context_ty_lvars τx) (dom Σ)
      ltac:(cbn [context_ty_lvars context_ty_lvars_at] in Hvars; set_solver))
      as Hmono.
    apply Hmono. rewrite context_ty_lvars_fv. exact Hybad.
  }
  assert (Hsrc_env_fresh :
    y ∉ lvars_fv
      (dom (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)))).
  { apply wand_typed_relevant_bind_fresh; assumption. }
  assert (Htgt_env_fresh :
    y ∉ lvars_fv
      (dom (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx)))).
  { apply wand_typed_relevant_bind_inst_fresh; assumption. }
  assert (Hsrc_tm_fresh :
    y ∉ fv_tm (tapp_tm (tm_shift 0 e) (vbvar 0))).
  { rewrite fv_tapp_tm, tm_shift_fv. cbn [fv_value]. set_solver. }
  assert (Htgt_tm_fresh :
    y ∉ fv_tm
      (tapp_tm
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (vbvar 0))).
  {
    pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
    pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset
      σ e Hclosed) as Hfv.
    rewrite fv_tapp_tm, tm_shift_fv. cbn [fv_value]. set_solver.
  }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e) (vbvar 0))) in Hsrc_scope
    by (assumption || exact Hsrc_env_fresh || exact Hsrc_tm_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    τr
    (tapp_tm
      (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
      (vbvar 0))) in Htgt_scope
    by (assumption || exact Htgt_env_fresh || exact Htgt_tm_fresh).
  split.
  - intros Hsrc.
    rewrite formula_open_msubst_store_fresh in Hsrc by exact Hyσ.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e) (vbvar 0))) in Hsrc
      by (assumption || exact Hsrc_env_fresh || exact Hsrc_tm_fresh).
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx))
      τr
      (tapp_tm
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (vbvar 0)))
      by (assumption || exact Htgt_env_fresh || exact Htgt_tm_fresh).
    fold Σsrc τres esrc in Hsrc_scope, Hsrc.
    fold Σtgt τres etgt in Htgt_scope |- *.
    set (p_src := denot_ty_lvar_gas gas Σsrc τres esrc).
    set (σres := store_restrict σ (formula_fv p_src)).
    assert (Hwf_res : basic_context_ty_lvars (dom Σmid) τres).
    { subst Σmid τres. apply basic_context_ty_lvars_wand_result_open_one.
      exact Hwf. }
    assert (Htm_res : tm_lvars esrc ⊆ dom Σmid).
    { subst Σmid esrc.
      apply tm_lvars_wand_opened_result_subset; assumption. }
    assert (Hlc_res : lc_tm esrc).
    { subst esrc. apply lc_tm_wand_opened_result. exact Hlc. }
    assert (Hσty_res : atom_store_has_ltype Σmid σres).
    {
      subst Σmid σres.
      apply atom_store_has_ltype_lty_env_open_one_fresh.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - apply atom_store_has_ltype_typed_lty_env_bind.
        apply atom_store_has_ltype_restrict_store. exact Hσty.
    }
    change (formula_scoped_in_world m (formula_msubst_store σ p_src))
      in Hsrc_scope.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
    fold σres in Hsrc_scope.
    change (m ⊨ formula_msubst_store σ p_src) in Hsrc.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc.
    fold σres in Hsrc.
    assert (Heq_res :
      lstore_instantiate_tm (lstore_lift_free σres) esrc = etgt).
    {
      pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
      assert (Hinst_e :
        lstore_instantiate_tm (lstore_lift_free σres) e =
        lstore_instantiate_tm (lstore_lift_free σ) e).
      {
        eapply lstore_instantiate_tm_lift_free_agree_subset
          with (X := formula_fv p_src).
        - subst p_src Σsrc τres esrc.
          apply fv_tm_wand_opened_result_source_subset_formula; assumption.
        - subst σres. rewrite storeA_restrict_twice_same. reflexivity.
      }
      subst esrc etgt σres.
      rewrite lstore_instantiate_tm_opened_wand_result.
      - rewrite Hinst_e. reflexivity.
      - apply store_closed_restrict. exact Hclosed.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - exact Hye.
      - exact Hlc.
    }
    assert (Hsrc_env_agree :
      lty_env_restrict_lvars Σsrc (denot_relevant_lvars τres esrc) =
      lty_env_restrict_lvars Σmid (denot_relevant_lvars τres esrc)).
    {
      subst Σsrc Σmid τres esrc.
      apply wand_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y. exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc e Hlc) in Hn.
            set_solver.
    }
    assert (Htgt_env_agree :
      lty_env_restrict_lvars Σmid
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc)) =
      lty_env_restrict_lvars Σtgt
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc))).
    {
      rewrite Heq_res.
      subst Σmid Σtgt τres etgt.
      symmetry.
      apply wand_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y.
          apply lstore_instantiate_tm_lift_free_lc.
          * pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
            exact Hclosed.
          * exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc
              (lstore_instantiate_tm (lstore_lift_free σ) e)) in Hn.
            -- set_solver.
            -- apply lstore_instantiate_tm_lift_free_lc.
               ++ pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
                  exact Hclosed.
               ++ exact Hlc.
    }
    rewrite <- Heq_res.
    eapply denot_msubst_local_scoped_IH_forward_env_agree
      with (Σmid := Σmid)
           (Xsrc := denot_relevant_lvars τres esrc)
           (Xtgt := denot_relevant_lvars τres
             (lstore_instantiate_tm (lstore_lift_free σres) esrc)).
    + exact IH.
    + set_solver.
    + exact Hsrc_env_agree.
    + set_solver.
    + exact Htgt_env_agree.
    + exact Hwf_res.
    + exact Htm_res.
    + exact Hlc_res.
    + exact Hσty_res.
    + exact Hsrc_proj.
    + exact Hsrc_scope.
    + rewrite Heq_res. exact Htgt_scope.
    + exact Hsrc.
  - intros Htgt.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx))
      τr
      (tapp_tm
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (vbvar 0))) in Htgt
      by (assumption || exact Htgt_env_fresh || exact Htgt_tm_fresh).
    change (m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))).
    rewrite formula_open_msubst_store_fresh by exact Hyσ.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e) (vbvar 0)))
      by (assumption || exact Hsrc_env_fresh || exact Hsrc_tm_fresh).
    fold Σsrc τres esrc in Hsrc_scope |- *.
    fold Σtgt τres etgt in Htgt_scope, Htgt.
    set (p_src := denot_ty_lvar_gas gas Σsrc τres esrc).
    set (σres := store_restrict σ (formula_fv p_src)).
    assert (Hwf_res : basic_context_ty_lvars (dom Σmid) τres).
    { subst Σmid τres. apply basic_context_ty_lvars_wand_result_open_one.
      exact Hwf. }
    assert (Htm_res : tm_lvars esrc ⊆ dom Σmid).
    { subst Σmid esrc.
      apply tm_lvars_wand_opened_result_subset; assumption. }
    assert (Hlc_res : lc_tm esrc).
    { subst esrc. apply lc_tm_wand_opened_result. exact Hlc. }
    assert (Hσty_res : atom_store_has_ltype Σmid σres).
    {
      subst Σmid σres.
      apply atom_store_has_ltype_lty_env_open_one_fresh.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - apply atom_store_has_ltype_typed_lty_env_bind.
        apply atom_store_has_ltype_restrict_store. exact Hσty.
    }
    change (formula_scoped_in_world m (formula_msubst_store σ p_src))
      in Hsrc_scope.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
    fold σres in Hsrc_scope.
    change (m ⊨ formula_msubst_store σ p_src).
    rewrite (formula_msubst_store_restrict_fv σ p_src).
    fold σres.
    assert (Heq_res :
      lstore_instantiate_tm (lstore_lift_free σres) esrc = etgt).
    {
      pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
      assert (Hinst_e :
        lstore_instantiate_tm (lstore_lift_free σres) e =
        lstore_instantiate_tm (lstore_lift_free σ) e).
      {
        eapply lstore_instantiate_tm_lift_free_agree_subset
          with (X := formula_fv p_src).
        - subst p_src Σsrc τres esrc.
          apply fv_tm_wand_opened_result_source_subset_formula; assumption.
        - subst σres. rewrite storeA_restrict_twice_same. reflexivity.
      }
      subst esrc etgt σres.
      rewrite lstore_instantiate_tm_opened_wand_result.
      - rewrite Hinst_e. reflexivity.
      - apply store_closed_restrict. exact Hclosed.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - exact Hye.
      - exact Hlc.
    }
    assert (Hsrc_env_agree :
      lty_env_restrict_lvars Σsrc (denot_relevant_lvars τres esrc) =
      lty_env_restrict_lvars Σmid (denot_relevant_lvars τres esrc)).
    {
      subst Σsrc Σmid τres esrc.
      apply wand_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y. exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc e Hlc) in Hn.
            set_solver.
    }
    assert (Htgt_env_agree :
      lty_env_restrict_lvars Σmid
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc)) =
      lty_env_restrict_lvars Σtgt
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc))).
    {
      rewrite Heq_res.
      subst Σmid Σtgt τres etgt.
      symmetry.
      apply wand_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y.
          apply lstore_instantiate_tm_lift_free_lc.
          * pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
            exact Hclosed.
          * exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc
              (lstore_instantiate_tm (lstore_lift_free σ) e)) in Hn.
            -- set_solver.
            -- apply lstore_instantiate_tm_lift_free_lc.
               ++ pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
                  exact Hclosed.
               ++ exact Hlc.
    }
    rewrite <- Heq_res in Htgt.
    eapply denot_msubst_local_scoped_IH_backward_env_agree
      with (Σmid := Σmid)
           (Xsrc := denot_relevant_lvars τres esrc)
           (Xtgt := denot_relevant_lvars τres
             (lstore_instantiate_tm (lstore_lift_free σres) esrc)).
    + exact IH.
    + set_solver.
    + exact Hsrc_env_agree.
    + set_solver.
    + exact Htgt_env_agree.
    + exact Hwf_res.
    + exact Htm_res.
    + exact Hlc_res.
    + exact Hσty_res.
    + exact Hsrc_proj.
    + exact Hsrc_scope.
    + rewrite Heq_res. exact Htgt_scope.
    + exact Htgt.
Qed.

Lemma denot_msubst_wand_opened_arg_source_projection_from_target_scope
    gas σ Σ τx τr e y (m n : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  world_compat n m ->
  store_singleton_projection σ m ->
  formula_scoped_in_world n
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y (cty_shift 0 τx))
          (tret (vfvar y))))) n.
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty Hcompat Hproj Htgt_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  {
    eapply wand_typed_relevant_bind_inst_fresh; eauto.
  }
  assert (Htgt_eq :
    formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))) =
    denot_ty_lvar_gas gas Σtgt τa ea).
  {
    subst Σtgt τa ea.
    rewrite formula_open_denot_ty_lvar_gas_singleton;
      [reflexivity|exact Htgt_env_fresh| |].
    - cbn [fv_tm fv_value]. set_solver.
    - rewrite cty_shift_fv. exact Hyτx.
  }
  rewrite Htgt_eq in Htgt_scope.
  assert (Hsrc_mid :
    denot_ty_lvar_gas gas Σsrc τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σsrc Σmid τa ea.
      apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Htgt_mid :
    denot_ty_lvar_gas gas Σtgt τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σtgt Σmid τa ea.
      apply wand_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Hsrc_scope :
    formula_scoped_in_world n (denot_ty_lvar_gas gas Σsrc τa ea)).
  {
    rewrite Hsrc_mid.
    rewrite <- Htgt_mid.
    exact Htgt_scope.
  }
  change (store_singleton_projection
    (store_restrict σ (formula_fv (denot_ty_lvar_gas gas Σsrc τa ea))) n).
  eapply store_singleton_projection_compat_restrict_of_scope; eauto.
Qed.

Lemma denot_msubst_wand_opened_result_source_projection_from_source_scope
    gas σ Σ τx τr e y (m n : WfWorldT) (Hc : world_compat n m) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world (res_product n m Hc)
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y τr)
          (open_tm 0 (vfvar y)
            (tapp_tm (tm_shift 0 e) (vbvar 0))))))
    (res_product n m Hc).
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty Hproj Hsrc_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))).
  set (τres := cty_open 0 y τr).
  set (esrc := open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e)
      (erase_ty τx)))).
  { eapply wand_typed_relevant_bind_fresh; eauto. }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e) (vbvar 0))) in Hsrc_scope.
  2: exact Hsrc_env_fresh.
  2:{
    unfold tapp_tm.
    cbn [fv_tm fv_value].
    rewrite tm_shift_fv, value_shift_fv.
    set_solver.
  }
  2: exact Hyτr.
  fold Σsrc τres esrc in Hsrc_scope.
  set (p_src := denot_ty_lvar_gas gas Σsrc τres esrc).
  change (formula_scoped_in_world (res_product n m Hc)
    (formula_msubst_store σ p_src)) in Hsrc_scope.
  assert (Hp_src_scope :
    formula_scoped_in_world (res_product n m Hc) p_src).
  {
    eapply formula_scoped_in_world_from_formula_fv.
    unfold formula_scoped_in_world in Hsrc_scope.
    pose proof (formula_msubst_store_fv_restore σ p_src) as Hrestore.
    pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
      as Hσdom.
    cbn [res_product raw_world world_dom] in *.
    set_solver.
  }
  change (store_singleton_projection
    (store_restrict σ (formula_fv p_src)) (res_product n m Hc)).
  eapply store_singleton_projection_product_restrict_of_scope; eauto.
Qed.

Lemma denot_msubst_arrow_opened_arg_source_projection_from_target_scope
    gas σ Σ τx τr e y (m my : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  store_singleton_projection σ m ->
  formula_scoped_in_world my
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y (cty_shift 0 τx))
          (tret (vfvar y))))) my.
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
    Hdom Hrestrict Hproj Htgt_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  { apply arrow_typed_relevant_bind_inst_fresh; assumption. }
  assert (Htgt_eq :
    formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))) =
    denot_ty_lvar_gas gas Σtgt τa ea).
  {
    subst Σtgt τa ea.
    rewrite formula_open_denot_ty_lvar_gas_singleton;
      [reflexivity|exact Htgt_env_fresh| |].
    - cbn [fv_tm fv_value]. set_solver.
    - rewrite cty_shift_fv. exact Hyτx.
  }
  rewrite Htgt_eq in Htgt_scope.
  assert (Hsrc_mid :
    denot_ty_lvar_gas gas Σsrc τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σsrc Σmid τa ea.
      apply arrow_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Htgt_mid :
    denot_ty_lvar_gas gas Σtgt τa ea =
    denot_ty_lvar_gas gas Σmid τa ea).
  {
    apply denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars τa ea).
    - reflexivity.
    - subst Σtgt Σmid τa ea.
      apply arrow_arg_relevant_env_agree_open_one. exact Hyτx.
  }
  assert (Hsrc_scope :
    formula_scoped_in_world my (denot_ty_lvar_gas gas Σsrc τa ea)).
  {
    rewrite Hsrc_mid.
    rewrite <- Htgt_mid.
    exact Htgt_scope.
  }
  change (store_singleton_projection
    (store_restrict σ (formula_fv (denot_ty_lvar_gas gas Σsrc τa ea))) my).
  eapply store_singleton_projection_forall_restrict_of_scope; eauto.
Qed.

Lemma denot_msubst_arrow_opened_result_source_projection_from_source_scope
    gas σ Σ τx τr e y (m my : WfWorldT) :
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  store_singleton_projection σ m ->
  formula_scoped_in_world my
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y τr)
          (open_tm 0 (vfvar y)
            (tapp_tm (tm_shift 0 e) (vbvar 0))))))
    my.
Proof.
  intros Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
    Hdom Hrestrict Hproj Hsrc_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))).
  set (τres := cty_open 0 y τr).
  set (esrc := open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e)
      (erase_ty τx)))).
  { apply arrow_typed_relevant_bind_fresh; assumption. }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e) (vbvar 0))) in Hsrc_scope.
  2: exact Hsrc_env_fresh.
  2:{
    unfold tapp_tm.
    cbn [fv_tm fv_value].
    rewrite tm_shift_fv, value_shift_fv.
    set_solver.
  }
  2: exact Hyτr.
  fold Σsrc τres esrc in Hsrc_scope.
  set (p_src := denot_ty_lvar_gas gas Σsrc τres esrc).
  change (formula_scoped_in_world my (formula_msubst_store σ p_src))
    in Hsrc_scope.
  assert (Hp_src_scope : formula_scoped_in_world my p_src).
  {
    eapply formula_scoped_in_world_from_formula_fv.
    unfold formula_scoped_in_world in Hsrc_scope.
    pose proof (formula_msubst_store_fv_restore σ p_src) as Hrestore.
    pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
      as Hσdom.
    rewrite Hdom.
    set_solver.
  }
  change (store_singleton_projection
    (store_restrict σ (formula_fv p_src)) my).
  eapply store_singleton_projection_forall_restrict_of_scope; eauto.
Qed.

Lemma denot_msubst_arrow_opened_arg_transport_iff
    gas σ Σ τx τr e y (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  formula_scoped_in_world m
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y (cty_shift 0 τx))
          (tret (vfvar y))))) m ->
  formula_scoped_in_world m
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) ->
  m ⊨ formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))) <->
  m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e)
            (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))).
Proof.
  intros IH Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
    Hsrc_scope Hsrc_proj Htgt_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
	  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
	    (typed_lty_env_bind
	      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)))).
  { eapply arrow_typed_relevant_bind_fresh; eauto. }
	  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
	    (typed_lty_env_bind
	      (denot_relevant_env Σ (CTArrow τx τr)
	        (lstore_instantiate_tm (lstore_lift_free σ) e))
	      (erase_ty τx)))).
  { eapply arrow_typed_relevant_bind_inst_fresh; eauto. }
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_body_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
	  assert (Hwf_arg : basic_context_ty_lvars (dom Σmid) τa).
  {
    subst Σmid τa.
    eapply basic_context_ty_lvars_arrow_arg_open_one; eauto.
  }
	  assert (Htm_arg : tm_lvars ea ⊆ dom Σmid).
  { subst Σmid ea. apply tm_lvars_wand_opened_arg_subset. }
  assert (Hlc_arg : lc_tm ea).
  { subst ea. constructor. constructor. }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc_scope
    by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Htgt_scope
    by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea
    in Hsrc_scope, Htgt_scope
    by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  fold Σsrc Σtgt τa in Hsrc_scope, Htgt_scope.
  split.
  - intros Htgt.
    rewrite formula_open_msubst_store_fresh by exact Hyσ.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0)))
      by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) in Htgt
      by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
    replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea in *
      by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
    fold Σsrc Σtgt τa in Htgt |- *.
    set (p_src := denot_ty_lvar_gas gas Σsrc τa ea).
    set (σarg := store_restrict σ (formula_fv p_src)).
    change (formula_scoped_in_world m (formula_msubst_store σ p_src))
      in Hsrc_scope.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
    fold σarg in Hsrc_scope.
    change (m ⊨ formula_msubst_store σ p_src).
    rewrite (formula_msubst_store_restrict_fv σ p_src).
    fold σarg.
	    assert (Heq_ea :
	      lstore_instantiate_tm (lstore_lift_free σarg) ea = ea).
    {
      subst ea σarg. apply lstore_instantiate_tm_lift_free_tret_fvar_fresh.
      change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
      rewrite storeA_restrict_dom. set_solver.
    }
    rewrite <- Heq_ea in Htgt.
    eapply denot_msubst_local_scoped_IH_backward_env_agree
      with (Σmid := Σmid)
           (Xsrc := denot_relevant_lvars τa ea)
           (Xtgt := denot_relevant_lvars τa
             (lstore_instantiate_tm (lstore_lift_free σarg) ea)).
    + exact IH.
    + set_solver.
    + subst Σsrc Σmid τa ea.
      apply arrow_arg_relevant_env_agree_open_one. exact Hyτx.
    + set_solver.
    + subst Σmid Σtgt τa ea.
      rewrite Heq_ea.
      symmetry. apply arrow_arg_relevant_env_agree_open_one. exact Hyτx.
    + exact Hwf_arg.
    + exact Htm_arg.
    + exact Hlc_arg.
    + subst Σmid σarg.
      apply atom_store_has_ltype_lty_env_open_one_fresh.
      * change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
        rewrite storeA_restrict_dom. set_solver.
      * apply atom_store_has_ltype_typed_lty_env_bind.
        apply atom_store_has_ltype_restrict_store. exact Hσty.
    + exact Hsrc_proj.
    + exact Hsrc_scope.
    + rewrite Heq_ea. exact Htgt_scope.
    + exact Htgt.
  - intros Hsrc.
    rewrite formula_open_msubst_store_fresh in Hsrc by exact Hyσ.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) in Hsrc
      by (exact Hsrc_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0)))
      by (exact Htgt_env_fresh || exact Hea_body_fresh || exact Hτa_fresh).
    replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with ea in *
      by (subst ea; cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
    fold Σsrc Σtgt τa in Hsrc |- *.
    set (p_src := denot_ty_lvar_gas gas Σsrc τa ea).
    set (σarg := store_restrict σ (formula_fv p_src)).
    change (formula_scoped_in_world m (formula_msubst_store σ p_src))
      in Hsrc_scope.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
    fold σarg in Hsrc_scope.
    change (m ⊨ formula_msubst_store σ p_src) in Hsrc.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc.
    fold σarg in Hsrc.
	    assert (Heq_ea :
	      lstore_instantiate_tm (lstore_lift_free σarg) ea = ea).
    {
      subst ea σarg. apply lstore_instantiate_tm_lift_free_tret_fvar_fresh.
      change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
      rewrite storeA_restrict_dom. set_solver.
    }
    rewrite <- Heq_ea.
    eapply denot_msubst_local_scoped_IH_forward_env_agree
      with (Σmid := Σmid)
           (Xsrc := denot_relevant_lvars τa ea)
           (Xtgt := denot_relevant_lvars τa
             (lstore_instantiate_tm (lstore_lift_free σarg) ea)).
    + exact IH.
    + set_solver.
    + subst Σsrc Σmid τa ea.
      apply arrow_arg_relevant_env_agree_open_one. exact Hyτx.
    + set_solver.
    + subst Σmid Σtgt τa ea.
      rewrite Heq_ea.
      symmetry. apply arrow_arg_relevant_env_agree_open_one. exact Hyτx.
    + exact Hwf_arg.
    + exact Htm_arg.
    + exact Hlc_arg.
    + subst Σmid σarg.
      apply atom_store_has_ltype_lty_env_open_one_fresh.
      * change (y ∉ dom (storeA_restrict σ (formula_fv p_src) : gmap atom value)).
        rewrite storeA_restrict_dom. set_solver.
      * apply atom_store_has_ltype_typed_lty_env_bind.
        apply atom_store_has_ltype_restrict_store. exact Hσty.
    + exact Hsrc_proj.
    + exact Hsrc_scope.
    + rewrite Heq_ea. exact Htgt_scope.
    + exact Hsrc.
Qed.

Lemma denot_msubst_arrow_opened_result_transport_iff
    gas σ Σ τx τr e y (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  y ∉ dom (σ : StoreT) ->
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  formula_scoped_in_world m
    (formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))) ->
  store_singleton_projection
    (store_restrict σ
      (formula_fv
        (denot_ty_lvar_gas gas
          (lty_env_open_one 0 y
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr) e)
              (erase_ty τx)))
          (cty_open 0 y τr)
          (open_tm 0 (vfvar y)
            (tapp_tm (tm_shift 0 e) (vbvar 0)))))) m ->
  formula_scoped_in_world m
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        τr
        (tapp_tm
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (vbvar 0)))) ->
  m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0)))) <->
  m ⊨ formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTArrow τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        τr
        (tapp_tm
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (vbvar 0))).
Proof.
  intros IH Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
    Hsrc_scope Hsrc_proj Htgt_scope.
  set (Σsrc := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))).
  set (Σmid := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (Σtgt := lty_env_open_one 0 y
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))).
  set (τres := cty_open 0 y τr).
  set (esrc := open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 e) (vbvar 0))).
  set (etgt := open_tm 0 (vfvar y)
    (tapp_tm
      (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
      (vbvar 0))).
  assert (Hsrc_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)))).
  { apply arrow_typed_relevant_bind_fresh; assumption. }
  assert (Htgt_env_fresh : y ∉ lvars_fv (dom
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx)))).
  { apply arrow_typed_relevant_bind_inst_fresh; assumption. }
  assert (Hsrc_tm_fresh :
    y ∉ fv_tm (tapp_tm (tm_shift 0 e) (vbvar 0))).
  { rewrite fv_tapp_tm, tm_shift_fv. cbn [fv_value]. set_solver. }
  assert (Htgt_tm_fresh :
    y ∉ fv_tm
      (tapp_tm
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (vbvar 0))).
  {
    pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
    pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset
      σ e Hclosed) as Hfv.
    rewrite fv_tapp_tm, tm_shift_fv. cbn [fv_value]. set_solver.
  }
  rewrite formula_open_msubst_store_fresh in Hsrc_scope by exact Hyσ.
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e) (vbvar 0))) in Hsrc_scope
    by (exact Hsrc_env_fresh || exact Hsrc_tm_fresh || exact Hyτr).
  rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
    (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr)
        (lstore_instantiate_tm (lstore_lift_free σ) e))
      (erase_ty τx))
    τr
    (tapp_tm
      (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
      (vbvar 0))) in Htgt_scope
    by (exact Htgt_env_fresh || exact Htgt_tm_fresh || exact Hyτr).
  fold Σsrc τres esrc in Hsrc_scope.
  fold Σtgt τres etgt in Htgt_scope.
  split.
  - intros Hsrc.
    rewrite formula_open_msubst_store_fresh in Hsrc by exact Hyσ.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e) (vbvar 0))) in Hsrc
      by (exact Hsrc_env_fresh || exact Hsrc_tm_fresh || exact Hyτr).
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx))
      τr
      (tapp_tm
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (vbvar 0)))
      by (exact Htgt_env_fresh || exact Htgt_tm_fresh || exact Hyτr).
    fold Σsrc τres esrc in Hsrc.
    fold Σtgt τres etgt.
    set (p_src := denot_ty_lvar_gas gas Σsrc τres esrc).
    set (σres := store_restrict σ (formula_fv p_src)).
    change (m ⊨ formula_msubst_store σ p_src) in Hsrc.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc.
    fold σres in Hsrc.
    change (formula_scoped_in_world m (formula_msubst_store σ p_src))
      in Hsrc_scope.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
    fold σres in Hsrc_scope.
    assert (Hwf_res : basic_context_ty_lvars (dom Σmid) τres).
    { subst Σmid τres. apply basic_context_ty_lvars_arrow_result_open_one.
      exact Hwf. }
    assert (Htm_res : tm_lvars esrc ⊆ dom Σmid).
    { subst Σmid esrc.
      apply tm_lvars_wand_opened_result_subset; assumption. }
    assert (Hlc_res : lc_tm esrc).
    { subst esrc. apply lc_tm_wand_opened_result. exact Hlc. }
    assert (Hσty_res : atom_store_has_ltype Σmid σres).
    {
      subst Σmid σres.
      apply atom_store_has_ltype_lty_env_open_one_fresh.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - apply atom_store_has_ltype_typed_lty_env_bind.
        apply atom_store_has_ltype_restrict_store. exact Hσty.
    }
    assert (Hsrc_env_agree :
      lty_env_restrict_lvars Σsrc (denot_relevant_lvars τres esrc) =
      lty_env_restrict_lvars Σmid (denot_relevant_lvars τres esrc)).
    {
      subst Σsrc Σmid τres esrc.
      apply arrow_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y. exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc e Hlc) in Hn.
            set_solver.
    }
    assert (Heq_res :
      lstore_instantiate_tm (lstore_lift_free σres) esrc = etgt).
    {
      pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
      assert (Hinst_e :
        lstore_instantiate_tm (lstore_lift_free σres) e =
        lstore_instantiate_tm (lstore_lift_free σ) e).
      {
        eapply lstore_instantiate_tm_lift_free_agree_subset
          with (X := formula_fv p_src).
        - subst p_src Σsrc τres esrc.
          apply fv_tm_arrow_opened_result_source_subset_formula; assumption.
        - subst σres. rewrite storeA_restrict_twice_same. reflexivity.
      }
      subst esrc etgt σres.
      rewrite lstore_instantiate_tm_opened_wand_result.
      - rewrite Hinst_e. reflexivity.
      - apply store_closed_restrict. exact Hclosed.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - exact Hye.
      - exact Hlc.
    }
    assert (Htgt_env_agree :
      lty_env_restrict_lvars Σmid
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc)) =
      lty_env_restrict_lvars Σtgt
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc))).
    {
      rewrite Heq_res.
      subst Σmid Σtgt τres etgt.
      symmetry.
      apply arrow_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y.
          apply lstore_instantiate_tm_lift_free_lc.
          * pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
            exact Hclosed.
          * exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc
              (lstore_instantiate_tm (lstore_lift_free σ) e)) in Hn.
            -- set_solver.
            -- apply lstore_instantiate_tm_lift_free_lc.
               ++ pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
                  exact Hclosed.
               ++ exact Hlc.
    }
    rewrite <- Heq_res.
    eapply denot_msubst_local_scoped_IH_forward_env_agree
      with (Σmid := Σmid)
           (Xsrc := denot_relevant_lvars τres esrc)
           (Xtgt := denot_relevant_lvars τres
             (lstore_instantiate_tm (lstore_lift_free σres) esrc)).
    + exact IH.
    + set_solver.
    + exact Hsrc_env_agree.
    + set_solver.
    + exact Htgt_env_agree.
    + exact Hwf_res.
    + exact Htm_res.
    + exact Hlc_res.
    + exact Hσty_res.
    + exact Hsrc_proj.
    + exact Hsrc_scope.
    + rewrite Heq_res. exact Htgt_scope.
    + exact Hsrc.
  - intros Htgt.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr)
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (erase_ty τx))
      τr
      (tapp_tm
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (vbvar 0))) in Htgt
      by (exact Htgt_env_fresh || exact Htgt_tm_fresh || exact Hyτr).
    change (m ⊨ formula_open 0 y
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTArrow τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))).
    rewrite formula_open_msubst_store_fresh by exact Hyσ.
    rewrite (formula_open_denot_ty_lvar_gas_singleton 0 y gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e) (vbvar 0)))
      by (exact Hsrc_env_fresh || exact Hsrc_tm_fresh || exact Hyτr).
    fold Σsrc τres esrc.
    fold Σtgt τres etgt in Htgt.
    set (p_src := denot_ty_lvar_gas gas Σsrc τres esrc).
    set (σres := store_restrict σ (formula_fv p_src)).
    change (m ⊨ formula_msubst_store σ p_src).
    rewrite (formula_msubst_store_restrict_fv σ p_src).
    fold σres.
    change (formula_scoped_in_world m (formula_msubst_store σ p_src))
      in Hsrc_scope.
    rewrite (formula_msubst_store_restrict_fv σ p_src) in Hsrc_scope.
    fold σres in Hsrc_scope.
    assert (Hwf_res : basic_context_ty_lvars (dom Σmid) τres).
    { subst Σmid τres. apply basic_context_ty_lvars_arrow_result_open_one.
      exact Hwf. }
    assert (Htm_res : tm_lvars esrc ⊆ dom Σmid).
    { subst Σmid esrc.
      apply tm_lvars_wand_opened_result_subset; assumption. }
    assert (Hlc_res : lc_tm esrc).
    { subst esrc. apply lc_tm_wand_opened_result. exact Hlc. }
    assert (Hσty_res : atom_store_has_ltype Σmid σres).
    {
      subst Σmid σres.
      apply atom_store_has_ltype_lty_env_open_one_fresh.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - apply atom_store_has_ltype_typed_lty_env_bind.
        apply atom_store_has_ltype_restrict_store. exact Hσty.
    }
    assert (Hsrc_env_agree :
      lty_env_restrict_lvars Σsrc (denot_relevant_lvars τres esrc) =
      lty_env_restrict_lvars Σmid (denot_relevant_lvars τres esrc)).
    {
      subst Σsrc Σmid τres esrc.
      apply arrow_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y. exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc e Hlc) in Hn.
            set_solver.
    }
    assert (Heq_res :
      lstore_instantiate_tm (lstore_lift_free σres) esrc = etgt).
    {
      pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
      assert (Hinst_e :
        lstore_instantiate_tm (lstore_lift_free σres) e =
        lstore_instantiate_tm (lstore_lift_free σ) e).
      {
        eapply lstore_instantiate_tm_lift_free_agree_subset
          with (X := formula_fv p_src).
        - subst p_src Σsrc τres esrc.
          apply fv_tm_arrow_opened_result_source_subset_formula; assumption.
        - subst σres. rewrite storeA_restrict_twice_same. reflexivity.
      }
      subst esrc etgt σres.
      rewrite lstore_instantiate_tm_opened_wand_result.
      - rewrite Hinst_e. reflexivity.
      - apply store_closed_restrict. exact Hclosed.
      - intros Hyres. apply Hyσ.
        pose proof (@storeA_restrict_dom value atom _ _ σ
          (formula_fv p_src)) as Hdom_res.
        change (dom (store_restrict σ (formula_fv p_src) : StoreT) =
          dom (σ : StoreT) ∩ formula_fv p_src) in Hdom_res.
        rewrite Hdom_res in Hyres.
        apply elem_of_intersection in Hyres as [Hyres _].
        exact Hyres.
      - exact Hye.
      - exact Hlc.
    }
    assert (Htgt_env_agree :
      lty_env_restrict_lvars Σmid
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc)) =
      lty_env_restrict_lvars Σtgt
        (denot_relevant_lvars τres
          (lstore_instantiate_tm (lstore_lift_free σres) esrc))).
    {
      rewrite Heq_res.
      subst Σmid Σtgt τres etgt.
      symmetry.
      apply arrow_body_relevant_env_agree_open_one.
      - exact Hyτr.
      - etransitivity.
        + apply tm_lvars_wand_opened_result_without_y.
          apply lstore_instantiate_tm_lift_free_lc.
          * pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
            exact Hclosed.
          * exact Hlc.
        + rewrite lvars_shift_from_below_id.
          * set_solver.
          * intros n Hn.
            rewrite (tm_lvars_no_bv_of_lc
              (lstore_instantiate_tm (lstore_lift_free σ) e)) in Hn.
            -- set_solver.
            -- apply lstore_instantiate_tm_lift_free_lc.
               ++ pose proof (atom_store_has_ltype_closed _ _ Hσty) as Hclosed.
                  exact Hclosed.
               ++ exact Hlc.
    }
    rewrite <- Heq_res in Htgt.
    eapply denot_msubst_local_scoped_IH_backward_env_agree
      with (Σmid := Σmid)
           (Xsrc := denot_relevant_lvars τres esrc)
           (Xtgt := denot_relevant_lvars τres
             (lstore_instantiate_tm (lstore_lift_free σres) esrc)).
    + exact IH.
    + set_solver.
    + exact Hsrc_env_agree.
    + set_solver.
    + exact Htgt_env_agree.
    + exact Hwf_res.
    + exact Htm_res.
    + exact Hlc_res.
    + exact Hσty_res.
    + exact Hsrc_proj.
    + exact Hsrc_scope.
    + rewrite Heq_res. exact Htgt_scope.
    + exact Htgt.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_arrow_body_scoped
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr) e) ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FImpl
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0))))))) ->
  formula_scoped_in_world m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0)))))) ->
  m ⊨ formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FImpl
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0)))))) <->
  m ⊨ FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FImpl
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0))))).
Proof.
  intros IH _ Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  formula_msubst_syntax_norm_in Hsrc_scope.
  split.
  - intros Hsrc.
    formula_msubst_syntax_norm_in Hsrc.
    eapply res_models_forall_full_world_impl2_map;
      [exact Htgt_scope | | exact Hsrc].
	    exists (dom (σ : StoreT) ∪ lvars_fv (dom Σ) ∪ fv_tm e ∪
	      fv_cty τx ∪ fv_cty τr).
	    intros y Hy my Hdom Hrestrict.
	    assert (Hyσ : y ∉ dom (σ : StoreT)) by set_solver.
    assert (HyΣ : y ∉ lvars_fv (dom Σ)) by set_solver.
    assert (Hye : y ∉ fv_tm e) by set_solver.
    assert (Hyτx : y ∉ fv_cty τx) by set_solver.
    assert (Hyτr : y ∉ fv_cty τr) by set_solver.
	    split.
    + intros HA.
      apply (proj2 (basic_world_formula_open_msubst_store_fresh_iff
        σ y (erase_ty τx) my Hyσ)).
      exact HA.
    + split.
      * intros HB.
        pose proof (formula_scoped_forall_impl2_opened m my y
          (formula_msubst_store σ
            (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0))))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0))))
          Hsrc_scope Hdom) as [_ [Hsrc_arg_scope _]].
        pose proof (formula_scoped_forall_impl2_opened m my y
          (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0)))
          Htgt_scope Hdom) as [_ [Htgt_arg_scope _]].
        assert (Hsrc_arg_proj :
          store_singleton_projection
            (store_restrict σ
              (formula_fv
                (denot_ty_lvar_gas gas
                  (lty_env_open_one 0 y
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTArrow τx τr) e)
                      (erase_ty τx)))
                  (cty_open 0 y (cty_shift 0 τx))
                  (tret (vfvar y))))) my).
        {
          eapply denot_msubst_arrow_opened_arg_source_projection_from_target_scope;
            eauto.
        }
	      apply (proj1 (denot_msubst_arrow_opened_arg_transport_iff
	        gas σ Σ τx τr e y my IH Hyσ HyΣ Hye Hyτx Hyτr
          Hwf He Hlc Hσty Hsrc_arg_scope Hsrc_arg_proj Htgt_arg_scope)).
        exact HB.
      * intros HC.
        pose proof (res_models_scoped _ _ HC) as Hsrc_res_scope.
        pose proof (formula_scoped_forall_impl2_opened m my y
          (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0)))
          Htgt_scope Hdom) as [_ [_ Htgt_res_scope]].
        assert (Hsrc_res_proj :
          store_singleton_projection
            (store_restrict σ
              (formula_fv
                (denot_ty_lvar_gas gas
                  (lty_env_open_one 0 y
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTArrow τx τr) e)
                      (erase_ty τx)))
                  (cty_open 0 y τr)
                  (open_tm 0 (vfvar y)
                    (tapp_tm (tm_shift 0 e) (vbvar 0)))))) my).
        {
          eapply denot_msubst_arrow_opened_result_source_projection_from_source_scope;
            eauto.
        }
	      apply (proj1 (denot_msubst_arrow_opened_result_transport_iff
	        gas σ Σ τx τr e y my IH Hyσ HyΣ Hye Hyτx Hyτr
          Hwf He Hlc Hσty Hsrc_res_scope Hsrc_res_proj Htgt_res_scope)).
        exact HC.
  - intros Htgt.
    eapply res_models_forall_full_world_impl2_map;
      [exact Hsrc_scope | | exact Htgt].
	    exists (dom (σ : StoreT) ∪ lvars_fv (dom Σ) ∪ fv_tm e ∪
	      fv_cty τx ∪ fv_cty τr).
	    intros y Hy my Hdom Hrestrict.
	    assert (Hyσ : y ∉ dom (σ : StoreT)) by set_solver.
    assert (HyΣ : y ∉ lvars_fv (dom Σ)) by set_solver.
    assert (Hye : y ∉ fv_tm e) by set_solver.
    assert (Hyτx : y ∉ fv_cty τx) by set_solver.
    assert (Hyτr : y ∉ fv_cty τr) by set_solver.
	    split.
    + intros HA.
      apply (proj1 (basic_world_formula_open_msubst_store_fresh_iff
        σ y (erase_ty τx) my Hyσ)).
      exact HA.
    + split.
      * intros HB.
        pose proof (formula_scoped_forall_impl2_opened m my y
          (formula_msubst_store σ
            (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0))))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0))))
          Hsrc_scope Hdom) as [_ [Hsrc_arg_scope _]].
        pose proof (formula_scoped_forall_impl2_opened m my y
          (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0)))
          Htgt_scope Hdom) as [_ [Htgt_arg_scope _]].
        assert (Hsrc_arg_proj :
          store_singleton_projection
            (store_restrict σ
              (formula_fv
                (denot_ty_lvar_gas gas
                  (lty_env_open_one 0 y
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTArrow τx τr) e)
                      (erase_ty τx)))
                  (cty_open 0 y (cty_shift 0 τx))
                  (tret (vfvar y))))) my).
        {
          eapply denot_msubst_arrow_opened_arg_source_projection_from_target_scope;
            eauto.
        }
	      apply (proj2 (denot_msubst_arrow_opened_arg_transport_iff
	        gas σ Σ τx τr e y my IH Hyσ HyΣ Hye Hyτx Hyτr
          Hwf He Hlc Hσty Hsrc_arg_scope Hsrc_arg_proj Htgt_arg_scope)).
        exact HB.
      * intros HC.
        pose proof (formula_scoped_forall_impl2_opened m my y
          (formula_msubst_store σ
            (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0))))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTArrow τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0))))
          Hsrc_scope Hdom) as [_ [_ Hsrc_res_scope]].
        pose proof (res_models_scoped _ _ HC) as Htgt_res_scope.
        assert (Hsrc_res_proj :
          store_singleton_projection
            (store_restrict σ
              (formula_fv
                (denot_ty_lvar_gas gas
                  (lty_env_open_one 0 y
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTArrow τx τr) e)
                      (erase_ty τx)))
                  (cty_open 0 y τr)
                  (open_tm 0 (vfvar y)
                    (tapp_tm (tm_shift 0 e) (vbvar 0)))))) my).
        {
          eapply denot_msubst_arrow_opened_result_source_projection_from_source_scope;
            eauto.
        }
	      apply (proj2 (denot_msubst_arrow_opened_result_transport_iff
	        gas σ Σ τx τr e y my IH Hyσ HyΣ Hye Hyτx Hyτr
          Hwf He Hlc Hσty Hsrc_res_scope Hsrc_res_proj Htgt_res_scope)).
        exact HC.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_wand_body_scoped
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) e) ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FWand
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0))))))) ->
  formula_scoped_in_world m
    (FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0)))))) ->
  m ⊨ formula_msubst_store σ
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FWand
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0)))))) <->
  m ⊨ FForall
      (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
        (FWand
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            (cty_shift 0 τx) (tret (vbvar 0)))
          (denot_ty_lvar_gas gas
            (typed_lty_env_bind
              (denot_relevant_env Σ (CTWand τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e))
              (erase_ty τx))
            τr
            (tapp_tm
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (vbvar 0))))).
Proof.
  intros IH _ Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  formula_msubst_syntax_norm_in Hsrc_scope.
  split.
  - intros Hsrc.
    formula_msubst_syntax_norm_in Hsrc.
    eapply res_models_forall_full_world_impl_wand_map;
      [exact Htgt_scope | | exact Hsrc].
    exists (dom (σ : StoreT) ∪ lvars_fv (dom Σ) ∪ fv_tm e ∪
      fv_cty τx ∪ fv_cty τr).
		    intros y Hy my Hdom Hrestrict.
		    assert (Hyσ : y ∉ dom (σ : StoreT)) by set_solver.
        assert (HyΣ : y ∉ lvars_fv (dom Σ)) by set_solver.
        assert (Hye : y ∉ fv_tm e) by set_solver.
        assert (Hyτx : y ∉ fv_cty τx) by set_solver.
        assert (Hyτr : y ∉ fv_cty τr) by set_solver.
		    assert (Hproj_my : store_singleton_projection σ my).
	    { eapply store_singleton_projection_of_restrict_base; eauto. }
	    pose proof (formula_scoped_forall_impl_wand_opened
	      m my y
	      (formula_msubst_store σ
	        (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)))
	      (formula_msubst_store σ
	        (denot_ty_lvar_gas gas
	          (typed_lty_env_bind
	            (denot_relevant_env Σ (CTWand τx τr) e)
	            (erase_ty τx))
	          (cty_shift 0 τx) (tret (vbvar 0))))
	      (formula_msubst_store σ
	        (denot_ty_lvar_gas gas
	          (typed_lty_env_bind
	            (denot_relevant_env Σ (CTWand τx τr) e)
	            (erase_ty τx))
	          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))
	      Hsrc_scope Hdom) as [_ [HB_src_scope HC_src_scope]].
	    pose proof (formula_scoped_forall_impl_wand_opened
	      m my y
	      (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
	      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env Σ (CTWand τx τr)
            (lstore_instantiate_tm (lstore_lift_free σ) e))
          (erase_ty τx))
        τr
        (tapp_tm
          (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
          (vbvar 0)))
      Htgt_scope Hdom) as [HA_scope [HB_scope HC_scope]].
    split.
    + intros HA.
      apply (proj2 (basic_world_formula_open_msubst_store_fresh_iff
        σ y (erase_ty τx) my Hyσ)).
      exact HA.
	    + split.
		      * intros n Hc HB.
		        assert (Harg_proj : store_singleton_projection
		          (store_restrict σ
		            (formula_fv
		              (denot_ty_lvar_gas gas
		                (lty_env_open_one 0 y
		                  (typed_lty_env_bind
		                    (denot_relevant_env Σ (CTWand τx τr) e)
		                    (erase_ty τx)))
		                (cty_open 0 y (cty_shift 0 τx))
		                (tret (vfvar y))))) n).
		        {
		          eapply denot_msubst_wand_opened_arg_source_projection_from_target_scope;
		            eauto using res_models_scoped.
			        }
	          pose proof (denot_msubst_wand_opened_arg_source_scope_from_target
	            gas σ Σ τx τr e y n Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
	            (res_models_scoped _ _ HB)) as Harg_src_scope.
			        eapply denot_msubst_wand_opened_arg_target_to_source;
			          eauto using res_models_scoped.
		      * intros n Hc HC.
	          assert (Hres_src_proj : store_singleton_projection
	            (store_restrict σ
	              (formula_fv
	                (denot_ty_lvar_gas gas
	                  (lty_env_open_one 0 y
	                    (typed_lty_env_bind
	                      (denot_relevant_env Σ (CTWand τx τr) e)
	                      (erase_ty τx)))
	                  (cty_open 0 y τr)
	                  (open_tm 0 (vfvar y)
	                    (tapp_tm (tm_shift 0 e) (vbvar 0))))))
	            (res_product n my Hc)).
	          {
	            eapply denot_msubst_wand_opened_result_source_projection_from_source_scope;
	              eauto using res_models_scoped.
	          }
		        apply (proj1 (denot_msubst_wand_opened_result_transport_iff
		          gas σ Σ τx τr e y (res_product n my Hc) IH Hyσ HyΣ Hye Hyτr
	            Hwf He Hlc Hσty
		          (res_models_scoped _ _ HC)
		          (HC_scope n Hc)
	            Hres_src_proj)).
        exact HC.
  - intros Htgt.
    formula_msubst_syntax_norm.
    eapply res_models_forall_full_world_map;
      [exact Hsrc_scope | | exact Htgt].
    exists (dom (σ : StoreT) ∪ lvars_fv (dom Σ) ∪ fv_tm e ∪
      fv_cty τx ∪ fv_cty τr).
    intros y Hy my Hdom Hrestrict Hopen_tgt.
    assert (Hyσ : y ∉ dom (σ : StoreT)) by set_solver.
    assert (HyΣ : y ∉ lvars_fv (dom Σ)) by set_solver.
    assert (Hye : y ∉ fv_tm e) by set_solver.
    assert (Hyτx : y ∉ fv_cty τx) by set_solver.
    assert (Hyτr : y ∉ fv_cty τr) by set_solver.
    assert (Hproj_my : store_singleton_projection σ my).
    { eapply store_singleton_projection_of_restrict_base; eauto. }
    pose proof (formula_scoped_open_from_forall_world_dom
      m my
      (FImpl
        (formula_msubst_store σ
          (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)))
        (FWand
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0))))
          (formula_msubst_store σ
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx))
              τr (tapp_tm (tm_shift 0 e) (vbvar 0))))))
      y Hsrc_scope Hdom) as Hopen_src_scope.
    pose proof (formula_scoped_forall_impl_wand_opened
      m my y
      (formula_msubst_store σ
        (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)))
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0))))
      (formula_msubst_store σ
        (denot_ty_lvar_gas gas
          (typed_lty_env_bind
            (denot_relevant_env Σ (CTWand τx τr) e)
            (erase_ty τx))
          τr (tapp_tm (tm_shift 0 e) (vbvar 0))))
      Hsrc_scope Hdom) as [_ [_ HC_src_scope]].
    formula_open_syntax_norm_in Hopen_src_scope.
    formula_open_syntax_norm_in Hopen_tgt.
    formula_open_syntax_norm.
    eapply res_models_impl_intro; [exact Hopen_src_scope |].
    intros HA_src.
    assert (HA_tgt :
      my ⊨ formula_open 0 y
        (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))).
    {
      apply (proj1 (basic_world_formula_open_msubst_store_fresh_iff
        σ y (erase_ty τx) my Hyσ)).
      exact HA_src.
    }
    pose proof (res_models_impl_elim _ _ _ Hopen_tgt HA_tgt) as Hwand_tgt.
    eapply res_models_wand_intro.
    {
      eapply formula_scoped_impl_r. exact Hopen_src_scope.
    }
    intros n Hc HB_src.
    destruct (denot_msubst_wand_completed_arg_frame
      gas σ Σ τx τr e y my n Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
      Hc Hproj_my HB_src)
      as [nσ [Hcσ [HB_src_lift [Harg_tgt_scope [Harg_proj Hagree]]]]].
    pose proof (denot_msubst_wand_opened_arg_source_to_target
      gas σ Σ τx τr e y nσ IH Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty
      (res_models_scoped _ _ HB_src_lift) Harg_proj Harg_tgt_scope
      HB_src_lift) as HB_tgt.
    pose proof (res_models_wand_elim nσ my Hcσ _ _ Hwand_tgt HB_tgt)
      as HC_tgt.
    assert (Hres_src_proj : store_singleton_projection
      (store_restrict σ
        (formula_fv
          (denot_ty_lvar_gas gas
            (lty_env_open_one 0 y
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) e)
                (erase_ty τx)))
            (cty_open 0 y τr)
            (open_tm 0 (vfvar y)
              (tapp_tm (tm_shift 0 e) (vbvar 0))))))
      (res_product nσ my Hcσ)).
    {
      eapply denot_msubst_wand_opened_result_source_projection_from_source_scope;
        eauto.
    }
    pose proof (proj2 (denot_msubst_wand_opened_result_transport_iff
      gas σ Σ τx τr e y (res_product nσ my Hcσ) IH Hyσ HyΣ Hye Hyτr
      Hwf He Hlc Hσty
	      (HC_src_scope nσ Hcσ)
	      (res_models_scoped _ _ HC_tgt)
	      Hres_src_proj) HC_tgt) as HC_src_completed.
    refine (denot_msubst_wand_drop_completed_frame_result
      gas σ Σ τx τr e y my n nσ Hc Hcσ
      Hyσ HyΣ Hye Hyτx Hyτr Hwf He Hlc Hσty HB_src _ HC_src_completed).
    exact Hagree.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_inter_local_scoped_succ
    gas σ Σ τ1 τ2 e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTInter τ1 τ2) e) ->
  basic_context_ty_lvars (dom Σ) (CTInter τ1 τ2) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTInter τ1 τ2) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTInter τ1 τ2)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTInter τ1 τ2) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTInter τ1 τ2)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  assert (Hwf1 : basic_context_ty_lvars (dom Σ) τ1).
  {
    destruct Hwf as [Hvars Hshape]. split.
    - intros v Hv. apply Hvars.
      cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
    - cbn [context_ty_shape_ok] in Hshape. tauto.
  }
  assert (Hwf2 : basic_context_ty_lvars (dom Σ) τ2).
  {
    destruct Hwf as [Hvars Hshape]. split.
    - intros v Hv. apply Hvars.
      cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
    - cbn [context_ty_shape_ok] in Hshape. tauto.
  }
  cbn [denot_ty_lvar_gas] in *.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  repeat rewrite res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTInter τ1 τ2) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  assert (Hsrc1_scope :
    formula_scoped_in_world m
      (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ1 e))).
  {
    eapply formula_scoped_and_l.
    eapply formula_scoped_and_r.
    exact Hsrc_scope.
  }
  assert (Hsrc2_scope :
    formula_scoped_in_world m
      (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ2 e))).
  {
    eapply formula_scoped_and_r.
    eapply formula_scoped_and_r.
    exact Hsrc_scope.
  }
  assert (Htgt1_scope :
    formula_scoped_in_world m
      (denot_ty_lvar_gas gas Σ τ1
        (lstore_instantiate_tm (lstore_lift_free σ) e))).
  {
    eapply formula_scoped_and_l.
    eapply formula_scoped_and_r.
    exact Htgt_scope.
  }
  assert (Htgt2_scope :
    formula_scoped_in_world m
      (denot_ty_lvar_gas gas Σ τ2
        (lstore_instantiate_tm (lstore_lift_free σ) e))).
  {
    eapply formula_scoped_and_r.
    eapply formula_scoped_and_r.
    exact Htgt_scope.
  }
  split.
  - intros [Hguard [H1 H2]].
    split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTInter τ1 τ2) e)
              (CTInter τ1 τ2))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTInter τ1 τ2) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTInter τ1 τ2) e) e
                  (erase_ty (CTInter τ1 τ2)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + split.
      * eapply denot_msubst_local_scoped_IH_forward; eauto.
      * eapply denot_msubst_local_scoped_IH_forward; eauto.
  - intros [Hguard [H1 H2]].
    split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTInter τ1 τ2)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTInter τ1 τ2))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTInter τ1 τ2)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTInter τ1 τ2)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTInter τ1 τ2)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + split.
      * eapply denot_msubst_local_scoped_IH_backward; eauto.
      * eapply denot_msubst_local_scoped_IH_backward; eauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_union_local_scoped_succ
    gas σ Σ τ1 τ2 e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTUnion τ1 τ2) e) ->
  basic_context_ty_lvars (dom Σ) (CTUnion τ1 τ2) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTUnion τ1 τ2) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTUnion τ1 τ2)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTUnion τ1 τ2) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTUnion τ1 τ2)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  assert (Hwf1 : basic_context_ty_lvars (dom Σ) τ1).
  {
    destruct Hwf as [Hvars Hshape]. split.
    - intros v Hv. apply Hvars.
      cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
    - cbn [context_ty_shape_ok] in Hshape. tauto.
  }
  assert (Hwf2 : basic_context_ty_lvars (dom Σ) τ2).
  {
    destruct Hwf as [Hvars Hshape]. split.
    - intros v Hv. apply Hvars.
      cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
    - cbn [context_ty_shape_ok] in Hshape. tauto.
  }
  cbn [denot_ty_lvar_gas] in *.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTUnion τ1 τ2) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  assert (Hsrc_body_scope :
    formula_scoped_in_world m
      (FOr
        (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ1 e))
        (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ2 e)))).
  { eapply formula_scoped_and_r. exact Hsrc_scope. }
  assert (Htgt_body_scope :
    formula_scoped_in_world m
      (FOr
        (denot_ty_lvar_gas gas Σ τ1
          (lstore_instantiate_tm (lstore_lift_free σ) e))
        (denot_ty_lvar_gas gas Σ τ2
          (lstore_instantiate_tm (lstore_lift_free σ) e)))).
  { eapply formula_scoped_and_r. exact Htgt_scope. }
  assert (Hsrc1_scope :
    formula_scoped_in_world m
      (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ1 e))).
  { eapply formula_scoped_or_l. exact Hsrc_body_scope. }
  assert (Hsrc2_scope :
    formula_scoped_in_world m
      (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ2 e))).
  { eapply formula_scoped_or_r. exact Hsrc_body_scope. }
  assert (Htgt1_scope :
    formula_scoped_in_world m
      (denot_ty_lvar_gas gas Σ τ1
        (lstore_instantiate_tm (lstore_lift_free σ) e))).
  { eapply formula_scoped_or_l. exact Htgt_body_scope. }
  assert (Htgt2_scope :
    formula_scoped_in_world m
      (denot_ty_lvar_gas gas Σ τ2
        (lstore_instantiate_tm (lstore_lift_free σ) e))).
  { eapply formula_scoped_or_r. exact Htgt_body_scope. }
  split.
  - intros [Hguard Hbody].
    split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTUnion τ1 τ2) e)
              (CTUnion τ1 τ2))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTUnion τ1 τ2) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTUnion τ1 τ2) e) e
                  (erase_ty (CTUnion τ1 τ2)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + apply (proj2 (res_models_or_iff m _ _ Htgt_body_scope)).
      apply (proj1 (res_models_or_iff m _ _ Hsrc_body_scope)) in Hbody.
      destruct Hbody as [H1|H2].
      * left. eapply denot_msubst_local_scoped_IH_forward; eauto.
      * right. eapply denot_msubst_local_scoped_IH_forward; eauto.
  - intros [Hguard Hbody].
    split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTUnion τ1 τ2)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTUnion τ1 τ2))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTUnion τ1 τ2)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTUnion τ1 τ2)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTUnion τ1 τ2)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + apply (proj2 (res_models_or_iff m _ _ Hsrc_body_scope)).
      apply (proj1 (res_models_or_iff m _ _ Htgt_body_scope)) in Hbody.
      destruct Hbody as [H1|H2].
      * left. eapply denot_msubst_local_scoped_IH_backward; eauto.
      * right. eapply denot_msubst_local_scoped_IH_backward; eauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_sum_local_scoped_succ
    gas σ Σ τ1 τ2 e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTSum τ1 τ2) e) ->
  basic_context_ty_lvars (dom Σ) (CTSum τ1 τ2) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTSum τ1 τ2) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTSum τ1 τ2)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTSum τ1 τ2) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTSum τ1 τ2)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  assert (Hwf1 : basic_context_ty_lvars (dom Σ) τ1).
  {
    destruct Hwf as [Hvars Hshape]. split.
    - intros v Hv. apply Hvars.
      cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
    - cbn [context_ty_shape_ok] in Hshape. tauto.
  }
  assert (Hwf2 : basic_context_ty_lvars (dom Σ) τ2).
  {
    destruct Hwf as [Hvars Hshape]. split.
    - intros v Hv. apply Hvars.
      cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
    - cbn [context_ty_shape_ok] in Hshape. tauto.
  }
  cbn [denot_ty_lvar_gas] in *.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTSum τ1 τ2) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  split.
  - intros [Hguard Hbody]. split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTSum τ1 τ2) e)
              (CTSum τ1 τ2))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTSum τ1 τ2) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTSum τ1 τ2) e) e
                  (erase_ty (CTSum τ1 τ2)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + apply (proj1 (res_models_plus_iff m _ _)) in Hbody as
        [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]].
      destruct (res_sum_le_singleton_pullback
        m n1 n2 Hdef (dom (σ : StoreT)) σ Hle ltac:(reflexivity) Hproj)
        as [m1 [m2 [Hdef' [Hle' [Hsing1 [Hsing2 [Hrest1 Hrest2]]]]]]].
      assert (Hm1_src :
        m1 ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ1 e)).
      {
        eapply res_models_of_restrict_eq; [|exact Hrest1|exact Hn1].
        eapply res_models_scoped; exact Hn1.
      }
      assert (Hm2_src :
        m2 ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ2 e)).
      {
        eapply res_models_of_restrict_eq; [|exact Hrest2|exact Hn2].
        eapply res_models_scoped; exact Hn2.
      }
      assert (Hproj1 : store_singleton_projection σ m1) by exact Hsing1.
      assert (Hproj2 : store_singleton_projection σ m2) by exact Hsing2.
      pose proof (res_models_scoped _ _ Hm1_src) as Hm1_src_scope.
      pose proof (res_models_scoped _ _ Hm2_src) as Hm2_src_scope.
      pose proof (denot_ty_lvar_gas_msubst_store_target_scope_from_source
        gas σ Σ τ1 e m1 Hwf1 He Hlc Hσty Hproj1 Hm1_src_scope)
        as Hm1_tgt_scope.
      pose proof (denot_ty_lvar_gas_msubst_store_target_scope_from_source
        gas σ Σ τ2 e m2 Hwf2 He Hlc Hσty Hproj2 Hm2_src_scope)
        as Hm2_tgt_scope.
      pose proof (denot_msubst_local_scoped_IH_forward
        gas σ Σ τ1 e m1 IH Hwf1 He Hlc Hσty Hproj1
        Hm1_src_scope Hm1_tgt_scope Hm1_src) as Hm1_tgt.
      pose proof (denot_msubst_local_scoped_IH_forward
        gas σ Σ τ2 e m2 IH Hwf2 He Hlc Hσty Hproj2
        Hm2_src_scope Hm2_tgt_scope Hm2_src) as Hm2_tgt.
      eapply res_models_plus_intro; [exact Hle'|exact Hm1_tgt|exact Hm2_tgt].
  - intros [Hguard Hbody]. split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTSum τ1 τ2)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTSum τ1 τ2))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTSum τ1 τ2)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTSum τ1 τ2)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTSum τ1 τ2)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + apply (proj1 (res_models_plus_iff m _ _)) in Hbody as
        [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]].
      destruct (res_sum_le_singleton_pullback
        m n1 n2 Hdef (dom (σ : StoreT)) σ Hle ltac:(reflexivity) Hproj)
        as [m1 [m2 [Hdef' [Hle' [Hsing1 [Hsing2 [Hrest1 Hrest2]]]]]]].
      assert (Hm1_tgt :
        m1 ⊨ denot_ty_lvar_gas gas Σ τ1
          (lstore_instantiate_tm (lstore_lift_free σ) e)).
      {
        eapply res_models_of_restrict_eq; [|exact Hrest1|exact Hn1].
        eapply res_models_scoped; exact Hn1.
      }
      assert (Hm2_tgt :
        m2 ⊨ denot_ty_lvar_gas gas Σ τ2
          (lstore_instantiate_tm (lstore_lift_free σ) e)).
      {
        eapply res_models_of_restrict_eq; [|exact Hrest2|exact Hn2].
        eapply res_models_scoped; exact Hn2.
      }
      assert (Hproj1 : store_singleton_projection σ m1) by exact Hsing1.
      assert (Hproj2 : store_singleton_projection σ m2) by exact Hsing2.
      pose proof (res_models_scoped _ _ Hm1_tgt) as Hm1_tgt_scope.
      pose proof (res_models_scoped _ _ Hm2_tgt) as Hm2_tgt_scope.
      pose proof (denot_ty_lvar_gas_msubst_store_source_scope_from_target
        gas σ Σ τ1 e m1 Hwf1 He Hlc Hσty Hproj1 Hm1_tgt_scope)
        as Hm1_src_scope.
      pose proof (denot_ty_lvar_gas_msubst_store_source_scope_from_target
        gas σ Σ τ2 e m2 Hwf2 He Hlc Hσty Hproj2 Hm2_tgt_scope)
        as Hm2_src_scope.
      pose proof (denot_msubst_local_scoped_IH_backward
        gas σ Σ τ1 e m1 IH Hwf1 He Hlc Hσty Hproj1
        Hm1_src_scope Hm1_tgt_scope Hm1_tgt) as Hm1_src.
      pose proof (denot_msubst_local_scoped_IH_backward
        gas σ Σ τ2 e m2 IH Hwf2 He Hlc Hσty Hproj2
        Hm2_src_scope Hm2_tgt_scope Hm2_tgt) as Hm2_src.
      eapply res_models_plus_intro; [exact Hle'|exact Hm1_src|exact Hm2_src].
Qed.

Lemma denot_ty_lvar_gas_msubst_store_arrow_local_scoped_succ
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr) e) ->
  basic_context_ty_lvars (dom Σ) (CTArrow τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTArrow τx τr)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  cbn [denot_ty_lvar_gas] in *.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTArrow τx τr) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  pose proof (denot_ty_lvar_gas_msubst_store_arrow_body_scoped
    gas σ Σ τx τr e m IH Hrel Hwf He Hlc Hσty Hproj
    ltac:(eapply formula_scoped_and_r; exact Hsrc_scope)
    ltac:(eapply formula_scoped_and_r; exact Htgt_scope)) as Hbody_iff.
  split.
  - intros [Hguard Hbody]. split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTArrow τx τr) e)
              (CTArrow τx τr))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTArrow τx τr) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTArrow τx τr) e) e
                  (erase_ty (CTArrow τx τr)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + exact (proj1 Hbody_iff Hbody).
  - intros [Hguard Hbody]. split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTArrow τx τr)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTArrow τx τr))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTArrow τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTArrow τx τr)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTArrow τx τr)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + exact (proj2 Hbody_iff Hbody).
Qed.

Lemma denot_ty_lvar_gas_msubst_store_wand_local_scoped_succ
    gas σ Σ τx τr e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) e) ->
  basic_context_ty_lvars (dom Σ) (CTWand τx τr) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTWand τx τr)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  cbn [denot_ty_lvar_gas] in *.
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTWand τx τr) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  pose proof (denot_ty_lvar_gas_msubst_store_wand_body_scoped
    gas σ Σ τx τr e m IH Hrel Hwf He Hlc Hσty Hproj
    ltac:(eapply formula_scoped_and_r; exact Hsrc_scope)
    ltac:(eapply formula_scoped_and_r; exact Htgt_scope)) as Hbody_iff.
  split.
  - intros [Hguard Hbody]. split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTWand τx τr) e)
              (CTWand τx τr))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTWand τx τr) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTWand τx τr) e) e
                  (erase_ty (CTWand τx τr)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + exact (proj1 Hbody_iff Hbody).
  - intros [Hguard Hbody]. split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTWand τx τr)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTWand τx τr))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTWand τx τr)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTWand τx τr)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTWand τx τr)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + exact (proj2 Hbody_iff Hbody).
Qed.

Lemma denot_ty_lvar_gas_msubst_store_local_scoped_succ_rest
    gas σ Σ τ e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ τ e) ->
  (match τ with
   | CTOver _ _ | CTUnder _ _ => False
   | _ => True
   end) ->
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ τ e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros IH Hrel Hrest Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
    try contradiction.
  - eapply denot_ty_lvar_gas_msubst_store_inter_local_scoped_succ; eauto.
  - eapply denot_ty_lvar_gas_msubst_store_union_local_scoped_succ; eauto.
  - eapply denot_ty_lvar_gas_msubst_store_sum_local_scoped_succ; eauto.
  - eapply denot_ty_lvar_gas_msubst_store_arrow_local_scoped_succ; eauto.
  - eapply denot_ty_lvar_gas_msubst_store_wand_local_scoped_succ; eauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_over_local_scoped_succ
    gas σ Σ b φ e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTOver b φ) e) ->
  basic_context_ty_lvars (dom Σ) (CTOver b φ) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTOver b φ) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTOver b φ)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTOver b φ) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTOver b φ)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros _ Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  cbn [denot_ty_lvar_gas] in *.
  assert (Hsrc_body_scope :
    formula_scoped_in_world m
      (formula_msubst_store σ
        (FForall
          (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
            (FImpl
              (expr_result_formula (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FOver (type_qualifier_formula φ)))))))).
  { eapply formula_scoped_and_r. exact Hsrc_scope. }
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTOver b φ) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  assert (Htgt_body_scope :
    formula_scoped_in_world m
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (type_qualifier_formula φ))))))).
  { eapply formula_scoped_and_r. exact Htgt_scope. }
  split.
  - intros [Hguard Hbody]. split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTOver b φ) e)
              (CTOver b φ))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTOver b φ) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTOver b φ) e) e
                  (erase_ty (CTOver b φ)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + change (FOver (formula_msubst_store σ (type_qualifier_formula φ)))
        with (formula_msubst_store σ (FOver (type_qualifier_formula φ)))
        in Hbody.
      rewrite <- formula_msubst_store_fibvars in Hbody.
      change (m ⊨ formula_msubst_store σ
        (FForall
          (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
            (FImpl
              (expr_result_formula (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FOver (type_qualifier_formula φ))))))) in Hbody.
      exact (denot_ty_lvar_gas_msubst_store_over_body_keep_domain
        σ Σ b φ e m Hσty Hproj Hbody).
  - intros [Hguard Hbody]. split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTOver b φ)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTOver b φ))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTOver b φ)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTOver b φ)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTOver b φ)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + pose proof (denot_ty_lvar_gas_msubst_store_over_body_keep_domain_back
        σ Σ b φ e m Hσty Hproj Hsrc_body_scope Htgt_body_scope Hbody)
        as Hbody_src.
      formula_msubst_syntax_norm_in Hbody_src.
      exact Hbody_src.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_under_local_scoped_succ
    gas σ Σ b φ e (m : WfWorldT) :
  denot_msubst_local_scoped_induction_hyp gas ->
  dom (σ : StoreT) ⊆
    formula_fv (denot_ty_lvar_gas (S gas) Σ (CTUnder b φ) e) ->
  basic_context_ty_lvars (dom Σ) (CTUnder b φ) ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas (S gas) Σ (CTUnder b φ) e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas (S gas) Σ (CTUnder b φ)
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ
    (denot_ty_lvar_gas (S gas) Σ (CTUnder b φ) e) <->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTUnder b φ)
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros _ Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  cbn [denot_ty_lvar_gas] in *.
  assert (Hsrc_body_scope :
    formula_scoped_in_world m
      (formula_msubst_store σ
        (FForall
          (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
            (FImpl
              (expr_result_formula (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FUnder (type_qualifier_formula φ)))))))).
  { eapply formula_scoped_and_r. exact Hsrc_scope. }
  formula_msubst_syntax_norm.
  formula_msubst_syntax_norm_in Hsrc_scope.
  rewrite !res_models_and_iff.
  pose proof (denot_guard_msubst_store_local_singleton_iff
    σ Σ (CTUnder b φ) e m Hwf He Hlc Hσty Hproj) as Hguard_iff.
  assert (Htgt_body_scope :
    formula_scoped_in_world m
      (FForall
        (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
          (FImpl
            (expr_result_formula
              (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
              (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (type_qualifier_formula φ))))))).
  { eapply formula_scoped_and_r. exact Htgt_scope. }
  split.
  - intros [Hguard Hbody]. split.
    + assert (Hguard_src :
        m ⊨ formula_msubst_store σ
          (FAnd
            (context_ty_wf_formula (denot_relevant_env Σ (CTUnder b φ) e)
              (CTUnder b φ))
            (FAnd
              (basic_world_formula
                (denot_relevant_env Σ (CTUnder b φ) e))
              (FAnd
                (expr_basic_typing_formula
                  (denot_relevant_env Σ (CTUnder b φ) e) e
                  (erase_ty (CTUnder b φ)))
                (expr_total_formula e))))).
      { formula_msubst_syntax_norm. repeat rewrite res_models_and_iff.
        exact Hguard. }
      pose proof (proj1 Hguard_iff Hguard_src) as Hguard_tgt.
      repeat rewrite res_models_and_iff in Hguard_tgt.
      exact Hguard_tgt.
    + change (FUnder (formula_msubst_store σ (type_qualifier_formula φ)))
        with (formula_msubst_store σ (FUnder (type_qualifier_formula φ)))
        in Hbody.
      rewrite <- formula_msubst_store_fibvars in Hbody.
      change (m ⊨ formula_msubst_store σ
        (FForall
          (FImpl (basic_world_formula (<[LVBound 0 := TBase b]> ∅))
            (FImpl
              (expr_result_formula (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FUnder (type_qualifier_formula φ))))))) in Hbody.
      exact (denot_ty_lvar_gas_msubst_store_under_body_keep_domain
        σ Σ b φ e m Hσty Hproj Hbody).
  - intros [Hguard Hbody]. split.
    + assert (Hguard_tgt :
        m ⊨ FAnd
          (context_ty_wf_formula
            (denot_relevant_env Σ (CTUnder b φ)
              (lstore_instantiate_tm (lstore_lift_free σ) e))
            (CTUnder b φ))
          (FAnd
            (basic_world_formula
              (denot_relevant_env Σ (CTUnder b φ)
                (lstore_instantiate_tm (lstore_lift_free σ) e)))
            (FAnd
              (expr_basic_typing_formula
                (denot_relevant_env Σ (CTUnder b φ)
                  (lstore_instantiate_tm (lstore_lift_free σ) e))
                (lstore_instantiate_tm (lstore_lift_free σ) e)
                (erase_ty (CTUnder b φ)))
              (expr_total_formula
                (lstore_instantiate_tm (lstore_lift_free σ) e))))).
      { repeat rewrite res_models_and_iff. exact Hguard. }
      pose proof (proj2 Hguard_iff Hguard_tgt) as Hguard_src.
      formula_msubst_syntax_norm_in Hguard_src.
      repeat rewrite res_models_and_iff in Hguard_src.
      exact Hguard_src.
    + pose proof (denot_ty_lvar_gas_msubst_store_under_body_keep_domain_back
        σ Σ b φ e m Hσty Hproj Hsrc_body_scope Htgt_body_scope Hbody)
        as Hbody_src.
      formula_msubst_syntax_norm_in Hbody_src.
      exact Hbody_src.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_local_scoped_succ
    gas :
  denot_msubst_local_scoped_induction_hyp gas ->
  denot_msubst_local_scoped_induction_hyp (S gas).
Proof.
  intros IH σ Σ τ e m Hrel Hwf He Hlc Hσty Hproj Hsrc_scope Htgt_scope.
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
    try (eapply denot_ty_lvar_gas_msubst_store_local_scoped_succ_rest;
         [exact IH|exact Hrel|exact I|exact Hwf|exact He|exact Hlc|exact Hσty|exact Hproj
          |exact Hsrc_scope|exact Htgt_scope]).
  - eapply denot_ty_lvar_gas_msubst_store_over_local_scoped_succ;
      [exact IH|exact Hrel|exact Hwf|exact He|exact Hlc|exact Hσty|exact Hproj
       |exact Hsrc_scope|exact Htgt_scope].
  - eapply denot_ty_lvar_gas_msubst_store_under_local_scoped_succ;
      [exact IH|exact Hrel|exact Hwf|exact He|exact Hlc|exact Hσty|exact Hproj
       |exact Hsrc_scope|exact Htgt_scope].
Qed.

Lemma denot_ty_lvar_gas_msubst_store_local_scoped_iff
    gas σ Σ τ e (m : WfWorldT) :
  dom (σ : StoreT) ⊆ formula_fv (denot_ty_lvar_gas gas Σ τ e) ->
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  formula_scoped_in_world m
    (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
  formula_scoped_in_world m
    (denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e) <->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  induction gas as [|gas IH] in σ, Σ, τ, e, m |- *.
  - intros _ Hwf He Hlc Hσty Hproj _ _.
    eapply denot_ty_lvar_gas_zero_msubst_store_local_singleton_iff; eauto.
  - exact (denot_ty_lvar_gas_msubst_store_local_scoped_succ gas IH
      σ Σ τ e m).
Qed.

Lemma denot_ty_lvar_gas_msubst_store_local_iff
    gas σ Σ τ e (m : WfWorldT) :
  basic_context_ty_lvars (dom Σ) τ ->
  tm_lvars e ⊆ dom Σ ->
  lc_tm e ->
  atom_store_has_ltype Σ σ ->
  store_singleton_projection σ m ->
  m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e) <->
  m ⊨ denot_ty_lvar_gas gas Σ τ
        (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros Hwf He Hlc Hσty Hproj.
  set (p := denot_ty_lvar_gas gas Σ τ e).
  set (σp := store_restrict σ (formula_fv p)).
  assert (Hσp_rel : dom (σp : StoreT) ⊆ formula_fv p).
  { unfold σp. apply storeA_restrict_dom_subset. }
  assert (Hσp_ty : atom_store_has_ltype Σ σp).
  { unfold σp. apply atom_store_has_ltype_restrict_store. exact Hσty. }
  assert (Hσp_proj : store_singleton_projection σp m).
  { unfold σp. apply store_singleton_projection_restrict_any. exact Hproj. }
  assert (Heq_inst :
    lstore_instantiate_tm (lstore_lift_free σp) e =
    lstore_instantiate_tm (lstore_lift_free σ) e).
  {
    unfold σp, p.
    apply lstore_instantiate_tm_lift_free_restrict_denot_formula_fv.
    exact Hwf.
  }
  split.
  - intros Hsrc.
    rewrite (formula_msubst_store_restrict_fv σ p) in Hsrc.
    fold σp in Hsrc.
    pose proof (denot_ty_lvar_gas_msubst_store_local_scoped_iff
      gas σp Σ τ e m Hσp_rel Hwf He Hlc Hσp_ty Hσp_proj
      (res_models_scoped _ _ Hsrc)
      ltac:(eapply denot_ty_lvar_gas_msubst_store_target_scope_from_source; eauto;
            exact (res_models_scoped _ _ Hsrc))) as Hiff.
    rewrite <- Heq_inst.
    exact (proj1 Hiff Hsrc).
  - intros Htgt.
    rewrite <- Heq_inst in Htgt.
    pose proof (denot_ty_lvar_gas_msubst_store_local_scoped_iff
      gas σp Σ τ e m Hσp_rel Hwf He Hlc Hσp_ty Hσp_proj
      ltac:(eapply denot_ty_lvar_gas_msubst_store_source_scope_from_target; eauto;
            exact (res_models_scoped _ _ Htgt))
      (res_models_scoped _ _ Htgt)) as Hiff.
    pose proof (proj2 Hiff Htgt) as Hsrc.
    unfold σp in Hsrc.
    change (m ⊨ formula_msubst_store (store_restrict σ (formula_fv p)) p) in Hsrc.
    change (m ⊨ formula_msubst_store σ p).
    rewrite (formula_msubst_store_restrict_fv σ p).
    exact Hsrc.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_from_typing_wf_iff
    gas Σbase Δ σ τ e (m : WfWorldT) :
  context_typing_wf_erased Σbase Δ e τ ->
  storeA_has_type Σbase σ ->
  base_store_projection Σbase σ m ->
  m ⊨ formula_msubst_store σ
        (denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e) <->
  m ⊨ denot_ty_lvar_gas gas
        (atom_env_to_lty_env Δ) τ
        (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros Hwf Hty Hproj.
  destruct Hwf as [Henv [Hτ He]].
  pose proof (context_ty_wf_for_erased_regular
    Σbase Δ τ Henv Hτ) as Hbasicτ.
  pose proof (basic_typing_regular_tm _ _ _ He) as Hlc.
  pose proof (basic_typing_contains_fv_tm _ _ _ He) as Hfv.
  eapply denot_ty_lvar_gas_msubst_store_local_iff.
  - unfold basic_context_ty in Hbasicτ.
    rewrite atom_store_to_lvar_store_dom.
    exact Hbasicτ.
  - rewrite (tm_lvars_lc_eq_atoms e Hlc).
    rewrite atom_store_to_lvar_store_dom.
    unfold lvars_of_atoms.
    intros v Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply elem_of_map. exists x. split; [reflexivity|].
    exact (Hfv _ Hx).
  - exact Hlc.
  - eapply base_store_projection_atom_store_has_ltype_under; eauto.
  - eapply base_store_projection_to_store_singleton_projection; eauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_from_typing_wf
    gas Σbase Δ σ τ e (m : WfWorldT) :
  context_typing_wf_erased Σbase Δ e τ ->
  storeA_has_type Σbase σ ->
  base_store_projection Σbase σ m ->
  m ⊨ formula_msubst_store σ
        (denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e) ->
  m ⊨ denot_ty_lvar_gas gas
        (atom_env_to_lty_env Δ) τ
        (lstore_instantiate_tm (lstore_lift_free σ) e).
Proof.
  intros Hwf Hty Hproj Hmodels.
  eapply denot_ty_lvar_gas_msubst_store_from_typing_wf_iff; eauto.
Qed.

Lemma denot_ty_lvar_gas_msubst_store_to_typing_wf
    gas Σbase Δ σ τ e (m : WfWorldT) :
  context_typing_wf_erased Σbase Δ e τ ->
  storeA_has_type Σbase σ ->
  base_store_projection Σbase σ m ->
  m ⊨ denot_ty_lvar_gas gas
        (atom_env_to_lty_env Δ) τ
        (lstore_instantiate_tm (lstore_lift_free σ) e) ->
  m ⊨ formula_msubst_store σ
        (denot_ty_lvar_gas gas (atom_env_to_lty_env Δ) τ e).
Proof.
  intros Hwf Hty Hproj Hmodels.
  eapply denot_ty_lvar_gas_msubst_store_from_typing_wf_iff; eauto.
Qed.
End ContextTypeDenotationMsubst.
