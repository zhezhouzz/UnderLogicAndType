(** * Denotation.ContextTypeDenotationMsubstScoped

    Split from ContextTypeDenotationMsubst for incremental compilation. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationLvars
  ContextTypeDenotationMsubstCore
  ContextTypeDenotationMsubstGuard
  ContextTypeDenotationMsubstKeepDomain.

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
  (* Arrow-specific forall/negative-position transport. *)
Admitted.

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
  (* Wand-specific frame/product singleton transport. *)
Admitted.

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
