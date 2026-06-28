(** * Denotation.TypeEquivWand

    Wand case for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen TypeDenoteRegular.
From CoreLang Require Import Sugar.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTermBase
  TypeEquivTermResult
  TypeEquivFiberBaseCore
  TypeEquivFiberBaseProjected
  TypeEquivBody
  TypeEquivArrow.

Section TypeDenote.

Local Ltac wand_union_member :=
  first
    [ assumption
    | apply elem_of_union_l; wand_union_member
    | apply elem_of_union_r; wand_union_member ].

Local Lemma wand_open_world_term_scope
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (my : WorldT).
Proof.
  intros Hequiv Hdom a Ha.
  rewrite Hdom.
  apply elem_of_union_l.
  exact (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv a Ha).
Qed.

Local Lemma wand_open_product_tapp_tgt_scope
    (Σ : lty_env) τx τr e1 e2 (m my n : WfWorldT)
    y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  fv_tm (tapp_tm e2 (vfvar y)) ⊆ world_dom (res_product n my Hc : WorldT).
Proof.
  intros Hequiv Hdom a Ha.
  rewrite fv_tapp_tm in Ha.
  cbn [fv_value] in Ha.
  pose proof (raw_le_dom (my : WorldT)
    (res_product n my Hc : WorldT)
    (res_product_le_r n my Hc)) as Hdom_le.
  apply Hdom_le.
  apply elem_of_union in Ha as [Ha|Ha].
  - eapply wand_open_world_term_scope; [exact Hequiv|exact Hdom|].
    apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
Qed.

Local Lemma wand_open_world_tapp_apps_scope
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  fv_tm (tapp_tm e1 (vfvar y)) ∪
  fv_tm (tapp_tm e2 (vfvar y)) ⊆ world_dom (my : WorldT).
Proof.
  intros Hequiv Hdom a Ha.
  apply elem_of_union in Ha as [Ha|Ha];
    rewrite fv_tapp_tm in Ha; cbn [fv_value] in Ha;
    apply elem_of_union in Ha as [Ha|Ha].
  - eapply wand_open_world_term_scope; [exact Hequiv|exact Hdom|].
    apply elem_of_union_l. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  - eapply wand_open_world_term_scope; [exact Hequiv|exact Hdom|].
    apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
Qed.

Lemma wand_open_arg_to_inserted_env
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e))
    τx (tret (vfvar y)) ->
	  m ⊨ ty_denote_gas gas
	    (<[LVFree y := erase_ty τx]> Σ)
	    τx (tret (vfvar y)).
Proof.
  intros Harg.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - apply wand_arg_relevant_env_agree_insert_core.
  - exact Harg.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_open_arg_fbwand
    gas (Σ : lty_env) τx τr e1 e2
    (n : WfWorldT) y :
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e1))
    τx (tret (vfvar y)).
Proof.
  intros Htgt.
  pose proof (wand_open_arg_to_inserted_env
    gas Σ τx τr e2 n y Htgt) as Hmid.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - symmetry. apply wand_arg_relevant_env_agree_insert_core.
  - exact Hmid.
Qed.

Lemma ty_equiv_wand_result_src_mid
    gas (Σ : lty_env) τx τr e1
    (m : WfWorldT) y :
  y ∉ fv_cty τr ->
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hyτr Hτr_vars Hsrc.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - apply wand_body_relevant_env_agree_insert_core.
    + exact Hτr_vars.
    + apply tm_lvars_tapp_tm_fvar_without_arg.
  - exact Hsrc.
Qed.

Lemma ty_equiv_wand_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (m : WfWorldT) y :
  y ∉ fv_cty τr ->
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hyτr Hτr_vars Hmid.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - symmetry. apply wand_body_relevant_env_agree_insert_core.
    + exact Hτr_vars.
    + apply tm_lvars_tapp_tm_fvar_without_arg.
  - exact Hmid.
Qed.

Lemma wfworld_closed_on_wand_open_result_apps
    (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  n ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y)))
    (res_product n my Hc).
Proof.
  intros Hequiv Hdom Hrestrict Hworld.
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero2) as Hguard2.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard1) as Hworld1.
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard1) as Hbasic1.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard2) as Hworld2.
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard2) as Hbasic2.
  assert (Hle : m ⊑ my).
  {
    change (m ⊑ my).
    rewrite <- Hrestrict.
    apply res_restrict_le.
  }
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed1 : wfworld_closed_on (fv_tm e1) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. apply elem_of_union_l. exact Ha.
    - exact Hle.
    - eapply relevant_world_typing_closed_on_term.
      + exact Hworld1.
      + exact Hbasic1.
  }
  assert (Hclosed2 : wfworld_closed_on (fv_tm e2) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. apply elem_of_union_r. exact Ha.
    - exact Hle.
    - eapply relevant_world_typing_closed_on_term.
      + exact Hworld2.
      + exact Hbasic2.
  }
  assert (Hclosed_base :
      wfworld_closed_on
        (fv_tm e1 ∪ fv_tm e2) my).
  {
    apply (wfworld_closed_on_union (fv_tm e1) (fv_tm e2));
      [exact Hclosed1|exact Hclosed2].
  }
  assert (Hclosed_base_prod :
      wfworld_closed_on (fv_tm e1 ∪ fv_tm e2) (res_product n my Hc)).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. rewrite Hdom. set_solver.
    - apply res_product_le_r.
    - exact Hclosed_base.
  }
  assert (Hclosed_y_prod :
      wfworld_closed_on ({[y]} : aset) (res_product n my Hc)).
  {
    assert (Hy_n : ({[y]} : aset) ⊆ world_dom (n : WorldT)).
    {
      apply basic_world_formula_models_iff in Hworld as [_ [Hdom_y _]].
      rewrite dom_insert_L, dom_empty_L in Hdom_y.
      rewrite lvars_fv_union, lvars_fv_empty,
        lvars_fv_singleton_free in Hdom_y.
      intros a Ha. apply Hdom_y.
      apply elem_of_union_l. exact Ha.
    }
    eapply wfworld_closed_on_le.
    - exact Hy_n.
    - apply res_product_le_l.
    - eapply basic_world_formula_singleton_free_closed_on. exact Hworld.
  }
  eapply (wfworld_closed_on_mono _
    ((fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset)) (res_product n my Hc)).
  - apply tapp_fvar_apps_fv_subset.
  - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2) ({[y]} : aset));
      [exact Hclosed_base_prod|exact Hclosed_y_prod].
Qed.

Local Lemma wand_open_result_apps_equiv_total_product_right
    (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y)))
    (res_product n my Hc) ->
  tm_equiv_on (res_product n my Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)) /\
  tm_total_equiv_on (res_product n my Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hye Hclosed_apps.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Heq_base_product :
      tm_equiv_on (res_product n my Hc) e1 e2).
  {
    eapply tm_equiv_res_product_right.
    - eapply tm_equiv_full_world_extend_fresh.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + exact Hscope.
      + exact Hye.
      + exact Hdom.
      + exact Hrestrict.
    - eapply wand_open_world_term_scope; eauto.
  }
  assert (Htotal_base_my : tm_total_equiv_on my e1 e2).
  {
    eapply tm_total_equiv_full_world_extend_fresh.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - exact Hscope.
    - exact Hye.
    - exact Hdom.
    - exact Hrestrict.
  }
  assert (Htotal_base_product :
      tm_total_equiv_on (res_product n my Hc) e1 e2).
  {
    eapply tm_total_equiv_res_product_right.
    - exact Htotal_base_my.
    - exact Hlc1.
    - exact Hlc2.
    - eapply wand_open_world_term_scope; eauto.
  }
  split.
  - eapply tm_equiv_tapp_fvar; eauto.
  - eapply tm_total_equiv_tapp_fvar; eauto.
Qed.

Lemma wand_result_source_world
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ basic_world_formula (relevant_env Σ (CTWand τx τr) e2).
Proof.
  intros Hequiv Hrestrict.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_top_tgt)
    as Hworld_top_tgt.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  eapply res_models_kripke; [exact Hle|exact Hworld_top_tgt].
Qed.

Lemma basic_world_formula_wand_open_result_big
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ basic_world_formula (relevant_env Σ (CTWand τx τr) e2) ->
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
  my ⊨ basic_world_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTWand τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hyτx Hyτr Hye Hworld_src Hworld_y.
  pose proof Hworld_src as Hworld_src_parts.
  apply basic_world_formula_models_iff in Hworld_src_parts as [Hlc_rel [_ _]].
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_tgt)
    as Hwf_top_tgt.
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [_ [_ Hbasic_wand]].
  eapply wand_body_world_from_source_arg.
  - exact Hlc_rel.
  - eapply relevant_env_wand_fresh_free.
    + exact Hyτx.
    + exact Hyτr.
    + set_solver.
  - exact Hbasic_wand.
  - apply tm_lvars_tapp_tm_fvar_without_arg.
  - rewrite relevant_env_idemp. exact Hworld_src.
  - exact Hworld_y.
Qed.

Lemma basic_world_formula_wand_open_result_subenv
    (Σ : lty_env) τx τr e2 y :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  forall v T,
    relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T ->
    relevant_env
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTWand τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T.
Proof.
  intros Hτr_vars v T Hlook.
  change ((lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    : lty_env) !! v = Some T).
  pose proof (wand_body_relevant_env_agree_insert_core
    Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
    Hτr_vars (tm_lvars_tapp_tm_fvar_without_arg e2 y)) as Hagree.
  rewrite Hagree.
  exact Hlook.
Qed.

Lemma basic_world_formula_wand_open_result_target
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  res_product n my Hc ⊨ basic_world_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx y n Harg) as Hworld_arg.
  pose proof (wand_result_source_world
    Σ τx τr e1 e2 m my Hequiv Hrestrict) as Hworld_src_my.
  assert (Hworld_src_prod :
      res_product n my Hc ⊨
        basic_world_formula (relevant_env Σ (CTWand τx τr) e2)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld_src_my]. }
  assert (Hworld_y_prod :
      res_product n my Hc ⊨ basic_world_formula
        ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
  { eapply res_models_kripke; [apply res_product_le_l|exact Hworld_arg]. }
  pose proof (basic_world_formula_wand_open_result_big
    Σ τx τr e1 e2 m (res_product n my Hc) y
    Hequiv Hyτx Hyτr Hye Hworld_src_prod Hworld_y_prod) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  intros v T Hlook.
  eapply basic_world_formula_wand_open_result_subenv.
  apply cty_open_body_lvars_without_fresh_subset.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_tgt)
    as Hwf_top_tgt.
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [Hlc_rel [_ Hbasic_wand]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTWand τx τr) e2))
    (CTWand τx τr) Hlc_rel Hbasic_wand) as Hlc_wand.
  cbn [lc_context_ty cty_lc_at] in Hlc_wand.
  exact (proj2 Hlc_wand).
  exact Hyτr.
  exact Hlook.
Qed.

Lemma wand_result_target_typing
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  res_product n my Hc ⊨ expr_basic_typing_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (basic_world_formula_wand_open_result_target
    gas Σ τx τr e1 e2 m my n y Hc Hequiv Hdom Hrestrict
    Hyτx Hyτr Hye Hres_mid Harg) as Hworld_tgt.
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld_tgt
    as [Hlc_tgt [Hscope_tgt _]].
  split; [exact Hlc_tgt|].
  split; [exact Hscope_tgt|].
  rewrite cty_open_preserves_erasure.
  eapply basic_tm_has_ltype_tapp_tm_lvar.
  - exact Hlc_tgt.
  - eapply (basic_tm_has_ltype_arrow_inserted_result_target_fun
      Σ (CTWand τx τr) τx τr e1 e2 m y); eauto.
  - apply basic_value_has_ltype_arrow_inserted_result_target_arg.
Qed.

Lemma ty_denote_gas_zero_wand_open_result_target
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  res_product n my Hc ⊨ ty_denote_gas 0
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (res_product n my Hc) Hres_mid) as Hguard_res_src.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_res_src)
    as Hwf_res_src.
  pose proof (ty_guard_formula_total _ _ _ _ Hguard_res_src)
    as Htotal_res_src.
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n my Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps.
    - exact Hequiv.
    - exact Hdom.
    - exact Hrestrict.
    - eapply ty_denote_gas_ret_fvar_basic_world_singleton. exact Harg.
  }
  assert (Htotal_tgt :
      res_product n my Hc ⊨ expr_total_formula (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    assert (Htotal_apps :
        tm_total_equiv_on (res_product n my Hc)
          (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
    { eapply wand_open_result_apps_equiv_total_product_right; eauto. }
    eapply tm_equiv_total.
    - exact Htotal_apps.
    - apply lc_tapp_tm; [exact Hlc2|constructor].
    - eapply wand_open_product_tapp_tgt_scope; eauto.
    - exact Htotal_res_src.
  }
  assert (Hworld_tgt :
      res_product n my Hc ⊨ basic_world_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))).
  {
    eapply basic_world_formula_wand_open_result_target; eauto.
  }
  assert (Hwf_tgt :
      res_product n my Hc ⊨ context_ty_wf_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (cty_open 0 y τr)).
  {
    eapply context_ty_wf_formula_relevant_env_change_term.
    - exact Hworld_tgt.
    - exact Hwf_res_src.
  }
  assert (Hbasic_tgt :
      res_product n my Hc ⊨ expr_basic_typing_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr))).
  {
    eapply (wand_result_target_typing
      gas Σ τx τr e1 e2 m my n y Hc); eauto.
  }
  apply ty_denote_gas_zero_of_guard.
  repeat rewrite res_models_and_iff.
  split.
  - exact Hwf_tgt.
  - split.
    + exact Hworld_tgt.
    + split.
      * exact Hbasic_tgt.
      * exact Htotal_tgt.
Qed.

Lemma typed_total_equiv_wand_open_result_mid
    gas (Σ : lty_env) τx τr e1 e2
    (m my n : WfWorldT) y (Hc : world_compat n my) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  res_product n my Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  typed_total_equiv_on
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (res_product n my Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero_top_src) as Hguard_top_src.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_src)
    as Hwf_top_src.
  apply context_ty_wf_formula_models_iff in Hwf_top_src
    as [HΣclosed [_ Hbasic_wand]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTWand τx τr) e1))
    (CTWand τx τr) HΣclosed Hbasic_wand) as Hlc_wand.
  cbn [lc_context_ty cty_lc_at] in Hlc_wand.
  destruct Hlc_wand as [Hτx_lc Hτr_lc].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n my Hc)).
  {
    eapply (wfworld_closed_on_wand_open_result_apps
      Σ τx τr e1 e2 m my n y Hc); eauto.
    eapply ty_denote_gas_ret_fvar_basic_world_singleton. exact Harg.
  }
  split.
  - eapply wand_open_result_apps_equiv_total_product_right; eauto.
  - split.
    + eapply wand_open_result_apps_equiv_total_product_right; eauto.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hres_mid.
      * eapply (ty_denote_gas_zero_wand_open_result_target
        gas Σ τx τr e1 e2 m my n y Hc); eauto.
Qed.

Lemma wfworld_closed_on_wand_open_result_apps_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y)))
    (res_product n m Hc).
Proof.
  intros Hequiv Hyτx Hye HyΣ2 Harg.
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero2) as Hguard2.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard1) as Hworld1.
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard1) as Hbasic1.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard2) as Hworld2.
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard2) as Hbasic2.
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed1 : wfworld_closed_on (fv_tm e1) m).
  {
    eapply relevant_world_typing_closed_on_term.
    - exact Hworld1.
    - exact Hbasic1.
  }
  assert (Hclosed2 : wfworld_closed_on (fv_tm e2) m).
  {
    eapply relevant_world_typing_closed_on_term.
    - exact Hworld2.
    - exact Hbasic2.
  }
  assert (Hclosed_fun :
      wfworld_closed_on (fv_tm e1 ∪ fv_tm e2) (res_product n m Hc)).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. exact Ha.
    - apply res_product_le_r.
    - apply (wfworld_closed_on_union (fv_tm e1) (fv_tm e2));
        [exact Hclosed1|exact Hclosed2].
  }
  assert (Hworld_y :
      n ⊨ basic_world_formula
        ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
  { eapply ty_denote_gas_ret_fvar_basic_world_singleton. exact Harg. }
	  assert (Hy_n : ({[y]} : aset) ⊆ world_dom (n : WorldT)).
	  {
	    apply basic_world_formula_models_iff in Hworld_y as [_ [Hdom_y _]].
	    rewrite dom_insert_L, dom_empty_L in Hdom_y.
	    rewrite lvars_fv_union, lvars_fv_empty,
	      lvars_fv_singleton_free in Hdom_y.
	    intros a Ha. apply Hdom_y.
	    apply elem_of_union_l. exact Ha.
	  }
	  assert (Hclosed_y :
	      wfworld_closed_on ({[y]} : aset) (res_product n m Hc)).
	  {
	    eapply wfworld_closed_on_le.
	    - exact Hy_n.
	    - apply res_product_le_l.
	    - eapply basic_world_formula_singleton_free_closed_on.
	      exact Hworld_y.
	  }
  eapply (wfworld_closed_on_mono _
    ((fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset))).
  - apply tapp_fvar_apps_fv_subset.
  - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2)
      ({[y]} : aset)); [exact Hclosed_fun|exact Hclosed_y].
Qed.

Local Lemma wand_open_result_apps_equiv_total_product
    (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y)))
    (res_product n m Hc) ->
  tm_equiv_on (res_product n m Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)) /\
  tm_total_equiv_on (res_product n m Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hclosed_apps.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Heq_base_product :
      tm_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_equiv_res_product_right.
    - eapply typed_total_equiv_tm_equiv. exact Hequiv.
    - exact Hscope.
  }
  assert (Htotal_base_product :
      tm_total_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_total_equiv_res_product_right.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - exact Hscope.
  }
  split.
  - eapply tm_equiv_tapp_fvar; eauto.
  - eapply tm_total_equiv_tapp_fvar; eauto.
Qed.

Lemma basic_world_formula_wand_open_result_target_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  res_product n m Hc ⊨ basic_world_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ2 Hres_mid Harg.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_top_tgt)
    as Hworld_top_tgt.
  assert (Hworld_src_prod :
      res_product n m Hc ⊨
        basic_world_formula (relevant_env Σ (CTWand τx τr) e2)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld_top_tgt]. }
  assert (Hworld_y_prod :
      res_product n m Hc ⊨ basic_world_formula
        ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
  {
    assert (Hworld_y_n :
        n ⊨ basic_world_formula
          ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
    { eapply ty_denote_gas_ret_fvar_basic_world_singleton. exact Harg. }
    eapply res_models_kripke; [apply res_product_le_l|exact Hworld_y_n].
  }
  pose proof (basic_world_formula_wand_open_result_big
    Σ τx τr e1 e2 m (res_product n m Hc) y
    Hequiv Hyτx Hyτr Hye Hworld_src_prod Hworld_y_prod) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_wand_open_result_subenv; eauto.
  apply cty_open_body_lvars_without_fresh_subset.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt'.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt') as Hguard_top_tgt'.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_tgt')
    as Hwf_top_tgt'.
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt'
    as [Hlc_rel' [_ Hbasic_wand']].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTWand τx τr) e2))
    (CTWand τx τr) Hlc_rel' Hbasic_wand') as Hlc_wand'.
  cbn [lc_context_ty cty_lc_at] in Hlc_wand'.
  exact (proj2 Hlc_wand').
  exact Hyτr.
Qed.

Lemma ty_denote_gas_zero_wand_open_result_target_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  res_product n m Hc ⊨ ty_denote_gas 0
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ2 Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (res_product n m Hc) Hres_mid) as Hguard_res_src.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_res_src)
    as Hwf_res_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_res_src)
    as Hworld_res_src.
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard_res_src)
    as Hbasic_res_src.
  pose proof (ty_guard_formula_total _ _ _ _ Hguard_res_src)
    as Htotal_res_src.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_tgt)
    as Hwf_top_tgt.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_top_tgt)
    as Hworld_top_tgt.
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard_top_tgt)
    as Hbasic_top_tgt.
  pose proof (ty_guard_formula_total _ _ _ _ Hguard_top_tgt)
    as Htotal_top_tgt.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n m Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps_product; eauto.
  }
  assert (Htotal_apps :
      tm_total_equiv_on (res_product n m Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  { eapply wand_open_result_apps_equiv_total_product; eauto. }
	  assert (Htotal_tgt :
	      res_product n m Hc ⊨ expr_total_formula (tapp_tm e2 (vfvar y))).
	  {
	    eapply tm_equiv_total.
    - exact Htotal_apps.
    - apply lc_tapp_tm; [exact Hlc2|constructor].
    - rewrite fv_tapp_tm. cbn [fv_value].
      pose proof (typed_total_equiv_term_scope
        Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
      pose proof (raw_le_dom (n : WorldT)
        (res_product n m Hc : WorldT)
        (res_product_le_l n m Hc)) as Hdom_l.
	      pose proof (raw_le_dom (m : WorldT)
	        (res_product n m Hc : WorldT)
	        (res_product_le_r n m Hc)) as Hdom_r.
		      assert (Hy_prod : y ∈ world_dom (res_product n m Hc : WorldT)).
		      {
		        apply Hdom_l.
		        eapply ty_denote_gas_ret_fvar_world_dom. exact Harg.
		      }
		      intros a Ha.
		      apply elem_of_union in Ha as [Ha|Ha].
		      + apply Hdom_r. apply Hscope.
		        apply elem_of_union_r. exact Ha.
		      + apply elem_of_singleton in Ha. subst a. exact Hy_prod.
		    - exact Htotal_res_src.
		  }
  assert (Hworld_tgt :
      res_product n m Hc ⊨ basic_world_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))).
  {
    eapply basic_world_formula_wand_open_result_target_product; eauto.
  }
  assert (Hwf_tgt :
      res_product n m Hc ⊨ context_ty_wf_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (cty_open 0 y τr)).
  {
    eapply context_ty_wf_formula_relevant_env_change_term.
    - exact Hworld_tgt.
    - exact Hwf_res_src.
  }
  assert (Hbasic_tgt :
      res_product n m Hc ⊨ expr_basic_typing_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr))).
  {
    apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld_tgt
      as [Hlc_tgt [Hscope_tgt _]].
    split; [exact Hlc_tgt|].
    split; [exact Hscope_tgt|].
    rewrite cty_open_preserves_erasure.
    eapply basic_tm_has_ltype_tapp_tm_lvar.
    - exact Hlc_tgt.
    - eapply (basic_tm_has_ltype_arrow_inserted_result_target_fun
        Σ (CTWand τx τr) τx τr e1 e2 m y); eauto.
    - apply basic_value_has_ltype_arrow_inserted_result_target_arg.
  }
  apply ty_denote_gas_zero_of_guard.
  repeat rewrite res_models_and_iff.
  split.
  - exact Hwf_tgt.
  - split.
    + exact Hworld_tgt.
    + split.
      * exact Hbasic_tgt.
      * exact Htotal_tgt.
Qed.

Lemma typed_total_equiv_wand_open_result_mid_product
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx))) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  n ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) ->
  typed_total_equiv_on
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (res_product n m Hc)
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hyτx Hyτr Hye HyΣ2 Hres_mid Harg.
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n m Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps_product; eauto.
  }
  split.
  - eapply wand_open_result_apps_equiv_total_product; eauto.
  - split.
    + eapply wand_open_result_apps_equiv_total_product; eauto.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hres_mid.
      * eapply ty_denote_gas_zero_wand_open_result_target_product; eauto.
Qed.

End TypeDenote.

Section TypeDenote.

Lemma wand_result_first_result_to_regular_open
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  lty_env_closed (relevant_env Σ (CTWand τx τr) e) ->
  LVFree f ∉ dom (relevant_env Σ (CTWand τx τr) e : lty_env) ->
  LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e : lty_env) ->
  f <> y ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e)
            (erase_ty (CTWand τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τr)
        (tapp_tm (tret (vbvar 1)) (vbvar 0)))) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTWand τx τr)]>
        (relevant_env Σ (CTWand τx τr) e)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτr Hffresh Hyfresh Hres.
  rewrite (formula_open_result_first_fun_result_two gas
    (relevant_env Σ (CTWand τx τr) e) τx τr
    (erase_ty (CTWand τx τr)) f y) in Hres.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτr.
  2: exact Hffresh.
  2: exact Hyfresh.
  exact Hres.
Qed.

Lemma wand_result_first_regular_to_result_open
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  lty_env_closed (relevant_env Σ (CTWand τx τr) e) ->
  LVFree f ∉ dom (relevant_env Σ (CTWand τx τr) e : lty_env) ->
  LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e : lty_env) ->
  f <> y ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTWand τx τr)]>
        (relevant_env Σ (CTWand τx τr) e)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e)
            (erase_ty (CTWand τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τr)
        (tapp_tm (tret (vbvar 1)) (vbvar 0)))).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτr Hffresh Hyfresh Hres.
  rewrite (formula_open_result_first_fun_result_two gas
    (relevant_env Σ (CTWand τx τr) e) τx τr
    (erase_ty (CTWand τx τr)) f y).
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτr.
  2: exact Hffresh.
  2: exact Hyfresh.
  exact Hres.
Qed.

Local Lemma wand_result_body_relevant_subset τx τr e f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  (context_ty_lvars (cty_open 0 y τr) ∪
    tm_lvars (tapp_tm (tret (vfvar f)) (vfvar y))) ∖
    {[LVFree y]} ∖ {[LVFree f]} ⊆
  context_ty_lvars (CTWand τx τr) ∪ tm_lvars e.
Proof.
  intros Hlcτr Hffresh Hyfresh.
  eapply result_first_result_body_relevant_subset; [exact Hlcτr| |].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - intros Hy. apply Hyfresh. apply elem_of_union_r. exact Hy.
Qed.

Lemma wand_result_first_result_env_agree
    gas (Σ : lty_env) τx τr e1 e2
    (my : WfWorldT) f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTWand τx τr)]>
        (relevant_env Σ (CTWand τx τr) e1)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTWand τx τr)]>
        (relevant_env Σ (CTWand τx τr) e2)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)).
Proof.
  intros Hlcτr Hffresh Hyfresh Hres.
  eapply result_first_result_env_agree_general.
  - eapply wand_result_body_relevant_subset; eauto.
  - eapply wand_result_body_relevant_subset; eauto.
  - exact Hres.
Qed.

Lemma ty_denote_gas_tm_equiv_wand_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e1)
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e2)
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
	        (tret (vbvar 0)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_src.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_tgt) as Hguard_tgt.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_src) as Hwf_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src)
    as Hworld_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_tgt)
    as Hworld_tgt.
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_arrow_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTWand τx τr) e1)) _
    HlcΣ_wf_src Hbasic_arrow_src) as Hlc_arrow.
  cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
  destruct Hlc_arrow as [Hlcτx Hlcτr].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas)
    Σ (CTWand τx τr) e2 m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  assert (Hfib :
      tm_fiber_equiv_on m (lvars_fv (context_ty_lvars (CTWand τx τr)))
        e1 e2).
  {
    apply tm_equiv_on_to_fiber_equiv.
    eapply typed_total_equiv_tm_equiv. exact Hequiv.
  }
  pose proof (tm_fiber_equiv_to_projected_on
    Σ (CTWand τx τr) m (context_ty_lvars (CTWand τx τr))
    e1 e2 Hfib Hzero_src Hzero_tgt) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTWand τx τr) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTWand τx τr) e2)) ∪
    lvars_fv (context_ty_lvars (CTWand τx τr)) ∪
    fv_cty τx ∪ fv_cty τr).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTWand τx τr))).
  { clear -Hf. set_solver. }
  assert (Hf_src : f ∉ Lsrc).
  { clear -Hf. set_solver. }
  assert (Hfτx : f ∉ fv_cty τx).
  { clear -Hf. set_solver. }
  assert (Hfτr : f ∉ fv_cty τr).
  { clear -Hf. set_solver. }
  assert (Hfe : f ∉ fv_tm e1 ∪ fv_tm e2).
  { clear -Hf. set_solver. }
  assert (HfΣ1 :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx)))).
  {
    clear -Hf.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    set_solver.
  }
  assert (HfΣ2 :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))).
  {
    clear -Hf.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    set_solver.
  }
  pose proof (formula_scoped_forall_open_res_le m mf f
    (FImpl
      (expr_result_formula_at
        (lvars_shift_from 0
          (dom (relevant_env Σ (CTWand τx τr) e2)))
        (tm_shift 0 e2) (LVBound 0))
      (wand_value_denote_gas_with ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e2)
          (erase_ty (CTWand τx τr)))
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0))))
    Hscope_tgt
    ltac:(rewrite <- Hrestrict; apply res_restrict_le)
    ltac:(rewrite Hdom; clear; set_solver)) as Hopened_scope.
  rewrite formula_open_impl.
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (first
      [ exact Hlc2
      | apply result_first_lc_lvars_shift_from; exact HlcΣ_tgt
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hfe; set_solver ]).
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTWand τx τr) e2)) HlcΣ_tgt) in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTWand τx τr) e2 m Hzero_tgt) in Hres_tgt.
  destruct (H21 f mf Hf_proj Hdom Hrestrict Hres_tgt)
    as [mf_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev f Hf_src mf_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (first
      [ exact Hlc1
      | apply result_first_lc_lvars_shift_from; exact HlcΣ_src
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hfe; set_solver ]).
  rewrite (result_first_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTWand τx τr) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTWand τx τr) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hequiv_src :
      typed_total_equiv_on Σ (CTWand τx τr) mf_src e1 e2).
  {
    split.
    - eapply tm_equiv_full_world_extend_fresh.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + eapply typed_total_equiv_term_scope. exact Hequiv.
      + exact Hfe.
      + exact Hdom_src.
      + exact Hrestrict_src.
    - split.
      + eapply tm_total_equiv_full_world_extend_fresh.
        * eapply typed_total_equiv_total_equiv. exact Hequiv.
        * exact Hlc1.
        * exact Hlc2.
        * eapply typed_total_equiv_term_scope. exact Hequiv.
        * exact Hfe.
        * exact Hdom_src.
        * exact Hrestrict_src.
	      + split.
        * eapply (res_models_kripke m mf_src).
          -- change (m ⊑ mf_src).
             rewrite <- Hrestrict_src. apply res_restrict_le.
          -- exact Hzero_src.
        * eapply (res_models_kripke m mf_src).
          -- change (m ⊑ mf_src).
             rewrite <- Hrestrict_src. apply res_restrict_le.
          -- exact Hzero_tgt.
  }
  assert (Hvalue_tgt_src :
      mf_src ⊨ formula_open 0 f
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e2)
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
  {
    pose proof (formula_scoped_open_wand_value_body_obs
      gas (typed_lty_env_bind (relevant_env Σ (CTWand τx τr) e2)
        (erase_ty (CTWand τx τr)))
      τx τr f mf_src) as Hvalue_tgt_scope_src.
    specialize (Hvalue_tgt_scope_src ltac:(
      pose proof (ty_denote_gas_zero_type_fv_world
        Σ (CTWand τx τr) e1 m Hzero_src) as Hτworld;
      rewrite Hdom_src;
      intros a Ha;
      apply elem_of_union in Ha as [Ha|Ha];
      [ apply elem_of_union_l; exact (Hτworld a Ha)
      | apply elem_of_union_r; exact Ha ])).
    cbn [formula_open wand_value_denote_gas_with] in Hvalue_src |- *.
    cbn [formula_open wand_value_denote_gas_with] in Hvalue_tgt_scope_src.
    eapply res_models_fbwand_intro.
    - exact Hvalue_tgt_scope_src.
    - destruct (res_models_fbwand_rev _ _ _ _ Hvalue_src)
        as [Lwand Hwand_src].
      exists (Lwand ∪ world_dom (mf_src : WorldT) ∪ world_dom (mf : WorldT) ∪
        fv_cty τx ∪ fv_cty τr ∪ fv_tm e1 ∪ fv_tm e2 ∪
        lvars_fv (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx))) ∪
        lvars_fv (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))).
      intros η n Hc Hbind Hηfresh Hdom_prod Harg_tgt.
      destruct (open_env_binds_one_inv η Hbind) as [a ->].
      rewrite formula_open_env_singleton in Harg_tgt |- *.
      rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
      rewrite open_env_atoms_empty in Hηfresh.
      rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
      rewrite open_env_atoms_empty in Hdom_prod.
      assert (Hyτx : a ∉ fv_cty τx).
      { clear -Hηfresh. set_solver. }
      assert (Hyτr : a ∉ fv_cty τr).
      { clear -Hηfresh. set_solver. }
      assert (Hye : a ∉ fv_tm e1 ∪ fv_tm e2).
      { clear -Hηfresh. set_solver. }
      assert (HyΣ1 : a ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e1) (erase_ty τx)))).
      { clear -Hηfresh. set_solver. }
      assert (HyΣ2 : a ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e2) (erase_ty τx)))).
      { clear -Hηfresh. set_solver. }
      assert (Hfy : f <> a).
      {
        intros ->.
        rewrite elem_of_disjoint in Hηfresh.
        assert (Ha : a ∈ ({[a]} ∪ ∅ : aset)).
        {
          apply elem_of_union_l.
          rewrite elem_of_singleton.
          reflexivity.
        }
        specialize (Hηfresh a Ha).
        apply Hηfresh.
        clear -Hdom_src.
        rewrite Hdom_src.
        set_solver.
      }
      assert (Hf_rel2 :
          LVFree f ∉ dom (relevant_env Σ (CTWand τx τr) e2 : lty_env)).
      {
        intros Hbad. apply HfΣ2.
        apply lvars_fv_elem.
        rewrite typed_lty_env_bind_dom.
        rewrite (result_first_lvars_shift_from_lc_eq 0
          (dom (relevant_env Σ (CTWand τx τr) e2)) HlcΣ_tgt).
        apply elem_of_union_l. exact Hbad.
      }
      assert (Hy_rel2 :
          LVFree a ∉ dom (relevant_env Σ (CTWand τx τr) e2 : lty_env)).
      {
        intros Hbad. apply HyΣ2.
        apply lvars_fv_elem.
        rewrite typed_lty_env_bind_dom.
        rewrite (result_first_lvars_shift_from_lc_eq 0
          (dom (relevant_env Σ (CTWand τx τr) e2)) HlcΣ_tgt).
        apply elem_of_union_l. exact Hbad.
      }
	      assert (Harg_tgt_open :
		          n ⊨ ty_denote_gas gas
		            (<[LVFree a := erase_ty τx]>
		              (relevant_env Σ (CTWand τx τr) e2))
		            τx (tret (vfvar a))).
	      {
	        eapply result_first_fun_arg_open_to_inserted_env.
	        - exact HlcΣ_tgt.
	        - exact Hf_rel2.
	        - exact Hy_rel2.
	        - exact Hfy.
	        - exact Hlcτx.
	        - exact Hfτx.
	        - exact Hyτx.
	        - exact Harg_tgt.
	      }
	      assert (Hf_rel1 :
	          LVFree f ∉ dom (relevant_env Σ (CTWand τx τr) e1 : lty_env)).
	      {
	        intros Hbad. apply HfΣ1.
	        apply lvars_fv_elem.
	        rewrite typed_lty_env_bind_dom.
	        rewrite (result_first_lvars_shift_from_lc_eq 0
	          (dom (relevant_env Σ (CTWand τx τr) e1)) HlcΣ_src).
	        apply elem_of_union_l. exact Hbad.
	      }
	      assert (Hy_rel1 :
	          LVFree a ∉ dom (relevant_env Σ (CTWand τx τr) e1 : lty_env)).
	      {
	        intros Hbad. apply HyΣ1.
	        apply lvars_fv_elem.
	        rewrite typed_lty_env_bind_dom.
	        rewrite (result_first_lvars_shift_from_lc_eq 0
	          (dom (relevant_env Σ (CTWand τx τr) e1)) HlcΣ_src).
	        apply elem_of_union_l. exact Hbad.
	      }
		      pose proof (@ty_denote_gas_tm_equiv_wand_open_arg_fbwand
		        gas Σ τx τr e1 e2 n a
		        Harg_tgt_open) as Harg_src.
	      pose proof (Hwand_src _ n Hc Hbind
	        ltac:(rewrite open_env_atoms_insert by apply lookup_empty;
	              rewrite open_env_atoms_empty;
	              clear -Hηfresh; set_solver)
	        Hdom_prod
	        ltac:(eapply result_first_fun_arg_inserted_env_to_open;
	          [ exact HlcΣ_src
	          | exact Hf_rel1
	          | exact Hy_rel1
	          | exact Hfy
	          | exact Hlcτx
	          | exact Hfτx
	          | exact Hyτx
	          | exact Harg_src ])) as Hres_src_inner.
      assert (Hres_src_regular :
          res_product n mf_src Hc ⊨ ty_denote_gas gas
            (<[LVFree a := erase_ty τx]>
              (<[LVFree f := erase_ty (CTWand τx τr)]>
                (relevant_env Σ (CTWand τx τr) e1)))
            (cty_open 0 a τr)
            (tapp_tm (tret (vfvar f)) (vfvar a))).
      {
        eapply wand_result_first_result_to_regular_open.
        - exact HlcΣ_src.
        - exact Hf_rel1.
        - exact Hy_rel1.
        - exact Hfy.
        - exact Hlcτr.
        - intros Hin.
          apply elem_of_union in Hin as [Hin|Hin].
          + exact (Hfτx Hin).
          + exact (Hfτr Hin).
        - intros Hin.
          apply elem_of_union in Hin as [Hin|Hin].
          + exact (Hyτx Hin).
          + exact (Hyτr Hin).
        - exact Hres_src_inner.
      }
      assert (Hres_tgt_regular :
          res_product n mf_src Hc ⊨ ty_denote_gas gas
            (<[LVFree a := erase_ty τx]>
              (<[LVFree f := erase_ty (CTWand τx τr)]>
                (relevant_env Σ (CTWand τx τr) e2)))
            (cty_open 0 a τr)
            (tapp_tm (tret (vfvar f)) (vfvar a))).
      {
	        eapply wand_result_first_result_env_agree.
	        - exact Hlcτr.
	        - intros Hin.
	          apply elem_of_union in Hin as [Hin|Hin].
	          + exact (Hfτx Hin).
          + exact (Hfτr Hin).
        - intros Hin.
          apply elem_of_union in Hin as [Hin|Hin].
          + exact (Hyτx Hin).
          + exact (Hyτr Hin).
        - exact Hres_src_regular.
      }
	      eapply wand_result_first_regular_to_result_open;
	        [ exact HlcΣ_tgt
	        | exact Hf_rel2
	        | exact Hy_rel2
	        | exact Hfy
	        | exact Hlcτr
	        | intros Hin;
	          apply elem_of_union in Hin as [Hin|Hin];
	          [ exact (Hfτx Hin) | exact (Hfτr Hin) ]
	        | intros Hin;
	          apply elem_of_union in Hin as [Hin|Hin];
	          [ exact (Hyτx Hin) | exact (Hyτr Hin) ]
	        | exact Hres_tgt_regular ].
		  }
	  eapply res_models_projection; [|exact Hvalue_tgt_src].
	  eapply res_restrict_eq_subset; [|exact Hproj_obs].
	  etransitivity; [apply formula_open_fv_subset|].
	  unfold formula_fv, formula_lvars, wand_value_denote_gas_with.
	  cbn [formula_lvars_at].
	  rewrite lvars_fv_union.
	  pose proof (ty_denote_gas_lvars_subset gas 1
	    (typed_lty_env_bind
	      (typed_lty_env_bind
	        (relevant_env Σ (CTWand τx τr) e2)
	        (erase_ty (CTWand τx τr)))
	      (erase_ty (cty_shift 0 τx)))
	    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg_fv.
	  pose proof (ty_denote_gas_lvars_subset gas 1
	    (typed_lty_env_bind
	      (typed_lty_env_bind
	        (relevant_env Σ (CTWand τx τr) e2)
	        (erase_ty (CTWand τx τr)))
	      (erase_ty (cty_shift 0 τx)))
	    (cty_shift 1 τr)
	    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))) as Hres_fv.
	  apply lvars_fv_mono in Harg_fv.
	  apply lvars_fv_mono in Hres_fv.
	  rewrite !lvars_fv_union in Harg_fv, Hres_fv.
	  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg_fv, Hres_fv.
	  rewrite !cty_shift_fv in Harg_fv, Hres_fv.
	  rewrite fv_tapp_tm, tm_shift_fv in Hres_fv.
	  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at]
	    in Harg_fv, Hres_fv |- *.
	  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
	  intros a Ha.
	  repeat rewrite elem_of_union in Ha.
	  repeat rewrite elem_of_union.
	  destruct Ha as [[Ha_arg | Ha_res] | Ha_f].
	  - specialize (Harg_fv a Ha_arg). rewrite cty_shift_fv in Harg_fv.
	    clear -Harg_fv. set_solver.
	  - specialize (Hres_fv a Ha_res). try rewrite cty_shift_fv in Hres_fv.
	    clear -Hres_fv. set_solver.
	  - clear -Ha_f. set_solver.
Qed.

End TypeDenote.
