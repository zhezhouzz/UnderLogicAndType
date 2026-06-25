(** * Denotation.TypeEquivWand

    Wand case for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivTermApp
  TypeEquivBody
  TypeEquivArrow.

Section TypeDenote.

Local Ltac wand_union_member :=
  first
    [ assumption
    | apply elem_of_union_l; wand_union_member
    | apply elem_of_union_r; wand_union_member ].

Local Ltac wand_fresh_from_disjoint Hfresh :=
  intros Hy;
  eapply Hfresh;
    [ apply elem_of_union_l; apply elem_of_singleton; reflexivity
    | subst; wand_union_member ].

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

Local Lemma wand_tapp_apps_fv_subset e1 e2 y :
  fv_tm (tapp_tm e1 (vfvar y)) ∪
  fv_tm (tapp_tm e2 (vfvar y)) ⊆
  (fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset).
Proof.
  intros a Ha.
  apply elem_of_union in Ha as [Ha|Ha];
    rewrite fv_tapp_tm in Ha; cbn [fv_value] in Ha;
    apply elem_of_union in Ha as [Ha|Ha].
  - apply elem_of_union_l. apply elem_of_union_l. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  - apply elem_of_union_l. apply elem_of_union_r. exact Ha.
  - apply elem_of_singleton in Ha. subst a.
    apply elem_of_union_r. apply elem_of_singleton. reflexivity.
Qed.

Local Lemma wand_result_open_vars_subset τr y :
  cty_lc_at 1 τr ->
  y ∉ fv_cty τr ->
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr.
Proof.
  intros Hlc Hy.
  eapply cty_lvars_open_body_closed_no_fresh.
  - apply lc_lvars_no_bv.
    apply cty_lc_at_lvars_bv_empty. exact Hlc.
  - intros HyD. apply Hy.
    rewrite <- (context_ty_lvars_fv_at 1 τr).
    apply lvars_fv_elem. exact HyD.
  - reflexivity.
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
  lc_tm e1 ->
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
  intros Hlc Hyτr Hτr_vars Hsrc.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - apply wand_body_relevant_env_agree_insert_core.
    + exact Hτr_vars.
    + apply tm_lvars_tapp_tm_fvar_without_arg.
  - exact Hsrc.
Qed.

Lemma ty_equiv_wand_result_src_mid_inserted
    gas (Σ : lty_env) τx τr e1
    (m : WfWorldT) y :
  lc_tm e1 ->
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
  intros Hlc Hyτr Hτr_vars Hsrc.
  eapply ty_equiv_wand_result_src_mid; eauto.
Qed.

Lemma ty_equiv_wand_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (m : WfWorldT) y :
  lc_tm e2 ->
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
  intros Hlc Hyτr Hτr_vars Hmid.
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
  my ⊨ basic_world_formula
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
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [_ [Hworld2 [Hbasic2 _]]].
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
	  assert (Hclosed_y : wfworld_closed_on ({[y]} : aset) my).
	  { eapply basic_world_formula_singleton_free_closed_on. exact Hworld. }
  assert (Hclosed_my :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) my).
  {
    eapply (wfworld_closed_on_mono _
      ((fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset)) my).
    - apply wand_tapp_apps_fv_subset.
    - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2) ({[y]} : aset)).
      + apply (wfworld_closed_on_union (fv_tm e1) (fv_tm e2));
          [exact Hclosed1|exact Hclosed2].
      + exact Hclosed_y.
  }
  eapply wfworld_closed_on_le.
  - eapply wand_open_world_tapp_apps_scope; eauto.
  - apply res_product_le_r.
  - exact Hclosed_my.
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
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [_ [Hworld_top_tgt _]].
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
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [Hwf_top_tgt _].
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
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) y :
  typed_total_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
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
  intros _ _ _ _ Hτr_vars v T Hlook.
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
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
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
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (wand_result_source_world
    Σ τx τr e1 e2 m my Hequiv Hrestrict) as Hworld_src_my.
  assert (Hworld_src_prod :
      res_product n my Hc ⊨
        basic_world_formula (relevant_env Σ (CTWand τx τr) e2)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld_src_my]. }
  assert (Hworld_y_prod :
      res_product n my Hc ⊨ basic_world_formula
        ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)).
  { eapply res_models_kripke; [apply res_product_le_r|exact Hworld]. }
  pose proof (basic_world_formula_wand_open_result_big
    Σ τx τr e1 e2 m (res_product n my Hc) y
    Hequiv Hyτx Hyτr Hye Hworld_src_prod Hworld_y_prod) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_wand_open_result_subenv; eauto.
  apply wand_result_open_vars_subset.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [Hwf_top_tgt _].
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [Hlc_rel [_ Hbasic_wand]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTWand τx τr) e2))
    (CTWand τx τr) Hlc_rel Hbasic_wand) as Hlc_wand.
  cbn [lc_context_ty cty_lc_at] in Hlc_wand.
  exact (proj2 Hlc_wand).
  exact Hyτr.
Qed.

Local Lemma basic_value_has_ltype_wand_inserted_result_target_arg
    (Σ : lty_env) τx τr e y :
  basic_value_has_ltype
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e (vfvar y)))
    (vfvar y) (erase_ty τx).
Proof.
  apply basic_value_has_ltype_arrow_inserted_result_target_arg.
Qed.

Local Lemma basic_tm_has_ltype_wand_inserted_result_target_fun
    (Σ : lty_env) τtop τx τr e1 e2
    (m : WfWorldT) y :
  erase_ty τtop = erase_ty τx →ₜ erase_ty τr ->
  typed_total_equiv_on Σ τtop m e1 e2 ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  basic_tm_has_ltype
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    e2 (erase_ty τx →ₜ erase_ty τr).
Proof.
  apply basic_tm_has_ltype_arrow_inserted_result_target_fun.
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
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
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
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (basic_world_formula_wand_open_result_target
    gas Σ τx τr e1 e2 m my n y Hc Hequiv Hdom Hrestrict
    Hyτx Hyτr Hye Hworld Hres_mid Harg) as Hworld_tgt.
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld_tgt
    as [Hlc_tgt [Hscope_tgt _]].
  split; [exact Hlc_tgt|].
  split; [exact Hscope_tgt|].
  rewrite cty_open_preserves_erasure.
  eapply basic_tm_has_ltype_tapp_tm_lvar.
  - exact Hlc_tgt.
  - eapply (basic_tm_has_ltype_wand_inserted_result_target_fun
      Σ (CTWand τx τr) τx τr e1 e2 m y); eauto.
  - apply basic_value_has_ltype_wand_inserted_result_target_arg.
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
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
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
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (res_product n my Hc) Hres_mid) as Hguard_res_src.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTWand τx τr) e2))
    τx (tret (vfvar y)) n Harg)
    as Hguard_arg.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_res_src.
  repeat rewrite res_models_and_iff in Hguard_arg.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_res_src as [Hwf_res_src [Hworld_res_src
    [Hbasic_res_src Htotal_res_src]]].
  destruct Hguard_arg as [Hwf_arg [Hworld_arg [Hbasic_arg Htotal_arg]]].
  destruct Hguard_top_tgt as [Hwf_top_tgt [Hworld_top_tgt
    [Hbasic_top_tgt Htotal_top_tgt]]].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n my Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps; eauto.
  }
  assert (Heq_apps :
      tm_equiv_on (res_product n my Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    eapply tm_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - eapply tm_equiv_res_product_right.
      + pose proof (typed_total_equiv_term_scope
          Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
        destruct Hequiv as [Heq_base _].
        eapply tm_equiv_full_world_extend_fresh.
        * exact Heq_base.
        * exact Hscope.
        * exact Hye.
        * exact Hdom.
        * exact Hrestrict.
      + pose proof (typed_total_equiv_term_scope
          Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
        eapply wand_open_world_term_scope; eauto.
  }
  assert (Htotal_tgt :
      res_product n my Hc ⊨ expr_total_formula (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    pose proof (typed_total_equiv_term_scope
      Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
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
    assert (Htotal_apps :
        tm_total_equiv_on (res_product n my Hc)
          (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
    {
      eapply tm_total_equiv_tapp_fvar.
      - exact Hclosed_apps.
      - exact Hlc1.
      - exact Hlc2.
      - exact Heq_base_product.
      - exact Htotal_base_product.
    }
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
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
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
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_total_equiv_source_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e1 m Hzero_top_src) as Hguard_top_src.
  repeat rewrite res_models_and_iff in Hguard_top_src.
  destruct Hguard_top_src as [Hwf_top_src _].
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
  }
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
  - eapply tm_equiv_tapp_fvar.
    + exact Hclosed_apps.
    + exact Hlc1.
    + exact Hlc2.
    + exact Heq_base_product.
  - split.
    + eapply tm_total_equiv_tapp_fvar.
      * exact Hclosed_apps.
      * exact Hlc1.
      * exact Hlc2.
      * exact Heq_base_product.
      * exact Htotal_base_product.
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
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [_ [Hworld2 [Hbasic2 _]]].
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
  {
    pose proof (ty_denote_gas_guard gas
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTWand τx τr) e2))
      τx (tret (vfvar y)) n Harg) as Hguard_arg.
    repeat rewrite res_models_and_iff in Hguard_arg.
    destruct Hguard_arg as [_ [Hworld_arg _]].
    eapply (basic_world_formula_subenv
      ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)
      (relevant_env
        (<[LVFree y := erase_ty τx]>
          (relevant_env Σ (CTWand τx τr) e2))
        τx (tret (vfvar y))) n).
    - intros v T Hlook.
      rewrite lookup_insert_Some in Hlook.
      destruct Hlook as [[<- <-]|[Hne Hlook]].
      + unfold relevant_env, lty_env_restrict_lvars.
        change ((storeA_restrict
          (<[LVFree y := erase_ty τx]>
            (relevant_env Σ (CTWand τx τr) e2))
          (relevant_lvars τx (tret (vfvar y))) : lty_env) !!
          LVFree y = Some (erase_ty τx)).
        apply storeA_restrict_lookup_some_2.
        * rewrite lookup_insert_eq. reflexivity.
        * unfold relevant_lvars.
          cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
          set_solver.
      + rewrite lookup_empty in Hlook. congruence.
    - exact Hworld_arg.
  }
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
  - apply wand_tapp_apps_fv_subset.
  - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2)
      ({[y]} : aset)); [exact Hclosed_fun|exact Hclosed_y].
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
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [_ [Hworld_top_tgt _]].
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
    {
    pose proof (ty_denote_gas_guard gas
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTWand τx τr) e2))
      τx (tret (vfvar y)) n Harg) as Hguard_arg.
    repeat rewrite res_models_and_iff in Hguard_arg.
    destruct Hguard_arg as [_ [Hworld_arg _]].
    eapply (basic_world_formula_subenv
      ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env)
      (relevant_env
        (<[LVFree y := erase_ty τx]>
          (relevant_env Σ (CTWand τx τr) e2))
        τx (tret (vfvar y))) n).
    - intros v T Hlook.
      rewrite lookup_insert_Some in Hlook.
      destruct Hlook as [[<- <-]|[Hne Hlook]].
      + unfold relevant_env, lty_env_restrict_lvars.
        change ((storeA_restrict
          (<[LVFree y := erase_ty τx]>
            (relevant_env Σ (CTWand τx τr) e2))
          (relevant_lvars τx (tret (vfvar y))) : lty_env) !!
          LVFree y = Some (erase_ty τx)).
        apply storeA_restrict_lookup_some_2.
        * rewrite lookup_insert_eq. reflexivity.
        * unfold relevant_lvars.
          cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
          set_solver.
      + rewrite lookup_empty in Hlook. congruence.
    - exact Hworld_arg.
    }
    eapply res_models_kripke; [apply res_product_le_l|exact Hworld_y_n].
  }
  pose proof (basic_world_formula_wand_open_result_big
    Σ τx τr e1 e2 m (res_product n m Hc) y
    Hequiv Hyτx Hyτr Hye Hworld_src_prod Hworld_y_prod) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_wand_open_result_subenv; eauto.
  apply wand_result_open_vars_subset.
  pose proof (typed_total_equiv_target_zero
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hzero_top_tgt'.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e2 m Hzero_top_tgt') as Hguard_top_tgt'.
  repeat rewrite res_models_and_iff in Hguard_top_tgt'.
  destruct Hguard_top_tgt' as [Hwf_top_tgt' _].
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
  repeat rewrite res_models_and_iff in Hguard_res_src.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_res_src as [Hwf_res_src [Hworld_res_src
    [Hbasic_res_src Htotal_res_src]]].
  destruct Hguard_top_tgt as [Hwf_top_tgt [Hworld_top_tgt
    [Hbasic_top_tgt Htotal_top_tgt]]].
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
  assert (Heq_apps :
      tm_equiv_on (res_product n m Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    eapply tm_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - eapply tm_equiv_res_product_right.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + eapply typed_total_equiv_term_scope. exact Hequiv.
  }
  assert (Htotal_base_product :
      tm_total_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_total_equiv_res_product_right.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - eapply typed_total_equiv_term_scope. exact Hequiv.
  }
  assert (Heq_base_product :
      tm_equiv_on (res_product n m Hc) e1 e2).
  {
    eapply tm_equiv_res_product_right.
    - eapply typed_total_equiv_tm_equiv. exact Hequiv.
    - eapply typed_total_equiv_term_scope. exact Hequiv.
  }
  assert (Htotal_apps :
      tm_total_equiv_on (res_product n m Hc)
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    eapply tm_total_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - exact Heq_base_product.
    - exact Htotal_base_product.
  }
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
	        pose proof (ty_denote_gas_guard gas
	          (<[LVFree y := erase_ty τx]>
	            (relevant_env Σ (CTWand τx τr) e2))
	          τx (tret (vfvar y)) n Harg) as Hguard_arg_for_y.
	        repeat rewrite res_models_and_iff in Hguard_arg_for_y.
	        destruct Hguard_arg_for_y as [_ [Hworld_arg_for_y _]].
	        assert (Hworld_y :
	            n ⊨ basic_world_formula
	              ((<[LVFree y := erase_ty τx]>
	                (∅ : gmap logic_var ty)) : lty_env)).
	        {
		          eapply (basic_world_formula_subenv
		            ((<[LVFree y := erase_ty τx]>
		              (∅ : gmap logic_var ty)) : lty_env)
		            (relevant_env
		              (<[LVFree y := erase_ty τx]>
		                (relevant_env Σ (CTWand τx τr) e2))
		              τx (tret (vfvar y))) n).
		          - intros v T Hlook.
		            rewrite lookup_insert_Some in Hlook.
		            destruct Hlook as [[<- <-]|[Hne Hlook]].
		            + unfold relevant_env, lty_env_restrict_lvars.
		              change ((storeA_restrict
		                (<[LVFree y := erase_ty τx]>
		                  (relevant_env Σ (CTWand τx τr) e2))
		                (relevant_lvars τx (tret (vfvar y))) : lty_env) !!
		                LVFree y = Some (erase_ty τx)).
		              apply storeA_restrict_lookup_some_2.
		              * rewrite lookup_insert_eq. reflexivity.
			              * unfold relevant_lvars.
		                cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
		                set_solver.
		            + rewrite lookup_empty in Hlook. congruence.
		          - exact Hworld_arg_for_y.
	        }
		        apply basic_world_formula_models_iff in Hworld_y
		          as [_ [Hdom_y _]].
		        rewrite dom_insert_L, dom_empty_L in Hdom_y.
		        rewrite lvars_fv_union, lvars_fv_empty,
		          lvars_fv_singleton_free in Hdom_y.
		        apply Hdom_y.
		        apply elem_of_union_l. apply elem_of_singleton. reflexivity.
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
    - eapply (basic_tm_has_ltype_wand_inserted_result_target_fun
        Σ (CTWand τx τr) τx τr e1 e2 m y); eauto.
    - apply basic_value_has_ltype_wand_inserted_result_target_arg.
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
  pose proof (typed_total_equiv_term_lc
    Σ (CTWand τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_total_equiv_term_scope
    Σ (CTWand τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y)))
        (res_product n m Hc)).
  {
    eapply wfworld_closed_on_wand_open_result_apps_product; eauto.
  }
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
  - eapply tm_equiv_tapp_fvar.
    + exact Hclosed_apps.
    + exact Hlc1.
    + exact Hlc2.
    + exact Heq_base_product.
  - split.
    + eapply tm_total_equiv_tapp_fvar.
      * exact Hclosed_apps.
      * exact Hlc1.
      * exact Hlc2.
      * exact Heq_base_product.
      * exact Htotal_base_product.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hres_mid.
      * eapply ty_denote_gas_zero_wand_open_result_target_product; eauto.
Qed.

End TypeDenote.
