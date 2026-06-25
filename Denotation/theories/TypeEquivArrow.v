(** * Denotation.TypeEquivArrow

    Arrow case for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivTermApp
  TypeEquivBody.

Section TypeDenote.

Lemma arrow_open_arg_to_inserted_env
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros Harg.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - apply arrow_arg_relevant_env_agree_insert_core.
  - exact Harg.
Qed.

Lemma ty_denote_gas_tm_equiv_arrow_open_arg
    gas (Σ : lty_env) τx τr e1 e2
    (my : WfWorldT) y :
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    τx (tret (vfvar y)).
Proof.
  intros Htgt.
  pose proof (arrow_open_arg_to_inserted_env
    gas Σ τx τr e2 my y Htgt) as Hmid.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - symmetry. apply arrow_arg_relevant_env_agree_insert_core.
  - exact Hmid.
Qed.

Lemma arrow_result_open_vars_subset τr y :
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

Lemma ty_equiv_arrow_result_src_mid
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hlc Hyτr Hτr_vars Hsrc.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - apply arrow_body_relevant_env_agree.
    + exact Hτr_vars.
    + apply tm_lvars_tapp_tm_fvar_without_arg.
  - exact Hsrc.
Qed.

Lemma ty_equiv_arrow_result_src_mid_inserted
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  lc_tm e1 ->
  cty_lc_at 1 τr ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hlc Hlcτr Hyτr Hsrc.
  eapply ty_equiv_arrow_result_src_mid; eauto.
  apply arrow_result_open_vars_subset; assumption.
Qed.

Lemma ty_equiv_arrow_result_src_mid_current
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  Σ !! LVFree y = Some (erase_ty τx) ->
  lc_tm e1 ->
  cty_lc_at 1 τr ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    Σ (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros HyΣ Hlc Hlcτr Hyτr Hsrc.
  pose proof (ty_equiv_arrow_result_src_mid
    gas Σ τx τr e1 my y Hlc Hyτr
    (arrow_result_open_vars_subset τr y Hlcτr Hyτr) Hsrc) as Hmid.
  eapply (res_models_ty_denote_gas_env_agree_on gas
    (<[LVFree y := erase_ty τx]> Σ) Σ
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e1 (vfvar y))) my).
  - reflexivity.
  - rewrite (insert_id Σ (LVFree y) (erase_ty τx)) by exact HyΣ.
    reflexivity.
  - exact Hmid.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (my : WfWorldT) y :
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hyτr Hτr_vars Hmid.
  eapply res_models_ty_denote_gas_env_agree_on.
  - reflexivity.
  - symmetry. apply arrow_body_relevant_env_agree.
    + exact Hτr_vars.
    + apply tm_lvars_tapp_tm_fvar_without_arg.
  - exact Hmid.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal_inserted
    gas (Σ : lty_env) τx τr e2
    (my : WfWorldT) y :
  lc_tm e2 ->
  cty_lc_at 1 τr ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hlcτr Hyτr Hmid.
  eapply ty_equiv_arrow_result_tgt_goal; eauto.
  apply arrow_result_open_vars_subset; assumption.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal_inserted_lc
    gas (Σ : lty_env) τx τr e2
  (my : WfWorldT) y :
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  cty_lc_at 1 τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hyτr Hlcτr Hmid.
  eapply ty_equiv_arrow_result_tgt_goal; eauto.
  apply arrow_result_open_vars_subset; assumption.
Qed.

Lemma wfworld_closed_on_arrow_open_result_apps
    (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
  wfworld_closed_on
    (fv_tm (tapp_tm e1 (vfvar y)) ∪
     fv_tm (tapp_tm e2 (vfvar y))) my.
Proof.
  intros Hequiv Hdom Hrestrict Hworld.
  pose proof (typed_total_equiv_source_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero1.
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero2) as Hguard2.
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
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hscope.
  assert (Hclosed1 : wfworld_closed_on (fv_tm e1) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. set_solver.
    - exact Hle.
    - eapply relevant_world_typing_closed_on_term.
      + exact Hworld1.
      + exact Hbasic1.
  }
  assert (Hclosed2 : wfworld_closed_on (fv_tm e2) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply Hscope. set_solver.
    - exact Hle.
    - eapply relevant_world_typing_closed_on_term.
      + exact Hworld2.
      + exact Hbasic2.
  }
  assert (Hclosed_y : wfworld_closed_on ({[y]} : aset) my).
  { eapply basic_world_formula_singleton_free_closed_on. exact Hworld. }
  eapply (wfworld_closed_on_mono _
    ((fv_tm e1 ∪ fv_tm e2) ∪ ({[y]} : aset)) my).
  - rewrite !fv_tapp_tm. cbn [fv_value]. set_solver.
  - apply (wfworld_closed_on_union (fv_tm e1 ∪ fv_tm e2) ({[y]} : aset)).
    + apply (wfworld_closed_on_union (fv_tm e1) (fv_tm e2));
        [exact Hclosed1|exact Hclosed2].
      + exact Hclosed_y.
Qed.

Lemma arrow_result_source_world
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ basic_world_formula (relevant_env Σ (CTArrow τx τr) e2).
Proof.
  intros Hequiv Hrestrict.
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [_ [Hworld_top_tgt _]].
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  eapply res_models_kripke; [exact Hle|exact Hworld_top_tgt].
Qed.

Lemma basic_world_formula_arrow_open_result_big
    (Σ : lty_env) τx τr e1 e2 (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ basic_world_formula (relevant_env Σ (CTArrow τx τr) e2) ->
  my ⊨ basic_world_formula
    ((<[LVFree y := erase_ty τx]> (∅ : gmap logic_var ty)) : lty_env) ->
  my ⊨ basic_world_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTArrow τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hyτx Hyτr Hye Hworld_src Hworld_y.
  pose proof Hworld_src as Hworld_src_parts.
  apply basic_world_formula_models_iff in Hworld_src_parts as [Hlc_rel [_ _]].
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [Hwf_top_tgt _].
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [_ [_ Hbasic_arrow]].
  eapply arrow_body_world_from_source_arg.
  - exact Hlc_rel.
  - eapply relevant_env_arrow_fresh_free.
    + exact Hyτx.
    + exact Hyτr.
    + set_solver.
  - exact Hbasic_arrow.
  - apply tm_lvars_tapp_tm_fvar_without_arg.
  - rewrite relevant_env_idemp. exact Hworld_src.
  - exact Hworld_y.
Qed.

Lemma basic_world_formula_arrow_open_result_subenv
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
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
        (relevant_env Σ (CTArrow τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T.
Proof.
  intros _ _ _ _ Hτr_vars v T Hlook.
  change ((lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    : lty_env) !! v = Some T).
  pose proof (arrow_body_relevant_env_agree
    Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
    Hτr_vars (tm_lvars_tapp_tm_fvar_without_arg e2 y)) as Hagree.
  rewrite Hagree.
  exact Hlook.
Qed.

Lemma basic_world_formula_arrow_open_result_target
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx (tret (vfvar y)) ->
  my ⊨ basic_world_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx y my Harg) as Hworld.
  pose proof (arrow_result_source_world
    Σ τx τr e1 e2 m my Hequiv Hrestrict) as Hworld_src_my.
  pose proof (basic_world_formula_arrow_open_result_big
    Σ τx τr e1 e2 m my y Hequiv Hyτx Hyτr Hye
    Hworld_src_my Hworld) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_arrow_open_result_subenv; eauto.
  apply arrow_result_open_vars_subset.
  - pose proof (typed_total_equiv_target_zero
      Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
    pose proof (ty_denote_gas_guard_of_zero
      Σ (CTArrow τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
    repeat rewrite res_models_and_iff in Hguard_top_tgt.
    destruct Hguard_top_tgt as [Hwf_top_tgt _].
    apply context_ty_wf_formula_models_iff in Hwf_top_tgt
      as [Hlc_rel [_ Hbasic_arrow]].
    pose proof (basic_context_ty_lvars_lc
      (dom (relevant_env Σ (CTArrow τx τr) e2))
      (CTArrow τx τr) Hlc_rel Hbasic_arrow) as Hlc_arrow.
    cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
    exact (proj2 Hlc_arrow).
  - exact Hyτr.
Qed.

Lemma basic_value_has_ltype_arrow_inserted_result_target_arg
    (Σ : lty_env) τx τr e y :
  basic_value_has_ltype
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e (vfvar y)))
    (vfvar y) (erase_ty τx).
Proof.
  eapply BVT_FVar.
  unfold relevant_env, lty_env_restrict_lvars.
  apply storeA_restrict_lookup_some_2.
  - rewrite lookup_insert_eq. reflexivity.
  - unfold relevant_lvars, tapp_tm.
    cbn [context_ty_lvars tm_lvars tm_lvars_at value_lvars_at].
    set_solver.
Qed.

Lemma basic_tm_has_ltype_arrow_inserted_result_target_fun
    (Σ : lty_env) τtop τx τr e1 e2
    (m : WfWorldT) y :
  erase_ty τtop = erase_ty τx →ₜ erase_ty τr ->
  typed_total_equiv_on Σ τtop m e1 e2 ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  basic_tm_has_ltype
    (lty_env_restrict_lvars
      (<[LVFree y := erase_ty τx]> Σ)
      (context_ty_lvars (cty_open 0 y τr) ∪
       tm_lvars (tapp_tm e2 (vfvar y))))
    e2 (erase_ty τx →ₜ erase_ty τr).
Proof.
  intros Herase Hequiv Hfresh.
  destruct Hequiv as [_ [_ [_ Hzero_tgt]]].
  pose proof (ty_denote_gas_guard_of_zero Σ τtop e2 m Hzero_tgt)
    as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  rewrite Herase in Hty.
  pose proof (basic_tm_has_ltype_lc _ e2
    (erase_ty τx →ₜ erase_ty τr) HlcΣ Hty) as Hlc_e2.
  eapply basic_tm_has_ltype_env_agree_lc; [exact Hty|exact Hlc_e2|].
  apply storeA_map_eq. intros v.
  unfold relevant_env, lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ tm_lvars e2)) as [Hv|Hv]; [|reflexivity].
  assert (Hv_source : v ∈ relevant_lvars τtop e2).
  {
    unfold relevant_lvars. set_solver.
  }
  assert (Hv_target :
      v ∈ relevant_lvars (cty_open 0 y τr)
        (tapp_tm e2 (vfvar y))).
  {
    unfold relevant_lvars, tapp_tm.
    cbn [tm_lvars tm_lvars_at value_lvars_at].
    set_solver.
  }
  rewrite decide_True by exact Hv_source.
  rewrite decide_True by exact Hv_target.
  destruct v as [k|a].
  - exfalso. exact ((tm_lvars_lc e2 Hlc_e2) (LVBound k) Hv).
  - assert (Hay : a <> y).
    {
      intros ->. apply Hfresh. apply elem_of_union_r.
      rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
    }
    rewrite lookup_insert_ne by (intros Heq; inversion Heq; subst; auto).
    reflexivity.
Qed.

Lemma arrow_result_target_typing
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx (tret (vfvar y)) ->
  my ⊨ expr_basic_typing_formula
    (relevant_env
      (<[LVFree y := erase_ty τx]> Σ)
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (basic_world_formula_arrow_open_result_target
    gas Σ τx τr e1 e2 m my y Hequiv Hdom Hrestrict
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
      Σ (CTArrow τx τr) τx τr e1 e2 m y); eauto.
  - apply basic_value_has_ltype_arrow_inserted_result_target_arg.
Qed.

Lemma ty_denote_gas_zero_arrow_open_result_target
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas 0
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) my Hres_mid)
    as Hguard_res_src.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_res_src)
    as Hwf_res_src.
  pose proof (ty_guard_formula_total _ _ _ _ Hguard_res_src)
    as Htotal_res_src.
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx y my Harg) as Hworld_y.
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) my).
  {
    eapply wfworld_closed_on_arrow_open_result_apps.
    - exact Hequiv.
    - exact Hdom.
    - exact Hrestrict.
    - exact Hworld_y.
  }
  assert (Heq_apps :
      tm_equiv_on my
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    eapply tm_equiv_tapp_fvar.
    - exact Hclosed_apps.
    - exact Hlc1.
    - exact Hlc2.
    - pose proof (typed_total_equiv_term_scope
        Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hscope.
      destruct Hequiv as [Heq_base _].
      eapply tm_equiv_full_world_extend_fresh.
      + exact Heq_base.
      + exact Hscope.
      + exact Hye.
      + exact Hdom.
      + exact Hrestrict.
  }
  assert (Htotal_tgt :
      my ⊨ expr_total_formula (tapp_tm e2 (vfvar y))).
  {
    pose proof (typed_total_equiv_term_lc
      Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
    pose proof (typed_total_equiv_term_scope
      Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hscope.
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
    assert (Heq_base_my : tm_equiv_on my e1 e2).
    {
      eapply tm_equiv_full_world_extend_fresh.
      - eapply typed_total_equiv_tm_equiv. exact Hequiv.
      - exact Hscope.
      - exact Hye.
      - exact Hdom.
      - exact Hrestrict.
    }
    assert (Htotal_apps : tm_total_equiv_on my
        (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y))).
    {
      eapply tm_total_equiv_tapp_fvar.
      - exact Hclosed_apps.
      - exact Hlc1.
      - exact Hlc2.
      - exact Heq_base_my.
      - exact Htotal_base_my.
    }
    eapply tm_equiv_total.
    - exact Htotal_apps.
    - apply lc_tapp_tm; [exact Hlc2|constructor].
    - rewrite fv_tapp_tm. cbn [fv_value].
      rewrite Hdom. set_solver.
    - exact Htotal_res_src.
  }
  assert (Hworld_tgt :
      my ⊨ basic_world_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))).
  {
    eapply basic_world_formula_arrow_open_result_target; eauto.
  }
  assert (Hwf_tgt :
      my ⊨ context_ty_wf_formula
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
      my ⊨ expr_basic_typing_formula
        (relevant_env
          (<[LVFree y := erase_ty τx]> Σ)
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
        (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr))).
  {
    eapply arrow_result_target_typing; eauto.
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

Lemma typed_total_equiv_arrow_open_result_mid
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx (tret (vfvar y)) ->
  typed_total_equiv_on
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) my
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hres_mid Harg.
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx y my Harg) as Hworld_y.
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) my).
  {
    eapply wfworld_closed_on_arrow_open_result_apps.
    - exact Hequiv.
    - exact Hdom.
    - exact Hrestrict.
    - exact Hworld_y.
  }
  assert (Heq_base_my : tm_equiv_on my e1 e2).
  {
    eapply tm_equiv_full_world_extend_fresh.
    - eapply typed_total_equiv_tm_equiv. exact Hequiv.
    - eapply typed_total_equiv_term_scope. exact Hequiv.
    - exact Hye.
    - exact Hdom.
    - exact Hrestrict.
  }
  assert (Htotal_base_my : tm_total_equiv_on my e1 e2).
  {
    eapply tm_total_equiv_full_world_extend_fresh.
    - eapply typed_total_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - eapply typed_total_equiv_term_scope. exact Hequiv.
    - exact Hye.
    - exact Hdom.
    - exact Hrestrict.
  }
  split.
  - eapply tm_equiv_tapp_fvar.
    + exact Hclosed_apps.
    + exact Hlc1.
    + exact Hlc2.
    + exact Heq_base_my.
  - split.
    + eapply tm_total_equiv_tapp_fvar.
      * exact Hclosed_apps.
      * exact Hlc1.
      * exact Hlc2.
      * exact Heq_base_my.
      * exact Htotal_base_my.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hres_mid.
      * eapply (ty_denote_gas_zero_arrow_open_result_target
        gas Σ τx τr e1 e2 m my y); eauto.
Qed.

Lemma ty_denote_gas_tm_equiv_arrow_open_result
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye HyΣ1 HyΣ2 Harg Hres.
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_total_equiv_source_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e1 m Hzero_top_src) as Hguard_top_src.
  repeat rewrite res_models_and_iff in Hguard_top_src.
  destruct Hguard_top_src as [Hwf_top_src _].
  apply context_ty_wf_formula_models_iff in Hwf_top_src
    as [HΣclosed [_ Hbasic_arrow]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTArrow τx τr) e1))
    (CTArrow τx τr) HΣclosed Hbasic_arrow) as Hlc_arrow.
  cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
  destruct Hlc_arrow as [_ Hτr_lc].
  set (τres := cty_open 0 y τr).
  set (esrc := tapp_tm e1 (vfvar y)).
  set (etgt := tapp_tm e2 (vfvar y)).
  fold τres esrc etgt in Hres |- *.
	  assert (Hres_mid :
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]> Σ)
	        τres esrc).
  {
    unfold τres, esrc.
    eapply ty_equiv_arrow_result_src_mid.
    - exact Hlc1.
    - exact Hyτr.
    - apply arrow_result_open_vars_subset; assumption.
    - exact Hres.
  }
	  assert (Htgt_mid_to_goal :
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]> Σ)
	        τres etgt ->
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]>
	          (relevant_env Σ (CTArrow τx τr) e2))
	        τres etgt).
  {
    unfold τres, etgt.
    intros Hmid.
    eapply ty_equiv_arrow_result_tgt_goal.
    - exact Hlc2.
    - exact Hyτr.
    - apply arrow_result_open_vars_subset; assumption.
    - exact Hmid.
  }
  apply Htgt_mid_to_goal.
  eapply IH.
  - unfold τres, esrc, etgt in *.
    eapply (typed_total_equiv_arrow_open_result_mid
      gas Σ τx τr e1 e2 m my y).
    + exact Hequiv.
    + exact Hdom.
    + exact Hrestrict.
    + exact Hyτx.
    + exact Hyτr.
    + exact Hye.
    + exact Hres_mid.
    + exact Harg.
  - exact Hres_mid.
Qed.

Lemma ty_denote_gas_zero_type_fv_world
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  lvars_fv (context_ty_lvars τ) ⊆ world_dom (m : WorldT).
Proof.
  apply ty_denote_gas_type_lvars_world.
Qed.

End TypeDenote.
