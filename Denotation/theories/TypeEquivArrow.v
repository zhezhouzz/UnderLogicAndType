(** * Denotation.TypeEquivArrow

    Arrow case for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTermBase
  TypeEquivTermResult
  TypeEquivFiberBaseCore
  TypeEquivFiberBaseProjected
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
  intros Hyτr Hτr_vars Hsrc.
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
  intros Hlcτr Hyτr Hsrc.
  eapply ty_equiv_arrow_result_src_mid; eauto.
  apply arrow_result_open_vars_subset; assumption.
Qed.

Lemma ty_equiv_arrow_result_src_mid_current
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  Σ !! LVFree y = Some (erase_ty τx) ->
  cty_lc_at 1 τr ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    Σ (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros HyΣ Hlcτr Hyτr Hsrc.
  pose proof (ty_equiv_arrow_result_src_mid
    gas Σ τx τr e1 my y Hyτr
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
  intros Hyτr Hτr_vars Hmid.
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
  intros Hlcτr Hyτr Hmid.
  eapply ty_equiv_arrow_result_tgt_goal; eauto.
  apply arrow_result_open_vars_subset; assumption.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal_inserted_lc
    gas (Σ : lty_env) τx τr e2
  (my : WfWorldT) y :
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
  intros Hyτr Hlcτr Hmid.
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
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_top_tgt)
    as Hworld_top_tgt.
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
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_tgt)
    as Hwf_top_tgt.
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
    (Σ : lty_env) τx τr e2 y :
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
  intros Hτr_vars v T Hlook.
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
  intros v T Hlook.
  eapply basic_world_formula_arrow_open_result_subenv.
  apply arrow_result_open_vars_subset.
  - pose proof (typed_total_equiv_target_zero
      Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
    pose proof (ty_denote_gas_guard_of_zero
      Σ (CTArrow τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
    pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_tgt)
      as Hwf_top_tgt.
    apply context_ty_wf_formula_models_iff in Hwf_top_tgt
      as [Hlc_rel [_ Hbasic_arrow]].
    pose proof (basic_context_ty_lvars_lc
      (dom (relevant_env Σ (CTArrow τx τr) e2))
      (CTArrow τx τr) Hlc_rel Hbasic_arrow) as Hlc_arrow.
    cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
    exact (proj2 Hlc_arrow).
  - exact Hyτr.
  - exact Hlook.
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
  pose proof (ty_guard_formula_basic_typing _ _ _ _ Hguard) as Hbasic.
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
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_top_src)
    as Hwf_top_src.
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

Section TypeDenote.
Lemma arrow_result_first_arg_drop_fun_slot
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  f ∉ fv_cty τx ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e)))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)).
Proof.
  intros HfΣ Hfy Hfτx Harg.
  rewrite lvar_store_insert_free_commute in Harg by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) f (erase_ty (CTArrow τx τr))) in Harg.
  2:{
    rewrite dom_insert_L.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. congruence.
    - exact (HfΣ Hbad).
  }
  2:{
    intros Hbad. apply Hfτx.
    rewrite <- context_ty_lvars_fv.
    apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  exact Harg.
Qed.

Lemma arrow_result_first_arg_add_fun_slot
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  f ∉ fv_cty τx ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e)))
    τx (tret (vfvar y)).
Proof.
  intros HfΣ Hfy Hfτx Harg.
  rewrite lvar_store_insert_free_commute by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) f (erase_ty (CTArrow τx τr))).
  2:{
    rewrite dom_insert_L.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. congruence.
    - exact (HfΣ Hbad).
  }
  2:{
    intros Hbad. apply Hfτx.
    rewrite <- context_ty_lvars_fv.
    apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  exact Harg.
Qed.

Local Lemma arrow_result_body_relevant_subset τx τr e f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  (context_ty_lvars (cty_open 0 y τr) ∪
    tm_lvars (tapp_tm (tret (vfvar f)) (vfvar y))) ∖
    {[LVFree y]} ∖ {[LVFree f]} ⊆
  context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e.
Proof.
  intros Hlcτr Hffresh Hyfresh.
  eapply result_first_result_body_relevant_subset; [exact Hlcτr| |].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - intros Hy. apply Hyfresh. apply elem_of_union_r. exact Hy.
Qed.

Lemma arrow_result_first_result_env_agree
    gas (Σ : lty_env) τx τr e1 e2
    (my : WfWorldT) f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e1)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e2)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)).
Proof.
  intros Hlcτr Hffresh Hyfresh Hres.
  eapply result_first_result_env_agree_general.
  - eapply arrow_result_body_relevant_subset; eauto.
  - eapply arrow_result_body_relevant_subset; eauto.
  - exact Hres.
Qed.

Local Lemma arrow_lvars_shift_from_lc_eq k D :
  lc_lvars D ->
  lvars_shift_from k D = D.
Proof.
  apply result_first_lvars_shift_from_lc_eq.
Qed.

Local Ltac arrow_expr_result_shift0_side :=
  first
    [ assumption
    | apply result_first_lc_lvars_shift_from; assumption
    | rewrite lvars_shift_from_fv; assumption ].


Lemma ty_denote_gas_tm_equiv_arrow_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e1)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e2)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
	        (tret (vbvar 0)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_equiv_source_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_src.
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e1 m Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hguard_tgt.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_src) as Hwf_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src)
    as Hworld_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_tgt)
    as Hworld_tgt.
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_arrow_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTArrow τx τr) e1)) _
    HlcΣ_wf_src Hbasic_arrow_src) as Hlc_arrow.
  cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
  destruct Hlc_arrow as [Hlcτx Hlcτr].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas)
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  assert (Hfib :
      tm_fiber_equiv_on m (lvars_fv (context_ty_lvars (CTArrow τx τr)))
        e1 e2).
  {
    apply tm_equiv_on_to_fiber_equiv.
    eapply typed_total_equiv_tm_equiv. exact Hequiv.
  }
  pose proof (tm_fiber_equiv_to_projected_on
    Σ (CTArrow τx τr) m (context_ty_lvars (CTArrow τx τr))
    e1 e2 Hfib Hzero_src Hzero_tgt) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e2)) ∪
    lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪
    fv_cty τx ∪ fv_cty τr).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTArrow τx τr))).
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
          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))).
  {
    clear -Hf.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    set_solver.
  }
	  assert (HfΣ2 :
	      f ∉ lvars_fv
	        (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
	  {
	    clear -Hf.
	    rewrite typed_lty_env_bind_lvars_fv_dom.
	    set_solver.
	  }
	  assert (Hf_rel1 :
	      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
	  {
	    intros Hbad. apply HfΣ1.
	    apply lvars_fv_elem.
	    rewrite typed_lty_env_bind_dom.
	    rewrite (arrow_lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
	    apply elem_of_union_l. exact Hbad.
	  }
	  assert (Hf_rel2 :
	      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
	  {
	    intros Hbad. apply HfΣ2.
	    apply lvars_fv_elem.
	    rewrite typed_lty_env_bind_dom.
	    rewrite (arrow_lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
	    apply elem_of_union_l. exact Hbad.
	  }
	  assert (Hopened_scope :
	      formula_scoped_in_world mf
	        (FImpl
	          (expr_result_formula_at
	            (context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e2)
	            e2 (LVFree f))
	          (arrow_value_denote_gas_with ty_denote_gas gas
	            (<[LVFree f := erase_ty (CTArrow τx τr)]>
	              (relevant_env Σ (CTArrow τx τr) e2))
	            τx τr (tret (vfvar f))))).
	  {
	    pose proof (formula_scoped_forall_open_res_le m mf f
	      _ Hscope_tgt
	      ltac:(rewrite <- Hrestrict; apply res_restrict_le)
	      ltac:(rewrite Hdom; clear; set_solver)) as Hopened_scope_raw.
	    rewrite formula_open_impl in Hopened_scope_raw.
	    rewrite formula_open_expr_result_formula_at_shift0 in Hopened_scope_raw
	      by (first
	        [ exact Hlc2
	        | apply result_first_lc_lvars_shift_from; exact HlcΣ_tgt
	        | rewrite lvars_shift_from_fv; clear -Hf; set_solver
	        | clear -Hfe; set_solver ]).
	    rewrite (arrow_lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt)
	      in Hopened_scope_raw.
	    rewrite (ty_denote_gas_zero_relevant_env_dom_eq
	      Σ (CTArrow τx τr) e2 m Hzero_tgt) in Hopened_scope_raw.
	    rewrite (formula_open_result_first_arrow_value_ret_bvar0
	      gas (relevant_env Σ (CTArrow τx τr) e2) τx τr
	      (erase_ty (CTArrow τx τr)) f) in Hopened_scope_raw.
	    2: exact HlcΣ_tgt.
	    2: exact Hf_rel2.
	    2: exact Hlcτx.
	    2: exact Hlcτr.
	    2: exact Hfτx.
	    2: exact Hfτr.
	    exact Hopened_scope_raw.
	  }
	  rewrite formula_open_impl.
	  rewrite formula_open_expr_result_formula_at_shift0
	    by (first
	      [ exact Hlc2
	      | apply result_first_lc_lvars_shift_from; exact HlcΣ_tgt
	      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
	      | clear -Hfe; set_solver ]).
	  rewrite (arrow_lvars_shift_from_lc_eq 0
	    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
	  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
	    Σ (CTArrow τx τr) e2 m Hzero_tgt).
	  rewrite (formula_open_result_first_arrow_value_ret_bvar0
	    gas (relevant_env Σ (CTArrow τx τr) e2) τx τr
	    (erase_ty (CTArrow τx τr)) f).
	  2: exact HlcΣ_tgt.
	  2: exact Hf_rel2.
	  2: exact Hlcτx.
	  2: exact Hlcτr.
	  2: exact Hfτx.
	  2: exact Hfτr.
	  eapply res_models_impl_intro; [exact Hopened_scope|].
	  intros Hres_tgt.
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
  rewrite (arrow_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTArrow τx τr) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hequiv_src :
      typed_total_equiv_on Σ (CTArrow τx τr) mf_src e1 e2).
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
	          -- rewrite <- Hrestrict_src. apply res_restrict_le.
	          -- exact Hzero_src.
	        * eapply (res_models_kripke m mf_src).
	          -- rewrite <- Hrestrict_src. apply res_restrict_le.
	          -- exact Hzero_tgt.
  }
	  rewrite (formula_open_result_first_arrow_value_ret_bvar0
	    gas (relevant_env Σ (CTArrow τx τr) e1) τx τr
	    (erase_ty (CTArrow τx τr)) f) in Hvalue_src.
	  2: exact HlcΣ_src.
	  2: exact Hf_rel1.
	  2: exact Hlcτx.
	  2: exact Hlcτr.
	  2: exact Hfτx.
	  2: exact Hfτr.
	  assert (Hvalue_tgt_src :
	      mf_src ⊨
	        arrow_value_denote_gas_with ty_denote_gas gas
	          (<[LVFree f := erase_ty (CTArrow τx τr)]>
	            (relevant_env Σ (CTArrow τx τr) e2))
	          τx τr (tret (vfvar f))).
	  {
	    assert (Hvalue_tgt_scope_src :
	        formula_scoped_in_world mf_src
	          (arrow_value_denote_gas_with ty_denote_gas gas
	            (<[LVFree f := erase_ty (CTArrow τx τr)]>
	              (relevant_env Σ (CTArrow τx τr) e2))
	            τx τr (tret (vfvar f)))).
	    {
	      eapply formula_scoped_arrow_value_body_obs.
	      pose proof (ty_denote_gas_zero_type_fv_world
	        Σ (CTArrow τx τr) e1 m Hzero_src) as Hτworld.
	      rewrite Hdom_src.
	      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - apply elem_of_union_l. exact (Hτworld a Ha).
      - apply elem_of_union_r. exact Ha.
    }
		    eapply res_models_forall_full_world_map;
		      [exact Hvalue_tgt_scope_src| |exact Hvalue_src].
	    exists (world_dom (mf_src : WorldT) ∪ world_dom (mf : WorldT) ∪
	        fv_cty τx ∪ fv_cty τr ∪ fv_tm e1 ∪ fv_tm e2 ∪
	        lvars_fv (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ∪
	        lvars_fv (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
      intros y Hy my Hdom_y Hrestrict_y Hopened_arg.
      cbn [formula_open] in Hopened_arg |- *.
      pose proof (formula_scoped_forall_open_res_le mf_src my y
        _ Hvalue_tgt_scope_src
        ltac:(rewrite <- Hrestrict_y; apply res_restrict_le)
        ltac:(rewrite Hdom_y; clear; set_solver)) as Htarget_impl_scope.
      cbn [formula_open] in Htarget_impl_scope.
      eapply res_models_impl_intro.
      { exact Htarget_impl_scope. }
      intros Harg_tgt.
      assert (Hyτx : y ∉ fv_cty τx).
      { clear -Hy. set_solver. }
      assert (Hyτr : y ∉ fv_cty τr).
      { clear -Hy. set_solver. }
      assert (Hye : y ∉ fv_tm e1 ∪ fv_tm e2).
      { clear -Hy. set_solver. }
      assert (HyΣ1 : y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))).
      { clear -Hy. set_solver. }
	      assert (HyΣ2 : y ∉ lvars_fv
	        (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
	      { clear -Hy. set_solver. }
        assert (Hy_rel1 :
            LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
        {
          intros Hbad. apply HyΣ1.
          apply lvars_fv_elem.
          rewrite typed_lty_env_bind_dom.
          rewrite (arrow_lvars_shift_from_lc_eq 0
            (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
          apply elem_of_union_l. exact Hbad.
        }
        assert (Hy_rel2 :
            LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
        {
          intros Hbad. apply HyΣ2.
          apply lvars_fv_elem.
          rewrite typed_lty_env_bind_dom.
          rewrite (arrow_lvars_shift_from_lc_eq 0
            (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
          apply elem_of_union_l. exact Hbad.
        }
        assert (Hfy : f <> y).
        {
          intros ->. apply Hy.
          clear -Hdom.
          rewrite Hdom. set_solver.
        }
		      assert (Harg_tgt_open :
		          my ⊨ ty_denote_gas gas
		            (<[LVFree y := erase_ty τx]>
		              (relevant_env Σ (CTArrow τx τr) e2))
		            τx (tret (vfvar y))).
		      {
		        rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
		          y gas
		          (<[LVFree f := erase_ty (CTArrow τx τr)]>
		            (relevant_env Σ (CTArrow τx τr) e2))
		          τx) in Harg_tgt.
		        2:{ apply lty_env_closed_insert_free. exact HlcΣ_tgt. }
		        2:{
		          rewrite dom_insert_L.
		          intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
		          - apply elem_of_singleton in Hybad. congruence.
		          - exact (Hy_rel2 Hybad).
		        }
		        2: exact Hyτx.
		        2: exact Hlcτx.
		        eapply arrow_result_first_arg_drop_fun_slot.
		        - exact Hf_rel2.
		        - clear -Hfy. congruence.
	        - exact Hfτx.
	        - exact Harg_tgt.
      }
		      pose proof (ty_denote_gas_tm_equiv_arrow_open_arg
		        gas Σ τx τr e1 e2 my y Harg_tgt_open) as Harg_src.
	      assert (Harg_src_formula :
          my ⊨ ty_denote_gas gas
            (<[LVFree y := erase_ty τx]>
              (<[LVFree f := erase_ty (CTArrow τx τr)]>
                (relevant_env Σ (CTArrow τx τr) e1)))
            τx (tret (vfvar y))).
		      {
			eapply arrow_result_first_arg_add_fun_slot.
			- exact Hf_rel1.
				- intros ->. apply Hy.
				  clear -Hdom.
				  rewrite Hdom. set_solver.
			- exact Hfτx.
			- exact Harg_src.
		      }
		      pose proof (arrow_value_open_arg_to_regular_imp
		        gas (relevant_env Σ (CTArrow τx τr) e1) τx τr
		        (erase_ty (CTArrow τx τr)) f y mf_src my
		        HlcΣ_src Hf_rel1 Hfy
		        ltac:(rewrite dom_insert_L; clear -Hfy Hy_rel1; set_solver)
		        Hlcτx Hlcτr
		        ltac:(clear -Hfτx Hfτr; set_solver)
		        ltac:(clear -Hyτx Hyτr; set_solver)
		        Hvalue_src
		        ltac:(clear -Hy; set_solver)
		        Hdom_y Hrestrict_y) as Hopened_arg_regular.
		      pose proof (res_models_impl_elim _ _ _ Hopened_arg_regular Harg_src_formula)
		        as Hres_src_inner.
	      assert (Hres_src_regular :
		  my ⊨ ty_denote_gas gas
		    (<[LVFree y := erase_ty τx]>
		      (<[LVFree f := erase_ty (CTArrow τx τr)]>
			(relevant_env Σ (CTArrow τx τr) e1)))
		    (cty_open 0 y τr)
		    (tapp_tm (tret (vfvar f)) (vfvar y))).
	      {
          exact Hres_src_inner.
	      }
	      assert (Hres_tgt_regular :
		  my ⊨ ty_denote_gas gas
		    (<[LVFree y := erase_ty τx]>
		      (<[LVFree f := erase_ty (CTArrow τx τr)]>
			(relevant_env Σ (CTArrow τx τr) e2)))
		    (cty_open 0 y τr)
		    (tapp_tm (tret (vfvar f)) (vfvar y))).
	      {
			eapply arrow_result_first_result_env_agree.
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
	        rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
	          y gas
	          (<[LVFree f := erase_ty (CTArrow τx τr)]>
	            (relevant_env Σ (CTArrow τx τr) e2))
	          τr (erase_ty τx) (tret (vfvar f))).
	        2:{ apply lty_env_closed_insert_free. exact HlcΣ_tgt. }
	        2:{
	          rewrite dom_insert_L.
	          intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
	          - apply elem_of_singleton in Hybad. congruence.
	          - exact (Hy_rel2 Hybad).
	        }
	        2:{ cbn [fv_tm fv_value]. clear -Hfy. set_solver. }
	        2:{ clear -Hyτx Hyτr. set_solver. }
	        2:{ constructor. constructor. }
	        exact Hres_tgt_regular.
		  }
			  eapply res_models_projection; [|exact Hvalue_tgt_src].
		  eapply res_restrict_eq_subset; [|exact Hproj_obs].
		  apply formula_fv_open_arrow_value_body_obs.
Qed.

End TypeDenote.
