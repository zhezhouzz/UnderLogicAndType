(** * Denotation.TypeEquivArrow

    Arrow case for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivFiberTransport
  TypeEquivBody.

Section TypeDenote.

Lemma arrow_open_arg_to_inserted_env
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hfresh_arg Harg.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact Hfresh_arg || exact Hea_fresh || exact Hτa_fresh).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y)))
    ltac:(better_set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e Hyτx)) as Hagree.
  rewrite Hagree in Harg.
  rewrite typed_lty_env_bind_open_current in Harg
    by (exact HfreshΣ || exact HΣclosed).
  exact Harg.
Qed.

Lemma arrow_open_arg_to_inserted_env_normalized
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  lc_context_ty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hlc Hfresh_arg Harg.
  pose proof (arrow_open_arg_to_inserted_env
    gas Σ τx τr e m y HΣclosed HfreshΣ Hyτx Hfresh_arg Harg)
    as Harg_open.
  rewrite cty_open_shift_from_lc_fresh in Harg_open
    by (exact Hlc || exact Hyτx).
  exact Harg_open.
Qed.

Lemma arrow_inserted_env_to_open_arg
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hfresh_arg Harg.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0)))
    by (exact Hfresh_arg || exact Hea_fresh || exact Hτa_fresh).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)).
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y)))
    ltac:(better_set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e Hyτx)) as Hagree.
  rewrite Hagree.
  rewrite typed_lty_env_bind_open_current
    by (exact HfreshΣ || exact HΣclosed).
  exact Harg.
Qed.

Lemma arrow_inserted_env_to_open_arg_normalized
    gas (Σ : lty_env) τx τr e
    (m : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  y ∉ fv_cty τx ->
  lc_context_ty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e) (erase_ty τx))) ->
  m ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)) ->
  m ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros HΣclosed HfreshΣ Hyτx Hτx_lc Hfresh_arg Harg.
  eapply arrow_inserted_env_to_open_arg; eauto.
  replace (cty_open 0 y (cty_shift 0 τx)) with τx.
  - exact Harg.
  - symmetry. apply cty_open_shift_from_lc_fresh; assumption.
Qed.

Lemma ty_denote_gas_tm_equiv_arrow_open_arg
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros _ _ _ Hyτx HyΣ1 HyΣ2 Htgt.
  set (τa := cty_open 0 y (cty_shift 0 τx)).
  set (ea := tret (vfvar y)).
  fold τa ea in Htgt |- *.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (relevant_lvars τa ea)
    ltac:(set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 Hyτx)) as Hsrc_mid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (relevant_lvars τa ea)
    ltac:(set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 Hyτx)) as Htgt_mid.
  rewrite Hsrc_mid.
  rewrite Htgt_mid in Htgt.
  exact Htgt.
Qed.

Lemma ty_equiv_arrow_result_src_mid
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros Hlc Hyτr Hsrc.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e1 (vfvar y)))
    ltac:(set_solver)
    (arrow_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e1 (tapp_tm e1 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e1 y Hlc)))
    as Hagree.
  rewrite <- Hagree.
  exact Hsrc.
Qed.

Lemma ty_equiv_arrow_result_src_mid_inserted
    gas (Σ : lty_env) τx τr e1
    (my : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env) ->
  lc_tm e1 ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e1))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)).
Proof.
  intros HΣclosed HyΣ Hyrel Hlc Hyτr Hsrc.
  assert (Hsrc_open :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e1)
            (erase_ty τx)))
        (cty_open 0 y τr) (tapp_tm e1 (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current.
    - exact Hsrc.
    - exact Hyrel.
    - apply relevant_env_closed. exact HΣclosed.
  }
  pose proof (ty_equiv_arrow_result_src_mid
    gas Σ τx τr e1 my y Hlc Hyτr Hsrc_open) as Hmid.
  rewrite typed_lty_env_bind_open_current in Hmid
    by (exact HyΣ || exact HΣclosed).
  exact Hmid.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal
    gas (Σ : lty_env) τx τr e2
    (my : WfWorldT) y :
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hlc Hyτr Hmid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y))
    (relevant_lvars (cty_open 0 y τr)
      (tapp_tm e2 (vfvar y)))
    ltac:(set_solver)
    (arrow_body_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
      Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e2 y Hlc)))
    as Hagree.
  rewrite Hagree.
  exact Hmid.
Qed.

Lemma ty_equiv_arrow_result_tgt_goal_inserted
    gas (Σ : lty_env) τx τr e2
    (my : WfWorldT) y :
  lty_env_closed Σ ->
  LVFree y ∉ dom Σ ->
  LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env) ->
  lc_tm e2 ->
  y ∉ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros HΣclosed HyΣ Hyrel Hlc Hyτr Hmid.
  assert (Hmid_open :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind Σ (erase_ty τx)))
        (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current.
    - exact Hmid.
    - exact HyΣ.
    - exact HΣclosed.
  }
  pose proof (ty_equiv_arrow_result_tgt_goal
    gas Σ τx τr e2 my y Hlc Hyτr Hmid_open) as Hgoal.
  rewrite typed_lty_env_bind_open_current in Hgoal.
  - exact Hgoal.
  - exact Hyrel.
  - apply relevant_env_closed. exact HΣclosed.
Qed.

Lemma wfworld_closed_on_arrow_open_result_apps
    (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
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
  assert (Hworld_y :
      my ⊨ basic_world_formula
        (<[LVFree y := erase_ty τx]> (∅ : lty_env))).
  {
    change (<[LVBound 0 := erase_ty τx]> (∅ : gmap logic_var ty))
      with (typed_lty_env_bind (∅ : lty_env) (erase_ty τx)) in Hworld.
    rewrite formula_open_basic_world_bind0 in Hworld.
    - exact Hworld.
    - set_solver.
    - intros v Hv. set_solver.
  }
  assert (Hclosed_y : wfworld_closed_on ({[y]} : aset) my).
  { eapply basic_world_formula_singleton_free_closed_on. exact Hworld_y. }
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

Lemma basic_world_formula_opened_arg_world
    (Ty : ty) (my : WfWorldT) y :
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := Ty]> ∅)) ->
  my ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env).
Proof.
  intros Hworld.
  change (<[LVBound 0 := Ty]> (∅ : gmap logic_var ty))
    with (typed_lty_env_bind (∅ : lty_env) Ty) in Hworld.
  rewrite formula_open_basic_world_bind0 in Hworld.
  - exact Hworld.
  - set_solver.
  - intros v Hv. set_solver.
Qed.

Lemma basic_world_formula_opened_arg_from_denotation
    gas (Σarg : lty_env) τx (my : WfWorldT) y :
  y ∉ fv_cty τx ->
  y ∉ lvars_fv (dom Σarg) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas gas Σarg (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)).
Proof.
  intros Hyτx HyΣ Harg.
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Hea_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    Σarg (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact HyΣ || exact Hea_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in Harg
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  pose proof (ty_denote_gas_guard gas
    (lty_env_open_one 0 y Σarg)
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) my Harg)
    as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [_ [_ Hty]].
  change (<[LVBound 0 := erase_ty τx]> (∅ : gmap logic_var ty))
    with (typed_lty_env_bind (∅ : lty_env) (erase_ty τx)).
  rewrite formula_open_basic_world_bind0.
  apply basic_world_formula_subenv with
    (Σbig :=
      relevant_env (lty_env_open_one 0 y Σarg)
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  - intros v T Hlook.
    rewrite lookup_insert_Some in Hlook.
    destruct Hlook as [[<- <-]|[Hneq Hempty]].
    + inversion Hty; subst; clear Hty.
      match goal with
      | Hval : basic_value_has_ltype _ (vfvar y) _ |- _ =>
          inversion Hval; subst; clear Hval
      end.
      match goal with
      | Hlookup : _ !! LVFree y = Some _ |- _ =>
          rewrite cty_open_preserves_erasure,
            cty_shift_preserves_erasure in Hlookup;
          exact Hlookup
      end.
    + rewrite lookup_empty in Hempty. discriminate.
  - exact Hworld.
  - set_solver.
  - intros v Hv. set_solver.
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
  forall v T,
    relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T ->
    relevant_env
      (<[LVFree y := erase_ty τx]>
        (relevant_env Σ (CTArrow τx τr) e2))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)) !! v = Some T.
Proof.
  intros Hequiv Hyτx Hyτr Hye v T Hlook.
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [_ Hlc2].
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
  repeat rewrite res_models_and_iff in Hguard_top_tgt.
  destruct Hguard_top_tgt as [Hwf_top_tgt _].
  apply context_ty_wf_formula_models_iff in Hwf_top_tgt
    as [HlcΣ _].
  assert (Hlc_rel :
      lc_lvars (dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env))).
  { exact HlcΣ. }
  assert (Hy_rel :
      LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
  {
    eapply relevant_env_arrow_fresh_free.
    - exact Hyτx.
    - exact Hyτr.
    - set_solver.
  }
  pose proof (arrow_body_relevant_env_agree_open_one_core
    Σ (erase_ty τx) y τx τr e2 (tapp_tm e2 (vfvar y))
    Hyτr (tm_lvars_tapp_tm_fvar_without_arg_shift_lc e2 y Hlc2)) as Hagree.
  change ((lty_env_restrict_lvars
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    : lty_env) !! v = Some T) in Hlook.
  rewrite <- Hagree in Hlook.
  rewrite typed_lty_env_bind_open_current in Hlook by
    (exact Hy_rel || exact Hlc_rel).
  change ((lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e2))
    (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    : lty_env) !! v = Some T).
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
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ basic_world_formula
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (arrow_result_source_world
    Σ τx τr e1 e2 m my Hequiv Hrestrict) as Hworld_src_my.
  pose proof (basic_world_formula_opened_arg_world (erase_ty τx) my y Hworld)
    as Hworld_y.
  pose proof (basic_world_formula_arrow_open_result_big
    Σ τx τr e1 e2 m my y Hequiv Hyτx Hyτr Hye
    Hworld_src_my Hworld_y) as Hworld_big.
  eapply basic_world_formula_subenv; [|exact Hworld_big].
  eapply basic_world_formula_arrow_open_result_subenv; eauto.
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
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ expr_basic_typing_formula
    (relevant_env
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
    (tapp_tm e2 (vfvar y)) (erase_ty (cty_open 0 y τr)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (basic_world_formula_arrow_open_result_target
    gas Σ τx τr e1 e2 m my y Hequiv Hdom Hrestrict
    Hyτx Hyτr Hye Hworld Hres_mid Harg) as Hworld_tgt.
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld_tgt
    as [Hlc_tgt [Hscope_tgt _]].
  split; [exact Hlc_tgt|].
  split; [exact Hscope_tgt|].
  rewrite cty_open_preserves_erasure.
  eapply basic_tm_has_ltype_tapp_tm_lvar.
  - exact Hlc_tgt.
  - eapply (basic_tm_has_ltype_open_result_target_fun
      Σ (CTArrow τx τr) τx τr e1 e2 m y); eauto.
  - apply basic_value_has_ltype_open_result_target_arg.
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
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas 0
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (ty_denote_gas_guard gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) my Hres_mid)
    as Hguard_res_src.
  pose proof (ty_denote_gas_guard gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) my Harg)
    as Hguard_arg.
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_top_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_top_tgt) as Hguard_top_tgt.
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
         fv_tm (tapp_tm e2 (vfvar y))) my).
  {
    eapply wfworld_closed_on_arrow_open_result_apps; eauto.
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
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
          (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))).
  {
    eapply basic_world_formula_arrow_open_result_target; eauto.
  }
  assert (Hwf_tgt :
      my ⊨ context_ty_wf_formula
        (relevant_env
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
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
          (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
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
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) (tapp_tm e1 (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  typed_total_equiv_on
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) my
    (tapp_tm e1 (vfvar y)) (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye Hworld Hres_mid Harg.
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) my).
  {
    eapply (wfworld_closed_on_arrow_open_result_apps
      Σ τx τr e1 e2 m my y); eauto.
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
  all: eauto.
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
  my ⊨ formula_open 0 y
    (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅)) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e1)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e2)
        (erase_ty τx))
      τr (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye HyΣ1 HyΣ2 Hworld Harg Hres.
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  assert (Hτa_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. exact Hyτx. }
  assert (Harg_tm_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. set_solver. }
  assert (Hsrc_tm_fresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 e1) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_value]. set_solver.
  }
  assert (Htgt_tm_fresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 e2) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_value]. set_solver.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e1) (vbvar 0))) in Hres
    by (exact HyΣ1 || exact Hsrc_tm_fresh || exact Hyτr).
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))
    τr (tapp_tm (tm_shift 0 e2) (vbvar 0)))
    by (exact HyΣ2 || exact Htgt_tm_fresh || exact Hyτr).
  rewrite open_tapp_tm_shift_bvar0_lc in Hres by exact Hlc1.
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc2.
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact HyΣ2 || exact Harg_tm_fresh || exact Hτa_fresh).
  replace (open_tm 0 (vfvar y) (tret (vbvar 0))) with
      (tret (vfvar y)) in Harg
    by (cbn [open_tm open_value]; rewrite decide_True by lia; reflexivity).
  set (τres := cty_open 0 y τr).
  set (esrc := tapp_tm e1 (vfvar y)).
  set (etgt := tapp_tm e2 (vfvar y)).
  fold τres esrc etgt in Hres |- *.
  assert (Hres_mid :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres esrc).
  {
    unfold τres, esrc.
    eapply ty_equiv_arrow_result_src_mid;
      eauto.
  }
  assert (Htgt_mid_to_goal :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        τres etgt ->
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e2)
            (erase_ty τx)))
        τres etgt).
  {
    unfold τres, etgt.
    eapply ty_equiv_arrow_result_tgt_goal;
      eauto.
  }
  apply Htgt_mid_to_goal.
  eapply IH.
  - unfold τres, esrc, etgt in *.
    eapply typed_total_equiv_arrow_open_result_mid; eauto.
  - exact Hres_mid.
Qed.

Lemma ty_denote_gas_zero_type_fv_world
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  lvars_fv (context_ty_lvars τ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hzero.
  cbn [ty_denote_gas] in Hzero.
  rewrite res_models_and_iff in Hzero.
  destruct Hzero as [Hguard _].
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld _]].
  pose proof (context_ty_wf_formula_fv_cty_subset
    (relevant_env Σ τ e) τ m Hwf) as Hτ.
  pose proof (proj1 (basic_world_formula_models_iff
    (relevant_env Σ τ e) m) Hworld) as [_ [Hdom _]].
  rewrite context_ty_lvars_fv.
  set_solver.
Qed.

End TypeDenote.
