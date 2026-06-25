(** * Denotation.ResultFirstOpen

    Shared opening and scope facts for result-first Arrow/Wand denotations. *)

From Denotation Require Import Notation TypeDenote TypeEquivCore.

Section TypeDenote.

Lemma result_first_lc_lvars_shift_from k D :
  lc_lvars D ->
  lc_lvars (lvars_shift_from k D).
Proof.
  apply lvars_shift_from_lc.
Qed.

Lemma result_first_lvars_shift_from_lc_eq k D :
  lc_lvars D ->
  lvars_shift_from k D = D.
Proof.
  apply lvars_shift_from_lc_eq.
Qed.

Lemma result_first_lvars_lc_at_zero_of_lc D :
  lc_lvars D ->
  lvars_lc_at 0 D.
Proof.
  intros Hlc k Hk.
  rewrite lvars_bv_elem in Hk.
  exfalso. exact (Hlc (LVBound k) Hk).
Qed.

Lemma result_first_forall_impl_open_elim
    (m my : WfWorldT) y P Q :
  m ⊨ FForall (FImpl P Q) ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y P ->
  my ⊨ formula_open 0 y Q.
Proof.
  intros Hall Hy Hdom Hrestrict HP.
  pose proof (res_models_forall_open_named_fresh
    m my y (FImpl P Q) Hall Hy Hdom Hrestrict) as Hopen.
  cbn [formula_open] in Hopen.
  eapply res_models_impl_elim; eauto.
Qed.

Lemma formula_fv_open_arrow_value_body_obs
    gas (Σ : lty_env) τx τr f :
  formula_fv
    (arrow_value_denote_gas_with ty_denote_gas gas Σ τx τr
      (tret (vfvar f))) ⊆
  lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪ {[f]}.
Proof.
  unfold formula_fv, formula_lvars, arrow_value_denote_gas_with.
  cbn [formula_lvars_at].
  rewrite lvars_fv_union.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) as Harg.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty τx))
    τr
    (tapp_tm (tm_shift 0 (tret (vfvar f))) (vbvar 0))) as Hres.
  apply lvars_fv_mono in Harg.
  apply lvars_fv_mono in Hres.
  rewrite !lvars_fv_union in Harg, Hres.
  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg, Hres.
  rewrite fv_tapp_tm, tm_shift_fv in Hres.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Harg, Hres |- *.
  rewrite lvars_fv_union.
  rewrite !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [Ha_arg | Ha_res].
  - specialize (Harg a Ha_arg).
    repeat rewrite elem_of_union in Harg.
    repeat rewrite elem_of_empty in Harg.
    destruct Harg as [Hbad | Harg]; [contradiction|].
    rewrite cty_shift_fv in Harg.
    repeat rewrite elem_of_union. left. left. exact Harg.
  - specialize (Hres a Ha_res).
    repeat rewrite elem_of_union in Hres.
    repeat rewrite elem_of_empty in Hres.
    repeat rewrite elem_of_union.
    destruct Hres as [[Hres | Hbad] | Hres].
    + right. exact Hres.
    + contradiction.
    + left. right. exact Hres.
Qed.

Lemma formula_scoped_arrow_value_body_obs
    gas (Σ : lty_env) τx τr f (m : WfWorldT) :
  lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪ {[f]} ⊆
    world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (arrow_value_denote_gas_with ty_denote_gas gas Σ τx τr
      (tret (vfvar f))).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_open_arrow_value_body_obs|].
  exact Hsub.
Qed.

Lemma formula_scoped_open_arrow_value_body_obs
    gas (Σ : lty_env) τx τr f (m : WfWorldT) :
  lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪ {[f]} ⊆
    world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (formula_open 0 f
      (arrow_value_denote_gas_with ty_denote_gas gas Σ
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0)))).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_open_fv_subset|].
  etransitivity; [|exact Hsub].
  unfold formula_fv, formula_lvars, arrow_value_denote_gas_with.
  cbn [formula_lvars_at].
  rewrite lvars_fv_union.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty (cty_shift 0 τx)))
    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty (cty_shift 0 τx)))
    (cty_shift 1 τr)
    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))) as Hres.
  apply lvars_fv_mono in Harg.
  apply lvars_fv_mono in Hres.
  rewrite !lvars_fv_union in Harg, Hres.
  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg, Hres.
  rewrite !cty_shift_fv in Harg, Hres.
  rewrite fv_tapp_tm, tm_shift_fv in Hres.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Harg, Hres |- *.
  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [[Ha_arg | Ha_res] | Ha_f].
  - specialize (Harg a Ha_arg). rewrite cty_shift_fv in Harg. set_solver.
  - specialize (Hres a Ha_res). try rewrite cty_shift_fv in Hres. set_solver.
  - set_solver.
Qed.

Lemma result_first_result_body_relevant_subset τtop τr e f y :
  cty_lc_at 1 τr ->
  context_ty_lvars_at 1 τr ⊆ context_ty_lvars τtop ->
  y ∉ fv_cty τr ->
  (context_ty_lvars (cty_open 0 y τr) ∪
    tm_lvars (tapp_tm (tret (vfvar f)) (vfvar y))) ∖
    {[LVFree y]} ∖ {[LVFree f]} ⊆
  context_ty_lvars τtop ∪ tm_lvars e.
Proof.
  intros Hlcτr Hτr_top Hyfresh v Hv.
  apply elem_of_difference in Hv as [Hv Hvf].
  apply elem_of_difference in Hv as [Hv Hvy].
  apply elem_of_union in Hv as [Hvτ | Hve].
  - apply elem_of_union_l.
    apply Hτr_top.
    assert (HlcD : lc_lvars (context_ty_lvars_at 1 τr)).
    {
      apply lc_lvars_no_bv.
      apply cty_lc_at_lvars_bv_empty. exact Hlcτr.
    }
    assert (HyD : LVFree y ∉ context_ty_lvars_at 1 τr).
    {
      intros HyD.
      apply Hyfresh.
      rewrite <- (context_ty_lvars_fv_at 1 τr).
      apply lvars_fv_elem. exact HyD.
    }
    pose proof (cty_lvars_open_body_closed_no_fresh
      (context_ty_lvars_at 1 τr) τr y HlcD HyD
      ltac:(set_solver) v) as Hsubset.
    apply Hsubset.
    apply elem_of_difference. split; [exact Hvτ|exact Hvy].
  - cbn [tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at
          lvar_value_keys] in Hve.
    rewrite tm_lvars_tapp_tm_fvar in Hve.
    cbn [tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at
          lvar_value_keys] in Hve.
    set_solver.
Qed.

Lemma result_first_result_env_agree_general
    gas (Σ : lty_env) τtop τbody ebody e1 e2 Ty Tf
    (my : WfWorldT) f y :
  (context_ty_lvars τbody ∪ tm_lvars ebody) ∖
    {[LVFree y]} ∖ {[LVFree f]} ⊆
    context_ty_lvars τtop ∪ tm_lvars e1 ->
  (context_ty_lvars τbody ∪ tm_lvars ebody) ∖
    {[LVFree y]} ∖ {[LVFree f]} ⊆
    context_ty_lvars τtop ∪ tm_lvars e2 ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := Ty]>
      (<[LVFree f := Tf]>
        (relevant_env Σ τtop e1)))
    τbody ebody ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := Ty]>
      (<[LVFree f := Tf]>
        (relevant_env Σ τtop e2)))
    τbody ebody.
Proof.
  intros Hsub1 Hsub2 Hres.
  pose proof (ty_denote_gas_env_agree_on gas
    (<[LVFree y := Ty]> (<[LVFree f := Tf]> (relevant_env Σ τtop e1)))
    (<[LVFree y := Ty]> (<[LVFree f := Tf]> (relevant_env Σ τtop e2)))
    τbody ebody (context_ty_lvars τbody ∪ tm_lvars ebody)
    ltac:(reflexivity)) as Hagree.
  rewrite Hagree in Hres; [exact Hres|].
  unfold lty_env_restrict_lvars, relevant_env.
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ context_ty_lvars τbody ∪ tm_lvars ebody)) as [HvX|HvX];
    [|reflexivity].
  destruct (decide (v = LVFree y)) as [->|Hvy].
  { rewrite !lookup_insert. repeat case_decide; try congruence; reflexivity. }
  rewrite !lookup_insert_ne by congruence.
  destruct (decide (v = LVFree f)) as [->|Hvf].
  { rewrite !lookup_insert. repeat case_decide; try congruence; reflexivity. }
  rewrite !lookup_insert_ne by congruence.
  assert (Hvsmall :
      v ∈ (context_ty_lvars τbody ∪ tm_lvars ebody) ∖
        {[LVFree y]} ∖ {[LVFree f]}) by set_solver.
  pose proof (Hsub1 v Hvsmall) as Hvrel1.
  pose proof (Hsub2 v Hvsmall) as Hvrel2.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ context_ty_lvars τtop ∪ tm_lvars e1))
    as [_|Hbad]; [|exfalso; exact (Hbad Hvrel1)].
  destruct (decide (v ∈ context_ty_lvars τtop ∪ tm_lvars e2))
    as [_|Hbad]; [|exfalso; exact (Hbad Hvrel2)].
  reflexivity.
Qed.

Lemma formula_fv_open_wand_value_body_obs
    gas (Σ : lty_env) τx τr f :
  formula_fv
    (wand_value_denote_gas_with ty_denote_gas gas Σ τx τr
      (tret (vfvar f))) ⊆
  lvars_fv (context_ty_lvars (CTWand τx τr)) ∪ {[f]}.
Proof.
  unfold formula_fv, formula_lvars, wand_value_denote_gas_with.
  cbn [formula_lvars_at].
  rewrite lvars_fv_union.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) as Harg.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty τx))
    τr
    (tapp_tm (tm_shift 0 (tret (vfvar f))) (vbvar 0))) as Hres.
  apply lvars_fv_mono in Harg.
  apply lvars_fv_mono in Hres.
  rewrite !lvars_fv_union in Harg, Hres.
  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg, Hres.
  rewrite fv_tapp_tm, tm_shift_fv in Hres.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Harg, Hres |- *.
  rewrite lvars_fv_union.
  rewrite !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [Ha_arg | Ha_res].
  - specialize (Harg a Ha_arg).
    repeat rewrite elem_of_union in Harg.
    repeat rewrite elem_of_empty in Harg.
    destruct Harg as [Hbad | Harg]; [contradiction|].
    rewrite cty_shift_fv in Harg.
    repeat rewrite elem_of_union. left. left. exact Harg.
  - specialize (Hres a Ha_res).
    repeat rewrite elem_of_union in Hres.
    repeat rewrite elem_of_empty in Hres.
    repeat rewrite elem_of_union.
    destruct Hres as [[Hres | Hbad] | Hres].
    + right. exact Hres.
    + contradiction.
    + left. right. exact Hres.
Qed.

Lemma formula_scoped_wand_value_body_obs
    gas (Σ : lty_env) τx τr f (m : WfWorldT) :
  lvars_fv (context_ty_lvars (CTWand τx τr)) ∪ {[f]} ⊆
    world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (wand_value_denote_gas_with ty_denote_gas gas Σ τx τr
      (tret (vfvar f))).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_open_wand_value_body_obs|].
  exact Hsub.
Qed.

Lemma formula_scoped_open_wand_value_body_obs
    gas (Σ : lty_env) τx τr f (m : WfWorldT) :
  lvars_fv (context_ty_lvars (CTWand τx τr)) ∪ {[f]} ⊆
    world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (formula_open 0 f
      (wand_value_denote_gas_with ty_denote_gas gas Σ
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0)))).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_open_fv_subset|].
  etransitivity; [|exact Hsub].
  unfold formula_fv, formula_lvars, wand_value_denote_gas_with.
  cbn [formula_lvars_at].
  rewrite lvars_fv_union.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty (cty_shift 0 τx)))
    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind Σ (erase_ty (cty_shift 0 τx)))
    (cty_shift 1 τr)
    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))) as Hres.
  apply lvars_fv_mono in Harg.
  apply lvars_fv_mono in Hres.
  rewrite !lvars_fv_union in Harg, Hres.
  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg, Hres.
  rewrite !cty_shift_fv in Harg, Hres.
  rewrite fv_tapp_tm, tm_shift_fv in Hres.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Harg, Hres |- *.
  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [[Ha_arg | Ha_res] | Ha_f].
  - specialize (Harg a Ha_arg). rewrite cty_shift_fv in Harg. set_solver.
  - specialize (Hres a Ha_res). try rewrite cty_shift_fv in Hres. set_solver.
  - set_solver.
Qed.

Lemma formula_fv_open_persist_value_body_obs
    gas (Σ : lty_env) τ f :
  formula_fv
    (formula_open 0 f
      (FPersist
        (ty_denote_gas gas
          (typed_lty_env_bind Σ (erase_ty τ))
          (cty_shift 0 τ) (tret (vbvar 0))))) ⊆
  lvars_fv (context_ty_lvars (CTPersist τ)) ∪ {[f]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
  cbn [formula_fv].
  pose proof (ty_denote_gas_fv_subset gas
    (typed_lty_env_bind Σ (erase_ty τ))
    (cty_shift 0 τ) (tret (vbvar 0))) as Hbody.
  rewrite cty_shift_fv in Hbody.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Hbody |- *.
  intros a Ha.
  rewrite formula_fv_persist in Ha.
  repeat rewrite elem_of_union.
  apply elem_of_union in Ha as [Ha|Ha].
  - specialize (Hbody a Ha). set_solver.
  - set_solver.
Qed.

Lemma formula_scoped_open_persist_value_body_obs
    gas (Σ : lty_env) τ f (m : WfWorldT) :
  lvars_fv (context_ty_lvars (CTPersist τ)) ∪ {[f]} ⊆
    world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (formula_open 0 f
      (FPersist
        (ty_denote_gas gas
          (typed_lty_env_bind Σ (erase_ty τ))
          (cty_shift 0 τ) (tret (vbvar 0))))).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_open_persist_value_body_obs|].
  exact Hsub.
Qed.

Lemma formula_fv_persist_value_body_obs
    gas (Σ : lty_env) τ f :
  formula_fv
    (FPersist
      (ty_denote_gas gas (<[LVFree f := erase_ty τ]> Σ)
        τ (tret (vfvar f)))) ⊆
  lvars_fv (context_ty_lvars (CTPersist τ)) ∪ {[f]}.
Proof.
  cbn [formula_fv].
  pose proof (ty_denote_gas_fv_subset gas
    (<[LVFree f := erase_ty τ]> Σ) τ (tret (vfvar f))) as Hbody.
  intros a Ha.
  rewrite formula_fv_persist in Ha.
  specialize (Hbody a Ha).
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in Hbody |- *.
  set_solver.
Qed.

Lemma formula_scoped_persist_value_body_obs
    gas (Σ : lty_env) τ f (m : WfWorldT) :
  lvars_fv (context_ty_lvars (CTPersist τ)) ∪ {[f]} ⊆
    world_dom (m : WorldT) ->
  formula_scoped_in_world m
    (FPersist
      (ty_denote_gas gas (<[LVFree f := erase_ty τ]> Σ)
        τ (tret (vfvar f)))).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_persist_value_body_obs|].
  exact Hsub.
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
  change (@open_one atom context_ty open_cty_atom_inst 0 f (cty_shift 0 τx))
    with (cty_open 0 f (cty_shift 0 τx)).
  rewrite (cty_open_shift_from_lc_fresh 0 f τx Hlcτx Hfτx).
  rewrite (cty_open_shift_from_lc_fresh 1 f τr Hlcτr Hfτr).
  reflexivity.
Qed.

Lemma formula_open_wand_value_ret_bvar0
    gas (Σ : lty_env) τx τr f :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ->
  f ∉ fv_cty τr ->
  formula_open 0 f
    (wand_value_denote_gas_with ty_denote_gas gas Σ τx τr
      (tret (vbvar 0))) =
  wand_value_denote_gas_with ty_denote_gas gas Σ τx τr
    (tret (vfvar f)).
Proof.
  intros HΣclosed HfΣ Hlcτx Hlcτr Hfτx Hfτr.
  unfold wand_value_denote_gas_with.
  rewrite formula_open_fbwand.
  change (0 + 1) with 1.
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

Lemma formula_open_result_first_wand_value_ret_bvar0
    gas (Σ : lty_env) τx τr Tf f :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ->
  f ∉ fv_cty τr ->
  formula_open 0 f
    (wand_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))) =
  wand_value_denote_gas_with ty_denote_gas gas
    (<[LVFree f := Tf]> Σ) τx τr (tret (vfvar f)).
Proof.
  intros HΣclosed HfΣ Hlcτx Hlcτr Hfτx Hfτr.
  unfold wand_value_denote_gas_with.
  rewrite formula_open_fbwand.
  change (0 + 1) with 1.
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
  change (@open_one atom context_ty open_cty_atom_inst 0 f (cty_shift 0 τx))
    with (cty_open 0 f (cty_shift 0 τx)).
  rewrite (cty_open_shift_from_lc_fresh 0 f τx Hlcτx Hfτx).
  rewrite (cty_open_shift_from_lc_fresh 1 f τr Hlcτr Hfτr).
  reflexivity.
Qed.

Lemma arrow_value_open_arg_to_regular_imp
    gas (Σ : lty_env) τx τr Tf f y (my0 my : WfWorldT) :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  f <> y ->
  LVFree y ∉ dom (<[LVFree f := Tf]> Σ : lty_env) ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my0 ⊨ arrow_value_denote_gas_with ty_denote_gas gas
    (<[LVFree f := Tf]> Σ) τx τr (tret (vfvar f)) ->
  y ∉ world_dom (my0 : WorldT) ->
  world_dom (my : WorldT) = world_dom (my0 : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (my0 : WorldT)) = my0 ->
  my ⊨ FImpl
    (ty_denote_gas gas
      (<[LVFree y := erase_ty τx]> (<[LVFree f := Tf]> Σ))
      τx (tret (vfvar y)))
    (ty_denote_gas gas
      (<[LVFree y := erase_ty τx]> (<[LVFree f := Tf]> Σ))
      (cty_open 0 y τr)
      (tapp_tm (tret (vfvar f)) (vfvar y))).
Proof.
  intros HΣclosed HfΣ Hfy HyΣ Hlcτx Hlcτr Hffresh Hyfresh
    Hvalue Hyfresh_world Hdom Hrestrict.
  cbn [arrow_value_denote_gas arrow_value_denote_gas_with] in Hvalue.
  pose proof (res_models_forall_open_named_fresh
    my0 my y
    (FImpl
      (ty_denote_gas gas
        (typed_lty_env_bind (<[LVFree f := Tf]> Σ) (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))
      (ty_denote_gas gas
        (typed_lty_env_bind (<[LVFree f := Tf]> Σ) (erase_ty τx))
        τr (tapp_tm (tm_shift 0 (tret (vfvar f))) (vbvar 0))))
    Hvalue Hyfresh_world Hdom Hrestrict) as Hinner.
  cbn [formula_open] in Hinner.
  rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
    y gas (<[LVFree f := Tf]> Σ) τx) in Hinner.
  2:{ apply lty_env_closed_insert_free. exact HΣclosed. }
  2:{ exact HyΣ. }
  2:{ clear -Hyfresh. set_solver. }
  2:{ exact Hlcτx. }
  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
    y gas (<[LVFree f := Tf]> Σ) τr (erase_ty τx)
    (tret (vfvar f))) in Hinner.
  2:{ apply lty_env_closed_insert_free. exact HΣclosed. }
  2:{ exact HyΣ. }
  2:{ cbn [fv_tm fv_value]. clear -Hfy. set_solver. }
  2:{ clear -Hyfresh. set_solver. }
  2:{ constructor. constructor. }
  exact Hinner.
Qed.

Lemma result_first_fun_arg_open_to_inserted_env
    gas (Σ : lty_env) τx Tf
    (my : WfWorldT) f y :
  lty_env_closed Σ ->
  LVFree f ∉ dom (Σ : lty_env) ->
  LVFree y ∉ dom (Σ : lty_env) ->
  f <> y ->
  lc_context_ty τx ->
  f ∉ fv_cty τx ->
  y ∉ fv_cty τx ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind Σ Tf)
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτx Hfτx Hyτx Harg.
  rewrite (formula_open_result_first_fun_arg_two gas Σ τx Tf f y) in Harg.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτx.
  2: exact Hfτx.
  2: exact Hyτx.
  rewrite lvar_store_insert_free_commute in Harg by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)) f Tf) in Harg.
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

Lemma result_first_fun_arg_inserted_env_to_open
    gas (Σ : lty_env) τx Tf
    (my : WfWorldT) f y :
  lty_env_closed Σ ->
  LVFree f ∉ dom (Σ : lty_env) ->
  LVFree y ∉ dom (Σ : lty_env) ->
  f <> y ->
  lc_context_ty τx ->
  f ∉ fv_cty τx ->
  y ∉ fv_cty τx ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)) ->
  my ⊨ formula_open 0 y
    (formula_open 1 f
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind Σ Tf)
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))).
Proof.
  intros HΣclosed HfΣ HyΣ Hfy Hlcτx Hfτx Hyτx Harg.
  rewrite (formula_open_result_first_fun_arg_two gas Σ τx Tf f y).
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2:{
    rewrite dom_insert_L.
    intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
    - apply elem_of_singleton in Hybad. congruence.
    - exact (HyΣ Hybad).
  }
  2: exact Hlcτx.
  2: exact Hfτx.
  2: exact Hyτx.
  rewrite lvar_store_insert_free_commute by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]> Σ)
    τx (tret (vfvar y)) f Tf).
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

End TypeDenote.

Ltac result_first_open_norm :=
  repeat match goal with
  | |- context [formula_open 0 ?y
      (formula_open 1 ?f
        (ty_denote_gas ?gas
          (typed_lty_env_bind (typed_lty_env_bind ?Σ ?Tf)
            (erase_ty (cty_shift 0 ?τx)))
          (cty_shift 0 (cty_shift 0 ?τx)) (tret (vbvar 0))))] =>
      rewrite (formula_open_result_first_fun_arg_two gas Σ τx Tf f y)
        by (try eassumption; try congruence; try set_solver)
  | H : context [formula_open 0 ?y
      (formula_open 1 ?f
        (ty_denote_gas ?gas
          (typed_lty_env_bind (typed_lty_env_bind ?Σ ?Tf)
            (erase_ty (cty_shift 0 ?τx)))
          (cty_shift 0 (cty_shift 0 ?τx)) (tret (vbvar 0))))] |- _ =>
      rewrite (formula_open_result_first_fun_arg_two gas Σ τx Tf f y) in H
        by (try eassumption; try congruence; try set_solver)
  | |- context [formula_open 0 ?y
      (formula_open 1 ?f
        (ty_denote_gas ?gas
          (typed_lty_env_bind (typed_lty_env_bind ?Σ ?Tf)
            (erase_ty (cty_shift 0 ?τx)))
          (cty_shift 1 ?τr)
          (tapp_tm (tret (vbvar 1)) (vbvar 0))))] =>
      rewrite (formula_open_result_first_fun_result_two gas Σ τx τr Tf f y)
        by (try eassumption; try congruence; try set_solver)
  | H : context [formula_open 0 ?y
      (formula_open 1 ?f
        (ty_denote_gas ?gas
          (typed_lty_env_bind (typed_lty_env_bind ?Σ ?Tf)
            (erase_ty (cty_shift 0 ?τx)))
          (cty_shift 1 ?τr)
          (tapp_tm (tret (vbvar 1)) (vbvar 0))))] |- _ =>
      rewrite (formula_open_result_first_fun_result_two gas Σ τx τr Tf f y) in H
        by (try eassumption; try congruence; try set_solver)
  | |- context [formula_open 0 ?f
      (arrow_value_denote_gas_with ty_denote_gas ?gas ?Σ ?τx ?τr
        (tret (vbvar 0)))] =>
      rewrite (formula_open_arrow_value_ret_bvar0 gas Σ τx τr f)
        by (try eassumption; try set_solver)
  | H : context [formula_open 0 ?f
      (arrow_value_denote_gas_with ty_denote_gas ?gas ?Σ ?τx ?τr
        (tret (vbvar 0)))] |- _ =>
      rewrite (formula_open_arrow_value_ret_bvar0 gas Σ τx τr f) in H
        by (try eassumption; try set_solver)
  | |- context [formula_open 0 ?f
      (arrow_value_denote_gas_with ty_denote_gas ?gas
        (typed_lty_env_bind ?Σ ?Tf)
        (cty_shift 0 ?τx) (cty_shift 1 ?τr)
        (tret (vbvar 0)))] =>
      rewrite (formula_open_result_first_arrow_value_ret_bvar0
        gas Σ τx τr Tf f) by (try eassumption; try set_solver)
  | H : context [formula_open 0 ?f
      (arrow_value_denote_gas_with ty_denote_gas ?gas
        (typed_lty_env_bind ?Σ ?Tf)
        (cty_shift 0 ?τx) (cty_shift 1 ?τr)
        (tret (vbvar 0)))] |- _ =>
      rewrite (formula_open_result_first_arrow_value_ret_bvar0
        gas Σ τx τr Tf f) in H by (try eassumption; try set_solver)
  | |- context [formula_open 0 ?f
      (wand_value_denote_gas_with ty_denote_gas ?gas ?Σ ?τx ?τr
        (tret (vbvar 0)))] =>
      rewrite (formula_open_wand_value_ret_bvar0 gas Σ τx τr f)
        by (try eassumption; try set_solver)
  | H : context [formula_open 0 ?f
      (wand_value_denote_gas_with ty_denote_gas ?gas ?Σ ?τx ?τr
        (tret (vbvar 0)))] |- _ =>
      rewrite (formula_open_wand_value_ret_bvar0 gas Σ τx τr f) in H
        by (try eassumption; try set_solver)
  | |- context [formula_open 0 ?f
      (wand_value_denote_gas_with ty_denote_gas ?gas
        (typed_lty_env_bind ?Σ ?Tf)
        (cty_shift 0 ?τx) (cty_shift 1 ?τr)
        (tret (vbvar 0)))] =>
      rewrite (formula_open_result_first_wand_value_ret_bvar0
        gas Σ τx τr Tf f) by (try eassumption; try set_solver)
  | H : context [formula_open 0 ?f
      (wand_value_denote_gas_with ty_denote_gas ?gas
        (typed_lty_env_bind ?Σ ?Tf)
        (cty_shift 0 ?τx) (cty_shift 1 ?τr)
        (tret (vbvar 0)))] |- _ =>
      rewrite (formula_open_result_first_wand_value_ret_bvar0
        gas Σ τx τr Tf f) in H by (try eassumption; try set_solver)
  end;
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with
        wand_value_denote_gas wand_value_denote_gas_with] in *;
  denotation_open_norm.

Ltac result_first_open_norm_in H :=
  repeat match type of H with
  | context [formula_open 0 ?y
      (formula_open 1 ?f
        (ty_denote_gas ?gas
          (typed_lty_env_bind (typed_lty_env_bind ?Σ ?Tf)
            (erase_ty (cty_shift 0 ?τx)))
          (cty_shift 0 (cty_shift 0 ?τx)) (tret (vbvar 0))))] =>
      rewrite (formula_open_result_first_fun_arg_two gas Σ τx Tf f y) in H
        by (try eassumption; try congruence; try set_solver)
  | context [formula_open 0 ?y
      (formula_open 1 ?f
        (ty_denote_gas ?gas
          (typed_lty_env_bind (typed_lty_env_bind ?Σ ?Tf)
            (erase_ty (cty_shift 0 ?τx)))
          (cty_shift 1 ?τr)
          (tapp_tm (tret (vbvar 1)) (vbvar 0))))] =>
      rewrite (formula_open_result_first_fun_result_two gas Σ τx τr Tf f y) in H
        by (try eassumption; try congruence; try set_solver)
  | context [formula_open 0 ?f
      (arrow_value_denote_gas_with ty_denote_gas ?gas ?Σ ?τx ?τr
        (tret (vbvar 0)))] =>
      rewrite (formula_open_arrow_value_ret_bvar0 gas Σ τx τr f) in H
        by (try eassumption; try set_solver)
  | context [formula_open 0 ?f
      (arrow_value_denote_gas_with ty_denote_gas ?gas
        (typed_lty_env_bind ?Σ ?Tf)
        (cty_shift 0 ?τx) (cty_shift 1 ?τr)
        (tret (vbvar 0)))] =>
      rewrite (formula_open_result_first_arrow_value_ret_bvar0
        gas Σ τx τr Tf f) in H by (try eassumption; try set_solver)
  | context [formula_open 0 ?f
      (wand_value_denote_gas_with ty_denote_gas ?gas ?Σ ?τx ?τr
        (tret (vbvar 0)))] =>
      rewrite (formula_open_wand_value_ret_bvar0 gas Σ τx τr f) in H
        by (try eassumption; try set_solver)
  | context [formula_open 0 ?f
      (wand_value_denote_gas_with ty_denote_gas ?gas
        (typed_lty_env_bind ?Σ ?Tf)
        (cty_shift 0 ?τx) (cty_shift 1 ?τr)
        (tret (vbvar 0)))] =>
      rewrite (formula_open_result_first_wand_value_ret_bvar0
        gas Σ τx τr Tf f) in H by (try eassumption; try set_solver)
  end;
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with
        wand_value_denote_gas wand_value_denote_gas_with] in H;
  denotation_open_norm_in H.
