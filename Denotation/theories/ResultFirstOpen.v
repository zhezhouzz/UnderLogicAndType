(** * Denotation.ResultFirstOpen

    Shared opening and scope facts for result-first Arrow/Wand denotations. *)

From Denotation Require Import Notation TypeDenote.

Section TypeDenote.

Lemma result_first_lc_lvars_shift_from k D :
  lc_lvars D ->
  lc_lvars (lvars_shift_from k D).
Proof.
  intros Hlc v Hv.
  unfold lvars_shift_from in Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  destruct u as [n|x]; cbn [logic_var_shift_from].
  - destruct (decide (k <= n)); exfalso; exact (Hlc (LVBound n) Hu).
  - exact I.
Qed.

Lemma result_first_lvars_shift_from_lc_eq k D :
  lc_lvars D ->
  lvars_shift_from k D = D.
Proof.
  intros Hlc.
  apply set_eq. intros v. split.
  - unfold lvars_shift_from.
    intros Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    destruct u as [n|x]; cbn [logic_var_shift_from].
    + destruct (decide (k <= n)); exfalso; exact (Hlc (LVBound n) Hu).
    + exact Hu.
  - intros Hv.
    unfold lvars_shift_from.
    destruct v as [n|x].
    + exfalso. exact (Hlc (LVBound n) Hv).
    + apply elem_of_map. exists (LVFree x). split; [reflexivity|exact Hv].
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
    (formula_open 0 f
      (arrow_value_denote_gas_with ty_denote_gas gas Σ
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0)))) ⊆
  lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪ {[f]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
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
  rewrite lvars_fv_union.
  rewrite !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [[Ha|Ha]|Ha].
  - specialize (Harg a Ha). rewrite cty_shift_fv in Harg. set_solver.
  - specialize (Hres a Ha). try rewrite cty_shift_fv in Hres. set_solver.
  - set_solver.
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
  etransitivity; [apply formula_fv_open_arrow_value_body_obs|].
  exact Hsub.
Qed.

Lemma result_first_result_body_relevant_subset τtop τr e f y :
  cty_lc_at 1 τr ->
  context_ty_lvars_at 1 τr ⊆ context_ty_lvars τtop ->
  y ∉ fv_cty τr ->
  relevant_lvars (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ∖ {[LVFree y]} ∖ {[LVFree f]} ⊆
  relevant_lvars τtop e.
Proof.
  intros Hlcτr Hτr_top Hyfresh v Hv.
  apply elem_of_difference in Hv as [Hv Hvf].
  apply elem_of_difference in Hv as [Hv Hvy].
  unfold relevant_lvars in Hv |- *.
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

Lemma formula_fv_open_wand_value_body_obs
    gas (Σ : lty_env) τx τr f :
  formula_fv
    (formula_open 0 f
      (wand_value_denote_gas_with ty_denote_gas gas Σ
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0)))) ⊆
  lvars_fv (context_ty_lvars (CTWand τx τr)) ∪ {[f]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
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
  rewrite lvars_fv_union.
  rewrite !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [[Ha|Ha]|Ha].
  - specialize (Harg a Ha). rewrite cty_shift_fv in Harg. set_solver.
  - specialize (Hres a Ha). try rewrite cty_shift_fv in Hres. set_solver.
  - set_solver.
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
  etransitivity; [apply formula_fv_open_wand_value_body_obs|].
  exact Hsub.
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
  my0 ⊨ formula_open 0 f
    (arrow_value_denote_gas gas
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 τx) (cty_shift 1 τr) (tret (vbvar 0))) ->
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
  cbn [arrow_value_denote_gas arrow_value_denote_gas_with formula_open]
    in Hvalue.
  pose proof (res_models_forall_open_named_fresh
    my0 my y
    (FImpl
      (formula_open 1 f
        (ty_denote_gas gas
          (typed_lty_env_bind (typed_lty_env_bind Σ Tf)
            (erase_ty (cty_shift 0 τx)))
          (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))))
      (formula_open 1 f
        (ty_denote_gas gas
          (typed_lty_env_bind (typed_lty_env_bind Σ Tf)
            (erase_ty (cty_shift 0 τx)))
          (cty_shift 1 τr)
          (tapp_tm (tret (vbvar 1)) (vbvar 0)))))
    Hvalue Hyfresh_world Hdom Hrestrict) as Hinner.
  cbn [formula_open] in Hinner.
  rewrite (formula_open_result_first_fun_arg_two gas Σ τx Tf f y)
    in Hinner.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2: exact HyΣ.
  2: exact Hlcτx.
  2: set_solver.
  2: set_solver.
  rewrite (formula_open_result_first_fun_result_two gas Σ τx τr Tf f y)
    in Hinner.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: congruence.
  2: exact HyΣ.
  2: exact Hlcτr.
  2: exact Hffresh.
  2: exact Hyfresh.
  exact Hinner.
Qed.

Ltac result_first_open_norm :=
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with
        wand_value_denote_gas wand_value_denote_gas_with] in *;
  denotation_open_norm.

Ltac result_first_open_norm_in H :=
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with
        wand_value_denote_gas wand_value_denote_gas_with] in H;
  denotation_open_norm_in H.

End TypeDenote.
