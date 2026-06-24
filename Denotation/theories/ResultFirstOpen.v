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

Lemma result_first_lvars_lc_at_zero_of_lc D :
  lc_lvars D ->
  lvars_lc_at 0 D.
Proof.
  intros Hlc k Hk.
  rewrite lvars_bv_elem in Hk.
  exfalso. exact (Hlc (LVBound k) Hk).
Qed.

Lemma formula_open_result_first_expr_result_formula_at_shift0 y D e :
  lc_lvars D ->
  y ∉ lvars_fv D ->
  lc_tm e ->
  y ∉ fv_tm e ->
  formula_open 0 y
    (expr_result_formula_at (lvars_shift_from 0 D)
      (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula_at D e (LVFree y).
Proof.
  intros HlcD HyD Hlce Hye.
  rewrite formula_open_expr_result_formula_at_shift0.
  - rewrite lvars_shift_from_lc_at_id; [reflexivity|].
    apply result_first_lvars_lc_at_zero_of_lc. exact HlcD.
  - apply result_first_lc_lvars_shift_from. exact HlcD.
  - rewrite lvars_shift_from_fv. exact HyD.
  - exact Hlce.
  - exact Hye.
Qed.

Definition result_first_outer_ret_value_formula
    (Σ : lty_env) τ vf z : FormulaT :=
  formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0 (dom (relevant_env Σ τ (tret vf))))
      (tm_shift 0 (tret vf)) (LVBound 0)).

Definition result_first_outer_ret_value_formula_norm
    (Σ : lty_env) τ vf z : FormulaT :=
  expr_result_formula_at
    (dom (relevant_env Σ τ (tret vf))) (tret vf) (LVFree z).

Definition opened_arrow_value_body_obs
    gas (Σ : lty_env) τx τr f : FormulaT :=
  formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas Σ
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))).

Definition opened_wand_value_body_obs
    gas (Σ : lty_env) τx τr f : FormulaT :=
  formula_open 0 f
    (wand_value_denote_gas_with ty_denote_gas gas Σ
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))).

Definition opened_persist_value_body_obs
    gas (Σ : lty_env) τ f : FormulaT :=
  formula_open 0 f
    (FPersist
      (ty_denote_gas gas
        (typed_lty_env_bind Σ (erase_ty τ))
        (cty_shift 0 τ) (tret (vbvar 0)))).

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

Lemma result_first_outer_ret_value_at
    (Σ : lty_env) τ vf z (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_value vf ->
  z ∉ fv_value vf ->
  z ∉ lvars_fv (dom (relevant_env Σ τ (tret vf))) ->
  m ⊨ result_first_outer_ret_value_formula Σ τ vf z ->
  m ⊨ result_first_outer_ret_value_formula_norm Σ τ vf z.
Proof.
  intros HΣclosed Hvf Hzvf Hzrel Hres.
  unfold result_first_outer_ret_value_formula,
    result_first_outer_ret_value_formula_norm in Hres |- *.
  assert (Hlc_tm : lc_tm (tret vf)) by (constructor; exact Hvf).
  assert (Hz_tm : z ∉ fv_tm (tret vf)).
  { cbn [fv_tm fv_value]. exact Hzvf. }
  rewrite formula_open_result_first_expr_result_formula_at_shift0 in Hres.
  - exact Hres.
  - apply relevant_env_closed. exact HΣclosed.
  - exact Hzrel.
  - exact Hlc_tm.
  - exact Hz_tm.
Qed.

Lemma result_first_outer_ret_value_at_open
    (Σ : lty_env) τ vf z (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_value vf ->
  z ∉ fv_value vf ->
  z ∉ lvars_fv (dom (relevant_env Σ τ (tret vf))) ->
  m ⊨ result_first_outer_ret_value_formula_norm Σ τ vf z ->
  m ⊨ result_first_outer_ret_value_formula Σ τ vf z.
Proof.
  intros HΣclosed Hvf Hzvf Hzrel Hres.
  unfold result_first_outer_ret_value_formula,
    result_first_outer_ret_value_formula_norm in Hres |- *.
  rewrite formula_open_result_first_expr_result_formula_at_shift0.
  - exact Hres.
  - apply relevant_env_closed. exact HΣclosed.
  - exact Hzrel.
  - constructor. exact Hvf.
  - cbn [fv_tm fv_value]. exact Hzvf.
Qed.

Lemma formula_fv_open_arrow_value_body_obs
    gas (Σ : lty_env) τx τr f :
  formula_fv (opened_arrow_value_body_obs gas Σ τx τr f) ⊆
  lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪ {[f]}.
Proof.
  unfold opened_arrow_value_body_obs.
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
    (opened_arrow_value_body_obs gas Σ τx τr f).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_open_arrow_value_body_obs|].
  exact Hsub.
Qed.

Lemma formula_fv_open_wand_value_body_obs
    gas (Σ : lty_env) τx τr f :
  formula_fv (opened_wand_value_body_obs gas Σ τx τr f) ⊆
  lvars_fv (context_ty_lvars (CTWand τx τr)) ∪ {[f]}.
Proof.
  unfold opened_wand_value_body_obs.
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
    (opened_wand_value_body_obs gas Σ τx τr f).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_open_wand_value_body_obs|].
  exact Hsub.
Qed.

Lemma formula_fv_open_persist_value_body_obs
    gas (Σ : lty_env) τ f :
  formula_fv (opened_persist_value_body_obs gas Σ τ f) ⊆
  lvars_fv (context_ty_lvars (CTPersist τ)) ∪ {[f]}.
Proof.
  unfold opened_persist_value_body_obs.
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
    (opened_persist_value_body_obs gas Σ τ f).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  etransitivity; [apply formula_fv_open_persist_value_body_obs|].
  exact Hsub.
Qed.

Ltac result_first_open_norm :=
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with
        wand_value_denote_gas wand_value_denote_gas_with] in *;
  rewrite ?formula_open_result_first_expr_result_formula_at_shift0 in * by eauto;
  rewrite ?formula_open_expr_result_formula_at_shift0 in *;
  try denotation_open_norm.

End TypeDenote.
