(** * Denotation.ResultFirstOpen

    Shared opening and scope facts for result-first Arrow/Wand denotations. *)

From Denotation Require Import Notation TypeDenote.

Section TypeDenote.

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

Ltac result_first_open_norm :=
  cbn [formula_open arrow_value_denote_gas arrow_value_denote_gas_with
        wand_value_denote_gas wand_value_denote_gas_with] in *;
  rewrite ?formula_open_expr_result_formula_at_shift0 in *.

End TypeDenote.

