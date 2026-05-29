(** * Denotation.ContextTypeDenotationTactics

    Shared proof-normalization tactics for context-type denotation formulas. *)

From Denotation Require Import Notation.
From Denotation Require Export ContextTypeDenotationOpenModels.

Ltac normalize_denotation_formula_fv :=
  repeat first
    [ rewrite formula_fv_true | rewrite formula_fv_false
    | rewrite formula_fv_and | rewrite formula_fv_or
    | rewrite formula_fv_impl | rewrite formula_fv_star
    | rewrite formula_fv_wand | rewrite formula_fv_plus
    | rewrite formula_fv_forall | rewrite formula_fv_over
    | rewrite formula_fv_under | rewrite formula_fv_fibvars ];
  rewrite ?formula_fv_context_ty_wf_formula;
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  store_normalize;
  type_syntax_norm;
  rewrite ?typed_lty_env_bind_lvars_fv_dom;
  rewrite ?tm_shift_fv, ?cty_shift_fv, ?fv_tapp_tm;
  cbn [formula_fv formula_lvars fv_tm fv_value];
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free,
    ?lvars_fv_difference_singleton_free;
  rewrite ?formula_fv_true, ?formula_fv_false, ?tm_lvars_fv,
    ?context_ty_lvars_fv.

Ltac normalize_denotation_formula_fv_in H :=
  repeat first
    [ rewrite formula_fv_true in H | rewrite formula_fv_false in H
    | rewrite formula_fv_and in H | rewrite formula_fv_or in H
    | rewrite formula_fv_impl in H | rewrite formula_fv_star in H
    | rewrite formula_fv_wand in H | rewrite formula_fv_plus in H
    | rewrite formula_fv_forall in H | rewrite formula_fv_over in H
    | rewrite formula_fv_under in H | rewrite formula_fv_fibvars in H ];
  rewrite ?formula_fv_context_ty_wf_formula in H;
  rewrite ?formula_fv_basic_world_formula in H;
  rewrite ?formula_fv_expr_basic_typing_formula in H;
  rewrite ?formula_fv_expr_total_formula in H;
  rewrite ?formula_fv_expr_result_formula in H;
  rewrite ?formula_fv_type_qualifier_formula in H;
  store_normalize;
  type_syntax_norm_in H;
  rewrite ?typed_lty_env_bind_lvars_fv_dom in H;
  rewrite ?tm_shift_fv, ?cty_shift_fv, ?fv_tapp_tm in H;
  cbn [formula_fv formula_lvars fv_tm fv_value] in H;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms,
    ?lvars_fv_singleton_bound, ?lvars_fv_singleton_free,
    ?lvars_fv_difference_singleton_free in H;
  rewrite ?formula_fv_true, ?formula_fv_false, ?tm_lvars_fv,
    ?context_ty_lvars_fv in H.

Ltac denot_ty_fv_norm :=
  cbn [denot_ty_lvar_gas denot_relevant_env lty_env_restrict_lvars
    denot_relevant_lvars];
  normalize_denotation_formula_fv.

Ltac denot_ty_fv_norm_in H :=
  cbn [denot_ty_lvar_gas denot_relevant_env lty_env_restrict_lvars
    denot_relevant_lvars] in H;
  normalize_denotation_formula_fv_in H.

Ltac denot_ty_fv_set :=
  denot_ty_fv_norm;
  match goal with
  | |- context [lvars_fv (dom (denot_relevant_env ?Σ ?τ ?e))] =>
      let Hrel := fresh "Hrel" in
      pose proof (denot_relevant_env_fv_subset Σ τ e) as Hrel
  | _ => idtac
  end;
  set_solver.
