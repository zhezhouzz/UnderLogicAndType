(** * Denotation.ContextTypeDenotationCasesPrimop

    Primitive-operation direct denotation support for Fundamental. *)

From Denotation Require Import Context ContextTypeDenotationSaturate
  ContextTypeDenotationCasesContext.

Section ContextTypeDenotationCasesPrimop.

Lemma appop_intro_denotation
    gas (Σ : gmap atom ty) op x τarg τres (m : WfWorldT) :
  cty_depth ({0 ~> x} τres) <= gas ->
  basic_context_ty ∅ τarg ->
  basic_context_ty ∅ τres ->
  Σ !! x = Some (erase_ty τarg) ->
  Σ ⊢ₑ
    tprim op (vfvar x) ⋮ erase_ty ({0 ~> x} τres) ->
  (denot_ctx (CtxBind x τarg) ⊫
    denot_ty_in_ctx (CtxBind x τarg) ({0 ~> x} τres)
      (tprim op (vfvar x))) ->
  m ⊨ denot_ty_lvar_gas (cty_depth τarg) (atom_env_to_lty_env Σ)
    τarg (tret (vfvar x)) ->
  m ⊨ denot_ty_lvar_gas gas
    (atom_env_to_lty_env Σ) ({0 ~> x} τres) (tprim op (vfvar x)).
Proof.
  intros Hgas Hbasic_arg Hbasic_res Hlookup _ Hop Harg.
  rewrite denot_ty_lvar_gas_saturate by exact Hgas.
  pose proof (res_models_denot_ty_lvar_gas_env_agree_on
    (cty_depth τarg)
    (atom_env_to_lty_env Σ)
    (atom_env_to_lty_env (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
    τarg (tret (vfvar x)) ({[LVFree x]}) m
    (denot_relevant_lvars_basic_ret_fvar_subset x τarg Hbasic_arg)
    (atom_env_to_lty_env_restrict_singleton_lookup
      Σ x (erase_ty τarg) Hlookup)
    Harg) as Harg_single.
  assert (Harg_bind : m ⊨ denot_ctx (CtxBind x τarg)).
  {
    eapply denot_ctx_bind_from_arg_denotation; eauto.
  }
  pose proof (Hop m Harg_bind) as Hres_single.
  unfold denot_ty_in_ctx, denot_ty in Hres_single.
  change (erase_ctx (CtxBind x τarg))
    with (<[x := erase_ty τarg]> (∅ : gmap atom ty)) in Hres_single.
  eapply res_models_denot_ty_lvar_gas_env_agree_on
    with (Σ1 := atom_env_to_lty_env
        (<[x := erase_ty τarg]> (∅ : gmap atom ty)))
      (X := {[LVFree x]});
    [ apply denot_relevant_lvars_basic_open_tprim_fvar_subset;
      exact Hbasic_res
    | symmetry;
      apply atom_env_to_lty_env_restrict_singleton_lookup;
      exact Hlookup
    | exact Hres_single ].
Qed.
End ContextTypeDenotationCasesPrimop.
