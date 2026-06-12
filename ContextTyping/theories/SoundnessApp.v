(** * ContextTyping.SoundnessApp

    App proof support for the direct Fundamental theorem.
    Keeping this case in a focused file makes timing diagnostics local and
    avoids re-checking the full Fundamental dispatch while proving Arrow
    application transport. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivTerm
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma app_arrow_arg_to_opened_antecedent
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ formula_open 0 x
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros Hwf_fun Hfresh Harg.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)) in *.
  assert (Hxlookup : Δ !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup (cty_depth τx) Δ τx x m Harg). }
  assert (Hopen_env_fresh :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ (CTArrow τx τ) (tret v1)) (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_fv_subset
      Δ (CTArrow τx τ) (tret v1)) as Hrel_fv.
    intros Hbad.
    apply Hrel_fv in Hbad.
    exfalso. apply Hfresh.
    cbn [fv_tm fv_value] in Hbad.
    unfold fv_cty in Hbad.
    cbn [context_ty_lvars context_ty_lvars_at] in Hbad.
    rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hbad.
    better_set_solver.
  }
  assert (Hopen_tm_fresh : x ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  assert (Hopen_ty_fresh : x ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. better_set_solver. }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ (CTArrow τx τ) (tret v1)) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))
    Hopen_env_fresh Hopen_tm_fresh Hopen_ty_fresh).
  change (open_tm 0 (vfvar x) (tret (vbvar 0))) with (tret (vfvar x)).
  assert (Hτx_norm : cty_open 0 x (cty_shift 0 τx) = τx).
  {
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret v1) (CTArrow τx τ) Hwf_fun) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    apply cty_open_shift_from_lc_fresh.
    - eapply wf_context_ty_at_lc. exact Hτx.
    - better_set_solver.
  }
  rewrite Hτx_norm.
  assert (Hrel_env_fresh :
      LVFree x ∉ dom (relevant_env Δ (CTArrow τx τ) (tret v1) : lty_env)).
  {
    apply relevant_env_arrow_fresh_free; better_set_solver.
  }
  assert (Hrel_env_closed :
      lty_env_closed (relevant_env Δ (CTArrow τx τ) (tret v1))).
  { apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  rewrite (typed_lty_env_bind_open_current
    x (relevant_env Δ (CTArrow τx τ) (tret v1)) (erase_ty τx)
    Hrel_env_fresh Hrel_env_closed).
  assert (Harg_big :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        Δ τx (tret (vfvar x))).
  {
    rewrite ty_denote_gas_saturate by (cbn [cty_depth]; lia).
    exact Harg.
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    Δ
    (<[LVFree x := erase_ty τx]>
      (relevant_env Δ (CTArrow τx τ) (tret v1)))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x))) m).
  - reflexivity.
  - apply lty_env_restrict_relevant_arrow_arg_insert_eq; assumption.
  - exact Harg_big.
Qed.

Lemma app_arrow_result_to_target
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ formula_open 0 x
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret v1))
          (erase_ty τx))
        τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))) ->
  m ⊨ ty_denote_gas (cty_depth ({0 ~> x} τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma app_arrow_open_result_from_fresh_drop
    Σ Γ τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth (CTArrow τx τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret v1) ->
  m ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ))
        τx (tret (vfvar x)) ->
  m ⊨ ty_denote_gas (cty_depth ({0 ~> x} τ))
        (atom_env_to_lty_env (erase_ctx Γ))
        ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fundamental_app_case Σ Γ τx τ v1 x :
  context_typing_wf Σ Γ (tret v1) (CTArrow τx τ) ->
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τx (tret (vfvar x))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf_fun Hwf Hfresh HfunIH HargIH m Hctx.
  pose proof (HfunIH m Hctx) as Hfun.
  pose proof (HargIH m Hctx) as Harg.
  unfold ty_denote_under, ty_denote in Hfun, Harg |- *.
  eapply app_arrow_open_result_from_fresh_drop; eauto.
Qed.
