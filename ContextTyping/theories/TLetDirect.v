(** * ContextTyping.TLetDirect

    The new TLet bridge is intentionally a one-hop wrapper around
    [Denotation.TLet.tlet_intro_denotation].  It does not depend on the old
    continuation/reduction helper stack. *)

From CoreLang Require Import BasicTyping.
From ContextAlgebra Require Import ResourceInterfaceExtension ResourceExtensionCore.
From ContextTyping Require Export RegularDenotation.
From ContextTyping Require Import Naming.
From ContextBasicDenotation Require Import StoreTyping TermTLet Qualifier BasicTypingFormula.
From Denotation Require Import Context ContextTypeDenotationSaturate TLet.

Lemma denot_tlet_direct_in_ctx
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) e1 e2
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ))
          τ2 (tlete e1 e2)) ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  LVFree x ∉ dom (atom_env_to_lty_env (erase_ctx_under Σ Γ)) ∪
    context_ty_lvars τ2 ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
          τ2 (e2 ^^ x) ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros He1 Hlet HFx Htotal Hworld Hxfresh Hxlvar Hext Hbody.
  unfold denot_ty_in_ctx_under, denot_ty in Hbody |- *.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1 Hxfresh) in Hbody.
  replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (erase_ctx_under Σ Γ)))
    with (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ))) in Hbody.
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  eapply tlet_intro_denotation; eauto.
  - apply atom_store_to_lvar_store_closed.
  - rewrite lvar_store_to_atom_store_atom_store. exact He1.
  - rewrite lvar_store_to_atom_store_atom_store. exact Hlet.
Qed.

Lemma denot_tlet_direct_total_model_in_ctx
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) e1 e2
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m ->
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 ->
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ))
          τ2 (tlete e1 e2)) ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  LVFree x ∉ dom (atom_env_to_lty_env (erase_ctx_under Σ Γ)) ∪
    context_ty_lvars τ2 ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
          τ2 (e2 ^^ x) ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hmodel He1 Hlet HFx Hworld Hxfresh Hxlvar Hext Hbody.
  eapply denot_tlet_direct_in_ctx; eauto.
  exact (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel).
Qed.
