(** * ContextTyping.TLetDenotation

    Compatibility names for the ContextTyping TLet case.

    The old version of this file routed through totality, expression
    continuations, and reduction helpers.  The new route is deliberately thin:
    the proof-facing bridge is [denot_tlet_direct_in_ctx], which directly calls
    [Denotation.TLet.tlet_intro_denotation]. *)

From CoreLang Require Import BasicTyping.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermTLet Qualifier BasicTypingFormula.
From Denotation Require Import ContextTypeDenotationSaturate.
From ContextTyping Require Export TLetDirect.

Lemma denot_tlet_semantic_direct
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) e1 e2
    (m mx : WfWorld (V := value)) (Fx : fiber_extension (V := value))
    (x : atom) :
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
  eapply denot_tlet_direct_in_ctx.
Qed.

(** The old [denot_tlet_semantic] shape quantified over context entailments and
    internally constructed the result extension.  Reintroducing that exact
    surface should be a small wrapper over [denot_tlet_direct_in_ctx], but it is
    intentionally not rebuilt through the old helper stack. *)
