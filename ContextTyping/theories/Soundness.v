(** * ContextTyping.Soundness

    Soundness entry points for the current denotation route. *)

From CoreLang Require Import BasicTyping.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermTLet Qualifier BasicTypingFormula.
From Denotation Require Import ContextTypeDenotationSaturate.
From ContextTyping Require Export TLet.

(** * ContextTyping.SoundnessDirect

    A compile-facing soundness entry for the new route.  The point of this
    file is to make the TLet case consume [TLetDenotation] directly while the
    broad old [Soundness.v]/[SoundnessCommon.v] surface is being retired. *)


Lemma fundamental_let_case_direct
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
  eapply denot_tlet_semantic_direct.
Qed.

(** The full induction will be restored case by case.  Non-TLet cases are not
    part of this checkpoint; the current branch only wires the TLet rule to the
    new denotation route, without exporting a fake top-level skeleton. *)

(** * ContextTyping.Soundness

    Public soundness entry for the new denotation route.

    This file intentionally no longer imports the old [SoundnessCommon] /
    [TLetReduction] / continuation-helper stack.  The only proof case wired in this
    checkpoint is TLet, via [fundamental_let_case_direct].  The remaining cases
    are left as the top-level induction skeleton so they can be restored one by
    one without reintroducing the old route. *)


Lemma fundamental_let_case
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
  eapply fundamental_let_case_direct.
Qed.

(** The full [Fundamental] induction is deliberately not re-exported from a
    skeleton theorem.  It should come back only as the non-TLet cases are rebuilt
    on the new denotation route.

    Corollaries from the old safety/refinement route are deliberately not
    rebuilt here yet; they should be reintroduced after the non-TLet cases use
    the new denotation definitions. *)
