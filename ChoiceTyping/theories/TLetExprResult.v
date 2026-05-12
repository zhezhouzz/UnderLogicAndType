(** * ChoiceTyping.TLetExprResult

    Top-level placeholder for the final semantic [tlet] statement.

    Older expression-result/fiber bridge experiments used to live in this file.
    They have been removed because the current [TLetDenotation] proof path uses
    the exact-domain [FExprCont] bridge and [let_result_world_on_tlete_decompose]
    instead. *)

From CoreLang Require Import Instantiation.
From ChoiceTyping Require Export TLetTotal.

Lemma denot_tlet_semantic_at_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
(** Placeholder: this is the final semantic [tlet] statement and should not be
    used as evidence that the [tlet] case is proved. *)
Admitted.
