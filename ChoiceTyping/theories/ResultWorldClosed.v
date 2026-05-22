(** * ChoiceTyping.ResultWorldClosed

    Typing-context bridge from denotation contexts to [world_closed_on].  The
    pure closedness and result-world lemmas live in lower TypeDenotation layers. *)

From CoreLang Require Import BasicTypingProps.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Import Naming.

Lemma denot_ctx_in_env_world_closed_on_erased Σ Γ m :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  world_closed_on (dom (erase_ctx_under Σ Γ)) m.
Proof.
  intros Hbasic Hctx σ Hσ.
  assert (Hdom_erase :
    dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ).
  { apply erase_ctx_under_dom_basic. exact Hbasic. }
  rewrite Hdom_erase.
  split.
  - exact (proj1 (denot_ctx_in_env_store_erased_typed
      Σ Γ m σ Hbasic Hctx Hσ)).
  - exact (denot_ctx_in_env_store_erased_lc
      Σ Γ m σ Hbasic Hctx Hσ).
Qed.
