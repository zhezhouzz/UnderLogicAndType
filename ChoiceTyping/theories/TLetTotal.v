(** * ChoiceTyping.TLetTotal

    Context-preservation helpers for the [tlet] result world.

    These lemmas build the comma-extended denotation context after evaluating
    the let-bound expression. *)

From ChoiceTyping Require Export RegularDenotation.
From ChoiceTyping Require Import Naming ResultWorldClosed ResultWorldExtension
  SoundnessCommon.
From ChoiceType Require Import BasicStore.

Lemma tlet_e1_choice_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : choice_ty) e1
    (m : WfWorld) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  choice_typing_wf Σ Γ e1 τ1.
Proof.
  intros Herase Hm Hmodel.
  eapply denot_ty_total_model_choice_typing_wf; eauto.
Qed.


Lemma tlet_body_ctx_from_result_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : choice_ty) e1 x
    (m mx : WfWorld) F :
  result_extends e1 x m F mx →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  mx ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
  intros Hext Herase Hm Hmodel.
  (* Extension-style replacement for the old result-world context extension
     chain.  The missing direct proof should use [Hext] to recover exactly the
     new [x]-fiber, prove the inserted erased/basic atom, and transport the
     denotation of [τ1] from [e1] to [ret x].  This is the proof obligation we
     want to review next instead of routing through the concrete construction. *)
  admit.
Admitted.
