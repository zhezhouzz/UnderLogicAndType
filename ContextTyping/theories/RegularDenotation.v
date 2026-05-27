(** * ContextTyping.RegularDenotation

    Prop-level regularity and totality around context-type denotation.

    The context-type denotation formulas intentionally stay semantic.  The
    typing proof, however, often needs the regularity facts that the paper keeps
    implicit: the context is basic, and the type is basic in the erased context.
    This file packages those facts outside the logic, so we do not encode
    naming or well-formedness as logic atoms. *)

From ContextTyping Require Export Typing.
From ContextTyping Require Import Naming.
From CoreLang Require Import BasicTyping.
From ContextAlgebra Require Import ResourceInterface.
From ContextBasicDenotation Require Import Term.

Definition denot_ty_regular_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) : Prop :=
  basic_ctx (dom Σ) Γ ∧ basic_context_ty (dom (erase_ctx_under Σ Γ)) τ.

Definition denot_ty_total_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm)
    (m : WfWorldT) : Prop :=
  denot_ty_regular_in_ctx_under Σ Γ τ ∧
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  m ⊨ expr_total_formula e.

Definition total_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : context_ty) (e : tm) : Prop :=
  ∀ m,
    m ⊨ denot_ctx_in_env Σ Γ →
    denot_ty_total_model_in_ctx_under Σ Γ τ e m.

Lemma denot_ty_total_model_regular Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  denot_ty_regular_in_ctx_under Σ Γ τ.
Proof. intros [H _]. exact H. Qed.

Lemma denot_ty_total_model_basic_ctx Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  basic_ctx (dom Σ) Γ.
Proof. intros [[H _] _]. exact H. Qed.

Lemma denot_ty_total_model_formula Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.
Proof. intros [_ [H _]]. exact H. Qed.

Lemma denot_ty_total_model_total Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  m ⊨ expr_total_formula e.
Proof. intros [_ [_ H]]. exact H. Qed.

Lemma total_model_to_total_denot Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  denot_ty_total_in_ctx_under Σ Γ τ e m.
Proof.
  intros.
  split.
  - eauto 6 using denot_ty_total_model_formula.
  - eauto 6 using denot_ty_total_model_total.
Qed.

Lemma total_model_of_total_denot Σ Γ τ e m :
  basic_ctx (dom Σ) Γ →
  basic_context_ty (dom (erase_ctx_under Σ Γ)) τ →
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m.
Proof.
  intros Hctx Hτ [Hden Htotal].
  split.
  - split; assumption.
  - split; assumption.
Qed.

Lemma context_typing_wf_from_erased_basic Σ Γ e τ m :
  basic_ctx (dom Σ) Γ →
  basic_context_ty (dom (erase_ctx_under Σ Γ)) τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  context_typing_wf Σ Γ e τ.
Proof.
  intros Hctx Hτ Hm Herase.
  split; [|exact Herase].
  split.
  - split; [exact Hctx|]. exists m. exact Hm.
  - rewrite erase_ctx_under_dom_basic in Hτ by exact Hctx.
    exact Hτ.
Qed.

Lemma denot_ty_total_model_context_typing_wf Σ Γ e τ m :
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  context_typing_wf Σ Γ e τ.
Proof.
  intros Herase Hctx Hmodel.
  eapply context_typing_wf_from_erased_basic; eauto.
  - exact (denot_ty_total_model_basic_ctx Σ Γ τ e m Hmodel).
  - exact (proj2 (denot_ty_total_model_regular Σ Γ τ e m Hmodel)).
Qed.

Lemma context_typing_wf_regular_denotation Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  denot_ty_regular_in_ctx_under Σ Γ τ.
Proof.
  intros Hwf.
  split.
  - exact (wf_ctx_under_basic Σ Γ
      (wf_context_ty_under_ctx Σ Γ τ (proj1 Hwf))).
  - exact (context_typing_wf_basic_context_ty_erased Σ Γ e τ Hwf).
Qed.

Lemma context_typing_wf_to_total_model Σ Γ e τ m :
  context_typing_wf Σ Γ e τ →
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m.
Proof.
  intros Hwf Htotal.
  eapply total_model_of_total_denot; eauto.
  - exact (proj1 (context_typing_wf_regular_denotation Σ Γ e τ Hwf)).
  - exact (proj2 (context_typing_wf_regular_denotation Σ Γ e τ Hwf)).
Qed.

Lemma entails_total_to_total_model Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ e) →
  total_model_in_ctx_under Σ Γ τ e.
Proof.
  intros Hwf Hent m Hm.
  apply context_typing_wf_to_total_model; eauto 6.
Qed.
