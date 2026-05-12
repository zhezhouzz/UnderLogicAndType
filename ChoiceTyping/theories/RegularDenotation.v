(** * ChoiceTyping.RegularDenotation

    Prop-level wrappers around type denotation.

    The denotation formulas in [ChoiceType] intentionally stay semantic.  The
    typing proof, however, often needs the regularity facts that the paper keeps
    implicit: the context is basic, and the type is basic in the erased context.
    This file packages those facts outside the logic, so we do not encode
    naming or well-formedness as logic atoms. *)

From ChoiceTyping Require Export Typing.
From ChoiceTyping Require Import Naming.

Definition denot_ty_regular_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) : Prop :=
  basic_ctx (dom Σ) Γ ∧ basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ.

Definition denot_ty_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  denot_ty_regular_in_ctx_under Σ Γ τ ∧
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.

Definition denot_ty_total_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  denot_ty_model_in_ctx_under Σ Γ τ e m ∧
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.

Definition total_model_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : Prop :=
  ∀ m,
    m ⊨ denot_ctx_in_env Σ Γ →
    denot_ty_total_model_in_ctx_under Σ Γ τ e m.

Lemma denot_ty_total_model_regular Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  denot_ty_regular_in_ctx_under Σ Γ τ.
Proof. intros [[Hregular _] _]. exact Hregular. Qed.

Lemma denot_ty_total_model_basic_ctx Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  basic_ctx (dom Σ) Γ.
Proof. intros H. exact (proj1 (denot_ty_total_model_regular Σ Γ τ e m H)). Qed.

Lemma denot_ty_total_model_basic_choice_ty Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ.
Proof. intros H. exact (proj2 (denot_ty_total_model_regular Σ Γ τ e m H)). Qed.

Lemma denot_ty_total_model_formula Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.
Proof. intros [[_ Hmodel] _]. exact Hmodel. Qed.

Lemma denot_ty_total_model_total Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.
Proof. intros [_ Htotal]. exact Htotal. Qed.

Lemma denot_ty_total_model_old Σ Γ τ e m :
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  denot_ty_total_in_ctx_under Σ Γ τ e m.
Proof.
  intros H.
  split.
  - exact (denot_ty_total_model_formula Σ Γ τ e m H).
  - exact (denot_ty_total_model_total Σ Γ τ e m H).
Qed.

Lemma denot_ty_total_model_from_old Σ Γ τ e m :
  basic_ctx (dom Σ) Γ →
  basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ →
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m.
Proof.
  intros Hctx Hτ [Hmodel Htotal].
  split; [split; [split; [exact Hctx | exact Hτ] | exact Hmodel] | exact Htotal].
Qed.

Lemma choice_typing_wf_from_erased_denot_ctx_basic_ty Σ Γ e τ m :
  basic_ctx (dom Σ) Γ →
  basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  choice_typing_wf Σ Γ e τ.
Proof.
  intros Hctx Hτ Hm Herase.
  split; [| exact Herase].
  split.
  - split; [exact Hctx | exists m; exact Hm].
  - rewrite <- (erase_ctx_under_dom_basic Σ Γ Hctx).
    exact Hτ.
Qed.

Lemma denot_ty_total_model_choice_typing_wf Σ Γ e τ m :
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  choice_typing_wf Σ Γ e τ.
Proof.
  intros Herase Hm Hmodel.
  eapply choice_typing_wf_from_erased_denot_ctx_basic_ty; eauto.
  - exact (denot_ty_total_model_basic_ctx Σ Γ τ e m Hmodel).
  - exact (denot_ty_total_model_basic_choice_ty Σ Γ τ e m Hmodel).
Qed.

Lemma choice_typing_wf_regular_denotation Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  denot_ty_regular_in_ctx_under Σ Γ τ.
Proof.
  intros Hwf.
  split.
  - destruct Hwf as [Hwfτ _].
    exact (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwfτ)).
  - exact (choice_typing_wf_basic_choice_ty_erased Σ Γ e τ Hwf).
Qed.

Lemma choice_typing_wf_to_total_model Σ Γ e τ m :
  choice_typing_wf Σ Γ e τ →
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m.
Proof.
  intros Hwf Hold.
  destruct (choice_typing_wf_regular_denotation Σ Γ e τ Hwf) as [Hctx Hτ].
  eapply denot_ty_total_model_from_old; eauto.
Qed.

Lemma entails_total_to_total_model Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ e) →
  total_model_in_ctx_under Σ Γ τ e.
Proof.
  intros Hwf Hent m Hm.
  apply choice_typing_wf_to_total_model; [exact Hwf |].
  exact (Hent m Hm).
Qed.
