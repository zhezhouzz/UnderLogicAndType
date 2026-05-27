(** * ChoiceTyping.WellFormed

    Paper-level well-formedness for choice contexts and choice types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  The paper's context well-formedness also
    requires semantic nonemptiness, which depends on denotation and therefore
    lives in this layer. *)

From CoreLang Require Import BasicTyping.
From ChoiceAlgebra Require Import ResourceInterface.
From ChoiceLogic Require Import FormulaScope.
From ChoiceTypeLanguage Require Export Sugar.
From Denotation Require Export Context.

(** ** Context and type well-formedness *)

Definition ctx_nonempty_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  ∃ r : WfWorldT, r ⊨ denot_ctx_in_env Σ Γ.

Definition wf_ctx_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  basic_ctx (dom Σ) Γ ∧ ctx_nonempty_under Σ Γ.

Definition wf_ctx (Γ : ctx) : Prop :=
  wf_ctx_under ∅ Γ.

Definition wf_choice_ty_under (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) : Prop :=
  wf_ctx_under Σ Γ ∧ basic_choice_ty (dom Σ ∪ ctx_dom Γ) τ.

Definition wf_choice_ty (Γ : ctx) (τ : choice_ty) : Prop :=
  wf_choice_ty_under ∅ Γ τ.

(** ** Regularity skeletons *)

Lemma wf_ctx_basic Γ :
  wf_ctx Γ →
  basic_ctx ∅ Γ.
Proof. intros [Hbasic _]. exact Hbasic. Qed.

Lemma wf_ctx_under_basic Σ Γ :
  wf_ctx_under Σ Γ →
  basic_ctx (dom Σ) Γ.
Proof. intros [Hbasic _]. exact Hbasic. Qed.

Lemma wf_choice_ty_ctx Γ τ :
  wf_choice_ty Γ τ →
  wf_ctx Γ.
Proof. intros [Hwf _]. exact Hwf. Qed.

Lemma wf_choice_ty_under_ctx Σ Γ τ :
  wf_choice_ty_under Σ Γ τ →
  wf_ctx_under Σ Γ.
Proof. intros [Hwf _]. exact Hwf. Qed.

Lemma wf_choice_ty_basic Γ τ :
  wf_choice_ty Γ τ →
  basic_choice_ty (ctx_dom Γ) τ.
Proof.
  intros [_ Hbasic].
  replace (ctx_dom Γ) with (dom (∅ : gmap atom ty) ∪ ctx_dom Γ) by set_solver.
  exact Hbasic.
Qed.

Lemma wf_choice_ty_under_basic Σ Γ τ :
  wf_choice_ty_under Σ Γ τ →
  basic_choice_ty (dom Σ ∪ ctx_dom Γ) τ.
Proof. intros [_ Hbasic]. exact Hbasic. Qed.

Lemma wf_ctx_fv_subset Γ :
  wf_ctx Γ →
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
  intros Hwf.
  pose proof (wf_ctx_basic Γ Hwf) as Hbasic.
  apply basic_ctx_empty_fv. exact Hbasic.
Qed.

Lemma wf_choice_ty_lc Γ τ :
  wf_choice_ty Γ τ →
  lc_choice_ty τ.
Proof.
  intros Hwf.
  eapply basic_choice_ty_lc.
  exact (wf_choice_ty_basic Γ τ Hwf).
Qed.

Lemma wf_choice_ty_fv_subset Γ τ :
  wf_choice_ty Γ τ →
  fv_cty τ ⊆ ctx_dom Γ.
Proof.
  intros Hwf.
  eapply basic_choice_ty_fv_subset.
  exact (wf_choice_ty_basic Γ τ Hwf).
Qed.

Lemma wf_choice_ty_under_fv_subset Σ Γ τ :
  wf_choice_ty_under Σ Γ τ →
  fv_cty τ ⊆ dom Σ ∪ ctx_dom Γ.
Proof.
  intros Hwf.
  eapply basic_choice_ty_fv_subset.
  exact (wf_choice_ty_under_basic Σ Γ τ Hwf).
Qed.
