(** * ChoiceType.WellFormed

    Paper-level well-formedness for choice contexts and choice types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  The paper's context well-formedness also
    requires semantic nonemptiness, which depends on denotation and therefore
    lives in this layer. *)

From ChoiceType Require Export BasicTyping Denotation.

(** ** Context and type well-formedness *)

Definition ctx_nonempty (Γ : ctx) : Prop :=
  ∃ r : WfWorld, r ⊨ ⟦Γ⟧.

Definition wf_ctx (Γ : ctx) : Prop :=
  basic_ctx ∅ Γ ∧ ctx_nonempty Γ.

Definition wf_choice_ty (Γ : ctx) (τ : choice_ty) : Prop :=
  wf_ctx Γ ∧ basic_choice_ty (ctx_dom Γ) τ.

(** ** Small wrappers matching the paper judgments *)

Notation "'⊢wf' Γ" := (wf_ctx Γ) (at level 40).
Notation "Γ '⊢wf' τ" := (wf_choice_ty Γ τ) (at level 40).

(** ** Regularity skeletons *)

Lemma wf_ctx_basic Γ :
  wf_ctx Γ →
  basic_ctx ∅ Γ.
Proof. Admitted.

Lemma wf_ctx_nonempty Γ :
  wf_ctx Γ →
  ctx_nonempty Γ.
Proof. Admitted.

Lemma wf_choice_ty_ctx Γ τ :
  wf_choice_ty Γ τ →
  wf_ctx Γ.
Proof. Admitted.

Lemma wf_choice_ty_basic Γ τ :
  wf_choice_ty Γ τ →
  basic_choice_ty (ctx_dom Γ) τ.
Proof. Admitted.

Lemma wf_ctx_fv_subset Γ :
  wf_ctx Γ →
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof. Admitted.

Lemma wf_choice_ty_lc Γ τ :
  wf_choice_ty Γ τ →
  lc_choice_ty τ.
Proof. Admitted.

Lemma wf_choice_ty_fv_subset Γ τ :
  wf_choice_ty Γ τ →
  fv_cty τ ⊆ ctx_dom Γ.
Proof. Admitted.
