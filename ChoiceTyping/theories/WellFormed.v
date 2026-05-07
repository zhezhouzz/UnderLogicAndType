(** * ChoiceTyping.WellFormed

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

(** ** Paper-judgment notations

    These notations make printed statements closer to the paper.  Proof scripts
    should prefer the explicit names [wf_ctx] and [wf_choice_ty]. *)

Notation "'⊢wf' Γ" := (wf_ctx Γ) (at level 40).
Notation "Γ '⊢wf' τ" := (wf_choice_ty Γ τ) (at level 40).

(** ** Regularity skeletons *)

Lemma wf_ctx_basic Γ :
  wf_ctx Γ →
  basic_ctx ∅ Γ.
Proof. intros [Hbasic _]. exact Hbasic. Qed.

Lemma wf_ctx_nonempty Γ :
  wf_ctx Γ →
  ctx_nonempty Γ.
Proof. intros [_ Hnonempty]. exact Hnonempty. Qed.

Lemma wf_choice_ty_ctx Γ τ :
  wf_choice_ty Γ τ →
  wf_ctx Γ.
Proof. intros [Hwf _]. exact Hwf. Qed.

Lemma wf_choice_ty_basic Γ τ :
  wf_choice_ty Γ τ →
  basic_choice_ty (ctx_dom Γ) τ.
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

Lemma denot_ty_scoped_from_ctx Γ τ e m :
  wf_choice_ty Γ τ →
  fv_tm e ⊆ ctx_dom Γ →
  m ⊨ ⟦Γ⟧ →
  formula_scoped_in_world ∅ m (⟦τ⟧ e).
Proof.
  intros Hwf Hfv Hmodels.
  unfold formula_scoped_in_world. simpl.
  intros z Hz.
  assert (Hzφ : z ∈ formula_fv (⟦τ⟧ e)) by set_solver.
  pose proof (denot_ty_formula_fv_subset τ e z Hzφ) as Hzvars.
  pose proof (wf_choice_ty_fv_subset Γ τ Hwf) as Hτfv.
  pose proof (denot_ctx_models_dom Γ m Hmodels) as Hdom.
  set_solver.
Qed.
