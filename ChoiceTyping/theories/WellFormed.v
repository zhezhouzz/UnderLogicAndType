(** * ChoiceTyping.WellFormed

    Paper-level well-formedness for choice contexts and choice types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  The paper's context well-formedness also
    requires semantic nonemptiness, which depends on denotation and therefore
    lives in this layer. *)

From ChoiceType Require Export BasicTyping Denotation.

(** ** Context and type well-formedness *)

Definition ctx_nonempty_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  ∃ r : WfWorld, r ⊨ denot_ctx_in_env Σ Γ.

Definition ctx_nonempty (Γ : ctx) : Prop :=
  ctx_nonempty_under ∅ Γ.

Definition wf_ctx_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  basic_ctx (dom Σ) Γ ∧ ctx_nonempty_under Σ Γ.

Definition wf_ctx (Γ : ctx) : Prop :=
  wf_ctx_under ∅ Γ.

Definition wf_choice_ty_under (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) : Prop :=
  wf_ctx_under Σ Γ ∧ basic_choice_ty (dom Σ ∪ ctx_dom Γ) τ.

Definition wf_choice_ty (Γ : ctx) (τ : choice_ty) : Prop :=
  wf_choice_ty_under ∅ Γ τ.

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

Lemma wf_ctx_under_basic Σ Γ :
  wf_ctx_under Σ Γ →
  basic_ctx (dom Σ) Γ.
Proof. intros [Hbasic _]. exact Hbasic. Qed.

Lemma wf_ctx_nonempty Γ :
  wf_ctx Γ →
  ctx_nonempty Γ.
Proof. intros [_ Hnonempty]. exact Hnonempty. Qed.

Lemma wf_ctx_under_nonempty Σ Γ :
  wf_ctx_under Σ Γ →
  ctx_nonempty_under Σ Γ.
Proof. intros [_ Hnonempty]. exact Hnonempty. Qed.

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

Lemma denot_ty_scoped_from_ctx_under Σ Γ τ e m :
  wf_choice_ty_under Σ Γ τ →
  fv_tm e ⊆ dom Σ ∪ ctx_dom Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  formula_scoped_in_world ∅ m (denot_ty_in_ctx_under Σ Γ τ e).
Proof.
  intros Hwf Hfv Hctx.
  pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwf)) as HbasicΓ.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
  pose proof (wf_choice_ty_under_fv_subset Σ Γ τ Hwf) as Hτfv.
  pose proof (denot_ty_in_ctx_under_formula_fv_subset Σ Γ τ e) as Hdenot_fv.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (denot_ctx_in_env Σ Γ)) ∅ m (denot_ctx_in_env Σ Γ) Hctx)
    as Hctx_scope.
  unfold formula_scoped_in_world in *.
  intros z Hz.
  rewrite dom_empty_L in Hz.
  assert (Hzfv : z ∈ formula_fv (denot_ty_in_ctx_under Σ Γ τ e)) by set_solver.
  apply Hdenot_fv in Hzfv.
  apply Hctx_scope.
  pose proof (denot_ctx_in_env_dom_subset_formula_fv Σ Γ) as Hctx_fv.
  unfold erase_ctx_under in Hzfv.
  rewrite dom_union_L, HdomΓ in Hzfv.
  set_solver.
Qed.

Lemma denot_ty_scoped_from_ctx Γ τ e m :
  wf_choice_ty Γ τ →
  fv_tm e ⊆ ctx_dom Γ →
  m ⊨ ⟦Γ⟧ →
  formula_scoped_in_world ∅ m (denot_ty_in_ctx Γ τ e).
Proof.
  intros Hwf Hfv Hctx.
  unfold denot_ty_in_ctx.
  pose proof (wf_ctx_basic Γ (wf_choice_ty_ctx Γ τ Hwf)) as HbasicΓ.
  pose proof (basic_ctx_erase_dom ∅ Γ HbasicΓ) as HdomΓ.
  pose proof (wf_choice_ty_fv_subset Γ τ Hwf) as Hτfv.
  pose proof (denot_ty_under_formula_fv_subset (erase_ctx Γ) τ e) as Hdenot_fv.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (⟦Γ⟧)) ∅ m (⟦Γ⟧) Hctx) as Hctx_scope.
  unfold formula_scoped_in_world in *.
  intros z Hz.
  rewrite dom_empty_L in Hz.
  assert (Hzfv : z ∈ formula_fv (denot_ty_under (erase_ctx Γ) τ e)) by set_solver.
  apply Hdenot_fv in Hzfv.
  apply Hctx_scope.
  unfold denot_ctx in Hctx_scope.
  pose proof (denot_ctx_dom_subset_formula_fv Γ) as Hctx_fv.
  rewrite HdomΓ in Hzfv.
  set_solver.
Qed.
