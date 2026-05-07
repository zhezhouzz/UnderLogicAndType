(** * ChoiceTyping.Auxiliary

    Auxiliary judgments for the choice typing rules: semantic subtyping,
    context restriction, and context-level over-approximation coercion. *)

From ChoiceTyping Require Export WellFormed.

(** ** Semantic subtyping and context restriction *)

Definition sub_type (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  wf_choice_ty Γ τ1 ∧
  wf_choice_ty Γ τ2 ∧
  erase_ty τ1 = erase_ty τ2 ∧
  ∀ e, fv_tm e ⊆ ctx_dom Γ → ⟦Γ⟧ ⊫ FImpl (⟦τ1⟧ e) (⟦τ2⟧ e).

Definition ctx_sub (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx Γ1 ∧
  wf_ctx Γ2 ∧
  ∀ r, r ⊨ ⟦Γ1⟧ → res_restrict r X ⊨ ⟦Γ2⟧.

Definition ctx_to_over (Γ Γ' : ctx) : Prop :=
  wf_ctx Γ ∧
  wf_ctx Γ' ∧
  (FOver (⟦Γ⟧) ⊫ ⟦Γ'⟧).

(** ** Regularity and reflexivity skeletons *)

Lemma sub_type_wf_l Γ τ1 τ2 :
  sub_type Γ τ1 τ2 →
  wf_choice_ty Γ τ1.
Proof. intros [Hwf _]. exact Hwf. Qed.

Lemma sub_type_wf_r Γ τ1 τ2 :
  sub_type Γ τ1 τ2 →
  wf_choice_ty Γ τ2.
Proof. intros [_ [Hwf _]]. exact Hwf. Qed.

Lemma sub_type_erase Γ τ1 τ2 :
  sub_type Γ τ1 τ2 →
  erase_ty τ1 = erase_ty τ2.
Proof. intros [_ [_ [Herase _]]]. exact Herase. Qed.

Lemma ctx_sub_wf_l X Γ1 Γ2 :
  ctx_sub X Γ1 Γ2 →
  wf_ctx Γ1.
Proof. intros [Hwf _]. exact Hwf. Qed.

Lemma ctx_sub_wf_r X Γ1 Γ2 :
  ctx_sub X Γ1 Γ2 →
  wf_ctx Γ2.
Proof. intros [_ [Hwf _]]. exact Hwf. Qed.

Lemma ctx_to_over_wf_l Γ Γ' :
  ctx_to_over Γ Γ' →
  wf_ctx Γ.
Proof. intros [Hwf _]. exact Hwf. Qed.

Lemma ctx_to_over_wf_r Γ Γ' :
  ctx_to_over Γ Γ' →
  wf_ctx Γ'.
Proof. intros [_ [Hwf _]]. exact Hwf. Qed.

Lemma sub_type_refl Γ τ :
  wf_choice_ty Γ τ →
  sub_type Γ τ τ.
Proof.
  intros Hwf.
  split; [exact Hwf |]. split; [exact Hwf |]. split; [reflexivity |].
  intros e Hfv m HΓ.
  apply res_models_impl_refl.
  eapply denot_ty_scoped_from_ctx; eauto.
Qed.

Lemma ctx_sub_refl Γ :
  wf_ctx Γ →
  ctx_sub (ctx_stale Γ) Γ Γ.
Proof.
  intros Hwf.
  split; [exact Hwf |]. split; [exact Hwf |].
  intros r Hr.
  apply denot_ctx_restrict_stale. exact Hr.
Qed.

Lemma ctx_to_over_refl Γ :
  wf_ctx Γ →
  ctx_to_over Γ Γ.
Proof. Admitted.
