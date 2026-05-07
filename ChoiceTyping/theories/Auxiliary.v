(** * ChoiceTyping.Auxiliary

    Auxiliary judgments for the choice typing rules: semantic subtyping,
    context restriction, and context-level over-approximation coercion. *)

From ChoiceTyping Require Export WellFormed.

(** ** Semantic subtyping and context restriction *)

Definition sub_type_under (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  wf_choice_ty_under Σ Γ τ1 ∧
  wf_choice_ty_under Σ Γ τ2 ∧
  erase_ty τ1 = erase_ty τ2 ∧
  ∀ e, fv_tm e ⊆ dom Σ ∪ ctx_dom Γ →
    denot_ctx_in_env Σ Γ ⊫
      FImpl (denot_ty_in_ctx_under Σ Γ τ1 e)
            (denot_ty_in_ctx_under Σ Γ τ2 e).

Definition sub_type (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  sub_type_under ∅ Γ τ1 τ2.

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (erase_ctx_under Σ Γ1) (erase_ctx_under Σ Γ2) ∧
  ∀ r, r ⊨ denot_ctx_in_env Σ Γ1 →
       res_restrict r X ⊨ denot_ctx_in_env Σ Γ2.

Definition ctx_sub (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx Γ1 ∧
  wf_ctx Γ2 ∧
  ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2) ∧
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

Lemma ctx_sub_env_agree X Γ1 Γ2 :
  ctx_sub X Γ1 Γ2 →
  ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2).
Proof.
  intros [_ [_ [Hagree _]]].
  exact Hagree.
Qed.

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
  eapply denot_ty_scoped_from_ctx_under; eauto.
Qed.

Lemma ctx_sub_refl Γ :
  wf_ctx Γ →
  ctx_sub (ctx_stale Γ) Γ Γ.
Proof.
  intros Hwf.
  split; [exact Hwf |]. split; [exact Hwf |]. split.
  - intros x Hx. reflexivity.
  -
  intros r Hr.
  apply denot_ctx_restrict_stale. exact Hr.
Qed.

Lemma ctx_to_over_refl Γ :
  wf_ctx Γ →
  ctx_to_over Γ Γ.
Proof. Admitted.
