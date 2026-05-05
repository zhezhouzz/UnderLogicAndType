(** * ChoiceTyping.Auxiliary

    Auxiliary judgments for the choice typing rules: semantic subtyping,
    context restriction, and context-level over-approximation coercion. *)

From ChoiceTyping Require Export WellFormed.

(** ** Semantic subtyping and context restriction *)

Definition sub_type (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  wf_choice_ty Γ τ1 ∧
  wf_choice_ty Γ τ2 ∧
  ∀ e, ⟦Γ⟧ ⊫ FImpl (⟦τ1⟧ e) (⟦τ2⟧ e).

Definition ctx_sub (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx Γ1 ∧
  wf_ctx Γ2 ∧
  ∀ r, r ⊨ ⟦Γ1⟧ → res_restrict r X ⊨ ⟦Γ2⟧.

Definition ctx_to_over (Γ Γ' : ctx) : Prop :=
  wf_ctx Γ ∧
  wf_ctx Γ' ∧
  (FOver (⟦Γ⟧) ⊫ ⟦Γ'⟧).

(** ** Reflexivity skeletons *)

Lemma sub_type_refl Γ τ :
  wf_choice_ty Γ τ →
  sub_type Γ τ τ.
Proof. Admitted.

Lemma ctx_sub_refl Γ :
  wf_ctx Γ →
  ctx_sub (ctx_fv Γ) Γ Γ.
Proof. Admitted.

Lemma ctx_to_over_refl Γ :
  wf_ctx Γ →
  ctx_to_over Γ Γ.
Proof. Admitted.
