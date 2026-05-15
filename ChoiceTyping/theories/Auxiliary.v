(** * ChoiceTyping.Auxiliary

    Auxiliary judgments for the choice typing rules. *)

From ChoiceTyping Require Export WellFormed.

(** ** Semantic subtyping *)

Definition sub_type_under (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  wf_choice_ty_under Σ Γ τ1 ∧
  wf_choice_ty_under Σ Γ τ2 ∧
  erase_ty τ1 = erase_ty τ2 ∧
  ∀ e, fv_tm e ⊆ dom Σ ∪ ctx_dom Γ →
    denot_ctx_in_env Σ Γ ⊫
      FImpl (denot_ty_in_ctx_under Σ Γ τ1 e)
            (denot_ty_in_ctx_under Σ Γ τ2 e).

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (erase_ctx_under Σ Γ1) (erase_ctx_under Σ Γ2) ∧
  ∀ r, r ⊨ denot_ctx_in_env Σ Γ1 →
       res_restrict r X ⊨ denot_ctx_in_env Σ Γ2.
