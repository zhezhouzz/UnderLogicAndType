(** * ContextTyping.TypingRegular

    Regularity and erasure facts derived from the core context typing
    definitions and judgment. *)

From CoreLang Require Import BasicTyping BasicTypingProps Sugar.
From ContextLogic Require Import FormulaSemantics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextTypeLanguage Require Import WF.
From ContextBasicDenotation Require Import BasicTypingFormula.
From Denotation Require Import Context.
From ContextTyping Require Import PrimOpContext Typing.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).

(** ** Regularity skeletons *)

Lemma wf_ctx_basic Γ :
  wf_ctx Γ →
  basic_ctx ∅ Γ.
Proof. intros Hbasic. exact Hbasic. Qed.

Lemma wf_ctx_under_basic Σ Γ :
  wf_ctx_under Σ Γ →
  basic_ctx (dom Σ) Γ.
Proof. intros Hbasic. exact Hbasic. Qed.

Lemma wf_context_ty_basic Γ τ :
  wf_context_ty Γ τ →
  basic_context_ty (dom (erase_ctx Γ)) τ.
Proof. intros Hwf. exact Hwf. Qed.

Lemma wf_ctx_fv_subset Γ :
  wf_ctx Γ →
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
  intros Hwf.
  pose proof (wf_ctx_basic Γ Hwf) as Hbasic.
  apply basic_ctx_empty_fv. exact Hbasic.
Qed.

Lemma wf_context_ty_lc Γ τ :
  wf_context_ty Γ τ →
  lc_context_ty τ.
Proof.
  intros Hwf.
  eapply basic_context_ty_lc.
  exact (wf_context_ty_basic Γ τ Hwf).
Qed.

Lemma wf_context_ty_fv_subset Γ τ :
  wf_context_ty Γ τ →
  fv_cty τ ⊆ dom (erase_ctx Γ).
Proof.
  intros Hwf.
  eapply basic_context_ty_fv_subset.
  exact (wf_context_ty_basic Γ τ Hwf).
Qed.

(** ** Typing side-condition regularity *)

Lemma context_typing_wf_basic_typing Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. intros [_ [_ Hbasic]]. exact Hbasic. Qed.

Lemma context_typing_wf_lc_tm Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  lc_tm e.
Proof.
  intros Hwf.
  eapply typing_tm_lc.
  exact (context_typing_wf_basic_typing Σ Γ e τ Hwf).
Qed.

Lemma context_typing_wf_ret_lc_value Σ Γ v τ :
  context_typing_wf Σ Γ (tret v) τ ->
  lc_value v.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_lc_tm Σ Γ (tret v) τ Hwf) as Hlc.
  inversion Hlc; subst.
  assumption.
Qed.

Lemma context_typing_wf_app_fun_lc_value Σ Γ v1 v2 τ :
  context_typing_wf Σ Γ (tapp v1 v2) τ ->
  lc_value v1.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_lc_tm Σ Γ (tapp v1 v2) τ Hwf) as Hlc.
  inversion Hlc; subst.
  assumption.
Qed.

Lemma context_typing_wf_lam_body Σ Γ T e τ :
  context_typing_wf Σ Γ (tret (vlam T e)) τ ->
  body_tm e.
Proof.
  intros Hwf.
  apply (proj1 (lc_lam_iff_body T e)).
  exact (context_typing_wf_ret_lc_value Σ Γ (vlam T e) τ Hwf).
Qed.

Lemma context_typing_wf_ctx Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  wf_ctx_under Σ Γ.
Proof. intros [Hctx _]. exact Hctx. Qed.

Lemma context_typing_wf_context_ty Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ.
Proof. intros [_ [Hτ _]]. exact Hτ. Qed.

Lemma context_typing_wf_arrow_arg_lc Σ Γ e τx τ :
  context_typing_wf Σ Γ e (CTArrow τx τ) ->
  lc_context_ty τx.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ Γ e
    (CTArrow τx τ) Hwf) as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  exact (wf_context_ty_at_lc 0 (dom (erase_ctx Γ)) τx (proj1 Hτ)).
Qed.

Lemma context_typing_wf_arrow_result_lc1 Σ Γ e τx τ :
  context_typing_wf Σ Γ e (CTArrow τx τ) ->
  cty_lc_at 1 τ.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ Γ e
    (CTArrow τx τ) Hwf) as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  exact (wf_context_ty_at_lc 1 (dom (erase_ctx Γ)) τ (proj2 Hτ)).
Qed.

Lemma context_typing_wf_wand_arg_lc Σ Γ e τx τ :
  context_typing_wf Σ Γ e (CTWand τx τ) ->
  lc_context_ty τx.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ Γ e
    (CTWand τx τ) Hwf) as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  exact (wf_context_ty_at_lc 0 ∅ τx (proj1 Hτ)).
Qed.

Lemma context_typing_wf_wand_result_lc1 Σ Γ e τx τ :
  context_typing_wf Σ Γ e (CTWand τx τ) ->
  cty_lc_at 1 τ.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ Γ e
    (CTWand τx τ) Hwf) as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  exact (wf_context_ty_at_lc 1 (dom (erase_ctx Γ)) τ (proj2 Hτ)).
Qed.

Lemma context_union_fresh_erase_ctx_from_erasure_under
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (erase_ctx Γ).
Proof.
  intros Hy.
  eapply ctx_erasure_under_notin_erase_ctx.
  intros Hyctx.
  apply Hy.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_r.
  exact Hyctx.
Qed.

Lemma context_union_fresh_ctx_erasure_under
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (ctx_erasure_under Σ Γ).
Proof.
  intros Hy Hyctx.
  apply Hy.
  clear -Hyctx. set_solver.
Qed.

Lemma context_union_fresh_env_erase_ctx
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom Σ ∪ dom (erase_ctx Γ).
Proof.
  intros Hy Hin.
  apply elem_of_union in Hin as [HyΣ|HyΓ].
  - apply Hy. clear -HyΣ. set_solver.
  - eapply context_union_fresh_erase_ctx_from_erasure_under; eauto.
Qed.

Lemma context_typing_wf_bind_context_ty Σ x τ e :
  context_typing_wf Σ (CtxBind x τ) e τ ->
  basic_context_ty {[x]} τ.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ (CtxBind x τ) e τ Hwf)
    as Hτ.
  rewrite erase_ctx_bind_dom in Hτ.
  exact Hτ.
Qed.

Lemma context_typing_wf_fv_tm_subset Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  fv_tm e ⊆ dom (erase_ctx Γ).
Proof.
  intros Hct.
  apply basic_typing_contains_fv_tm with (T := erase_ty τ).
  exact (context_typing_wf_basic_typing Σ Γ e τ Hct).
Qed.

Lemma context_typing_wf_erase_dom Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof.
  intros Hct.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hct) as Hctx.
  pose proof (wf_ctx_under_basic Σ Γ Hctx) as Hbasic.
  apply (basic_ctx_erase_dom (dom Σ)). exact Hbasic.
Qed.

Lemma context_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  fv_cty τ ⊆ dom (erase_ctx Γ).
Proof.
  intros Hct.
  eapply wf_context_ty_at_fv_subset.
  exact (context_typing_wf_context_ty Σ Γ e τ Hct).
Qed.

Lemma context_typing_wf_wand_arg_global Σ Γ e τx τr :
  context_typing_wf Σ Γ e (CTWand τx τr) ->
  basic_context_ty ∅ τx.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ Γ e (CTWand τx τr) Hwf)
    as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  exact (proj1 Hτ).
Qed.

Lemma soundness_wf_ret_persist_obs_subset
    Σ Γ τ v :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  fv_cty τ ∪ fv_value v ⊆ dom (erase_ctx Γ).
Proof.
  intros Hwf a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply context_typing_wf_fv_cty_subset_erase_dom with
      (Σ := Σ) (e := tret v) (τ := CTPersist τ) in Hwf.
    cbn [fv_cty context_ty_lvars context_ty_lvars_at] in Hwf.
    exact (Hwf a Ha).
  - pose proof (context_typing_wf_fv_tm_subset Σ Γ (tret v)
      (CTPersist τ) Hwf) as Hfv.
    cbn [fv_tm] in Hfv.
    exact (Hfv a Ha).
Qed.

Lemma soundness_wf_ret_persist_observed_world
    Σ Γ τ v (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  fv_cty τ ∪ fv_value v ⊆ world_dom (m : WorldT).
Proof.
  intros Hwf Hctx.
  pose proof (soundness_wf_ret_persist_obs_subset
    Σ Γ τ v Hwf) as Hobs.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as Hctxdom.
  ctx_erasure_under_norm_in Hctxdom.
  intros a Ha.
  pose proof (Hobs a Ha) as Haobs.
  apply Hctxdom.
  ctx_erasure_under_norm.
  set_solver.
Qed.

Ltac soundness_regular_observed_world :=
  match goal with
  | Hwf : context_typing_wf ?Σ ?Γ (tret ?v) (CTPersist ?τ),
    Hctx : ?m ⊨ ctx_denote_under ?Σ ?Γ |- _ =>
      lazymatch goal with
      | H : fv_cty τ ∪ fv_value v ⊆ world_dom (m : WorldT) |- _ =>
          fail
      | _ =>
          let H := fresh "Hobs_world" in
          pose proof (soundness_wf_ret_persist_observed_world
            Σ Γ τ v m Hwf Hctx) as H
      end
  end.

Ltac soundness_regular_lc :=
  repeat match goal with
  | Hwf : context_typing_wf ?Σ ?Γ (tret ?v) (CTPersist ?τ) |- _ =>
      lazymatch goal with
      | H : lc_value v |- _ => fail
      | _ =>
          let H := fresh "Hv" in
          pose proof (context_typing_wf_ret_lc_value
            Σ Γ v (CTPersist τ) Hwf) as H
      end
  | Hwf : context_typing_wf ?Σ ?Γ ?e (CTArrow ?τx ?τ) |- _ =>
      lazymatch goal with
      | H : lc_context_ty τx |- _ => fail
      | _ =>
          let H := fresh "Hτx_lc" in
          pose proof (context_typing_wf_arrow_arg_lc
            Σ Γ e τx τ Hwf) as H
      end
  | Hwf : context_typing_wf ?Σ ?Γ ?e (CTArrow ?τx ?τ) |- _ =>
      lazymatch goal with
      | H : cty_lc_at 1 τ |- _ => fail
      | _ =>
          let H := fresh "Hτ_lc1" in
          pose proof (context_typing_wf_arrow_result_lc1
            Σ Γ e τx τ Hwf) as H
      end
  | Hwf : context_typing_wf ?Σ ?Γ ?e (CTWand ?τx ?τ) |- _ =>
      lazymatch goal with
      | H : lc_context_ty τx |- _ => fail
      | _ =>
          let H := fresh "Hτx_lc" in
          pose proof (context_typing_wf_wand_arg_lc
            Σ Γ e τx τ Hwf) as H
      end
  | Hwf : context_typing_wf ?Σ ?Γ ?e (CTWand ?τx ?τ) |- _ =>
      lazymatch goal with
      | H : cty_lc_at 1 τ |- _ => fail
      | _ =>
          let H := fresh "Hτ_lc1" in
          pose proof (context_typing_wf_wand_result_lc1
            Σ Γ e τx τ Hwf) as H
      end
  end.

Ltac soundness_regular_obs_subset :=
  match goal with
  | Hwf : context_typing_wf ?Σ ?Γ (tret ?v) (CTPersist ?τ) |- _ =>
      lazymatch goal with
      | H : fv_cty τ ∪ fv_value v ⊆ dom (erase_ctx Γ) |- _ =>
          fail
      | _ =>
          let H := fresh "Hobs" in
          pose proof (soundness_wf_ret_persist_obs_subset
            Σ Γ τ v Hwf) as H
      end
  end.

Ltac soundness_regular :=
  try soundness_regular_observed_world;
  try soundness_regular_lc;
  try soundness_regular_obs_subset.

Lemma typing_wf Φ Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  context_typing_wf ∅ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma typing_wf_under Φ Σ Γ e τ :
  has_context_type Φ Σ Γ e τ →
  context_typing_wf Σ Γ e τ.
Proof. induction 1; assumption. Qed.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Φ Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hty.
  exact (context_typing_wf_basic_typing ∅ Γ e τ
    (typing_wf Φ Γ e τ Hty)).
Qed.
