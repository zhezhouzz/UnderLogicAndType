(** * ChoiceTyping.TLetDenotation

    Thin denotation-level interface for the [tlet] soundness case. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Export TLetReductionTotal.
From ChoiceTyping Require Import Naming ResultWorldBridge ResultWorldFreshForall.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** The total [tlet] rule after splitting the body premise cofinally. *)
Lemma denot_tlet_total_semantic
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_model_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_model_in_ctx_under Σ Γ τ2 (tlete e1 e2)).
Proof.
  intros Herase Hwflet IH1 Hbody m Hm.
  pose proof (IH1 m Hm) as Hmodel.
  pose proof (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel) as Htotal1.
  pose (Fresh :=
    L ∪ world_dom (m : World) ∪ dom (erase_ctx_under Σ Γ) ∪
    fv_tm e2 ∪ fv_cty τ2).
  pose (x := fresh_for Fresh).
  assert (HxFresh : x ∉ Fresh) by (subst x; apply fresh_for_not_in).
  assert (HxL : x ∉ L) by (subst Fresh; set_solver).
  assert (Hfresh : x ∉ world_dom (m : World)) by (subst Fresh; set_solver).
  assert (Hx_tlet :
    x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2)
    by (subst Fresh; set_solver).
  assert (Hclosed_erased :
    world_store_closed_on (dom (erase_ctx_under Σ Γ)) m).
  {
    pose proof (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel)
      as Hbasic.
    intros σ Hσ.
    assert (Hdom_erase :
      dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ).
    { apply erase_ctx_under_dom_basic. exact Hbasic. }
    rewrite Hdom_erase.
    split.
    - exact (proj1 (denot_ctx_in_env_store_erased_typed
        Σ Γ m σ Hbasic Hm Hσ)).
    - exact (denot_ctx_in_env_store_erased_lc
        Σ Γ m σ Hbasic Hm Hσ).
  }
  assert (Hresult : ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx).
  { eapply expr_total_on_to_fv_result; eauto. }
  set (m' := let_result_world_on e1 x m Hfresh Hresult).
  assert (Hctx :
    m' ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))).
  {
    subst m'. eapply tlet_split_premises_body_ctx_from_result; eauto.
  }
  pose proof (Hbody x HxL m' Hctx) as Hbody_model.
  exact (proj1
    (denot_ty_total_tlet_reduction
      Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult
      Herase Hwflet Hm Hmodel Hx_tlet)
    Hbody_model).
Qed.

Lemma denot_tlet_semantic
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
(** Placeholder: this is the non-total semantic [tlet] statement and should not
    be used as evidence that the [tlet] case is proved.  The current active
    route is the total statement [denot_tlet_total_semantic] above. *)
Admitted.
