(** * ChoiceTyping.TLetDenotation

    Thin denotation-level interface for the [tlet] soundness case. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Export TLetReductionTotal.
From ChoiceTyping Require Import Naming SoundnessCommon LetResultWorld
  ResultWorldClosed ResultWorldExprCont.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

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
    world_closed_on (dom (erase_ctx_under Σ Γ)) m).
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
  assert (Htotal_result :
    expr_total_result_on (dom (erase_ctx_under Σ Γ)) e1 m).
  { split; eauto. }
  set (m' := let_result_world_on_total
    (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Htotal_result).
  assert (Hctx :
    m' ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))).
  {
    subst m'. unfold let_result_world_on_total.
    eapply tlet_body_ctx_from_result_world; eauto.
  }
  pose proof (Hbody x HxL m' Hctx) as Hbody_model.
  eapply (proj1
    (denot_ty_total_tlet_reduction
      Σ Γ τ1 τ2 e1 e2 m x Hfresh Htotal_result
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
  intros Hwf1 Hwflet IH1 IH2.
  pose (L' := L ∪ dom (erase_ctx_under Σ Γ) ∪ fv_tm e2 ∪ fv_cty τ2).
  intros m Hctx.
  apply denot_ty_total_model_formula.
  refine (denot_tlet_total_semantic
    Σ Γ τ1 τ2 e1 e2 L' (proj2 Hwf1) (proj2 Hwflet) _ _ m Hctx).
  - intros n Hn.
    pose proof (IH1 n Hn) as Hφ.
    split.
    + eapply choice_typing_wf_regular_denotation; eauto 6.
      + split; [exact Hφ |].
        unfold denot_ty_in_ctx_under in Hφ.
        eapply denot_ty_expr_total_on_of_formula; eauto 6.
  - intros x Hx n Hn.
    subst L'.
    assert (Hx_body : x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_tm e2)
      by set_solver.
    assert (HxL : x ∉ L) by set_solver.
    assert (Hwf_body :
      choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2).
    {
      destruct Hwf1 as [[[HctxΓ HnonemptyΓ] Hbasicτ1] He1].
      destruct Hwflet as [[_ Hbasicτ2] Hlet].
      eapply choice_typing_wf_from_erased_basic.
      - eapply Basic_CtxComma.
        + exact HctxΓ.
        + eapply Basic_CtxBind.
          * intros Hbad. apply Hx_body. apply elem_of_union_l.
            rewrite erase_ctx_under_dom_basic by exact HctxΓ.
            exact Hbad.
          * exact Hbasicτ1.
        + apply elem_of_disjoint. intros z HzΓ Hzx.
          simpl in Hzx.
          apply elem_of_singleton in Hzx. subst z.
          apply Hx_body. apply elem_of_union_l.
          rewrite erase_ctx_under_dom_basic by exact HctxΓ.
          set_solver.
      - rewrite erase_ctx_under_comma_bind_dom_nf.
        eapply basic_choice_ty_mono; [| exact Hbasicτ2].
        intros z Hz. apply elem_of_union_l.
        rewrite erase_ctx_under_dom_basic by exact HctxΓ.
        eauto 6.
      - eauto 6.
      - rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1)
          by (intros Hbad; apply Hx_body; apply elem_of_union_l; exact Hbad).
        eapply basic_typing_tlete_body_for_fresh.
        + eauto 6.
        + eauto 6.
        + eauto 6.
    }
    pose proof (IH2 x HxL n Hn) as Hφ.
    split.
    + eapply choice_typing_wf_regular_denotation; eauto 6.
    + split; [exact Hφ |].
      unfold denot_ty_in_ctx_under in Hφ.
      eapply denot_ty_expr_total_on_of_formula; eauto 6.
Qed.
