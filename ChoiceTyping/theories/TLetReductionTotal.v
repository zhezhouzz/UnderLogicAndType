(** * ChoiceTyping.TLetReductionTotal

    Total/model-level wrappers for the [tlet] reduction theorem.  The
    fuel-level reduction proof stays in [TLetReduction]. *)

From ChoiceTyping Require Export TLetReduction.
From ChoiceTyping Require Import Auxiliary LetResultWorld Naming ResultWorldClosed
  SoundnessCommon TLetTotal.

Import Tactics.

Lemma expr_total_tlet_reduction
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e1 m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_tm e2 →
  expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
    (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult)
  <->
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m.
Proof.
  intros Hlet HbasicΓ Hctx Htotal1 Hx.
  rewrite erase_ctx_under_comma_bind_dom_nf.
  split.
  - intros Hbody.
    eapply expr_total_on_tlete_intro_strong.
    + eapply denot_ctx_in_env_world_covers_erased; eauto.
    + intros Hbad. apply Hx. apply elem_of_union_l. exact Hbad.
    + intros Hbad. apply Hx. apply elem_of_union_r. exact Hbad.
    + eapply denot_ctx_in_env_world_store_closed_on_erased; eauto.
    + eapply typing_tm_lc; eauto.
    + exact Htotal1.
    + exact Hbody.
  - intros Hlet_total.
    eapply expr_total_on_tlete_elim_body_strong.
    + eapply denot_ctx_in_env_world_covers_erased; eauto.
    + intros Hbad. apply Hx. apply elem_of_union_l. exact Hbad.
    + intros Hbad. apply Hx. apply elem_of_union_r. exact Hbad.
    + eapply denot_ctx_in_env_world_store_closed_on_erased; eauto.
    + eapply typing_tm_lc; eauto.
    + exact Hlet_total.
Qed.

Lemma denot_ty_regular_tlet_context_iff
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) x :
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 →
  denot_ty_regular_in_ctx_under Σ Γ τ1 →
  denot_ty_regular_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 ↔
  denot_ty_regular_in_ctx_under Σ Γ τ2.
Proof.
  intros Hfresh [HctxΓ Hτ1]. split.
  - intros [Hctxcomma Hτ2_body].
    split.
    + inversion Hctxcomma; subst; assumption.
    + eapply basic_choice_ty_drop_fresh.
      * intros Hxτ. apply Hfresh. apply elem_of_union_r. exact Hxτ.
      * replace (dom (erase_ctx_under Σ Γ) ∪ {[x]}) with
          (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)))).
        -- exact Hτ2_body.
        -- rewrite erase_ctx_under_comma_bind_dom_nf. set_solver.
  - intros [HctxΓ' Hτ2].
    split.
    + eapply Basic_CtxComma.
      * exact HctxΓ'.
      * eapply Basic_CtxBind.
        -- rewrite <- (erase_ctx_under_dom_basic Σ Γ HctxΓ').
           set_solver.
        -- replace (dom Σ ∪ ctx_dom Γ) with
             (dom (erase_ctx_under Σ Γ)).
           ++ exact Hτ1.
           ++ rewrite erase_ctx_under_dom_basic by exact HctxΓ'. set_solver.
      * simpl. pose proof (erase_ctx_under_dom_basic Σ Γ HctxΓ') as HdomΓ.
        set_solver.
    + rewrite erase_ctx_under_comma_bind_dom_nf.
      eapply (basic_choice_ty_mono
        (dom (erase_ctx_under Σ Γ))
        (dom (erase_ctx_under Σ Γ) ∪ {[x]})); [set_solver | exact Hτ2].
Qed.

Lemma denot_ty_total_tlet_reduction
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2 →
  denot_ty_total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2
    (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult)
  <->
  denot_ty_total_model_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros He1 Hlet Hctx Hmodel1 Hfreshx.
  pose proof (denot_ty_regular_tlet_context_iff
    Σ Γ τ1 τ2 x ltac:(set_solver)
    (denot_ty_total_model_regular Σ Γ τ1 e1 m Hmodel1))
    as Hregular_iff.
  split; intros Hmodel.
  - destruct Hmodel as [Hregular_body [Hformula_body Htotal_body]].
    pose proof (proj1 (expr_total_tlet_reduction
        Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult Hlet
        (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel1) Hctx
        (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel1)
        ltac:(set_solver))
        Htotal_body) as Htotal_target.
    split.
    + apply (proj1 Hregular_iff). exact Hregular_body.
    + split.
      * apply (proj1 (denot_ty_tlet_reduction_formula_any_world
            τ2 Σ Γ τ1 e1 e2 m x Hfresh Hresult
            (proj1 Hregular_iff Hregular_body) He1 Hlet Hctx
            Htotal_target Hfreshx)).
        exact Hformula_body.
      * exact Htotal_target.
  - destruct Hmodel as [Hregular_target [Hformula_target Htotal_target]].
    split.
    + apply (proj2 Hregular_iff). exact Hregular_target.
    + split.
      * apply (proj2 (denot_ty_tlet_reduction_formula_any_world
            τ2 Σ Γ τ1 e1 e2 m x Hfresh Hresult
            Hregular_target He1 Hlet Hctx Htotal_target Hfreshx)).
        exact Hformula_target.
      * apply (proj2 (expr_total_tlet_reduction
          Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult Hlet
          (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel1) Hctx
          (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel1)
          ltac:(set_solver))).
        exact Htotal_target.
Qed.
