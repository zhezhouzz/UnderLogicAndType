(** * ChoiceTyping.TLetReductionTotal

    Total/model-level bridges for the [tlet] reduction theorem.  The
    type-denotation reduction proof stays in [TLetReduction]. *)

From ChoiceTyping Require Export TLetReduction.
From CoreLang Require Import BasicTypingProps.
From ChoiceTyping Require Import Naming ResultWorldClosed
  ResultWorldExtension SoundnessCommon TLetTotal.

Import Tactics.

Lemma expr_total_tlet_reduction
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (m mx : WfWorld) F x
    (Hclosed_result : world_closed_on (dom (erase_ctx_under Σ Γ)) m) :
  result_extends e1 x m F mx →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  x ∉ dom (erase_ctx_under Σ Γ) →
  expr_total_on (e2 ^^ x) mx
  <->
  expr_total_on (tlete e1 e2) m.
Proof.
  intros Hext Hlet HbasicΓ Hctx Hx.
  split.
  - (* Extension-style operational introduction for tlet totality:
       recompose the body totality on [mx] with the result extension [Hext]
       to recover totality of [tlete e1 e2] on [m]. *)
    admit.
  - intros Htotal_let.
    eapply (expr_total_on_tlete_elim_body_ext
      (world_dom (m : World)) e1 e2 x m mx F).
    + apply result_extends_to_on. exact Hext.
    + set_solver.
    + rewrite <- (denot_ctx_in_env_world_covers_erased Σ Γ m HbasicΓ Hctx).
      eapply basic_typing_contains_fv_tm. exact Hlet.
    + exact (result_extends_fresh _ _ _ _ _ Hext).
    + pose proof (basic_typing_contains_fv_tm
        (erase_ctx_under Σ Γ) (tlete e1 e2) (erase_ty τ2) Hlet)
        as Hfvlet.
      simpl in Hfvlet. set_solver.
    + (* This should be weakened to require closedness only on the free vars;
         [world_dom m] is too large for the current lemma. *)
      admit.
    + eapply typing_tm_lc; eauto.
    + exact Htotal_let.
Admitted.

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
        -- eauto 6.
        -- rewrite erase_ctx_under_comma_bind_dom_nf. set_solver.
  - intros [HctxΓ' Hτ2].
    split.
    + eapply Basic_CtxComma.
      * eauto 6.
      * eapply Basic_CtxBind.
        -- rewrite <- (erase_ctx_under_dom_basic Σ Γ HctxΓ').
           set_solver.
        -- replace (dom Σ ∪ ctx_dom Γ) with
             (dom (erase_ctx_under Σ Γ)).
           ++ eauto 6.
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
    (m mx : WfWorld) F x
    (Hclosed_result : world_closed_on (dom (erase_ctx_under Σ Γ)) m) :
  result_extends e1 x m F mx →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 →
  denot_ty_total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2
    (e2 ^^ x) mx
  <->
  denot_ty_total_model_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros Hext He1 Hlet Hctx Hmodel1 Hfreshx.
  pose proof (denot_ty_regular_tlet_context_iff
    Σ Γ τ1 τ2 x ltac:(set_solver)
    (denot_ty_total_model_regular Σ Γ τ1 e1 m Hmodel1))
    as Hregular_iff.
  assert (Hdom : world_dom (m : World) = dom (erase_ctx_under Σ Γ)).
  {
    (* This is not derivable from the model directly when [m] carries extra
       domain.  The real replacement is an [any_world_ext] lemma: restrict [m]
       to [dom (erase_ctx_under Σ Γ)], commute/restrict the result extension,
       apply [denot_ty_tlet_reduction_in_ctx_ext], and lift back by
       [res_models_minimal_on]. *)
    admit.
  }
  split; intros Hmodel.
  - destruct Hmodel as [Hregular_body [Hformula_body Htotal_body]].
    pose proof (proj1 (expr_total_tlet_reduction
      Σ Γ τ1 τ2 e1 e2 m mx F x Hclosed_result Hext Hlet
      (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel1)
      Hctx ltac:(set_solver)) Htotal_body) as Htotal_target.
    split.
    + apply (proj1 Hregular_iff); eauto 6.
    + split.
      * apply (proj1 (denot_ty_tlet_reduction_in_ctx_ext
          τ2 Σ Γ τ1 e1 e2 m mx F x Hext
          (proj1 Hregular_iff Hregular_body) He1 Hlet Hdom Hctx
          Htotal_target Hfreshx)); eauto 6.
      * exact Htotal_target.
  - destruct Hmodel as [Hregular_target [Hformula_target Htotal_target]].
    pose proof (proj2 (expr_total_tlet_reduction
      Σ Γ τ1 τ2 e1 e2 m mx F x Hclosed_result Hext Hlet
      (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel1)
      Hctx ltac:(set_solver)) Htotal_target) as Htotal_body.
    split.
    + apply (proj2 Hregular_iff); eauto 6.
    + split.
      * apply (proj2 (denot_ty_tlet_reduction_in_ctx_ext
          τ2 Σ Γ τ1 e1 e2 m mx F x Hext Hregular_target
          He1 Hlet Hdom Hctx Htotal_target Hfreshx)); eauto 6.
      * exact Htotal_body.
Admitted.
