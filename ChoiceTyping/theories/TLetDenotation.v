(** * ChoiceTyping.TLetDenotation

    Denotation-level [tlet] soundness helpers.

    Status note: this file records the intended final shape of the [tlet]
    soundness proof, but the type-denotation transport from an expression-result
    bridge to an arbitrary [denot_ty_on] is still open.  Lemmas below
    [denot_ty_on_expr_result_model_bridge_fresh_bind] should therefore be read
    as conditional plumbing around that missing transport principle, not as a
    completed fundamental [tlet] case. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export TLetExprResult.
From ChoiceTyping Require Import Naming TLetResultBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma denot_ty_on_expr_result_model_bridge_fresh_bind
    Xsrc Xtgt Σ τ esrc etgt x Tx (msrc mtgt : WfWorld) :
  basic_choice_ty (dom Σ) τ →
  x ∉ Xtgt ∪ fv_cty τ →
  expr_result_model_bridge Xsrc esrc Xtgt etgt msrc mtgt →
  msrc ⊨ denot_ty_on Xsrc (<[x := Tx]> Σ) τ esrc →
  mtgt ⊨ denot_ty_on Xtgt Σ τ etgt.
Proof.
(** Open: the current statement is too weak.  The bridge only transports
    formulas whose free variables are included in [Xsrc]/[Xtgt ∪ {ν}], while
    [denot_ty_on] may also observe [dom Σ], [fv_cty τ], and expression free
    variables.  A repaired statement should add explicit scope assumptions such
    as [dom (<[x := Tx]> Σ) ⊆ Xsrc], [dom Σ ⊆ Xtgt],
    [fv_tm esrc ⊆ Xsrc], and [fv_tm etgt ⊆ Xtgt] (or an equivalent packaged
    invariant). *)
Admitted.

Lemma denot_ty_on_let_result_body_to_let
    X Σ τ e1 e2 Tx (L : aset) (m : WfWorld) :
  basic_choice_ty (dom Σ) τ →
  fv_tm (tlete e1 e2) ⊆ X →
  X ⊆ world_dom (m : World) →
  lc_tm (tlete e1 e2) →
  (∀ σ, (m : World) σ → ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
  (∀ σ, (m : World) σ → closed_env (store_restrict σ X)) →
  (∀ σ, (m : World) σ → lc_env (store_restrict σ X)) →
  (∀ σ vx,
    (m : World) σ →
    subst_map (store_restrict σ X) e1 →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  (∀ σ, (m : World) σ → body_tm (subst_map (store_restrict σ X) e2)) →
  (∀ n,
    m ⊑ n →
    ∀ σ v,
      (n : World) σ →
      subst_map (store_restrict σ X) (tlete e1 e2) →* tret v →
      ∅ ⊢ᵥ v ⋮ erase_ty τ) →
  m ⊨ basic_world_formula Σ (dom Σ) →
  (∀ n,
    m ⊑ n →
    X ⊆ world_dom (n : World) →
    (∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
    ∀ x,
      x ∉ L →
      x ∉ world_dom (n : World) →
      x ∉ X ∪ fv_cty τ ∪ fv_tm e2 →
      ∀ Hfresh Hresult,
        expr_total_on (X ∪ {[x]}) (e2 ^^ x)
          (let_result_world_on X e1 x n Hfresh Hresult)) →
  (∀ n,
    m ⊑ n →
    X ⊆ world_dom (n : World) →
    (∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
    ∀ x,
      x ∉ L →
      x ∉ world_dom (n : World) →
      x ∉ X ∪ fv_cty τ ∪ fv_tm e2 →
      ∀ Hfresh Hresult σx v,
        (let_result_world_on X e1 x n Hfresh Hresult : World) σx →
        subst_map (store_restrict σx (X ∪ {[x]})) (e2 ^^ x) →* tret v →
        stale v = ∅ ∧ is_lc v) →
  (∀ n,
    m ⊑ n →
    X ⊆ world_dom (n : World) →
    (∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
    ∀ x,
      x ∉ L →
      x ∉ world_dom (n : World) →
      x ∉ X ∪ fv_cty τ ∪ fv_tm e2 →
      ∀ Hfresh Hresult,
        let_result_world_on X e1 x n Hfresh Hresult ⊨
          denot_ty_on (X ∪ {[x]}) (<[x := Tx]> Σ) τ (e2 ^^ x)) →
  m ⊨ denot_ty_on X Σ τ (tlete e1 e2).
Proof.
  intros Hbasic Hfv HX Hlc Hresult Hclosed Hlc_env Hresult_closed Hbody
    Htyped Hbasic_world Hbody_total Hbody_regular Hbody_model.
  set (x := fresh_for (tlet_fresh_avoid L X τ e2 m)).
  pose proof (tlet_fresh_name_for L X τ e2 m) as Hxname.
  change (tlet_fresh_name L X τ e2 m x) in Hxname.
  destruct Hxname as [HxL Hfresh Hx].
  eapply (denot_ty_on_expr_result_model_bridge_fresh_bind
    (X ∪ {[x]}) X Σ τ (e2 ^^ x) (tlete e1 e2) x Tx
    (let_result_world_on X e1 x m Hfresh Hresult) m).
  - exact Hbasic.
  - set_solver.
  - eapply expr_result_model_bridge_tlete.
    + set_solver.
    + exact Hfv.
    + exact HX.
    + intros σ Hσ. split; [apply Hclosed | apply Hlc_env]; exact Hσ.
    + exact Hlc.
    + intros n Hmn HXn Hresultn Hfreshn Hresultn'.
      eapply Hbody_total; eauto.
  - eapply Hbody_model; eauto; try reflexivity.
Qed.

Lemma denot_tlet_formula_at_world_given_bind_total
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (∀ x, x ∉ L →
    choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1 →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e1 m →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  (∀ x (HxL : x ∉ L)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx),
    let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
      denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))) →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hbody_wf Hm Hτ1 Htotal1 IH2 Hbind.
  destruct Htotal1 as [Hfv1 Hresult].
  set (X := dom (erase_ctx_under Σ Γ)).
  set (x := fresh_for (tlet_fresh_avoid L X τ2 e2 m)).
  pose proof (tlet_fresh_name_for L X τ2 e2 m) as Hxname.
  change (tlet_fresh_name L X τ2 e2 m x) in Hxname.
  destruct Hxname as [HxL Hfresh Hx].
  unfold denot_ty_in_ctx_under.
  subst X.
  eapply denot_ty_on_let_result_body_to_let with
    (Tx := erase_ty τ1)
    (L := L ∪ world_dom (m : World) ∪ dom (erase_ctx_under Σ Γ)
          ∪ fv_cty τ1 ∪ fv_tm e1 ∪ fv_cty τ2 ∪ fv_tm e2).
  - pose proof Hwflet as Hwflet_basic.
    destruct Hwflet_basic as [Hwfτ _].
    pose proof (wf_choice_ty_under_basic Σ Γ τ2 Hwfτ) as Hbasicτ.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hbasicτ.
    + pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ2 Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - pose proof (choice_typing_wf_fv_tm_subset Σ Γ (tlete e1 e2) τ2 Hwflet)
      as Hfv.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact Hfv.
    + pose proof Hwflet as Hwflet_ctx.
      destruct Hwflet_ctx as [Hwfτ _].
      pose proof (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ2 Hwfτ))
        as Hctx.
      unfold erase_ctx_under.
      rewrite dom_union_L, (basic_ctx_erase_dom (dom Σ) Γ Hctx).
      reflexivity.
  - apply (basic_world_formula_dom_subset (erase_ctx_under Σ Γ)
      (dom (erase_ctx_under Σ Γ))).
    apply denot_ctx_in_env_erased_basic. exact Hm.
  - exact (basic_typing_regular_tm
      (erase_ctx_under Σ Γ) (tlete e1 e2) (erase_ty τ2) (proj2 Hwflet)).
  - exact Hresult.
  - intros σ Hσ.
    eapply basic_world_formula_store_restrict_closed_env.
    + apply denot_ctx_in_env_erased_basic. exact Hm.
    + set_solver.
    + exact Hσ.
  - intros σ Hσ.
    eapply basic_world_formula_store_restrict_lc_env.
    + apply denot_ctx_in_env_erased_basic. exact Hm.
    + set_solver.
    + exact Hσ.
  - intros σ vx Hσ Hsteps.
    eapply (choice_typing_wf_result_regular_restrict_in_ctx
      Σ Γ e1 τ1 m σ vx); eauto.
  - intros σ Hσ.
    apply body_tm_msubst.
    + eapply basic_world_formula_store_restrict_closed_env.
      * apply denot_ctx_in_env_erased_basic. exact Hm.
      * set_solver.
      * exact Hσ.
    + eapply basic_world_formula_store_restrict_lc_env.
      * apply denot_ctx_in_env_erased_basic. exact Hm.
      * set_solver.
      * exact Hσ.
    + eapply choice_typing_wf_let_body_helper; eauto.
  - intros n Hmn σ v Hσ Hsteps.
    assert (Hnctx : n ⊨ denot_ctx_in_env Σ Γ).
    { eapply res_models_kripke; eauto. }
    replace (store_restrict σ (dom (erase_ctx_under Σ Γ)))
      with (store_restrict σ (dom (erase_ctx_under Σ Γ))) in Hsteps by reflexivity.
    eapply choice_typing_wf_result_typed_restrict_in_ctx; eauto.
  - apply denot_ctx_in_env_erased_basic. exact Hm.
  - intros n Hmn HXn Hresult_n y HyL Hyfresh Hy Hfresh_y Hresult_y.
    set (wy := let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 y n Hfresh_y Hresult_y).
    assert (HyL0 : y ∉ L) by set_solver.
    assert (Hnctx : n ⊨ denot_ctx_in_env Σ Γ).
    { eapply res_models_kripke; eauto. }
    assert (Hτ1n : n ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1).
    { eapply res_models_kripke; eauto. }
    assert (Hctxy : wy ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τ1))).
    {
      subst wy.
      eapply (let_result_world_on_denot_ctx_in_env
        Σ Γ τ1 e1 y n Hfresh_y Hresult_y).
      - exact Hwf1.
      - exact Hnctx.
      - exact Hτ1n.
      - set_solver.
    }
    destruct (IH2 y HyL0 wy Hctxy) as [_ Hbody_total].
    rewrite erase_ctx_under_comma_bind_dom_nf in Hbody_total.
    exact Hbody_total.
  - intros n Hmn HXn Hresult_n y HyL Hyfresh Hy Hfresh_y Hresult_y σx v Hσx Hsteps.
    set (wy := let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 y n Hfresh_y Hresult_y).
    assert (HyL0 : y ∉ L) by set_solver.
    assert (Hnctx : n ⊨ denot_ctx_in_env Σ Γ).
    { eapply res_models_kripke; eauto. }
    assert (Hτ1n : n ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1).
    { eapply res_models_kripke; eauto. }
    assert (Hctxy : wy ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τ1))).
    {
      subst wy.
      eapply (let_result_world_on_denot_ctx_in_env
        Σ Γ τ1 e1 y n Hfresh_y Hresult_y).
      - exact Hwf1.
      - exact Hnctx.
      - exact Hτ1n.
      - set_solver.
    }
    pose proof (Hbody_wf y HyL0) as Hwf_body.
    replace (dom (erase_ctx_under Σ Γ) ∪ {[y]})
      with (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind y τ1)))) in Hsteps
      by exact (erase_ctx_under_comma_bind_dom_nf Σ Γ y τ1).
    eapply (choice_typing_wf_result_regular_restrict_in_ctx
      Σ (CtxComma Γ (CtxBind y τ1)) (e2 ^^ y) τ2 wy σx v); eauto.
  - intros n Hmn HXn Hresult_n y HyL Hyfresh Hy.
    intros Hfresh_y Hresult_y.
    set (wy := let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 y n Hfresh_y Hresult_y).
    assert (HyL0 : y ∉ L) by set_solver.
    assert (Hnctx : n ⊨ denot_ctx_in_env Σ Γ).
    { eapply res_models_kripke; eauto. }
    assert (Hτ1n : n ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1).
    { eapply res_models_kripke; eauto. }
    assert (Hctxy : wy ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τ1))).
    {
      subst wy.
      eapply (let_result_world_on_denot_ctx_in_env
        Σ Γ τ1 e1 y n Hfresh_y Hresult_y).
      - exact Hwf1.
      - exact Hnctx.
      - exact Hτ1n.
      - set_solver.
    }
	    destruct (IH2 y HyL0 wy Hctxy) as [Hbody _].
	    assert (Hdom_ctxx :
	      (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind y τ1))) : aset) =
	      dom (erase_ctx_under Σ Γ) ∪ {[y]})
        by apply erase_ctx_under_comma_bind_dom_nf.
	    assert (Henv_ctxx :
	      erase_ctx_under Σ (CtxComma Γ (CtxBind y τ1)) =
	      <[y := erase_ty τ1]> (erase_ctx_under Σ Γ)).
    { apply erase_ctx_under_comma_bind_env_fresh. set_solver. }
    unfold denot_ty_in_ctx_under in Hbody.
    rewrite Hdom_ctxx, Henv_ctxx in Hbody.
    exact Hbody.
Qed.

Lemma denot_tlet_formula_at_world_total
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (∀ x, x ∉ L →
    choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hbody_wf IH1 IH2 Hm.
  destruct (IH1 m Hm) as [Hτ1 Htotal1].
  eapply denot_tlet_formula_at_world_given_bind_total; eauto.
  intros x HxL Hfresh Hresult.
  eapply let_result_world_on_denot_ctx_in_env; eauto.
  eapply let_result_world_on_bound_fresh; eauto.
Qed.

Lemma denot_tlet_expr_total_at_world_given_bind
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e1 m →
  (∀ x (HxL : x ∉ L)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx),
    expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
      (e2 ^^ x)
      (let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult)) →
  (∀ σ, (m : World) σ →
    closed_env (store_restrict σ (dom (erase_ctx_under Σ Γ)))) →
  (∀ σ, (m : World) σ →
    lc_env (store_restrict σ (dom (erase_ctx_under Σ Γ)))) →
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m.
Proof.
  intros Hwf1 Hwflet Hm Htotal1 Hbody_total Hclosed Hlc.
  destruct Htotal1 as [Hfv1 Hresult].
  set (X := dom (erase_ctx_under Σ Γ)).
  set (x := fresh_for (body_fresh_avoid L X e2 m)).
  pose proof (body_fresh_name_for L X e2 m) as Hxname.
  change (body_fresh_name L X e2 m x) in Hxname.
  destruct Hxname as [HxL Hfresh HxX Hxe2].
  pose proof (Hbody_total x HxL Hfresh Hresult) as Hbody.
  eapply expr_total_on_tlete_from_open with
    (Hfresh := Hfresh) (Hresult := Hresult).
  - exact HxX.
  - exact Hxe2.
  - exact Hclosed.
  - exact Hlc.
  - intros σ vx Hσ Hsteps.
    subst X.
    eapply (choice_typing_wf_result_regular_restrict_in_ctx
      Σ Γ e1 τ1 m σ vx); eauto.
  - intros σ Hσ.
    apply body_tm_msubst.
    + apply Hclosed. exact Hσ.
    + apply Hlc. exact Hσ.
    + eapply choice_typing_wf_let_body_helper; eauto.
  - subst X.
    rewrite erase_ctx_under_comma_bind_dom_nf in Hbody.
    exact Hbody.
  - pose proof (choice_typing_wf_fv_tm_subset Σ Γ (tlete e1 e2) τ2 Hwflet).
    subst X.
    replace (dom (erase_ctx_under Σ Γ)) with (dom Σ ∪ ctx_dom Γ).
    + exact H.
    + destruct Hwflet as [Hwfτ _].
      unfold erase_ctx_under.
      rewrite dom_union_L.
      rewrite (basic_ctx_erase_dom (dom Σ) Γ
        (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ2 Hwfτ))).
      reflexivity.
Qed.

Lemma denot_tlet_total_at_world_given_bind
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (∀ x, x ∉ L →
    choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  (∀ x (HxL : x ∉ L)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx),
    let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
      denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))) →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros Hwf1 Hwflet Hbody_wf IH1 IH2 Hbind Hm.
  destruct (IH1 m Hm) as [Hτ1 Htotal1].
  split.
  - eapply denot_tlet_formula_at_world_total; eauto.
  - eapply denot_tlet_expr_total_at_world_given_bind; eauto.
    + intros x HxL Hfresh Hresult.
      set (wx := let_result_world_on
        (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult).
      assert (Hctxx : wx ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))).
      { subst wx. apply Hbind; exact HxL. }
      exact (proj2 (IH2 x HxL wx Hctxx)).
    + intros σ Hσ.
      eapply basic_world_formula_store_restrict_closed_env.
      * apply denot_ctx_in_env_erased_basic. exact Hm.
      * set_solver.
      * exact Hσ.
    + intros σ Hσ.
      eapply basic_world_formula_store_restrict_lc_env.
      * apply denot_ctx_in_env_erased_basic. exact Hm.
      * set_solver.
      * exact Hσ.
Qed.

Lemma denot_tlet_total_at_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (∀ x, x ∉ L →
    choice_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))) →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros Hwf1 Hwflet Hbody_wf IH1 IH2 Hm.
  eapply denot_tlet_total_at_world_given_bind; eauto.
  intros x HxL Hfresh Hresult.
  eapply let_result_world_on_denot_ctx_in_env; eauto.
  - exact (proj1 (IH1 m Hm)).
  - eapply let_result_world_on_bound_fresh; eauto.
    exact (proj2 (IH1 m Hm)).
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
  intros Hwf1 Hwf IH1 IH2 m Hm.
  eapply denot_tlet_semantic_at_world; eauto.
Qed.
