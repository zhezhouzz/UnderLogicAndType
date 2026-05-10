(** * ChoiceTyping.TLetDenotation

    Denotation-level [tlet] soundness helpers.  This file should stay close to
    the main [tlet] rule; bulky expression-result bridge experiments live in
    the result-world files instead of here. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps.
From ChoiceTyping Require Export TLetExprResult RegularDenotation.
From ChoiceTyping Require Import Naming TLetResultBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

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
Admitted.

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
  - subst X.
    exact (choice_typing_wf_fv_tm_subset_erase_dom
      Σ Γ (tlete e1 e2) τ2 Hwflet).
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

Import Tactics.

(** High-risk semantic transport for [tlet].

    This is the denotation-level form of the result-world identity:
    first run [e1] and record its possible results at the fresh coordinate [x],
    then type the body [e2 ^^ x]; nested result worlds can be decomposed back
    into the whole-let result world for [tlete e1 e2].

    The proof should use [expr_result_model_bridge_tlete] /
    [let_result_world_on_tlete_decompose] plus the locality of [denot_ty_on] in
    its input domain.  The statement is intentionally about
    [denot_ty_in_ctx_under] so callers do not have to expose the erased-context
    normal forms. *)
Lemma denot_ty_in_ctx_under_tlete_from_body_result_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 x
    (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx) :
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_tm e2 ∪ fv_cty τ2 →
  fv_tm (tlete e1 e2) ⊆ dom (erase_ctx_under Σ Γ) →
  dom (erase_ctx_under Σ Γ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (erase_ctx_under Σ Γ)) m →
  lc_tm (tlete e1 e2) →
  expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
    (e2 ^^ x)
    (let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult) →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
    denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x) →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof. Admitted.

Lemma choice_typing_wf_from_erased_denot_ctx_basic_ty Σ Γ e τ m :
  basic_ctx (dom Σ) Γ →
  basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  choice_typing_wf Σ Γ e τ.
Proof.
  intros Hctx Hτ Hm Herase.
  split; [| exact Herase].
  split.
  - split; [exact Hctx | exists m; exact Hm].
  - rewrite <- (erase_ctx_under_dom_basic Σ Γ Hctx).
    exact Hτ.
Qed.

Lemma denot_ty_total_model_choice_typing_wf Σ Γ e τ m :
  erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ e m →
  choice_typing_wf Σ Γ e τ.
Proof.
  intros Herase Hm Hmodel.
  eapply choice_typing_wf_from_erased_denot_ctx_basic_ty; eauto.
  - exact (denot_ty_total_model_basic_ctx Σ Γ τ e m Hmodel).
  - exact (denot_ty_total_model_basic_choice_ty Σ Γ τ e m Hmodel).
Qed.

Lemma tlet_split_premises_choice_typing_wf_e1
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : choice_ty) e1
    (m : WfWorld) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  choice_typing_wf Σ Γ e1 τ1.
Proof.
  intros Herase Hm Hmodel.
  eapply denot_ty_total_model_choice_typing_wf; eauto.
Qed.

Lemma denot_ctx_in_env_world_store_closed_on_erased
    (Σ : gmap atom ty) (Γ : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_in_env Σ Γ →
  world_store_closed_on (dom (erase_ctx_under Σ Γ)) m.
Proof.
  intros Hm.
  unfold world_store_closed_on.
  intros σ Hσ.
  split.
  - eapply basic_world_formula_store_restrict_closed_env.
    + apply denot_ctx_in_env_erased_basic. exact Hm.
    + set_solver.
    + exact Hσ.
  - eapply basic_world_formula_store_restrict_lc_env.
    + apply denot_ctx_in_env_erased_basic. exact Hm.
    + set_solver.
    + exact Hσ.
Qed.

Lemma tlet_split_premises_body_ctx_from_result
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : choice_ty) e1 x
    (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
  intros Herase Hm Hmodel.
  eapply let_result_world_on_denot_ctx_in_env.
  - eapply tlet_split_premises_choice_typing_wf_e1; eauto.
  - exact Hm.
  - exact (denot_ty_total_model_formula Σ Γ τ1 e1 m Hmodel).
  - eapply let_result_world_on_bound_fresh.
    + eapply tlet_split_premises_choice_typing_wf_e1; eauto.
    + exact Hm.
    + exact (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel).
    + exact Hfresh.
Qed.

Lemma tlet_body_total_model_on_result_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (L : aset) x (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx) :
  x ∉ L →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  (∀ y, y ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind y τ1)) τ2 (e2 ^^ y)) →
  denot_ty_total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
    τ2 (e2 ^^ x)
    (let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult).
Proof.
  intros HxL Herase Hm Hmodel Hbody.
  apply Hbody; [exact HxL |].
  eapply tlet_split_premises_body_ctx_from_result; eauto.
Qed.

Lemma tlet_body_total_on_result_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (L : aset) x (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx) :
  x ∉ L →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  (∀ y, y ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind y τ1)) τ2 (e2 ^^ y)) →
  expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
    (e2 ^^ x)
    (let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult).
Proof.
  intros HxL Herase Hm Hmodel Hbody.
  eapply denot_ty_total_model_total.
  eapply tlet_body_total_model_on_result_world; eauto.
Qed.

Lemma tlet_body_formula_on_result_world
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (L : aset) x (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (dom (erase_ctx_under Σ Γ))) e1 →* tret vx) :
  x ∉ L →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  (∀ y, y ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind y τ1)) τ2 (e2 ^^ y)) →
  let_result_world_on (dom (erase_ctx_under Σ Γ)) e1 x m Hfresh Hresult ⊨
    denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x).
Proof.
  intros HxL Herase Hm Hmodel Hbody.
  eapply denot_ty_total_model_formula.
  eapply tlet_body_total_model_on_result_world; eauto.
Qed.

(** A deliberately split version of [denot_tlet_total_at_world].

    This is not meant to be the final interface.  It records the direction we
    want for the next cleanup: the syntactic/basic obligations are separated
    from the semantic nonemptiness obligations.  In particular, the body context
    [CtxComma Γ (CtxBind x τ1)] still needs its own nonemptiness witness; this
    is the part that should ultimately be derived from the fact that [τ1] is
    inhabited by the result world generated from [e1]. *)
Lemma denot_tlet_total_at_world_split
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    (m : WfWorld) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ2 →
  (∀ x, x ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ty_total_model_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros Herase1 Heraselet Hm Hmodel Hbasicτ2 Hbody.
  pose proof (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel) as HbasicΓ.
  pose proof (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel) as Htotal1.
  destruct Htotal1 as [Hfv1 Hresult].
  set (X := dom (erase_ctx_under Σ Γ)).
  pose proof (denot_ty_total_model_choice_typing_wf
    Σ Γ e1 τ1 m Herase1 Hm Hmodel) as Hwf1.
  pick_tlet_fresh x L X τ2 e2 m.
  destruct Hfresh as [HxL Hfresh_m Hxbody].
  set (m' := let_result_world_on X e1 x m Hfresh_m Hresult).
  pose proof (choice_typing_wf_from_erased_denot_ctx_basic_ty
    Σ Γ (tlete e1 e2) τ2 m HbasicΓ Hbasicτ2 Hm Heraselet) as Hwflet.
  split.
  - split.
    + split; [exact HbasicΓ | exact Hbasicτ2].
    + subst m' X.
      eapply denot_ty_in_ctx_under_tlete_from_body_result_world with
        (x := x) (Hfresh := Hfresh_m) (Hresult := Hresult).
      * set_solver.
      * eapply basic_typing_contains_fv_tm. exact Heraselet.
      * eapply denot_ctx_in_env_world_covers_erased; eauto.
      * eapply denot_ctx_in_env_world_store_closed_on_erased; eauto.
      * exact (basic_typing_regular_tm
          (erase_ctx_under Σ Γ) (tlete e1 e2) (erase_ty τ2) Heraselet).
      * exact (tlet_body_total_on_result_world
          Σ Γ τ1 τ2 e1 e2 L x m Hfresh_m Hresult
          HxL Herase1 Hm Hmodel Hbody).
      * exact (tlet_body_formula_on_result_world
          Σ Γ τ1 τ2 e1 e2 L x m Hfresh_m Hresult
          HxL Herase1 Hm Hmodel Hbody).
  - refine (denot_tlet_expr_total_at_world_given_bind
      Σ Γ τ1 τ2 e1 e2 L m Hwf1 Hwflet Hm (conj Hfv1 Hresult) _ _ _).
    + intros y HyL Hyfresh Hyresult.
      exact (tlet_body_total_on_result_world
        Σ Γ τ1 τ2 e1 e2 L y m Hyfresh Hyresult
        HyL Herase1 Hm Hmodel Hbody).
    + intros σ Hσ.
      exact (proj1 (denot_ctx_in_env_world_store_closed_on_erased
        Σ Γ m Hm σ Hσ)).
    + intros σ Hσ.
      exact (proj2 (denot_ctx_in_env_world_store_closed_on_erased
        Σ Γ m Hm σ Hσ)).
Qed.

(** These lemmas check the direction that matters for the split interface:
    starting from the split premises, recover the pieces of the old
    [denot_tlet_total_at_world] interface that are still genuinely needed.

    Not every old premise should be recoverable.  In particular, the old global
    [entails_total] premise for [e1] is intentionally replaced by the current
    at-world witness below, and the old body [choice_typing_wf] premise bundled
    nonemptiness for every representative name instead of constructing the
    representative actually used by the proof. *)

Lemma tlet_split_premises_body_total_to_entails_total
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e2 (L : aset) :
  (∀ x, x ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  ∀ x, x ∉ L →
    entails_total (denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)))
      (denot_ty_total_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)).
Proof.
  intros Hbody x HxL mx Hctx.
  apply denot_ty_total_model_old.
  exact (Hbody x HxL mx Hctx).
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
