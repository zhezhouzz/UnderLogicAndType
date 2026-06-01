(** * ContextTyping.Soundness

    Fundamental theorem entry point for the current context-type denotation.

    This file restores the proof-facing goal shape from the old ChoiceTyping
    development while keeping the new direct denotation route.  The TLet branch
    is routed through [denot_tlet_direct_in_ctx]; the remaining higher-order and
    branching cases stop at explicit direct bridge lemmas so their future proofs
    can unfold directly to [denot_ty_lvar_gas] instead of rebuilding the old
    helper stack. *)

From CoreLang Require Import BasicTyping SmallStep StrongNormalization.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import ContextTypeDenotationSaturate
  ContextTypeDenotationCases TLet.
From ContextTyping Require Export TLet.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

(** ** Guard facts exposed by type denotation *)

Lemma denot_ty_lvar_gas_guard
    gas (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ denot_ty_lvar_gas gas Σ τ e ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd
      (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))).
Proof.
  intros Hden.
  destruct gas as [|gas']; cbn [denot_ty_lvar_gas] in Hden;
    rewrite res_models_and_iff in Hden;
    exact (proj1 Hden).
Qed.

Lemma denot_ty_in_ctx_under_guard
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env
        (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env
            (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e)
          e (erase_ty τ))
        (expr_total_formula e))).
Proof.
  unfold denot_ty_in_ctx_under, denot_ty.
  apply denot_ty_lvar_gas_guard.
Qed.

Lemma denot_ty_in_ctx_under_context_ty_wf
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ->
  m ⊨ context_ty_wf_formula
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e) τ.
Proof.
  intros Hden.
  pose proof (denot_ty_in_ctx_under_guard Σ Γ τ e m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  exact (proj1 Hguard).
Qed.

Lemma denot_ty_in_ctx_under_basic_world
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ->
  m ⊨ basic_world_formula
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e).
Proof.
  intros Hden.
  pose proof (denot_ty_in_ctx_under_guard Σ Γ τ e m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  exact (proj1 (proj2 Hguard)).
Qed.

Lemma denot_ty_in_ctx_under_basic_typing
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e)
    e (erase_ty τ).
Proof.
  intros Hden.
  pose proof (denot_ty_in_ctx_under_guard Σ Γ τ e m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  exact (proj1 (proj2 (proj2 Hguard))).
Qed.

(** Totality extraction is intentionally a named review point.  The denotation
    guard contains [expr_total_formula], but future proofs around recursive
    functions should decide whether this extraction is direct or goes through
    the well-founded operational totality interface. *)
Lemma denot_ty_in_ctx_under_total
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ->
  m ⊨ expr_total_formula e.
Proof.
  intros Hden.
  pose proof (denot_ty_in_ctx_under_guard Σ Γ τ e m Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  exact (proj2 (proj2 (proj2 Hguard))).
Qed.

Lemma denot_ty_in_ctx_under_fiber_elim_projection_instantiated_from_wf
    (Σ : gmap atom ty) Γ τ e (m mfib : WfWorldT) (σΣ : StoreT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ denot_ctx_under Σ Γ ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  m ⊨ denot_ty_in_ctx_under_fiber Σ Γ τ e ->
  mfib ⊨ denot_ty_lvar_gas (cty_depth τ)
    (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ
    (lstore_instantiate_tm (lstore_lift_free σΣ) e).
Proof.
  intros [_ Hwf_erased] Hctx Hproj Hden.
  eapply denot_ty_in_ctx_under_fiber_elim_projection_instantiated; eauto.
  eapply denot_ctx_under_projection_store_has_type; eauto.
Qed.

(** ** Direct case bridges *)

Lemma context_typing_wf_denot_static_guard
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env
        (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e))
      (expr_basic_typing_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e)
        e (erase_ty τ))).
Proof.
  intros Hwf Hctx.
  pose proof (denot_ctx_under_relevant_basic_world Σ Γ τ e m Hctx)
    as Hworld.
  pose proof (basic_world_formula_models_iff
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e)
    m) as Hworld_iff.
  apply Hworld_iff in Hworld as [Hlc [Hscope Htyped_world]].
  rewrite res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [exact Hscope|].
    apply basic_context_ty_lvars_denot_relevant_env.
    pose proof (context_typing_wf_basic_context_ty_erased Σ Γ e τ Hwf)
      as Hτ.
    unfold basic_context_ty in Hτ.
    rewrite atom_store_to_lvar_store_dom.
    exact Hτ.
  - rewrite res_models_and_iff. split.
    + apply basic_world_formula_models_iff.
      split; [exact Hlc|]. split; [exact Hscope|exact Htyped_world].
    + apply expr_basic_typing_formula_models_iff.
      split; [exact Hlc|]. split; [exact Hscope|].
      apply basic_tm_has_ltype_of_atom_typing.
      * apply denot_relevant_env_closed. apply atom_store_to_lvar_store_closed.
      * apply basic_typing_lty_env_to_atom_env_denot_relevant_env.
      rewrite lvar_store_to_atom_store_atom_store.
      exact (context_typing_wf_basic_typing Σ Γ e τ Hwf).
Qed.

Lemma appop_context_typing_arg_lookup
    (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) ->
  context_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) ->
  erase_ctx_under Σ Γ !! x = Some (erase_ty (primop_arg_ty (Φ op))).
Proof.
  intros Hsig Hwf.
  pose proof (context_typing_wf_basic_typing Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) Hwf) as Hbasic.
  inversion Hbasic as
    [| |Γop op' v arg_b ret_b Hop_type Harg_basic| |]; subst; clear Hbasic.
  inversion Harg_basic as [|Γv xv T Hlookup| |]; subst; clear Harg_basic.
  pose proof (wf_primop_erasure op (Φ op) Hsig) as Herasure.
  unfold primop_erasure_ok in Herasure.
  rewrite Hop_type in Herasure.
  inversion Herasure. subst.
  unfold primop_arg_ty, over_ty.
  cbn [erase_ty].
  exact Hlookup.
Qed.

(** ** Fiberwise case bridges

    The new Fundamental statement is fiberwise over [ctx_base_vars Σ].  These
    are the proof-facing case boundaries for that route.  They intentionally do
    not call the old ambient direct lemmas above. *)

Lemma denot_ty_in_ctx_under_fiber_scoped_from_context_typing
    Σ Γ e τ (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ denot_ctx_under Σ Γ ->
  formula_scoped_in_world m (denot_ty_in_ctx_under_fiber Σ Γ τ e).
Proof.
  intros Hwf Hctx.
  unfold denot_ty_in_ctx_under_fiber, denot_ty_in_ctx_under, denot_ty.
  apply (proj2 (formula_scoped_fibvars_iff m (ctx_base_vars Σ)
    (denot_ty_lvar_gas (cty_depth τ)
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ e))).
  split.
  - rewrite ctx_base_vars_fv.
    pose proof (res_models_scoped _ _ Hctx) as Hscope_ctx.
    rewrite denot_ctx_under_unfold_body in Hscope_ctx.
    apply formula_scoped_fibvars_l in Hscope_ctx.
    rewrite ctx_base_vars_fv in Hscope_ctx.
    exact Hscope_ctx.
  - eapply formula_scoped_in_world_from_formula_fv.
    transitivity (fv_tm e ∪ fv_cty τ).
    + apply formula_fv_denot_ty_lvar_gas_subset_relevant.
    + pose proof (context_typing_wf_fv_tm_subset_erase_dom Σ Γ e τ Hwf) as Htm.
      pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf) as Hτ.
      pose proof (denot_ctx_under_basic_world Σ Γ m Hctx) as Hworld.
      pose proof (proj1 (basic_world_formula_models_iff
        (atom_env_to_lty_env (erase_ctx_under Σ Γ)) m) Hworld)
        as [_ [Hdom _]].
      rewrite atom_store_to_lvar_store_dom in Hdom.
      rewrite lvars_fv_of_atoms in Hdom.
      intros a Ha.
      apply elem_of_union in Ha as [Ha | Ha].
      * apply Hdom. apply Htm. exact Ha.
      * apply Hdom. apply Hτ. exact Ha.
Qed.

Lemma fundamental_var_case_fiber Σ x τ :
  context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ ->
  denot_ctx_under Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under_fiber Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  pose proof (context_typing_wf_wf_context_ty_under Σ (CtxBind x τ)
    (tret (vfvar x)) τ Hwf) as Hwfτ.
  pose proof (wf_context_ty_under_ctx Σ (CtxBind x τ) τ Hwfτ) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ (CtxBind x τ) Hwfctx) as Hbasicctx.
  cbn [basic_ctx] in Hbasicctx.
  destruct Hbasicctx as [HxΣ _].
  eapply denot_ty_in_ctx_under_fiber_intro.
  - unfold denot_ty_in_ctx_under_fiber, denot_ty_in_ctx_under, denot_ty,
      erase_ctx_under.
    cbn [erase_ctx].
    replace (Σ ∪ ({[x := erase_ty τ]} : gmap atom ty))
      with (<[x := erase_ty τ]> Σ).
    2:{
      symmetry.
      apply (storeA_union_singleton_insert_fresh
        (V := ty) (K := atom) (Σ : gmap atom ty) x (erase_ty τ) HxΣ).
    }
    apply (proj2 (formula_scoped_fibvars_iff m (ctx_base_vars Σ)
      (denot_ty (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))))).
    split.
    + rewrite ctx_base_vars_fv.
      pose proof (res_models_scoped _ _ Hctx) as Hscope_ctx.
      rewrite denot_ctx_under_unfold_body in Hscope_ctx.
      apply formula_scoped_fibvars_l in Hscope_ctx.
      rewrite ctx_base_vars_fv in Hscope_ctx.
      exact Hscope_ctx.
    + pose proof (res_models_scoped _ _ Hctx) as Hscope_ctx.
      cbn [denot_ctx_under] in Hscope_ctx.
      apply formula_scoped_fibvars_r in Hscope_ctx.
      apply formula_scoped_and_r in Hscope_ctx.
      exact Hscope_ctx.
  - intros σΣ mfib Hproj.
    pose proof (denot_ctx_under_projected_body Σ (CtxBind x τ)
      m mfib σΣ Hproj Hctx) as Hbody.
    unfold denot_ctx_under_body in Hbody.
    cbn [erase_ctx formula_msubst_store formula_mlsubst] in Hbody.
    rewrite res_models_and_iff in Hbody.
    destruct Hbody as [_ Hbind].
    unfold denot_ty_in_ctx_under, denot_ty, erase_ctx_under.
    cbn [erase_ctx].
    replace (Σ ∪ ({[x := erase_ty τ]} : gmap atom ty))
      with (<[x := erase_ty τ]> Σ).
    2:{
      symmetry.
      apply (storeA_union_singleton_insert_fresh
        (V := ty) (K := atom) (Σ : gmap atom ty) x (erase_ty τ) HxΣ).
    }
    exact Hbind.
Qed.

Lemma fundamental_const_case_fiber Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  denot_ctx_under Σ CtxEmpty ⊫
    denot_ty_in_ctx_under_fiber Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  intros Hwf m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - unfold denot_ty_in_ctx_under_fiber, denot_ty_in_ctx_under, denot_ty,
      erase_ctx_under.
    cbn [erase_ctx].
    replace (Σ ∪ ∅) with Σ
      by (symmetry; apply map_union_empty).
    apply (proj2 (formula_scoped_fibvars_iff m (ctx_base_vars Σ)
      (denot_ty_lvar_gas (cty_depth (const_precise_ty c))
        (atom_env_to_lty_env Σ) (const_precise_ty c) (tret (vconst c))))).
    split.
    + rewrite ctx_base_vars_fv.
      pose proof (res_models_scoped _ _ Hctx) as Hscope_ctx.
      cbn [denot_ctx_under] in Hscope_ctx.
      apply formula_scoped_fibvars_l in Hscope_ctx.
      rewrite ctx_base_vars_fv in Hscope_ctx.
      exact Hscope_ctx.
    + eapply formula_scoped_in_world_from_formula_fv.
      rewrite formula_fv_const_precise_denot_ty_lvar_gas_empty.
      apply empty_subseteq.
  - intros σΣ mfib Hproj.
    unfold denot_ty_in_ctx_under, denot_ty, erase_ctx_under.
    cbn [erase_ctx].
    rewrite formula_msubst_store_fresh.
    + eapply const_direct_denotation_gas_in_ctx.
      * eapply denot_ctx_under_fiber_from_projection; eauto.
      * exact (context_typing_wf_basic_typing Σ CtxEmpty
          (tret (vconst c)) (const_precise_ty c) Hwf).
    + rewrite formula_fv_const_precise_denot_ty_lvar_gas_empty.
      set_solver.
Qed.

Lemma sub_type_under_msubst_transport
    (Σ : gmap atom ty) Γ e τ1 τ2
    (m mfib : WfWorldT) (σΣ : StoreT) :
  sub_type_under Σ Γ τ1 τ2 ->
  m ⊨ denot_ctx_under Σ Γ ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ1 e) ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ2 e).
Proof.
Admitted.

Lemma ctx_sub_under_msubst_transport
    (Σ : gmap atom ty) Γ1 Γ2 e τ
    (m mfib : WfWorldT) (σΣ : StoreT) :
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
  (denot_ctx_under Σ Γ2 ⊫ denot_ty_in_ctx_under_fiber Σ Γ2 τ e) ->
  m ⊨ denot_ctx_under Σ Γ1 ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ1 τ e).
Proof.
Admitted.

Lemma fundamental_sub_case_fiber
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (e : tm) (τ1 τ2 : context_ty) :
  context_typing_wf Σ Γ e τ2 ->
  sub_type_under Σ Γ τ1 τ2 ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ1 e) ->
  denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ2 e.
Proof.
  intros Hwf Hsub IH m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - eapply denot_ty_in_ctx_under_fiber_scoped_from_context_typing; eauto.
  - intros σΣ mfib Hproj.
    eapply sub_type_under_msubst_transport; eauto.
    eapply denot_ty_in_ctx_under_fiber_elim_projection; eauto.
Qed.

Lemma fundamental_ctx_sub_case_fiber
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ1 Γ2 : ctx)
    (e : tm) (τ : context_ty) :
  context_typing_wf Σ Γ1 e τ ->
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
  (denot_ctx_under Σ Γ2 ⊫ denot_ty_in_ctx_under_fiber Σ Γ2 τ e) ->
  denot_ctx_under Σ Γ1 ⊫ denot_ty_in_ctx_under_fiber Σ Γ1 τ e.
Proof.
  intros Hwf Hsub IH m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - eapply denot_ty_in_ctx_under_fiber_scoped_from_context_typing; eauto.
  - intros σΣ mfib Hproj.
    eapply ctx_sub_under_msubst_transport; eauto.
Qed.

Lemma fundamental_let_case_fiber
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (τ1 τ2 : context_ty) e1 e2 (L : aset) :
  context_typing_wf Σ Γ (tlete e1 e2) τ2 ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma fundamental_letd_case_fiber
    (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 ->
  (denot_ctx_under Σ Γ1 ⊫ denot_ty_in_ctx_under_fiber Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_under Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under_fiber Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma fundamental_lam_case_fiber
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (CTArrow τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma fundamental_lamd_case_fiber
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (CTWand τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
Admitted.

Lemma fundamental_app_case_fiber
    (Φ : primop_ctx) Σ Γ τx τ v1 x :
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (CTArrow τx τ) (tret v1)) ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ τx (tret (vfvar x))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fundamental_appd_case_fiber
    (Φ : primop_ctx) Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (denot_ctx_under Σ Γ1 ⊫
    denot_ty_in_ctx_under_fiber Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (denot_ctx_under Σ Γ2 ⊫
    denot_ty_in_ctx_under_fiber Σ Γ2 τx (tret (vfvar x))) ->
  denot_ctx_under Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under_fiber Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ)
      (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fundamental_fix_case_fiber
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (CTArrow τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

Lemma fundamental_fixd_case_fiber
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxStar Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (CTWand τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

Lemma fundamental_appop_case_fiber
    (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) ->
  context_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (primop_arg_ty (Φ op)) (tret (vfvar x))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ ({0 ~> x} (primop_result_ty (Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros Hsig Hwf IH m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - eapply denot_ty_in_ctx_under_fiber_scoped_from_context_typing; eauto.
  - intros σΣ mfib Hproj.
    pose proof (denot_ty_in_ctx_under_fiber_elim_projection Σ Γ
      (primop_arg_ty (Φ op)) (tret (vfvar x)) m mfib σΣ
      Hproj (IH m Hctx)) as Harg.
    pose proof (proj1 (wf_primop_semantic op (Φ op) Hsig x)) as Hop.
    pose proof (appop_context_typing_arg_lookup Φ Σ Γ op x Hsig Hwf)
      as Hlookup.
    unfold denot_ty_in_ctx_under, denot_ty in Harg |- *.
    eapply appop_intro_denotation_msubst.
    + reflexivity.
    + exact (wf_primop_arg_basic op (Φ op) Hsig).
    + exact (wf_primop_result_basic op (Φ op) Hsig).
    + exact Hlookup.
    + exact (context_typing_wf_basic_typing Σ Γ
        (tprim op (vfvar x))
        ({0 ~> x} (primop_result_ty (Φ op))) Hwf).
    + exact Hop.
    + exact Harg.
Qed.

Lemma fundamental_match_both_case_fiber
    (Φ : primop_ctx) Σ Γt Γf v τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf) ->
  (denot_ctx_under Σ Γt ⊫
    denot_ty_in_ctx_under_fiber Σ Γt (bool_precise_ty true) (tret v)) ->
  (denot_ctx_under Σ Γf ⊫
    denot_ty_in_ctx_under_fiber Σ Γf (bool_precise_ty false) (tret v)) ->
  (denot_ctx_under Σ Γt ⊫ denot_ty_in_ctx_under_fiber Σ Γt τt et) ->
  (denot_ctx_under Σ Γf ⊫ denot_ty_in_ctx_under_fiber Σ Γf τf ef) ->
  denot_ctx_under Σ (CtxSum Γt Γf) ⊫
    denot_ty_in_ctx_under_fiber Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch v et ef).
Proof.
Admitted.

Lemma fundamental_match_true_case_fiber
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (bool_precise_ty true) (tret v)) ->
  branch_unreachable Σ Γ v false ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ et) ->
  erase_ctx_under Σ Γ ⊢ₑ ef ⋮ erase_ty τ ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ τ (tmatch v et ef).
Proof.
Admitted.

Lemma fundamental_match_false_case_fiber
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ (bool_precise_ty false) (tret v)) ->
  branch_unreachable Σ Γ v true ->
  erase_ctx_under Σ Γ ⊢ₑ et ⋮ erase_ty τ ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ ef) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ τ (tmatch v et ef).
Proof.
Admitted.

(** ** Fundamental theorem *)

Theorem Fundamental
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) :
  wf_primop_ctx Φ ->
  has_context_type Φ Σ Γ e τ ->
  denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ e.
Proof.
  intros HΦ Hty.
  induction Hty.
  - eapply fundamental_var_case_fiber; eauto.
  - eapply fundamental_const_case_fiber; eauto.
  - eapply fundamental_sub_case_fiber; eauto.
  - eapply fundamental_ctx_sub_case_fiber; eauto.
  - eapply fundamental_let_case_fiber; eauto.
  - eapply fundamental_letd_case_fiber; eauto.
  - eapply fundamental_lam_case_fiber; eauto.
  - eapply fundamental_lamd_case_fiber; eauto.
  - eapply fundamental_app_case_fiber; eauto.
  - eapply fundamental_appd_case_fiber; eauto.
  - eapply fundamental_fix_case_fiber; eauto.
  - eapply fundamental_fixd_case_fiber; eauto.
  - eapply fundamental_appop_case_fiber; eauto.
  - eapply fundamental_match_both_case_fiber; eauto.
  - eapply fundamental_match_true_case_fiber; eauto.
  - eapply fundamental_match_false_case_fiber; eauto.
Qed.

(** ** Corollary targets *)

Corollary safety (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ ->
  has_context_type Φ ∅ CtxEmpty e (CTOver b qual_top) ->
  forall e', e →* e' -> is_val e' \/ exists e'', step e' e''.
Proof.
Admitted.

Corollary coverage (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ ->
  has_context_type Φ ∅ CtxEmpty e (CTUnder b qual_top) ->
  exists v, e →* tret v.
Proof.
Admitted.

Corollary refinement
    (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ ->
  has_context_type Φ ∅ CtxEmpty e (CTOver b φ) ->
  forall v, e →* tret v ->
    exists x (s : LStoreOnT (qual_vars (φ ^q^ x))),
      lso_store s !! LVFree x = Some v /\
      qual_prop (φ ^q^ x) s.
Proof.
Admitted.

Corollary incorrectness
    (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ ->
  has_context_type Φ ∅ CtxEmpty e (CTUnder b φ) ->
  exists v x (s : LStoreOnT (qual_vars (φ ^q^ x))),
    e →* tret v /\
    lso_store s !! LVFree x = Some v /\
    qual_prop (φ ^q^ x) s.
Proof.
Admitted.

Corollary exact_result (Φ : primop_ctx) (e : tm) (b : base_ty) (c : constant) :
  wf_primop_ctx Φ ->
  has_context_type Φ ∅ CtxEmpty e (CTUnder b (b0:c= c)) ->
  e →* tret (vconst c).
Proof.
Admitted.
