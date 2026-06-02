(** * ContextTyping.Soundness

    Fundamental theorem entry point for the current context-type denotation.

    This file restores the proof-facing goal shape from the old ChoiceTyping
    development while keeping the new direct denotation route.  The TLet branch
    is routed through [denot_tlet_direct_in_ctx]; the remaining higher-order and
    branching cases stop at explicit direct bridge lemmas so their future proofs
    can unfold directly to [denot_ty_lvar_gas] instead of rebuilding the old
    helper stack. *)

From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import ContextTypeDenotationSaturate
  ContextTypeDenotationMsubst ContextTypeDenotationCases TLet.
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

Lemma msubst_basic_typing_tm_weaken_same_env Γ σ e T :
  store_closed σ ->
  env_has_type Γ σ ->
  Γ ⊢ₑ e ⋮ T ->
  Γ ⊢ₑ lstore_instantiate_tm (lstore_lift_free σ) e ⋮ T.
Proof.
  intros Hclosed Htyped Hty.
  rewrite lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ change (lstore_to_store (lstore_lift_free σ)) with
        (lstore_free_part (lstore_lift_free σ));
      rewrite lstore_free_part_lift_free; exact (proj1 Hclosed). }
  change (lstore_to_store (lstore_lift_free σ)) with
    (lstore_free_part (lstore_lift_free σ)).
  rewrite lstore_free_part_lift_free.
  pose proof (msubst_basic_typing_tm Γ σ e T
    (proj1 Hclosed) Htyped Hty) as Hsubst.
  eapply basic_typing_weaken_tm; [exact Hsubst|].
  apply map_subseteq_spec.
  intros x U Hlookup.
  destruct (env_delete_lookup_some σ Γ x U Hlookup) as [HΓ _].
  exact HΓ.
Qed.

Lemma lstore_instantiate_tm_at_lift_free_depth_irrel d1 d2 σ e :
  store_closed σ ->
  lstore_instantiate_tm_at d1 (lstore_lift_free σ : LStoreT) e =
  lstore_instantiate_tm_at d2 (lstore_lift_free σ : LStoreT) e.
Proof.
  intros Hclosed.
  rewrite !lstore_instantiate_tm_at_lc_lstore.
  - reflexivity.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
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
  context_typing_wf Σ Γ e τ1 ->
  context_typing_wf Σ Γ e τ2 ->
  sub_type_under Σ Γ τ1 τ2 ->
  m ⊨ denot_ctx_under Σ Γ ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ1 e) ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ τ2 e).
Proof.
  intros Hwf1 Hwf2 Hsub Hctx Hproj Hsrc.
  destruct Hsub as [_ [_ [Herase Himpl]]].
  assert (Hstore_ty : storeA_has_type Σ σΣ).
  { eapply denot_ctx_under_projection_store_has_type; eauto. }
  assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
  {
    pose proof (res_models_scoped _ _ Hctx) as Hscope.
    rewrite denot_ctx_under_unfold_body in Hscope.
    apply formula_scoped_fibvars_l in Hscope.
    rewrite ctx_base_vars_fv in Hscope. exact Hscope.
  }
  assert (Hbase : base_store_projection Σ σΣ mfib).
  { eapply base_store_projection_from_fiber; eauto. }
  pose proof (denot_ty_lvar_gas_msubst_store_from_typing_wf
    (cty_depth τ1) Σ (erase_ctx_under Σ Γ) σΣ τ1 e mfib
    (proj2 Hwf1) Hstore_ty Hbase) as Hto_src.
  unfold denot_ty_in_ctx_under, denot_ty in Hsrc.
  pose proof (Hto_src Hsrc) as Hsrc_inst.
  set (eσ := lstore_instantiate_tm (lstore_lift_free σΣ) e).
  assert (Hfv_eσ : fv_tm eσ ⊆ dom Σ ∪ ctx_dom Γ).
  {
    unfold eσ.
    assert (Hclosed : store_closed σΣ).
    {
      eapply atom_store_has_ltype_closed.
      eapply storeA_has_type_atom_store_has_ltype.
      - exact (proj1 Hbase).
      - exact Hstore_ty.
    }
    pose proof (fv_tm_lstore_instantiate_lift_free_closed_subset
      σΣ e Hclosed) as Hfv_sub.
    pose proof (context_typing_wf_fv_tm_subset Σ Γ e τ2 Hwf2) as Hfv.
    set_solver.
  }
  pose proof (denot_ctx_under_fiber_from_projection
    Σ Γ m mfib σΣ Hproj Hctx) as Hctx_fib.
  pose proof (Himpl eσ Hfv_eσ mfib Hctx_fib) as Himpl_inst.
  unfold denot_ty_in_ctx_under, denot_ty in Himpl_inst.
  pose proof (res_models_impl_elim _ _ _ Himpl_inst Hsrc_inst)
    as Htgt_inst.
  pose proof (denot_ty_lvar_gas_msubst_store_to_typing_wf
    (cty_depth τ2) Σ (erase_ctx_under Σ Γ) σΣ τ2 e mfib
    (proj2 Hwf2) Hstore_ty Hbase Htgt_inst) as Htgt.
  unfold denot_ty_in_ctx_under, denot_ty.
  exact Htgt.
Qed.

Lemma ctx_sub_under_msubst_transport
    (Σ : gmap atom ty) Γ1 Γ2 e τ
    (m mfib : WfWorldT) (σΣ : StoreT) :
  context_typing_wf Σ Γ1 e τ ->
  context_typing_wf Σ Γ2 e τ ->
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
  (denot_ctx_under Σ Γ2 ⊫ denot_ty_in_ctx_under_fiber Σ Γ2 τ e) ->
  m ⊨ denot_ctx_under Σ Γ1 ->
  res_fiber_from_projection m (dom Σ) σΣ mfib ->
  mfib ⊨ formula_msubst_store σΣ (denot_ty_in_ctx_under Σ Γ1 τ e).
Proof.
  intros Hwf1 Hwf2 Hsub IH Hctx Hproj.
  set (X := fv_tm e ∪ fv_cty τ).
  destruct Hsub as [_ [_ [Hagree Hctx_sub]]].
  assert (Hstore_ty : storeA_has_type Σ σΣ).
  { eapply denot_ctx_under_projection_store_has_type; eauto. }
  assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
  {
    pose proof (res_models_scoped _ _ Hctx) as Hscope.
    rewrite denot_ctx_under_unfold_body in Hscope.
    apply formula_scoped_fibvars_l in Hscope.
    rewrite ctx_base_vars_fv in Hscope. exact Hscope.
  }
  assert (Hbase : base_store_projection Σ σΣ mfib).
  { eapply base_store_projection_from_fiber; eauto. }
  pose proof (denot_ctx_under_fiber_from_projection
    Σ Γ1 m mfib σΣ Hproj Hctx) as Hctx_fib1.
  pose proof (Hctx_sub mfib Hctx_fib1) as Hctx2_small.
  pose proof (res_models_kripke
    (res_restrict mfib X) mfib (denot_ctx_under Σ Γ2)
    (res_restrict_le mfib X) Hctx2_small) as Hctx_fib2.
  pose proof (IH mfib Hctx_fib2) as Hden2_fib.
  assert (Hden2_msubst :
    mfib ⊨ formula_msubst_store σΣ
      (denot_ty_in_ctx_under Σ Γ2 τ e)).
  {
    unfold denot_ty_in_ctx_under_fiber in Hden2_fib.
    eapply res_models_FFibVars_singleton_elim; [| |exact Hden2_fib].
    - rewrite ctx_base_vars_fv. exact (proj1 Hbase).
    - rewrite ctx_base_vars_fv. exact (proj2 Hbase).
  }
  pose proof (denot_ty_lvar_gas_msubst_store_from_typing_wf
    (cty_depth τ) Σ (erase_ctx_under Σ Γ2) σΣ τ e mfib
    (proj2 Hwf2) Hstore_ty Hbase) as Hto2.
  unfold denot_ty_in_ctx_under, denot_ty in Hden2_msubst.
  pose proof (Hto2 Hden2_msubst) as Hden2_inst.
  set (eσ := lstore_instantiate_tm (lstore_lift_free σΣ) e).
  assert (Hclosed : store_closed σΣ).
  {
    eapply atom_store_has_ltype_closed.
    eapply storeA_has_type_atom_store_has_ltype.
    - exact (proj1 Hbase).
    - exact Hstore_ty.
  }
  assert (Hfv_eσ : fv_tm eσ ⊆ fv_tm e).
  {
    unfold eσ.
    apply fv_tm_lstore_instantiate_lift_free_closed_subset.
    exact Hclosed.
  }
  assert (Hrel : lvars_fv (denot_relevant_lvars τ eσ) ⊆ X).
  {
    unfold X, eσ, denot_relevant_lvars.
    rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv.
    set_solver.
  }
  assert (Hden2_small :
    res_restrict mfib X ⊨ denot_ty_in_ctx_under Σ Γ2 τ eσ).
  {
    unfold denot_ty_in_ctx_under, denot_ty in Hden2_inst |- *.
    pose proof (res_models_minimal_on X mfib
      (denot_ty_lvar_gas (cty_depth τ)
        (atom_env_to_lty_env (erase_ctx_under Σ Γ2)) τ eσ)
      ltac:(transitivity (fv_tm eσ ∪ fv_cty τ);
        [apply formula_fv_denot_ty_lvar_gas_subset_relevant|];
        unfold denot_relevant_lvars in Hrel;
        rewrite lvars_fv_union, tm_lvars_fv, context_ty_lvars_fv in Hrel;
        set_solver)) as Hmin.
    apply (proj1 Hmin). exact Hden2_inst.
  }
  pose proof (denot_ty_in_ctx_under_restrict_agree_transport
    Σ Γ1 Γ2 X τ eσ mfib Hrel Hagree Hden2_small)
    as Hden1_inst.
  pose proof (denot_ty_lvar_gas_msubst_store_to_typing_wf
    (cty_depth τ) Σ (erase_ctx_under Σ Γ1) σΣ τ e mfib
    (proj2 Hwf1) Hstore_ty Hbase) as Hback1.
  unfold denot_ty_in_ctx_under, denot_ty in Hden1_inst |- *.
  exact (Hback1 Hden1_inst).
Qed.

Lemma fundamental_sub_case_fiber
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (e : tm) (τ1 τ2 : context_ty) :
  context_typing_wf Σ Γ e τ1 ->
  context_typing_wf Σ Γ e τ2 ->
  sub_type_under Σ Γ τ1 τ2 ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ1 e) ->
  denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ2 e.
Proof.
  intros Hwf1 Hwf2 Hsub IH m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - eapply denot_ty_in_ctx_under_fiber_scoped_from_context_typing; eauto.
  - intros σΣ mfib Hproj.
    eapply (sub_type_under_msubst_transport
      Σ Γ e τ1 τ2 m mfib σΣ);
      [exact Hwf1|exact Hwf2|exact Hsub|exact Hctx|exact Hproj|].
    eapply denot_ty_in_ctx_under_fiber_elim_projection; eauto.
Qed.

Lemma fundamental_ctx_sub_case_fiber
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ1 Γ2 : ctx)
    (e : tm) (τ : context_ty) :
  context_typing_wf Σ Γ1 e τ ->
  context_typing_wf Σ Γ2 e τ ->
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
  (denot_ctx_under Σ Γ2 ⊫ denot_ty_in_ctx_under_fiber Σ Γ2 τ e) ->
  denot_ctx_under Σ Γ1 ⊫ denot_ty_in_ctx_under_fiber Σ Γ1 τ e.
Proof.
  intros Hwf1 Hwf2 Hsub IH m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - eapply denot_ty_in_ctx_under_fiber_scoped_from_context_typing; eauto.
  - intros σΣ mfib Hproj.
    eapply (ctx_sub_under_msubst_transport
      Σ Γ1 Γ2 e τ m mfib σΣ);
      [exact Hwf1|exact Hwf2|exact Hsub|exact IH|exact Hctx|exact Hproj].
Qed.

Lemma fundamental_let_case_fiber
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (τ1 τ2 : context_ty) e1 e2 (L : aset) :
  context_typing_wf Σ Γ e1 τ1 ->
  context_typing_wf Σ Γ (tlete e1 e2) τ2 ->
  (forall x, x ∉ L ->
    context_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under_fiber Σ Γ τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under_fiber Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under_fiber Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hwfbody IH1 IH2 m Hctx.
  eapply denot_ty_in_ctx_under_fiber_intro.
  - eapply denot_ty_in_ctx_under_fiber_scoped_from_context_typing; eauto.
  - intros σΣ mfib Hproj.
    assert (HΣm : dom Σ ⊆ world_dom (m : WorldT)).
    {
      pose proof (res_models_scoped _ _ Hctx) as Hscope.
      rewrite denot_ctx_under_unfold_body in Hscope.
      apply formula_scoped_fibvars_l in Hscope.
      rewrite ctx_base_vars_fv in Hscope. exact Hscope.
    }
    assert (Hstore_ty : storeA_has_type Σ σΣ).
    { eapply denot_ctx_under_projection_store_has_type; eauto. }
    assert (Hbase : base_store_projection Σ σΣ mfib).
    { eapply base_store_projection_from_fiber; eauto. }
    pose proof (denot_ctx_under_fiber_from_projection
      Σ Γ m mfib σΣ Hproj Hctx) as Hctx_fib.
    pose proof (IH1 m Hctx) as Hden1_fiber.
    pose proof (denot_ty_in_ctx_under_fiber_elim_projection_instantiated_from_wf
      Σ Γ τ1 e1 m mfib σΣ Hwf1 Hctx Hproj Hden1_fiber)
      as Hden1_inst.
    set (e1σ := lstore_instantiate_tm (lstore_lift_free σΣ) e1).
    pose proof (denot_ty_lvar_gas_guard (cty_depth τ1)
      (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ1 e1σ mfib
      Hden1_inst) as Hguard1.
    repeat rewrite res_models_and_iff in Hguard1.
    destruct Hguard1 as [_ [_ [Hbasic1_inst Htotal1_inst]]].
    set (x := fresh_for
      (L ∪ dom (erase_ctx_under Σ Γ) ∪ world_dom (mfib : WorldT) ∪
       fv_tm e1σ ∪ fv_tm e2 ∪ fv_cty τ2 ∪ dom (σΣ : StoreT))).
    pose proof (fresh_for_not_in
      (L ∪ dom (erase_ctx_under Σ Γ) ∪ world_dom (mfib : WorldT) ∪
       fv_tm e1σ ∪ fv_tm e2 ∪ fv_cty τ2 ∪ dom (σΣ : StoreT))) as Hfresh.
    change (x ∉
      L ∪ dom (erase_ctx_under Σ Γ) ∪ world_dom (mfib : WorldT) ∪
      fv_tm e1σ ∪ fv_tm e2 ∪ fv_cty τ2 ∪ dom (σΣ : StoreT)) in Hfresh.
    assert (HxL : x ∉ L) by set_solver.
    assert (Hxctx : x ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
    assert (Hxworld : x ∉ world_dom (mfib : WorldT)) by set_solver.
    assert (Hxe1σ : x ∉ fv_tm e1σ) by set_solver.
    assert (Hxσ : x ∉ dom (σΣ : StoreT)) by set_solver.
    assert (Hxτ2 : x ∉ fv_cty τ2) by set_solver.
    destruct (expr_result_extension_witness_exists e1σ x Hxe1σ)
      as [Fx HFx].
    assert (Happ : extension_applicable Fx mfib).
    {
      constructor.
      - destruct HFx as [_ [Hin _] _].
        unfold ext_in in Hin. rewrite Hin.
        pose proof (res_models_scoped mfib (expr_total_formula e1σ)
          Htotal1_inst) as Hscope_total.
        unfold formula_scoped_in_world in Hscope_total.
        rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_total.
        exact Hscope_total.
      - destruct HFx as [_ [_ Hout] _].
        unfold ext_out in Hout. rewrite Hout. set_solver.
    }
    destruct (res_extend_by_exists mfib Fx Happ) as [mx Hext].
    assert (Hbase_mx : base_store_projection Σ σΣ mx).
    {
      split; [exact (proj1 Hbase)|].
      pose proof (base_store_projection_to_store_singleton_projection
        Σ σΣ mfib Hbase) as Hbase_single.
      pose proof (store_singleton_projection_extend_base σΣ mfib mx Fx
        Hext Hbase_single) as Hsingle_mx.
      unfold store_singleton_projection in Hsingle_mx.
      rewrite <- (proj1 Hbase). exact Hsingle_mx.
    }
    assert (Hσ_ltype :
      atom_store_has_ltype (atom_env_to_lty_env (erase_ctx_under Σ Γ)) σΣ).
    {
      eapply base_store_projection_atom_store_has_ltype_under; eauto.
      exact (proj1 (proj2 Hwf1)).
    }
    assert (Hσclosed : store_closed σΣ).
    { eapply atom_store_has_ltype_closed. exact Hσ_ltype. }
    assert (Hσ_env : env_has_type (erase_ctx_under Σ Γ) σΣ).
    {
      intros z T v Hlookup Hσz.
      unfold erase_ctx_under in Hlookup.
      apply map_lookup_union_Some_raw in Hlookup
        as [HΣz | [HΣnone HΓz]].
      - eapply Hstore_ty; eauto.
      - exfalso.
        assert (HzΣ : z ∈ dom Σ).
        {
          rewrite <- (proj1 Hbase).
          change (z ∈ dom (σΣ : gmap atom value)).
          rewrite elem_of_dom. eauto.
        }
        apply not_elem_of_dom in HΣnone.
        exact (HΣnone HzΣ).
    }
    assert (He1_basic :
      erase_ctx_under Σ Γ ⊢ₑ e1σ ⋮ erase_ty τ1).
    {
      subst e1σ.
      eapply msubst_basic_typing_tm_weaken_same_env; eauto.
      exact (context_typing_wf_basic_typing Σ Γ e1 τ1 Hwf1).
    }
    assert (Hwf1_inst :
      context_typing_wf_erased Σ (erase_ctx_under Σ Γ) e1σ τ1).
    {
      destruct Hwf1 as [_ [Henv [Hτ _]]].
      repeat split; eauto.
    }
    assert (Harg_ctx :
      mx ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1))).
    {
      eapply denot_ctx_under_comma_bind_from_result_denotation
        with (e1 := e1σ) (m := mfib) (Fx := Fx); eauto.
      intros σΔ msrc HprojΔ.
      eapply denot_ty_in_ctx_under_fiber_elim_erased_source_projection_instantiated_from_wf
        with (m := m) (mfib := mfib) (σΣ := σΣ) (σΔ := σΔ);
        eauto.
      exact (proj2 Hwf1).
    }
    pose proof (IH2 x HxL mx Harg_ctx) as Hbody_fiber.
    assert (Hbody_msubst :
      mx ⊨ formula_msubst_store σΣ
        (denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
          τ2 (e2 ^^ x))).
    {
      unfold denot_ty_in_ctx_under_fiber in Hbody_fiber.
      eapply res_models_FFibVars_singleton_elim; [| |exact Hbody_fiber].
      - rewrite ctx_base_vars_fv. exact (proj1 Hbase_mx).
      - rewrite ctx_base_vars_fv. exact (proj2 Hbase_mx).
    }
    pose proof (denot_ty_lvar_gas_msubst_store_from_typing_wf
      (cty_depth τ2) Σ
      (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))) σΣ τ2
      (e2 ^^ x) mx
      (proj2 (Hwfbody x HxL)) Hstore_ty Hbase_mx) as Hbody_to_inst.
    unfold denot_ty_in_ctx_under, denot_ty in Hbody_msubst.
    pose proof (Hbody_to_inst Hbody_msubst) as Hbody_inst_raw.
    assert (Hbody_inst :
      mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2
        (lstore_instantiate_tm (lstore_lift_free σΣ) (e2 ^^ x))).
    {
      unfold denot_ty_in_ctx_under, denot_ty.
      exact Hbody_inst_raw.
    }
    set (e2σ := lstore_instantiate_tm_at 1 (lstore_lift_free σΣ) e2).
    assert (Hbody_term :
      lstore_instantiate_tm (lstore_lift_free σΣ) (e2 ^^ x) =
      e2σ ^^ x).
    {
      subst e2σ.
      change (e2 ^^ x) with (open_tm 0 (vfvar x) e2).
      change (open_one 0 x
        (lstore_instantiate_tm_at 1 (lstore_lift_free σΣ) e2))
        with (open_tm 0 (vfvar x)
          (lstore_instantiate_tm_at 1 (lstore_lift_free σΣ) e2)).
      rewrite lstore_instantiate_tm_open_fresh_lift_free.
      2:{ exact Hσclosed. }
      2:{ set_solver. }
      change (lstore_instantiate_tm (lstore_lift_free σΣ) e2)
        with (lstore_instantiate_tm_at 0 (lstore_lift_free σΣ) e2).
      rewrite (lstore_instantiate_tm_at_lift_free_depth_irrel
        0 1 σΣ e2 Hσclosed).
      reflexivity.
    }
    assert (Hlet_term :
      lstore_instantiate_tm (lstore_lift_free σΣ) (tlete e1 e2) =
      tlete e1σ e2σ).
    {
      subst e1σ e2σ.
      reflexivity.
    }
    assert (Hlet_basic :
      erase_ctx_under Σ Γ ⊢ₑ tlete e1σ e2σ ⋮ erase_ty τ2).
    {
      pose proof (msubst_basic_typing_tm_weaken_same_env
        (erase_ctx_under Σ Γ) σΣ (tlete e1 e2) (erase_ty τ2)
        Hσclosed Hσ_env
        (context_typing_wf_basic_typing Σ Γ
          (tlete e1 e2) τ2 Hwflet)) as Hbasic_msubst.
      rewrite Hlet_term in Hbasic_msubst.
      exact Hbasic_msubst.
    }
    assert (Hworld_inst :
      mfib ⊨ basic_world_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx_under Σ Γ)) τ2
          (tlete e1σ e2σ))).
    {
      eapply denot_ctx_under_relevant_basic_world. exact Hctx_fib.
    }
    assert (Hbody_direct :
      mx ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1))
        τ2 (e2σ ^^ x)).
    {
      rewrite <- Hbody_term.
      exact Hbody_inst.
    }
    assert (Hdirect :
      mfib ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1σ e2σ)).
    {
      eapply denot_tlet_direct_in_ctx with
        (τ1 := τ1) (Fx := Fx) (x := x) (mx := mx); eauto.
      - intros Hbad.
        apply elem_of_union in Hbad as [Hbad|Hbad].
        + apply Hxctx.
          apply lvars_fv_elem in Hbad.
          rewrite atom_store_to_lvar_store_dom, lvars_fv_of_atoms in Hbad.
          exact Hbad.
        + apply Hxτ2.
          rewrite <- context_ty_lvars_fv.
          apply lvars_fv_elem. exact Hbad.
    }
    pose proof (denot_ty_lvar_gas_msubst_store_to_typing_wf
      (cty_depth τ2) Σ (erase_ctx_under Σ Γ) σΣ τ2
      (tlete e1 e2) mfib
      (proj2 Hwflet) Hstore_ty Hbase) as Hback.
    unfold denot_ty_in_ctx_under, denot_ty in Hdirect |- *.
    rewrite <- Hlet_term in Hdirect.
    exact (Hback Hdirect).
Qed.

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
  intros Hwf IH1 IH2.
  eapply letd_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IH1.
  - exact IH2.
Qed.

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
  intros Hwf IH.
  eapply lam_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IH.
Qed.

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
  intros Hwf IH.
  eapply lamd_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IH.
Qed.

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
  intros Hwf IHfun IHarg.
  eapply app_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IHfun.
  - exact IHarg.
Qed.

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
  intros Hwf IHfun IHarg.
  eapply appd_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IHfun.
  - exact IHarg.
Qed.

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
  intros Hτx Hτ Hwf IH.
  eapply fix_soundness_bridge.
  - exact Hτx.
  - exact Hτ.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IH.
Qed.

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
  intros Hτx Hτ Hwf IH.
  eapply fixd_soundness_bridge.
  - exact Hτx.
  - exact Hτ.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact IH.
Qed.

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
  intros Hwf Hvt Hvf IHt IHf.
  eapply match_both_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact Hvt.
  - exact Hvf.
  - exact IHt.
  - exact IHf.
Qed.

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
  intros Hwf Hv Hunreach IH Het.
  eapply match_true_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact Hv.
  - exact IH.
  - exact Het.
Qed.

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
  intros Hwf Hv Hunreach Het IH.
  eapply match_false_soundness_bridge.
  - unfold context_typing_wf in Hwf. exact (proj2 Hwf).
  - exact Hv.
  - exact Het.
  - exact IH.
Qed.

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
  - eapply (fundamental_sub_case_fiber Φ Σ Γ e τ1 τ2).
    + exact (typing_wf_under Φ Σ Γ e τ1 Hty).
    + exact H.
    + exact H0.
    + exact IHHty.
  - eapply (fundamental_ctx_sub_case_fiber Φ Σ Γ1 Γ2 e τ).
    + exact H.
    + exact (typing_wf_under Φ Σ Γ2 e τ Hty).
    + exact H0.
    + exact IHHty.
  - eapply (fundamental_let_case_fiber Φ Σ Γ τ1 τ2 e1 e2 L).
    + exact (typing_wf_under Φ Σ Γ e1 τ1 Hty).
    + eassumption.
    + intros x Hx.
      exact (typing_wf_under Φ Σ
        (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2 (H0 x Hx)).
    + eassumption.
    + intros x Hx.
      match goal with
      | IH : forall y, y ∉ _ ->
          denot_ctx_under _ (CtxComma _ (CtxBind y _)) ⊫
            denot_ty_in_ctx_under_fiber _ (CtxComma _ (CtxBind y _)) _ (_ ^^ y)
        |- _ =>
          exact (IH x Hx)
      end.
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
