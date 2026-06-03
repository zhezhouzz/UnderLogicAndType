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
        (atom_env_to_lty_env (erase_ctx Γ)) τ e) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx Γ)) τ e))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env
            (atom_env_to_lty_env (erase_ctx Γ)) τ e)
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
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e) τ.
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
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e).
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
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e)
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
  (* Compatibility obligation for the old fiberwise Fundamental route. *)
Admitted.

(** ** Direct case bridges *)

Lemma context_typing_wf_denot_static_guard
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env
        (atom_env_to_lty_env (erase_ctx Γ)) τ e) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx Γ)) τ e))
      (expr_basic_typing_formula
        (denot_relevant_env
          (atom_env_to_lty_env (erase_ctx Γ)) τ e)
        e (erase_ty τ))).
Proof.
  intros Hwf Hctx.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as Hbasicctx.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasicctx) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ Hbasicctx) as HfreshΓ.
  assert (Hworld :
      m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e)).
  {
    eapply basic_world_formula_subenv.
    - intros v T Hv.
      unfold denot_relevant_env, lty_env_restrict_lvars in Hv.
      apply storeA_restrict_lookup_some in Hv as [_ Hv].
      destruct v as [k|x].
      + rewrite atom_store_to_lvar_store_lookup_bound_none in Hv.
        discriminate.
      + rewrite atom_store_to_lvar_store_lookup_free in Hv.
        unfold erase_ctx_under.
        rewrite atom_store_to_lvar_store_lookup_free.
        apply map_lookup_union_Some_raw. right.
        split; [|exact Hv].
        apply not_elem_of_dom.
        apply elem_of_dom_2 in Hv.
        rewrite HdomΓ in Hv.
        better_set_solver.
    - exact (denot_ctx_under_basic_world Σ Γ m Hctx).
  }
  apply basic_world_formula_models_iff in Hworld
    as [Hlc [Hscope Htyped_world]].
  rewrite res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [exact Hscope|].
    apply basic_context_ty_lvars_denot_relevant_env.
    pose proof (context_typing_wf_basic_context_ty_erased Σ Γ e τ Hwf)
      as Hτ.
    rewrite atom_store_to_lvar_store_dom.
    apply basic_context_ty_to_lvars.
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
  erase_ctx Γ !! x = Some (erase_ty (primop_arg_ty (Φ op))).
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

(** ** Direct case bridges *)

Lemma denot_var_direct_in_ctx Σ x τ :
  context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ ->
  denot_ctx_under Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
Admitted.

Lemma fundamental_var_case Σ x τ :
  context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ ->
  denot_ctx_under Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  apply denot_var_direct_in_ctx.
Qed.

Lemma denot_const_direct_in_ctx Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  denot_ctx_under Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  intros Hwf m _.
  unfold denot_ty_in_ctx_under, denot_ty.
  replace (erase_ctx CtxEmpty) with (erase_ctx_under ∅ CtxEmpty).
  2:{
    unfold erase_ctx_under. cbn [erase_ctx].
    reflexivity.
  }
  eapply const_direct_denotation_gas_in_ctx with (Σ := ∅).
  - cbn [denot_ctx_under].
    rewrite res_models_and_iff.
    split.
    + apply basic_world_formula_empty.
    + apply res_models_true.
  - exact (context_typing_wf_basic_typing Σ CtxEmpty
      (tret (vconst c)) (const_precise_ty c) Hwf).
Qed.

Lemma fundamental_const_case Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  denot_ctx_under Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  apply denot_const_direct_in_ctx.
Qed.

Lemma fundamental_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (e : tm) (τ1 τ2 : context_ty) :
  context_typing_wf Σ Γ e τ2 ->
  sub_type_under Σ Γ τ1 τ2 ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e) ->
  denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 e.
Proof.
  intros Hwf Hsub IH m HΓ.
  destruct Hsub as [_ [_ [_ [Herase Hent]]]].
  pose proof (context_typing_wf_basic_typing Σ Γ e τ2 Hwf) as Hbasic.
  rewrite <- Herase in Hbasic.
  pose proof (Hent e Hbasic m HΓ) as Himpl.
  eapply res_models_impl_elim; [exact Himpl|].
  exact (IH m HΓ).
Qed.

Lemma fundamental_ctx_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ1 Γ2 : ctx)
    (e : tm) (τ : context_ty) :
  context_typing_wf Σ Γ1 e τ ->
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
  (denot_ctx_under Σ Γ2 ⊫ denot_ty_in_ctx_under Σ Γ2 τ e) ->
  denot_ctx_under Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ e.
Proof.
Admitted.

Lemma denot_ctx_under_comma_bind_from_result_extension
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf Σ Γ e1 τ1 ->
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx Γ) ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
Admitted.

Lemma denot_ctx_under_local_relevant_basic_world
    (Σ : gmap atom ty) (Γ : ctx) τ e (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ denot_ctx_under Σ Γ ->
  m ⊨ basic_world_formula
    (denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e).
Proof.
Admitted.

Lemma fundamental_let_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (τ1 τ2 : context_ty) e1 e2 (L : aset) :
  context_typing_wf Σ Γ e1 τ1 ->
  context_typing_wf Σ Γ (tlete e1 e2) τ2 ->
  (forall x, x ∉ L ->
    context_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma fundamental_letd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 ->
  (denot_ctx_under Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_under Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof.
  intros Hwf IH1 IH2.
  eapply letd_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ (CtxStar Γ1 Γ2)
      (tlete e1 e2) τ2 Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ (CtxStar Γ1 Γ2)
      τ2 (tlete e1 e2) m Hwf Hctx).
Qed.

Lemma fundamental_lam_case
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
  intros Hwf IH.
  eapply lam_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e)) m Hwf Hctx).
Qed.

Lemma fundamental_lamd_case
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
  intros Hwf IH.
  eapply lamd_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ
      (CTWand τx τ) (tret (vlam (erase_ty τx) e)) m Hwf Hctx).
Qed.

Lemma fundamental_app_case
    (Φ : primop_ctx) Σ Γ τx τ v1 x :
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τx (tret (vfvar x))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf IHfun IHarg.
  eapply app_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ
      (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ
      ({0 ~> x} τ) (tapp v1 (vfvar x)) m Hwf Hctx).
Qed.

Lemma fundamental_appd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (denot_ctx_under Σ Γ1 ⊫
    denot_ty_in_ctx_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (denot_ctx_under Σ Γ2 ⊫
    denot_ty_in_ctx_under Σ Γ2 τx (tret (vfvar x))) ->
  denot_ctx_under Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ)
      (tapp v1 (vfvar x)).
Proof.
  intros Hwf IHfun IHarg.
  eapply appd_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ (CtxStar Γ1 Γ2)
      (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ (CtxStar Γ1 Γ2)
      ({0 ~> x} τ) (tapp v1 (vfvar x)) m Hwf Hctx).
Qed.

Lemma fundamental_fix_case
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf IH.
  eapply fix_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ
      (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf)) m Hwf Hctx).
Qed.

Lemma fundamental_fixd_case
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf IH.
  eapply fixd_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTWand τx τ) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ
      (CTWand τx τ) (tret (vfix (TBase b →ₜ t) vf)) m Hwf Hctx).
Qed.

Lemma fundamental_appop_case
    (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) ->
  context_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (primop_arg_ty (Φ op)) (tret (vfvar x))) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ ({0 ~> x} (primop_result_ty (Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros Hsig Hwf IH m Hctx.
  pose proof (proj1 (wf_primop_semantic op (Φ op) Hsig x)) as Hop.
  pose proof (appop_context_typing_arg_lookup Φ Σ Γ op x Hsig Hwf)
    as Hlookup.
  pose proof (IH m Hctx) as Harg.
  unfold denot_ty_in_ctx_under, denot_ty in Harg |- *.
  eapply appop_intro_denotation.
  - reflexivity.
  - exact (wf_primop_arg_basic op (Φ op) Hsig).
  - exact (wf_primop_result_basic op (Φ op) Hsig).
  - exact Hlookup.
  - exact (context_typing_wf_basic_typing Σ Γ
      (tprim op (vfvar x))
      ({0 ~> x} (primop_result_ty (Φ op))) Hwf).
  - exact Hop.
  - exact Harg.
Qed.

Lemma fundamental_match_both_case
    (Φ : primop_ctx) Σ Γt Γf v τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf) ->
  (denot_ctx_under Σ Γt ⊫
    denot_ty_in_ctx_under Σ Γt (bool_precise_ty true) (tret v)) ->
  (denot_ctx_under Σ Γf ⊫
    denot_ty_in_ctx_under Σ Γf (bool_precise_ty false) (tret v)) ->
  (denot_ctx_under Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt τt et) ->
  (denot_ctx_under Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf τf ef) ->
  denot_ctx_under Σ (CtxSum Γt Γf) ⊫
    denot_ty_in_ctx_under Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch v et ef).
Proof.
  intros Hwf Ht Hf IHt IHf.
  eapply match_both_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ (CtxSum Γt Γf)
      (tmatch v et ef) (CTSum τt τf) Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ (CtxSum Γt Γf)
      (CTSum τt τf) (tmatch v et ef) m Hwf Hctx).
Qed.

Lemma fundamental_match_true_case
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty true) (tret v)) ->
  branch_unreachable Σ Γ v false ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ et) ->
  erase_ctx Γ ⊢ₑ ef ⋮ erase_ty τ ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof.
  intros Hwf IHtrue Hunreach IHt Hef.
  eapply match_true_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ (tmatch v et ef) τ Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ τ
      (tmatch v et ef) m Hwf Hctx).
Qed.

Lemma fundamental_match_false_case
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty false) (tret v)) ->
  branch_unreachable Σ Γ v true ->
  erase_ctx Γ ⊢ₑ et ⋮ erase_ty τ ->
  (denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ ef) ->
  denot_ctx_under Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof.
  intros Hwf IHfalse Hunreach Het IHf.
  eapply match_false_soundness_bridge; eauto.
  - exact (context_typing_wf_basic_typing Σ Γ (tmatch v et ef) τ Hwf).
  - intros m Hctx.
    exact (context_typing_wf_denot_static_guard Σ Γ τ
      (tmatch v et ef) m Hwf Hctx).
Qed.

(** ** Fundamental theorem *)

Theorem Fundamental
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) :
  wf_primop_ctx Φ ->
  has_context_type Φ Σ Γ e τ ->
  denot_ctx_under Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ e.
Proof.
  intros HΦ Hty.
  induction Hty.
  - eapply fundamental_var_case; eauto.
  - eapply fundamental_const_case; eauto.
  - eapply fundamental_sub_case; eauto.
  - eapply fundamental_ctx_sub_case; eauto.
  - eapply fundamental_let_case; eauto using typing_wf_under.
  - eapply fundamental_letd_case; eauto.
  - eapply fundamental_lam_case; eauto.
  - eapply fundamental_lamd_case; eauto.
  - eapply fundamental_app_case; eauto.
  - eapply fundamental_appd_case; eauto.
  - eapply fundamental_fix_case; eauto.
  - eapply fundamental_fixd_case; eauto.
  - eapply fundamental_appop_case; eauto.
  - eapply fundamental_match_both_case; eauto.
  - eapply fundamental_match_true_case; eauto.
  - eapply fundamental_match_false_case; eauto.
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
