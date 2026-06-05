(** * ContextTyping.Soundness

    Fundamental theorem entry point for the current context-type denotation.

    This file restores the proof-facing goal shape from the old ChoiceTyping
    development while keeping the new direct denotation route.  The TLet branch
    chooses the result-extension witness locally and calls
    [tlet_intro_denotation] directly; the remaining
    higher-order and branching cases stop at explicit direct bridge lemmas so
    their future proofs can unfold directly to [ty_denote_gas] instead of
    rebuilding the old helper stack. *)

From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLam.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

(** ** Guard facts exposed by type denotation *)

Lemma ty_denote_under_guard
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ ty_denote_under Σ Γ τ e ->
	m ⊨ ty_guard_formula
      (relevant_env
        (atom_env_to_lty_env (erase_ctx Γ)) τ e)
      τ e.
Proof.
  unfold ty_denote_under, ty_denote.
  apply ty_denote_gas_guard_formula.
Qed.

(** Totality extraction is intentionally a named review point.  The denotation
    guard contains [expr_total_formula], but future proofs around recursive
    functions should decide whether this extraction is direct or goes through
    the well-founded operational totality interface. *)
Lemma ty_denote_under_total
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ ty_denote_under Σ Γ τ e ->
  m ⊨ expr_total_formula e.
Proof.
  intros Hden.
  pose proof (ty_denote_under_guard Σ Γ τ e m Hden) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  exact (proj2 (proj2 (proj2 Hguard))).
Qed.

(** ** Direct case bridges *)

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
  ctx_denote_under Σ (CtxBind x τ) ⊫
    ty_denote_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  pose proof (ctx_denote_under_bind_inv Σ x τ m Hctx) as Hbind.
  unfold ty_denote_under, ty_denote in Hbind |- *.
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ (tret (vfvar x)));
    [reflexivity | | exact Hbind].
  assert (Hrel :
      relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}).
  {
    apply relevant_lvars_ret_fvar_subset_singleton.
    eapply context_typing_wf_bind_context_ty; eauto.
  }
  rewrite <- (lty_env_restrict_lvars_twice_subset
    (atom_env_to_lty_env
      (<[x := erase_ty τ]>
        (store_restrict Σ (ctx_fv (CtxBind x τ)))))
    ({[LVFree x]}) (relevant_lvars τ (tret (vfvar x))) Hrel).
  rewrite atom_env_insert_restrict_singleton.
  rewrite (lty_env_restrict_lvars_twice_subset
    (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty)))
    ({[LVFree x]}) (relevant_lvars τ (tret (vfvar x))) Hrel).
  reflexivity.
Qed.

Lemma fundamental_var_case Σ x τ :
  context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ ->
  ctx_denote_under Σ (CtxBind x τ) ⊫
    ty_denote_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  apply denot_var_direct_in_ctx.
Qed.

Lemma denot_const_direct_in_ctx Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  ctx_denote_under Σ CtxEmpty ⊫
    ty_denote_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  intros Hwf m _.
  unfold ty_denote_under, ty_denote.
  replace (erase_ctx CtxEmpty) with (ctx_erasure_under ∅ CtxEmpty).
  2:{
    unfold ctx_erasure_under. cbn [erase_ctx].
    reflexivity.
  }
  eapply const_direct_denotation_gas_in_ctx with (Σ := ∅).
  - cbn [ctx_denote_under].
    rewrite res_models_and_iff.
    split.
    + apply basic_world_formula_empty.
    + apply res_models_true.
  - exact (context_typing_wf_basic_typing Σ CtxEmpty
      (tret (vconst c)) (const_precise_ty c) Hwf).
Qed.

Lemma fundamental_const_case Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  ctx_denote_under Σ CtxEmpty ⊫
    ty_denote_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  apply denot_const_direct_in_ctx.
Qed.

Lemma fundamental_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (e : tm) (τ1 τ2 : context_ty) :
  context_typing_wf Σ Γ e τ2 ->
  sub_type_under Σ Γ τ1 τ2 ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ1 e) ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ2 e.
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
  (ctx_denote_under Σ Γ2 ⊫ ty_denote_under Σ Γ2 τ e) ->
  ctx_denote_under Σ Γ1 ⊫ ty_denote_under Σ Γ1 τ e.
Proof.
  intros Hwf Hsub IH m HΓ1.
  destruct Hsub as [_ [_ [Hagree Hctxsub]]].
  destruct (Hctxsub m HΓ1) as [m' [Hle HΓ2]].
  pose proof (IH m' HΓ2) as Hden2.
  assert (Hden1_m' : m' ⊨ ty_denote_under Σ Γ1 τ e).
  {
    unfold ty_denote_under, ty_denote in Hden2 |- *.
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ e); [reflexivity | | exact Hden2].
    apply atom_env_to_lty_env_restrict_lvars_agree_on
      with (X := fv_tm e ∪ fv_cty τ).
    - intros x Hx. symmetry. apply Hagree. exact Hx.
    - rewrite relevant_lvars_fv. set_solver.
  }
  eapply res_models_from_restrict_extension_on_fv
    with (X := fv_tm e ∪ fv_cty τ) (n := m').
  - unfold ty_denote_under, ty_denote.
    apply formula_fv_ty_denote_gas_subset_relevant.
  - unfold ty_denote_under, ty_denote.
    pose proof (formula_fv_ty_denote_gas_subset_relevant
      (cty_depth τ) (atom_env_to_lty_env (erase_ctx Γ1)) τ e) as Hfvden.
    pose proof (context_typing_wf_fv_tm_subset Σ Γ1 e τ Hwf)
      as Htm.
    pose proof (context_typing_wf_fv_cty_subset_erase_dom Σ Γ1 e τ Hwf)
      as Hτ.
    pose proof (ctx_denote_under_basic_world Σ Γ1 m HΓ1) as Hworld.
    pose proof (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ Γ1) m Hworld) as Hdom.
    unfold ctx_erasure_under in Hdom.
    set_solver.
  - exact Hle.
  - exact Hden1_m'.
Qed.

Lemma ctx_bind_of_result_ext
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf Σ Γ e1 τ1 ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (ctx_erasure_under Σ Γ) ->
  res_extend_by m Fx mx ->
  mx ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind x τ1).
Proof.
  intros Hwf Hctx Hden HFx HxΔ Hext.
  pose proof (context_typing_wf_ctx Σ Γ e1 τ1 Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hsource_full :
      m ⊨ ty_denote_gas (cty_depth τ1)
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ)) τ1 e1).
  {
    unfold ty_denote_under, ty_denote in Hden.
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ1 e1); [reflexivity| |exact Hden].
    apply atom_env_to_lty_env_restrict_lvars_agree_on
      with (X := fv_tm e1 ∪ fv_cty τ1).
    - intros y Hy.
      assert (HyΓ : y ∈ dom (erase_ctx Γ)).
      {
        pose proof (context_typing_wf_fv_tm_subset
          Σ Γ e1 τ1 Hwf) as Htm.
        pose proof (context_typing_wf_fv_cty_subset_erase_dom
          Σ Γ e1 τ1 Hwf) as Hτ.
        set_solver.
      }
      apply erase_ctx_lookup_ctx_erasure_under_of_basic_ctx; assumption.
    - rewrite relevant_lvars_fv. set_solver.
  }
  assert (Htarget :
      mx ⊨ ty_denote_gas (cty_depth τ1)
        (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
        τ1 (tret (vfvar x))).
  {
    replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree x := erase_ty τ1]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply ty_denote_gas_result_ext; eauto.
    - apply atom_store_to_lvar_store_closed.
    - apply atom_env_to_lty_env_dom_free_notin. exact HxΔ.
  }
  assert (Hworld_mx :
      mx ⊨ basic_world_formula
        (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))).
  {
    replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree x := erase_ty τ1]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply basic_world_insert_of_arg.
    - apply atom_env_to_lty_env_dom_free_notin. exact HxΔ.
    - eapply res_models_extend_mono; eauto.
      eapply ctx_denote_under_basic_world; eauto.
    - replace (atom_env_to_lty_env
          (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
        with (<[LVFree x := erase_ty τ1]>
          (atom_env_to_lty_env (ctx_erasure_under Σ Γ))) in Htarget.
      + exact Htarget.
      + symmetry. apply atom_store_to_lvar_store_insert.
  }
  eapply ctx_bind_from_inserted_erasure_denotation.
  - exact HxΔ.
  - eapply ctx_erasure_under_agree_union_on_ty. exact Hwf.
  - exact Hworld_mx.
  - exact Htarget.
Qed.

Lemma ctx_comma_bind_of_result_ext
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf Σ Γ e1 τ1 ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx Γ) ->
  res_extend_by m Fx mx ->
  mx ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
  intros Hwf Hctx Hden HFx HxΓ Hext.
  pose proof (context_typing_wf_ctx Σ Γ e1 τ1 Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ HbasicΓ) as HfreshΓ.
  assert (HΔworld : dom (ctx_erasure_under Σ Γ) ⊆ world_dom (m : WorldT)).
  {
    pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
    exact (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ Γ) m Hworld).
  }
  assert (HxΔ : x ∉ dom (ctx_erasure_under Σ Γ)).
  {
    intros Hx.
    pose proof (HΔworld x Hx) as Hxworld.
    pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hout_fresh.
    change (ext_out Fx ## world_dom (m : WorldT)) in Hout_fresh.
    destruct HFx as [_ [_ Hout] _].
    assert (x ∈ ext_out Fx) by (rewrite Hout; set_solver).
    set_solver.
  }
  assert (Hctx_mx : mx ⊨ ctx_denote_under Σ Γ).
  {
    eapply res_models_extend_mono; eauto.
  }
  assert (Hsource_full :
      m ⊨ ty_denote_gas (cty_depth τ1)
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ)) τ1 e1).
  {
    unfold ty_denote_under, ty_denote in Hden.
    eapply res_models_ty_denote_gas_env_agree_on
      with (X := relevant_lvars τ1 e1); [reflexivity| |exact Hden].
    apply atom_env_to_lty_env_restrict_lvars_agree_on
      with (X := fv_tm e1 ∪ fv_cty τ1).
    - intros y Hy.
      assert (HyΓ : y ∈ dom (erase_ctx Γ)).
      {
        pose proof (context_typing_wf_fv_tm_subset
          Σ Γ e1 τ1 Hwf) as Htm.
        pose proof (context_typing_wf_fv_cty_subset_erase_dom
          Σ Γ e1 τ1 Hwf) as Hτ.
        set_solver.
      }
      apply erase_ctx_lookup_ctx_erasure_under_of_basic_ctx; assumption.
    - rewrite relevant_lvars_fv. set_solver.
  }
  assert (Htarget :
      mx ⊨ ty_denote_gas (cty_depth τ1)
        (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
        τ1 (tret (vfvar x))).
  {
    replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree x := erase_ty τ1]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply ty_denote_gas_result_ext; eauto.
    - apply atom_store_to_lvar_store_closed.
    - apply atom_env_to_lty_env_dom_free_notin. exact HxΔ.
  }
  assert (Hworld_mx :
      mx ⊨ basic_world_formula
        (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))).
  {
    replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree x := erase_ty τ1]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply basic_world_insert_of_arg.
    - apply atom_env_to_lty_env_dom_free_notin. exact HxΔ.
    - eapply res_models_extend_mono; eauto.
      eapply ctx_denote_under_basic_world; eauto.
    - replace (atom_env_to_lty_env
          (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
        with (<[LVFree x := erase_ty τ1]>
          (atom_env_to_lty_env (ctx_erasure_under Σ Γ))) in Htarget.
      + exact Htarget.
      + symmetry. apply atom_store_to_lvar_store_insert.
  }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_mx|].
  eapply ctx_bind_from_inserted_erasure_denotation.
  - exact HxΔ.
  - eapply ctx_erasure_under_agree_union_on_ty. exact Hwf.
  - exact Hworld_mx.
  - exact Htarget.
Qed.

Lemma ty_denote_gas_zero_tlet_ext
    (Σ : gmap atom ty) Γsrc Γlet τ1 τ2 e1 e2 x Fx
    (mbase mx : WfWorldT) :
  context_typing_wf Σ Γsrc e1 τ1 ->
  context_typing_wf Σ Γlet (tlete e1 e2) τ2 ->
  mbase ⊨ ctx_denote_under Σ Γlet ->
  mbase ⊨ ty_denote_under Σ Γsrc τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx Γsrc) ->
  x ∉ dom (erase_ctx Γlet) ->
  x ∉ fv_tm (tlete e1 e2) ->
  LVFree x ∉ context_ty_lvars τ2 ->
  res_extend_by mbase Fx mx ->
  mx ⊨ ty_denote_gas 0
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γlet)))
    τ2 (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γlet)))
    τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hctx Hden1 HFx Hxsrc Hxlet Hxtlet Hxτ2 Hext Hbody_zero.
  pose proof (ty_denote_under_total Σ Γsrc τ1 e1 mbase Hden1)
    as Htotal1.
  pose proof (ty_denote_gas_guard_of_zero
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γlet)))
    τ2 (e2 ^^ x) mx Hbody_zero) as Hbody_guard.
  pose proof Hbody_guard as Hbody_guard_parts.
  repeat rewrite res_models_and_iff in Hbody_guard_parts.
  destruct Hbody_guard_parts as [_ [_ [_ Hbody_total]]].
  assert (Hbase_world :
      mbase ⊨ basic_world_formula
        (atom_env_to_lty_env (erase_ctx Γlet))).
  {
    pose proof (ctx_denote_under_basic_world Σ Γlet mbase Hctx) as Hworld.
    eapply basic_world_formula_subenv; [|exact Hworld].
    intros v T Hv.
    pose proof (context_typing_wf_ctx
      Σ Γlet (tlete e1 e2) τ2 Hwflet) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γlet Hwfctx) as HbasicΓlet.
    destruct v as [k|y].
    - rewrite atom_store_to_lvar_store_lookup_bound_none in Hv.
      discriminate.
    - rewrite atom_store_to_lvar_store_lookup_free in Hv.
      rewrite atom_store_to_lvar_store_lookup_free.
      change ((ctx_erasure_under Σ Γlet : gmap atom ty) !! y = Some T).
      rewrite <- (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
        Σ Γlet y HbasicΓlet).
      + exact Hv.
      + apply elem_of_dom_2 in Hv. exact Hv.
  }
  assert (Htotal_tlet_base :
      mbase ⊨ expr_total_formula (tlete e1 e2)).
  {
    eapply tlete_total_of_result_ext
      with (Σ := atom_env_to_lty_env (erase_ctx Γlet))
        (T := erase_ty τ2) (x := x) (mx := mx) (Fx := Fx);
      eauto.
    - apply atom_env_to_lty_env_dom_free_notin. exact Hxlet.
    - rewrite lvar_store_to_atom_store_atom_store.
      exact (context_typing_wf_basic_typing
        Σ Γlet (tlete e1 e2) τ2 Hwflet).
  }
  pose proof (context_typing_wf_denot_static_guard
    Σ Γlet τ2 (tlete e1 e2) mbase Hwflet Hctx) as Hstatic.
  assert (Hbase_zero :
      mbase ⊨ ty_denote_gas 0
        (atom_env_to_lty_env (erase_ctx Γlet)) τ2 (tlete e1 e2)).
  {
    apply ty_denote_gas_zero_of_guard.
    unfold ty_static_guard_formula in Hstatic.
    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [Hwf_static [Hworld_static Hbasic_static]].
    eapply res_models_and_intro_from_models; [exact Hwf_static|].
    eapply res_models_and_intro_from_models; [exact Hworld_static|].
    eapply res_models_and_intro_from_models; [exact Hbasic_static|].
    exact Htotal_tlet_base.
  }
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ1]> ∅)
        (res_restrict mbase (ext_in Fx)) Fx).
  {
    eapply result_ext_typed_of_guard
      with (Σ := atom_env_to_lty_env (erase_ctx Γsrc))
        (τ := τ1) (e := e1) (x := x) (m := mbase) (mx := mx);
      eauto.
    - apply atom_store_to_lvar_store_closed.
    - apply atom_env_to_lty_env_dom_free_notin. exact Hxsrc.
    - unfold ty_denote_under, ty_denote in Hden1.
      exact (ty_denote_gas_guard _ _ _ _ _ Hden1).
  }
  eapply ty_denote_gas_extend_typed_extension; eauto.
  - apply atom_env_to_lty_env_dom_free_notin. exact Hxlet.
Qed.

Lemma fundamental_let_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (τ1 τ2 : context_ty) e1 e2 (L : aset) :
  context_typing_wf Σ Γ e1 τ1 ->
  context_typing_wf Σ Γ (tlete e1 e2) τ2 ->
  (forall x, x ∉ L ->
    context_typing_wf Σ (CtxComma Γ (CtxBind x τ1)) (e2 ^^ x) τ2) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ1 e1) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hbody_wf IH1 IH2 m Hctx.
  pose proof (IH1 m Hctx) as Hden1.
  pose proof (ty_denote_under_total Σ Γ τ1 e1 m Hden1)
    as Htotal.
  set (x := fresh_for
    (L ∪ dom (erase_ctx Γ) ∪ world_dom (m : WorldT) ∪
     fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)).
  pose proof (fresh_for_not_in
    (L ∪ dom (erase_ctx Γ) ∪ world_dom (m : WorldT) ∪
     fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)) as Hfresh.
  change (x ∉
    L ∪ dom (erase_ctx Γ) ∪ world_dom (m : WorldT) ∪
    fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2) in Hfresh.
  assert (HxL : x ∉ L) by set_solver.
  assert (Hxctx : x ∉ dom (erase_ctx Γ)) by set_solver.
  assert (Hxworld : x ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hxe1 : x ∉ fv_tm e1) by set_solver.
  destruct (expr_result_extension_witness_exists e1 x Hxe1)
    as [Fx HFx].
  assert (Happ : extension_applicable Fx m).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin.
      rewrite Hin.
      pose proof (res_models_scoped m (expr_total_formula e1) Htotal)
        as Hscope_total.
      unfold formula_scoped_in_world in Hscope_total.
      rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_total.
      exact Hscope_total.
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout.
      rewrite Hout. set_solver.
  }
  destruct (res_extend_by_exists m Fx Happ) as [mx Hext].
  assert (Hctx_body :
      mx ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind x τ1))).
  {
    eapply ctx_comma_bind_of_result_ext; eauto.
  }
  pose proof (IH2 x HxL mx Hctx_body) as Hbody.
  pose proof (ty_denote_under_comma_bind_to_lvar_insert
    Σ Γ τ1 τ2 (e2 ^^ x) x mx Hxctx Hbody) as Hbody_insert.
  pose proof (ty_denote_gas_guard
    (cty_depth τ2)
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ2 (e2 ^^ x) mx Hbody_insert) as Hbody_guard.
  pose proof (ty_denote_gas_zero_of_guard
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ2 (e2 ^^ x) mx Hbody_guard) as Hbody_zero.
  assert (Hxτ2 : LVFree x ∉ context_ty_lvars τ2).
  {
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    rewrite context_ty_lvars_fv in Hbad.
    set_solver.
  }
  assert (Hxtlet : x ∉ fv_tm (tlete e1 e2)).
  { cbn [fv_tm]. set_solver. }
  assert (Hmx_zero_tlet :
      mx ⊨ ty_denote_gas 0
        (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γ)))
        τ2 (tlete e1 e2)).
  {
    eapply ty_denote_gas_zero_tlet_ext; eauto.
  }
  pose proof (tlet_intro_denotation
    (cty_depth τ2)
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ2 e1 e2 x Fx m mx
    ltac:(cbn [fv_tm] in Hxtlet; set_solver)
    HFx Hext Hbody_zero Hmx_zero_tlet Hbody_insert) as Hlet_mx_insert.
  unfold ty_denote_under, ty_denote.
  eapply ty_denote_gas_drop_fresh_ext; eauto.
  - pose proof (context_typing_wf_fv_tm_subset
      Σ Γ (tlete e1 e2) τ2 Hwflet) as Htm.
    pose proof (context_typing_wf_fv_cty_subset_erase_dom
      Σ Γ (tlete e1 e2) τ2 Hwflet) as Hτ.
    pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
    pose proof (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ Γ) m Hworld) as Hdom.
    unfold ctx_erasure_under in Hdom.
    set_solver.
  - apply atom_env_to_lty_env_dom_free_notin. exact Hxctx.
Qed.

Lemma ty_denote_gas_result_ext_base_env_transport
    (Σ : gmap atom ty) Γ τ x (mx : WfWorldT) :
  basic_context_ty (dom Σ) τ ->
  mx ⊨ ty_denote_gas (cty_depth τ)
    (atom_env_to_lty_env
      (<[x := erase_ty τ]>
        (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ)))))
    τ (tret (vfvar x)) ->
  mx ⊨ ty_denote_gas (cty_depth τ)
    (atom_env_to_lty_env (<[x := erase_ty τ]> Σ))
    τ (tret (vfvar x)).
Proof.
  intros Hτ Harg.
  replace (atom_env_to_lty_env
      (<[x := erase_ty τ]>
        (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ)))))
    with (<[LVFree x := erase_ty τ]>
      (atom_env_to_lty_env
        (store_restrict (Σ ∪ erase_ctx Γ) (ctx_fv (CtxBind x τ))))) in Harg.
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  replace (atom_env_to_lty_env (<[x := erase_ty τ]> Σ))
    with (<[LVFree x := erase_ty τ]> (atom_env_to_lty_env Σ)).
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ (tret (vfvar x)));
    [reflexivity| |exact Harg].
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars τ (tret (vfvar x))))
    as [Hv|Hv]; [|reflexivity].
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    destruct v as [k|y].
    + rewrite !atom_store_to_lvar_store_lookup_bound_none. reflexivity.
    + rewrite !atom_store_to_lvar_store_lookup_free.
      assert (HyΣ : y ∈ dom Σ).
      {
        pose proof (basic_context_ty_fv_subset (dom Σ) τ Hτ) as Hτfv.
        apply lvars_fv_elem in Hv.
        rewrite relevant_lvars_fv in Hv.
        cbn [fv_tm] in Hv. set_solver.
      }
      apply elem_of_dom in HyΣ as [T HT].
      transitivity (Some T).
      {
        rewrite storeA_restrict_lookup.
        destruct (decide (y ∈ ctx_fv (CtxBind x τ))) as [_|Hyfv].
        - apply map_lookup_union_Some_raw. left. exact HT.
        - exfalso. cbn [ctx_fv] in Hyfv.
          apply lvars_fv_elem in Hv.
          rewrite relevant_lvars_fv in Hv.
          cbn [fv_tm] in Hv. set_solver.
      }
      { symmetry. exact HT. }
Qed.

Lemma ctx_bind_from_result_ext
    (Σ : gmap atom ty) Γ τ1 e1 Γbody τ2 ebody
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf Σ Γ e1 τ1 ->
  context_typing_wf Σ (CtxStar Γbody (CtxBind x τ1)) ebody τ2 ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_denote_under Σ Γ τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom Σ ->
  res_extend_by m Fx mx ->
  mx ⊨ ctx_denote_under Σ (CtxBind x τ1).
Proof.
  intros Hwf1 Hwf_body Hctx Hden HFx HxΣ Hext.
  pose proof (context_typing_wf_ctx
    Σ (CtxStar Γbody (CtxBind x τ1)) ebody τ2 Hwf_body)
    as Hwfctx_body.
  pose proof (wf_ctx_under_basic
    Σ (CtxStar Γbody (CtxBind x τ1)) Hwfctx_body)
    as Hbasic_body.
  cbn [basic_ctx] in Hbasic_body.
  destruct Hbasic_body as [_ [[_ Hτ1_basic] _]].
  pose proof (basic_context_ty_fv_subset (dom Σ) τ1 Hτ1_basic)
    as Hτ1_fv.
  assert (HxΔ : x ∉ dom (ctx_erasure_under Σ Γ)).
  {
    pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
    pose proof (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ Γ) m Hworld) as Hdom_world.
    intros HxΔ.
    pose proof (Hdom_world x HxΔ) as Hxworld.
    pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh_out.
    destruct HFx as [_ [_ Hout] _].
    change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh_out.
    assert (x ∈ ext_out Fx) by (rewrite Hout; set_solver).
    set_solver.
  }
  pose proof (ctx_bind_of_result_ext
    Σ Γ τ1 e1 m mx Fx x Hwf1 Hctx Hden HFx HxΔ Hext)
    as Hbind_full.
  pose proof (ctx_denote_under_bind_inv
    (Σ ∪ erase_ctx Γ) x τ1 mx Hbind_full) as Harg_full.
  assert (Harg_base :
      mx ⊨ ty_denote_gas (cty_depth τ1)
        (atom_env_to_lty_env (<[x := erase_ty τ1]> Σ))
        τ1 (tret (vfvar x))).
  {
    unfold ty_denote in Harg_full.
    eapply ty_denote_gas_result_ext_base_env_transport; eauto.
  }
  eapply ctx_bind_from_base_denotation; eauto.
Qed.

Lemma ty_denote_under_star_bind_to_lvar_insert
    (Σ : gmap atom ty) Γ1 Γ2 τx τ e x τtop etop (m : WfWorldT) :
  context_typing_wf Σ (CtxStar Γ1 Γ2) etop τtop ->
  context_typing_wf Σ (CtxStar Γ2 (CtxBind x τx)) e τ ->
  x ∉ dom (erase_ctx (CtxStar Γ1 Γ2)) ->
  m ⊨ ty_denote_under Σ (CtxStar Γ2 (CtxBind x τx)) τ e ->
  m ⊨ ty_denote_gas (cty_depth τ)
    (<[LVFree x := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    τ e.
Proof.
  intros Hwf_top Hwf_body Hxctx Hden.
  pose proof (context_typing_wf_ctx
    Σ (CtxStar Γ1 Γ2) etop τtop Hwf_top) as Hwfctx_top.
  pose proof (wf_ctx_under_basic
    Σ (CtxStar Γ1 Γ2) Hwfctx_top) as Hbasic_top.
  cbn [basic_ctx] in Hbasic_top.
  destruct Hbasic_top as [Hbasic1 [Hbasic2 Hdisj12]].
  pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic1) as Hdom1.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ2 Hbasic2) as Hdom2.
  pose proof (context_typing_wf_fv_tm_subset
    Σ (CtxStar Γ2 (CtxBind x τx)) e τ Hwf_body) as Htm.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom
    Σ (CtxStar Γ2 (CtxBind x τx)) e τ Hwf_body) as Hτ.
  unfold ty_denote_under, ty_denote in Hden |- *.
  replace (<[LVFree x := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    with (atom_env_to_lty_env
      (<[x := erase_ty τx]> (erase_ctx (CtxStar Γ1 Γ2)))).
  2:{ apply atom_store_to_lvar_store_insert. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (X := relevant_lvars τ e); [reflexivity| |exact Hden].
  apply atom_env_to_lty_env_restrict_lvars_agree_on
    with (X := fv_tm e ∪ fv_cty τ).
  - intros y Hy.
    destruct (decide (y = x)) as [->|Hyx].
    + cbn [erase_ctx].
      transitivity (Some (erase_ty τx)).
      {
        apply map_lookup_union_Some_raw. right. split.
        - apply not_elem_of_dom. intros HxΓ2.
          apply Hxctx. cbn [erase_ctx].
          apply elem_of_dom in HxΓ2 as [Tx HTx].
          apply elem_of_dom.
          destruct ((erase_ctx Γ1 : gmap atom ty) !! x) as [T1|] eqn:HT1.
          + exists T1. apply map_lookup_union_Some_raw. left. exact HT1.
          + exists Tx. apply map_lookup_union_Some_raw. right. split; assumption.
        - apply map_lookup_singleton.
      }
      {
        symmetry. apply map_lookup_insert.
      }
    + assert (HyΓ2 : y ∈ dom (erase_ctx Γ2)).
      {
        assert (HySrc : y ∈ dom (erase_ctx (CtxStar Γ2 (CtxBind x τx)))).
        { set_solver. }
        cbn [erase_ctx] in HySrc.
        apply elem_of_dom in HySrc as [Ty HTy].
        apply map_lookup_union_Some_raw in HTy as [HTy|[_ HTy]].
        - apply elem_of_dom. eauto.
        - change (({[x := erase_ty τx]} : gmap atom ty) !! y = Some Ty) in HTy.
          apply (proj1 (lookup_singleton_Some x y (erase_ty τx) Ty)) in HTy
            as [Hy_eq _].
          congruence.
      }
      pose proof HyΓ2 as HyΓ2_dom.
      apply elem_of_dom in HyΓ2 as [T HT].
      transitivity (Some T).
      {
        cbn [erase_ctx].
        apply map_lookup_union_Some_raw. left. exact HT.
      }
      {
        symmetry.
        assert (Htarget :
            (<[x := erase_ty τx]>
              (erase_ctx (CtxStar Γ1 Γ2)) : gmap atom ty) !! y = Some T).
        {
          transitivity ((erase_ctx (CtxStar Γ1 Γ2) : gmap atom ty) !! y).
          - apply map_lookup_insert_ne. congruence.
          - cbn [erase_ctx].
            apply map_lookup_union_Some_raw. right. split.
            + apply not_elem_of_dom. intros HyΓ1.
              rewrite Hdom1 in HyΓ1.
              rewrite Hdom2 in HyΓ2_dom.
              set_solver.
            + exact HT.
        }
        exact Htarget.
      }
  - rewrite relevant_lvars_fv. set_solver.
Qed.

Lemma ty_denote_gas_zero_tletd_ext
    (Σ : gmap atom ty) Γ1 Γ2 τ1 τ2 e1 e2 x Fx
    (mbase mx : WfWorldT) :
  context_typing_wf Σ Γ1 e1 τ1 ->
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 ->
  mbase ⊨ ctx_denote_under Σ (CtxStar Γ1 Γ2) ->
  mbase ⊨ ty_denote_under Σ Γ1 τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx (CtxStar Γ1 Γ2)) ->
  x ∉ fv_tm (tlete e1 e2) ->
  LVFree x ∉ context_ty_lvars τ2 ->
  res_extend_by mbase Fx mx ->
  mx ⊨ ty_denote_gas 0
    (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    τ2 (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0
    (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hctx Hden1 HFx Hxctx Hxtlet Hxτ2 Hext Hbody_zero.
  eapply (ty_denote_gas_zero_tlet_ext
    Σ Γ1 (CtxStar Γ1 Γ2) τ1 τ2 e1 e2 x Fx); eauto.
  cbn [erase_ctx] in Hxctx. set_solver.
Qed.

Lemma fundamental_letd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  context_typing_wf Σ Γ1 e1 τ1 ->
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 ->
  (forall x, x ∉ L ->
    context_typing_wf Σ (CtxStar Γ2 (CtxBind x τ1)) (e2 ^^ x) τ2) ->
  (ctx_denote_under Σ Γ1 ⊫ ty_denote_under Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      ty_denote_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  ctx_denote_under Σ (CtxStar Γ1 Γ2) ⊫
    ty_denote_under Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet Hbody_wf IH1 IH2 m Hctx.
  pose proof (context_typing_wf_ctx Σ (CtxStar Γ1 Γ2)
    (tlete e1 e2) τ2 Hwflet) as Hwfctx_star.
  pose proof (wf_ctx_under_basic Σ (CtxStar Γ1 Γ2) Hwfctx_star)
    as Hbasic_star.
  cbn [basic_ctx] in Hbasic_star.
  destruct Hbasic_star as [HbasicΓ1 [HbasicΓ2 HdisjΓ12]].
  destruct (ctx_denote_under_star_elim Σ Γ1 Γ2 m Hctx)
    as [m1 [m2 [Hc12 [Hle12 [HΓ1 HΓ2]]]]].
  pose proof (IH1 m1 HΓ1) as Hden1.
  pose proof (ty_denote_under_total Σ Γ1 τ1 e1 m1 Hden1)
    as Htotal1.
  set (x := fresh_for
    (L ∪ dom Σ ∪ dom (erase_ctx (CtxStar Γ1 Γ2)) ∪
     world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT) ∪
     fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)).
  pose proof (fresh_for_not_in
    (L ∪ dom Σ ∪ dom (erase_ctx (CtxStar Γ1 Γ2)) ∪
     world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT) ∪
     fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)) as Hfresh.
  change (x ∉
    L ∪ dom Σ ∪ dom (erase_ctx (CtxStar Γ1 Γ2)) ∪
    world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT) ∪
    fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2) in Hfresh.
  assert (HxL : x ∉ L) by set_solver.
  assert (HxΣ : x ∉ dom Σ) by set_solver.
  assert (Hxctx : x ∉ dom (erase_ctx (CtxStar Γ1 Γ2))) by set_solver.
  assert (Hxm2 : x ∉ world_dom (m2 : WorldT)) by set_solver.
  assert (Hxe1 : x ∉ fv_tm e1) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  destruct (expr_result_extension_witness_exists e1 x Hxe1)
    as [Fx HFx].
  assert (Happ : extension_applicable Fx m1).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin.
      rewrite Hin.
      pose proof (res_models_scoped m1 (expr_total_formula e1) Htotal1)
        as Hscope_total.
      unfold formula_scoped_in_world in Hscope_total.
      rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_total.
      exact Hscope_total.
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout.
      rewrite Hout. set_solver.
  }
  destruct (res_extend_by_exists m1 Fx Happ) as [m1x Hext1].
  destruct (res_product_comm_eq m1 m2 Hc12) as [Hc21 Heq21].
  assert (Hle21 : res_product m2 m1 Hc21 ⊑ m).
  { rewrite <- Heq21. exact Hle12. }
  assert (Hout_m2 : extA_out Fx ## world_dom (m2 : WorldT)).
  {
    destruct HFx as [_ [_ Hout] _].
    change (ext_out Fx ## world_dom (m2 : WorldT)).
    rewrite Hout. set_solver.
  }
  destruct (res_extend_by_product_frame_l m1 m1x m2 Fx Hc21 Hext1 Hout_m2)
    as [Hc2x Hext_prod].
  assert (Hbind :
      m1x ⊨ ctx_denote_under Σ (CtxBind x τ1)).
  {
    eapply ctx_bind_from_result_ext; eauto.
  }
  pose proof (ctx_denote_under_star_intro_product
    Σ Γ2 (CtxBind x τ1) m2 m1x Hc2x HbasicΓ2 HΓ2 Hbind)
    as Hctx_body.
  pose proof (IH2 x HxL (res_product m2 m1x Hc2x) Hctx_body)
    as Hbody.
  pose proof (ty_denote_under_star_bind_to_lvar_insert
    Σ Γ1 Γ2 τ1 τ2 (e2 ^^ x) x τ2 (tlete e1 e2)
    (res_product m2 m1x Hc2x)
    Hwflet
    (Hbody_wf x HxL) Hxctx Hbody) as Hbody_insert.
  pose proof (ty_denote_gas_guard
    (cty_depth τ2)
    (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    τ2 (e2 ^^ x) (res_product m2 m1x Hc2x) Hbody_insert)
    as Hbody_guard.
  pose proof (ty_denote_gas_zero_of_guard
    (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    τ2 (e2 ^^ x) (res_product m2 m1x Hc2x) Hbody_guard)
    as Hbody_zero.
  assert (Hctx_prod21 :
      res_product m2 m1 Hc21 ⊨ ctx_denote_under Σ (CtxStar Γ1 Γ2)).
  {
    rewrite <- Heq21.
    eapply ctx_denote_under_star_intro_product; eauto.
  }
  assert (Hden1_prod :
      res_product m2 m1 Hc21 ⊨ ty_denote_under Σ Γ1 τ1 e1).
  {
    eapply res_models_kripke; [eapply res_product_le_r|].
    exact Hden1.
  }
  assert (Hxτ2 : LVFree x ∉ context_ty_lvars τ2).
  {
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    rewrite context_ty_lvars_fv in Hbad.
    set_solver.
  }
  assert (Hxtlet : x ∉ fv_tm (tlete e1 e2)).
  { cbn [fv_tm]. set_solver. }
  assert (Hmx_zero_tlet :
      res_product m2 m1x Hc2x ⊨ ty_denote_gas 0
        (<[LVFree x := erase_ty τ1]>
          (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
        τ2 (tlete e1 e2)).
  {
    eapply ty_denote_gas_zero_tletd_ext; eauto.
  }
  pose proof (tlet_intro_denotation
    (cty_depth τ2)
    (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    τ2 e1 e2 x Fx (res_product m2 m1 Hc21)
    (res_product m2 m1x Hc2x)
    Hxe2 HFx Hext_prod Hbody_zero Hmx_zero_tlet Hbody_insert)
    as Hlet_prod_insert.
  assert (Hctx_prod :
      res_product m1 m2 Hc12 ⊨ ctx_denote_under Σ (CtxStar Γ1 Γ2)).
  {
    eapply ctx_denote_under_star_intro_product; eauto.
  }
  assert (Hfv_prod :
      fv_tm (tlete e1 e2) ∪ fv_cty τ2 ⊆
        world_dom (res_product m2 m1 Hc21 : WorldT)).
  {
    rewrite <- Heq21.
    pose proof (context_typing_wf_fv_tm_subset
      Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 Hwflet) as Htm.
    pose proof (context_typing_wf_fv_cty_subset_erase_dom
      Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 Hwflet) as Hτ.
    pose proof (ctx_denote_under_basic_world
      Σ (CtxStar Γ1 Γ2) (res_product m1 m2 Hc12) Hctx_prod)
      as Hworld.
    pose proof (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ (CtxStar Γ1 Γ2))
      (res_product m1 m2 Hc12) Hworld) as Hdom.
    unfold ctx_erasure_under in Hdom.
    set_solver.
  }
  unfold ty_denote_under, ty_denote.
  eapply res_models_kripke; [exact Hle21|].
	  eapply ty_denote_gas_drop_fresh_ext; eauto.
	  apply atom_env_to_lty_env_dom_free_notin.
	  exact Hxctx.
	Qed.

Lemma fundamental_lam_case
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
  ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
  intros Hwf IH m Hctx.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (elam := tret (vlam (erase_ty τx) e)).
  pose proof (context_typing_wf_denot_static_guard
    Σ Γ (CTArrow τx τ) elam m Hwf Hctx) as Hguard.
  assert (Hfull_guard :
      m ⊨ ty_guard_formula
        (relevant_env Δ (CTArrow τx τ) elam)
        (CTArrow τx τ) elam).
  {
    unfold ty_static_guard_formula in Hguard.
    unfold ty_guard_formula.
    rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf_guard Hguard].
    rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hworld_guard Hbasic_guard].
    rewrite res_models_and_iff. split; [exact Hwf_guard|].
    rewrite res_models_and_iff. split; [exact Hworld_guard|].
    rewrite res_models_and_iff. split; [exact Hbasic_guard|].
    eapply expr_total_formula_tret_of_basic; eauto.
  }
  assert (Hzero : m ⊨ ty_denote_gas 0 Δ (CTArrow τx τ) elam).
  { apply ty_denote_gas_zero_of_guard. exact Hfull_guard. }
  unfold ty_denote_under, ty_denote.
  subst Δ elam.
  cbn [cty_depth ty_denote_gas].
  rewrite res_models_and_iff. split.
  - exact Hfull_guard.
  - pose proof (ty_denote_gas_scope_from_zero_any
      (S (Nat.max (cty_depth τx) (cty_depth τ)))
      (atom_env_to_lty_env (erase_ctx Γ)) (CTArrow τx τ)
      (tret (vlam (erase_ty τx) e)) m Hzero) as Hscope_full.
    cbn [ty_denote_gas] in Hscope_full.
    pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_body.
    eapply res_models_forall_rev_intro; [exact Hscope_body|].
    exists (L ∪ dom Σ ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    intros y Hy my Hdom Hrestrict.
    assert (Hle : m ⊑ my).
    { rewrite <- Hrestrict. apply res_restrict_le. }
    assert (Hy_my : y ∈ world_dom (my : WorldT)).
    { rewrite Hdom. set_solver. }
    pose proof (formula_scoped_forall_open_res_le
      m my y _ Hscope_body Hle Hy_my) as Hopen_scope.
    eapply res_models_impl_intro; [exact Hopen_scope|].
    intros Harg.
    eapply lam_opened_arrow_result; eauto.
    all: try set_solver.
Qed.

Lemma fundamental_lamd_case
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTWand τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
  intros Hwf IH m Hctx.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (elam := tret (vlam (erase_ty τx) e)).
  pose proof (context_typing_wf_denot_static_guard
    Σ Γ (CTWand τx τ) elam m Hwf Hctx) as Hguard.
  assert (Hfull_guard :
      m ⊨ ty_guard_formula
        (relevant_env Δ (CTWand τx τ) elam)
        (CTWand τx τ) elam).
  {
    unfold ty_static_guard_formula in Hguard.
    unfold ty_guard_formula.
    rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf_guard Hguard].
    rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hworld_guard Hbasic_guard].
    rewrite res_models_and_iff. split; [exact Hwf_guard|].
    rewrite res_models_and_iff. split; [exact Hworld_guard|].
    rewrite res_models_and_iff. split; [exact Hbasic_guard|].
    eapply expr_total_formula_tret_of_basic; eauto.
  }
  assert (Hzero : m ⊨ ty_denote_gas 0 Δ (CTWand τx τ) elam).
  { apply ty_denote_gas_zero_of_guard. exact Hfull_guard. }
  unfold ty_denote_under, ty_denote.
  subst Δ elam.
  cbn [cty_depth ty_denote_gas].
  rewrite res_models_and_iff. split.
  - exact Hfull_guard.
  - pose proof (ty_denote_gas_scope_from_zero_any
      (S (Nat.max (cty_depth τx) (cty_depth τ)))
      (atom_env_to_lty_env (erase_ctx Γ)) (CTWand τx τ)
      (tret (vlam (erase_ty τx) e)) m Hzero) as Hscope_full.
    cbn [ty_denote_gas] in Hscope_full.
    pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_body.
    eapply res_models_fbwand_intro; [exact Hscope_body|].
    exists (L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪
      fv_cty τx ∪ fv_cty τ ∪
      lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty τx)))).
    intros η n Hc Hbind Hfresh Hdom Harg.
    destruct (open_env_binds_one_inv η Hbind) as [y Hη].
    subst η.
    rewrite !formula_open_env_singleton in Harg |- *.
    rewrite open_env_atoms_insert in Hfresh by apply lookup_empty.
    rewrite open_env_atoms_empty in Hfresh.
    rewrite open_env_atoms_insert in Hdom by apply lookup_empty.
    rewrite open_env_atoms_empty in Hdom.
    eapply (lamd_opened_wand_result Σ Γ τx τ e L m n y Hc);
      eauto.
    + set_solver.
    + set_solver.
Qed.

Lemma fundamental_app_case
    (Φ : primop_ctx) Σ Γ τx τ v1 x :
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τx (tret (vfvar x))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fundamental_appd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (ctx_denote_under Σ Γ1 ⊫
    ty_denote_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (ctx_denote_under Σ Γ2 ⊫
    ty_denote_under Σ Γ2 τx (tret (vfvar x))) ->
  ctx_denote_under Σ (CtxStar Γ1 Γ2) ⊫
    ty_denote_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ)
      (tapp v1 (vfvar x)).
Proof.
Admitted.

Lemma fundamental_fix_case
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

Lemma fundamental_fixd_case
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTWand τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.

Lemma fundamental_appop_case
    (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) ->
  context_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (primop_arg_ty (Φ op)) (tret (vfvar x))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ ({0 ~> x} (primop_result_ty (Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros Hsig Hwf IH m Hctx.
  pose proof (proj1 (wf_primop_semantic op (Φ op) Hsig x)) as Hop.
  pose proof (appop_context_typing_arg_lookup Φ Σ Γ op x Hsig Hwf)
    as Hlookup.
  pose proof (IH m Hctx) as Harg.
  unfold ty_denote_under, ty_denote in Harg |- *.
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
  (ctx_denote_under Σ Γt ⊫
    ty_denote_under Σ Γt (bool_precise_ty true) (tret v)) ->
  (ctx_denote_under Σ Γf ⊫
    ty_denote_under Σ Γf (bool_precise_ty false) (tret v)) ->
  (ctx_denote_under Σ Γt ⊫ ty_denote_under Σ Γt τt et) ->
  (ctx_denote_under Σ Γf ⊫ ty_denote_under Σ Γf τf ef) ->
  ctx_denote_under Σ (CtxSum Γt Γf) ⊫
    ty_denote_under Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch v et ef).
Proof.
Admitted.

Lemma fundamental_match_true_case
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (bool_precise_ty true) (tret v)) ->
  branch_unreachable Σ Γ v false ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ et) ->
  erase_ctx Γ ⊢ₑ ef ⋮ erase_ty τ ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tmatch v et ef).
Proof.
Admitted.

Lemma fundamental_match_false_case
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (bool_precise_ty false) (tret v)) ->
  branch_unreachable Σ Γ v true ->
  erase_ctx Γ ⊢ₑ et ⋮ erase_ty τ ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ ef) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tmatch v et ef).
Proof.
Admitted.

(** ** Fundamental theorem *)

Theorem Fundamental
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) :
  wf_primop_ctx Φ ->
  has_context_type Φ Σ Γ e τ ->
  ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ e.
Proof.
  intros HΦ Hty.
  induction Hty.
  - eapply fundamental_var_case; eauto.
  - eapply fundamental_const_case; eauto.
  - eapply fundamental_sub_case; eauto.
  - eapply fundamental_ctx_sub_case; eauto.
  - eapply fundamental_let_case; eauto using typing_wf_under.
  - eapply fundamental_letd_case; eauto using typing_wf_under.
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
