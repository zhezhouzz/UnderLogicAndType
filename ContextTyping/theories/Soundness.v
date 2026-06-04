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
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

(** ** Guard facts exposed by type denotation *)

Lemma ty_denote_under_guard
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  m ⊨ ty_denote_under Σ Γ τ e ->
	m ⊨ ty_guard_formula
      (denot_relevant_env
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

Lemma context_typing_wf_denot_static_guard
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_static_guard_formula
    (denot_relevant_env
      (atom_env_to_lty_env (erase_ctx Γ)) τ e)
    τ e.
Proof.
  intros Hwf Hctx.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as Hbasicctx.
  assert (Hworld :
      m ⊨ basic_world_formula
        (denot_relevant_env (atom_env_to_lty_env (erase_ctx Γ)) τ e)).
  {
    eapply basic_world_formula_subenv.
    - intros v T Hv.
      unfold ctx_erasure_under.
      eapply denot_relevant_env_erase_ctx_union_subenv; eauto.
    - exact (ctx_denote_under_basic_world Σ Γ m Hctx).
  }
  apply basic_world_formula_models_iff in Hworld
    as [Hlc [Hscope Htyped_world]].
  unfold ty_static_guard_formula.
  rewrite res_models_and_iff. split.
  - apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [exact Hscope|].
    pose proof (context_typing_wf_context_ty Σ Γ e τ Hwf)
      as Hτ.
    apply basic_context_ty_atom_env_denot_relevant_env.
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
    with (X := denot_relevant_lvars τ (tret (vfvar x)));
    [reflexivity | | exact Hbind].
  assert (Hrel :
      denot_relevant_lvars τ (tret (vfvar x)) ⊆ {[LVFree x]}).
  {
    apply denot_relevant_lvars_ret_fvar_subset_singleton.
    eapply context_typing_wf_bind_context_ty; eauto.
  }
  rewrite <- (lty_env_restrict_lvars_twice_subset
    (atom_env_to_lty_env (<[x := erase_ty τ]> Σ))
    ({[LVFree x]}) (denot_relevant_lvars τ (tret (vfvar x))) Hrel).
  rewrite atom_env_to_lty_env_insert_restrict_singleton.
  rewrite (lty_env_restrict_lvars_twice_subset
    (atom_env_to_lty_env (<[x := erase_ty τ]> (∅ : gmap atom ty)))
    ({[LVFree x]}) (denot_relevant_lvars τ (tret (vfvar x))) Hrel).
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
      with (X := denot_relevant_lvars τ e); [reflexivity | | exact Hden2].
    apply atom_env_to_lty_env_restrict_lvars_agree_on
      with (X := fv_tm e ∪ fv_cty τ).
    - intros x Hx. symmetry. apply Hagree. exact Hx.
    - rewrite denot_relevant_lvars_fv. set_solver.
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

Lemma ctx_denote_under_comma_bind_from_result_extension
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
      with (X := denot_relevant_lvars τ1 e1); [reflexivity| |exact Hden].
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
      unfold ctx_erasure_under.
      apply erase_ctx_union_lookup_local_of_basic_ctx; assumption.
    - rewrite denot_relevant_lvars_fv. set_solver.
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
    eapply basic_world_formula_insert_from_arg_denotation.
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
  eapply ctx_denote_under_comma_intro; [exact Hctx_mx|].
  assert (Hbind_env :
      ctx_erasure_under (Σ ∪ erase_ctx Γ) (CtxBind x τ1) =
      <[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)).
  {
    unfold ctx_erasure_under.
    cbn [erase_ctx].
    change ((Σ ∪ erase_ctx Γ : gmap atom ty) ∪
        ({[x := erase_ty τ1]} : gmap atom ty) =
      <[x := erase_ty τ1]> (Σ ∪ erase_ctx Γ : gmap atom ty)).
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (Σ ∪ erase_ctx Γ : gmap atom ty)
      x (erase_ty τ1)).
    exact HxΔ.
  }
  cbn [ctx_denote_under].
  rewrite res_models_and_iff. split.
  - change (mx ⊨ basic_world_formula
      (atom_env_to_lty_env
        (ctx_erasure_under (Σ ∪ erase_ctx Γ) (CtxBind x τ1)))).
    rewrite Hbind_env. exact Hworld_mx.
  - change (mx ⊨ ty_denote_gas (cty_depth τ1)
      (atom_env_to_lty_env (<[x := erase_ty τ1]> (ctx_erasure_under Σ Γ)))
      τ1 (tret (vfvar x))).
    exact Htarget.
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
    eapply ctx_denote_under_comma_bind_from_result_extension; eauto.
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
  assert (Hctx_basic_world :
      m ⊨ basic_world_formula (atom_env_to_lty_env (erase_ctx Γ))).
  {
    pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
    eapply basic_world_formula_subenv; [|exact Hworld].
    intros v T Hv.
    unfold ctx_erasure_under.
    eapply atom_env_to_lty_env_erase_ctx_union_subenv; [|exact Hv].
    pose proof (context_typing_wf_ctx Σ Γ (tlete e1 e2) τ2 Hwflet)
      as Hwfctx.
    exact (wf_ctx_under_basic Σ Γ Hwfctx).
  }
  pose proof (Hbody_guard) as Hbody_guard_parts.
  repeat rewrite res_models_and_iff in Hbody_guard_parts.
  destruct Hbody_guard_parts as [_ [_ [_ Hbody_total]]].
  assert (Htotal_tlet_m : m ⊨ expr_total_formula (tlete e1 e2)).
  {
    eapply expr_total_formula_tlete_intro_from_result_extension
      with (Σ := atom_env_to_lty_env (erase_ctx Γ))
        (T := erase_ty τ2) (x := x) (mx := mx) (Fx := Fx);
      eauto.
    - apply atom_env_to_lty_env_dom_free_notin. exact Hxctx.
    - rewrite lvar_store_to_atom_store_atom_store.
      exact (context_typing_wf_basic_typing Σ Γ (tlete e1 e2) τ2 Hwflet).
  }
  pose proof (context_typing_wf_denot_static_guard
      Σ Γ τ2 (tlete e1 e2) m Hwflet Hctx) as Hstatic.
  assert (Hm_zero :
      m ⊨ ty_denote_gas 0
        (atom_env_to_lty_env (erase_ctx Γ)) τ2 (tlete e1 e2)).
	  {
	    apply ty_denote_gas_zero_of_guard.
	    unfold ty_static_guard_formula in Hstatic.
	    repeat rewrite res_models_and_iff in Hstatic.
    destruct Hstatic as [Hwf_static [Hworld_static Hbasic_static]].
    eapply res_models_and_intro_from_models; [exact Hwf_static|].
    eapply res_models_and_intro_from_models; [exact Hworld_static|].
    eapply res_models_and_intro_from_models; [exact Hbasic_static|].
    exact Htotal_tlet_m.
  }
  assert (HFx_ltype :
      extension_has_ltype (<[LVFree x := erase_ty τ1]> ∅)
        (res_restrict m (ext_in Fx)) Fx).
  {
    eapply expr_result_extension_has_ltype_from_source_guard
      with (Σ := atom_env_to_lty_env (erase_ctx Γ))
        (τ := τ1) (e := e1) (x := x) (m := m) (mx := mx);
      eauto.
    - apply atom_store_to_lvar_store_closed.
    - apply atom_env_to_lty_env_dom_free_notin. exact Hxctx.
    - unfold ty_denote_under, ty_denote in Hden1.
      exact (ty_denote_gas_guard _ _ _ _ _ Hden1).
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
      mx ⊨ ty_denote_gas 0
        (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γ)))
        τ2 (tlete e1 e2)).
  {
    eapply ty_denote_gas_extend_typed_extension; eauto.
    - apply atom_env_to_lty_env_dom_free_notin. exact Hxctx.
  }
  pose proof (tlet_intro_denotation
    (cty_depth τ2)
    (<[LVFree x := erase_ty τ1]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ2 e1 e2 x Fx m mx
    ltac:(cbn [fv_tm] in Hxtlet; set_solver)
    HFx Hext Hbody_zero Hmx_zero_tlet Hbody_insert) as Hlet_mx_insert.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq
    (cty_depth τ2) (atom_env_to_lty_env (erase_ctx Γ)) τ2
    (tlete e1 e2) x (erase_ty τ1)) in Hlet_mx_insert.
  2:{
    apply atom_env_to_lty_env_dom_free_notin. exact Hxctx.
  }
  2:{ exact Hxτ2. }
  2:{ exact Hxtlet. }
  unfold ty_denote_under, ty_denote.
  eapply res_models_from_restrict_extension_on_fv
    with (X := fv_tm (tlete e1 e2) ∪ fv_cty τ2) (n := mx).
  - eapply formula_fv_ty_denote_gas_subset_relevant.
  - pose proof (context_typing_wf_fv_tm_subset
      Σ Γ (tlete e1 e2) τ2 Hwflet) as Htm.
    pose proof (context_typing_wf_fv_cty_subset_erase_dom
      Σ Γ (tlete e1 e2) τ2 Hwflet) as Hτ.
    pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
    pose proof (basic_world_formula_atom_env_dom_subset
      (ctx_erasure_under Σ Γ) m Hworld) as Hdom.
    transitivity (fv_tm (tlete e1 e2) ∪ fv_cty τ2).
    {
      exact (formula_fv_ty_denote_gas_subset_relevant
        (cty_depth τ2) (atom_env_to_lty_env (erase_ctx Γ))
        τ2 (tlete e1 e2)).
    }
    unfold ctx_erasure_under in Hdom.
    set_solver.
  - transitivity m.
    + apply res_restrict_le.
    + eapply res_extend_by_le; eauto.
  - exact Hlet_mx_insert.
Qed.

Lemma fundamental_letd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 ->
  (ctx_denote_under Σ Γ1 ⊫ ty_denote_under Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    ctx_denote_under Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      ty_denote_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  ctx_denote_under Σ (CtxStar Γ1 Γ2) ⊫
    ty_denote_under Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof.
Admitted.

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
Admitted.

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
Admitted.

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
