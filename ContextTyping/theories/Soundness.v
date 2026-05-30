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
  BasicTypingFormula.
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

(** ** Direct case bridges *)

Lemma fundamental_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (e : tm) (τ1 τ2 : context_ty) :
  context_typing_wf Σ Γ e τ2 ->
  sub_type_under Σ Γ τ1 τ2 ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e) ->
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 e.
Proof.
  intros Hwf Hsub IH m HΓ.
  destruct Hsub as [_ [_ [_ Hent]]].
  pose proof (context_typing_wf_fv_tm_subset Σ Γ e τ2 Hwf) as Hfv.
  pose proof (Hent e Hfv m HΓ) as Himpl.
  eapply res_models_impl_elim; [exact Himpl |].
  apply IH. exact HΓ.
Qed.

Lemma fundamental_ctx_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ1 Γ2 : ctx)
    (e : tm) (τ : context_ty) :
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 ->
  (denot_ctx_in_env Σ Γ2 ⊫ denot_ty_in_ctx_under Σ Γ2 τ e) ->
  denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ e.
Proof.
Admitted.

Lemma denot_var_direct_in_ctx Σ x τ :
  context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ ->
  denot_ctx_in_env Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  intros Hwf m Hctx.
  unfold denot_ctx_in_env in Hctx.
  repeat rewrite res_models_and_iff in Hctx.
  destruct Hctx as [_ [_ Hbind]].
  destruct Hwf as [Hwfτ _].
  pose proof (wf_context_ty_under_ctx Σ (CtxBind x τ) τ Hwfτ) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ (CtxBind x τ) Hwfctx) as Hbasicctx.
  cbn [basic_ctx] in Hbasicctx.
  destruct Hbasicctx as [HxΣ _].
  unfold denot_ty_in_ctx_under, erase_ctx_under.
  cbn [denot_ctx_under] in Hbind.
  replace (Σ ∪ erase_ctx (CtxBind x τ))
    with (<[x := erase_ty τ]> Σ).
  - unfold res_models. models_fuel_irrel Hbind.
  - cbn [erase_ctx].
    symmetry.
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (Σ : gmap atom ty) x (erase_ty τ) HxΣ).
Qed.

Lemma fundamental_var_case Σ x τ :
  context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ ->
  denot_ctx_in_env Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  apply denot_var_direct_in_ctx.
Qed.

Lemma denot_const_direct_in_ctx Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  intros Hwf m Hctx.
  unfold denot_ty_in_ctx_under, denot_ty.
  eapply const_direct_denotation_gas_in_ctx; eauto; try exact (proj2 Hwf).
Qed.

Lemma fundamental_const_case Σ c :
  context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) ->
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  apply denot_const_direct_in_ctx.
Qed.

(** Extending a context denotation with the result extension of [e1].

    This is the one remaining semantic context-construction obligation for the
    induction-facing TLet case.  It should be proved from the typed result
    extension facts in [ContextBasicDenotation.TermExtension] and the comma
    definition of [denot_ctx_under], rather than by rebuilding any old TLet
    helper stack. *)
Lemma denot_ctx_in_env_comma_bind_from_result_extension
    (Σ : gmap atom ty) (Γ : ctx) (τ1 : context_ty) e1
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom) :
  context_typing_wf Σ Γ e1 τ1 ->
  m ⊨ denot_ctx_in_env Σ Γ ->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ1 e1 ->
  expr_result_extension_witness e1 x Fx ->
  x ∉ dom (erase_ctx_under Σ Γ) ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)).
Proof.
Admitted.

Lemma fundamental_let_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx)
    (τ1 τ2 : context_ty) e1 e2 (L : aset) :
  context_typing_wf Σ Γ e1 τ1 ->
  context_typing_wf Σ Γ (tlete e1 e2) τ2 ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Hwf1 Hwflet IH1 IH2 m Hctx.
  pose proof (IH1 m Hctx) as Hden1.
  pose proof (denot_ty_in_ctx_under_total Σ Γ τ1 e1 m Hden1) as Htotal.
  set (x := fresh_for
    (L ∪ dom (erase_ctx_under Σ Γ) ∪ world_dom (m : WorldT) ∪
     fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)).
  pose proof (fresh_for_not_in
    (L ∪ dom (erase_ctx_under Σ Γ) ∪ world_dom (m : WorldT) ∪
     fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)) as Hfresh.
  change (x ∉
    L ∪ dom (erase_ctx_under Σ Γ) ∪ world_dom (m : WorldT) ∪
    fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2) in Hfresh.
  assert (HxL : x ∉ L) by set_solver.
  assert (Hxctx : x ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
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
  pose proof (IH2 x HxL mx ltac:(
    eapply denot_ctx_in_env_comma_bind_from_result_extension; eauto))
    as Hbody.
  unfold denot_ty_in_ctx_under, denot_ty in Hbody |- *.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1 Hxctx) in Hbody.
  replace (atom_env_to_lty_env (<[x := erase_ty τ1]> (erase_ctx_under Σ Γ)))
    with (<[LVFree x := erase_ty τ1]>
      (atom_env_to_lty_env (erase_ctx_under Σ Γ))) in Hbody.
  2:{ symmetry. apply atom_store_to_lvar_store_insert. }
  eapply tlet_intro_denotation with
    (T1 := erase_ty τ1) (Fx := Fx) (x := x) (mx := mx); eauto.
  - apply atom_store_to_lvar_store_closed.
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf1).
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwflet).
  - eapply denot_ctx_in_env_relevant_basic_world. exact Hctx.
  - intros Hbad.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    + apply lvars_fv_elem in Hbad.
      rewrite atom_store_to_lvar_store_dom, lvars_fv_of_atoms in Hbad.
      set_solver.
    + apply lvars_fv_elem in Hbad.
      rewrite context_ty_lvars_fv in Hbad.
      set_solver.
Qed.

Lemma fundamental_letd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 ->
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ1 e1) ->
  (forall x, x ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) ->
  denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof.
  intros Hwf IH1 IH2 m Hctx.
  destruct (denot_ctx_in_env_star_elim Σ Γ1 Γ2 m Hctx)
    as [m1 [m2 [Hc [Hle [Hctx1 Hctx2]]]]].
  pose proof (IH1 m1 Hctx1) as Hden1.
  pose proof (denot_ty_in_ctx_under_total Σ Γ1 τ1 e1 m1 Hden1) as Htotal.
  set (x := fresh_for
    (L ∪ dom (erase_ctx_under Σ Γ2) ∪ world_dom (m1 : WorldT) ∪
     world_dom (m2 : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)).
  pose proof (fresh_for_not_in
    (L ∪ dom (erase_ctx_under Σ Γ2) ∪ world_dom (m1 : WorldT) ∪
     world_dom (m2 : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2)) as Hfresh.
  change (x ∉
    L ∪ dom (erase_ctx_under Σ Γ2) ∪ world_dom (m1 : WorldT) ∪
    world_dom (m2 : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τ2) in Hfresh.
  assert (HxL : x ∉ L) by set_solver.
  assert (HxΓ2 : x ∉ dom (erase_ctx_under Σ Γ2)) by set_solver.
  assert (Hxe1 : x ∉ fv_tm e1) by set_solver.
  destruct (expr_result_extension_witness_exists e1 x Hxe1)
    as [Fx HFx].
  assert (Happ : extension_applicable Fx m1).
  {
    constructor.
    - destruct HFx as [_ [Hin _] _].
      unfold ext_in in Hin.
      rewrite Hin.
      pose proof (res_models_scoped m1 (expr_total_formula e1) Htotal)
        as Hscope_total.
      unfold formula_scoped_in_world in Hscope_total.
      rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_total.
      exact Hscope_total.
    - destruct HFx as [_ [_ Hout] _].
      unfold ext_out in Hout.
      rewrite Hout. set_solver.
  }
  destruct (res_extend_by_exists m1 Fx Happ) as [mx1 Hext].
  pose proof (letd_body_world_compat e1 x m1 m2 mx1 Hc Fx HFx
    ltac:(set_solver) Hext) as Hcbody.
  set (mbody := res_product m2 mx1 Hcbody).
  pose proof (IH2 x HxL mbody ltac:(
    subst mbody;
    eapply denot_ctx_in_env_star_bind_from_result_extension; eauto;
    exact Hden1)) as Hbody.
  unfold denot_ty_in_ctx_under, denot_ty in Hden1, Hbody |- *.
  eapply denot_ty_in_ctx_under_star_bind_to_lvar_insert in Hbody;
    [| exact HxΓ2].
  eapply denot_ty_lvar_gas_star_union_to_ctx.
  eapply letd_intro_denotation with
    (m1 := m1) (m2 := m2) (mx1 := mx1) (mbody := mbody)
    (Hc := Hc) (Hcbody := Hcbody) (Fx := Fx) (x := x).
  - apply basic_typing_star_union_lty_env. exact (proj2 Hwf).
  - exact Hle.
  - exact HFx.
  - exact Hext.
  - subst mbody. reflexivity.
  - exact Hden1.
  - exact Hbody.
Qed.

Lemma fundamental_lam_case
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
  intros Hwf IH m Hctx.
  unfold denot_ty_in_ctx_under, denot_ty.
  eapply lam_intro_denotation
    with (L := L ∪ dom (erase_ctx_under Σ Γ)).
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - intros y F my Hy Hext Harg.
    assert (HyL : y ∉ L) by set_solver.
    assert (Hydom : y ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
    pose proof (IH y HyL my ltac:(
      eapply denot_ctx_in_env_comma_bind_from_arg_denotation; eauto))
      as Hbody.
    eapply denot_ty_in_ctx_under_comma_bind_to_lvar_insert in Hbody;
      [| exact Hydom].
    rewrite denot_ty_lvar_gas_saturate.
    + exact Hbody.
    + rewrite cty_open_preserves_depth. cbn [cty_depth]. lia.
Qed.

Lemma fundamental_lamd_case
    (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ)
      (tret (vlam (erase_ty τx) e)).
Proof.
  intros Hwf IH m Hctx.
  unfold denot_ty_in_ctx_under, denot_ty.
  eapply lamd_intro_denotation
    with (L := L ∪ dom (erase_ctx_under Σ Γ)).
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - intros y marg Hc Hy Harg.
    assert (HyL : y ∉ L) by set_solver.
    assert (Hydom : y ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
    pose proof (IH y HyL (res_product marg m Hc) ltac:(
      eapply denot_ctx_in_env_star_bind_from_arg_denotation; eauto))
      as Hbody.
    eapply denot_ty_in_ctx_under_star_bind_to_lvar_insert in Hbody;
      [| exact Hydom].
    rewrite denot_ty_lvar_gas_saturate.
    + exact Hbody.
    + rewrite cty_open_preserves_depth. cbn [cty_depth]. lia.
Qed.

Lemma fundamental_app_case
    (Φ : primop_ctx) Σ Γ τx τ v1 x :
  context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret v1)) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τx (tret (vfvar x))) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof.
  intros Hwf IHfun IHarg m Hctx.
  pose proof (IHfun m Hctx) as Hfun.
  pose proof (IHarg m Hctx) as Harg.
  unfold denot_ty_in_ctx_under, denot_ty in Hfun, Harg |- *.
  eapply app_elim_denotation.
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - exact Hfun.
  - exact Harg.
Qed.

Lemma fundamental_appd_case
    (Φ : primop_ctx) Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  (denot_ctx_in_env Σ Γ1 ⊫
    denot_ty_in_ctx_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (denot_ctx_in_env Σ Γ2 ⊫
    denot_ty_in_ctx_under Σ Γ2 τx (tret (vfvar x))) ->
  denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ)
      (tapp v1 (vfvar x)).
Proof.
  intros Hwf IHfun IHarg m Hctx.
  destruct (denot_ctx_in_env_star_elim Σ Γ1 Γ2 m Hctx)
    as [mfun [marg [Hc [Hle [Hctx_fun Hctx_arg]]]]].
  pose proof (IHfun mfun Hctx_fun) as Hfun.
  pose proof (IHarg marg Hctx_arg) as Harg.
  unfold denot_ty_in_ctx_under, denot_ty in Hfun, Harg.
  eapply denot_ty_lvar_gas_star_union_to_ctx.
  eapply appd_elim_denotation with
    (mfun := mfun) (marg := marg) (Hc := Hc).
  - apply basic_typing_star_union_lty_env. exact (proj2 Hwf).
  - exact Hle.
  - exact Hfun.
  - exact Harg.
Qed.

Lemma fundamental_fix_case
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf IH m Hctx.
  unfold denot_ty_in_ctx_under, denot_ty.
  eapply fix_intro_denotation
    with (L := L ∪ dom (erase_ctx_under Σ Γ)); eauto.
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - intros y F my Hy Hext Harg.
    assert (HyL : y ∉ L) by set_solver.
    assert (Hydom : y ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
    pose proof (IH y HyL my ltac:(
      eapply denot_ctx_in_env_comma_bind_from_arg_denotation; eauto))
      as Hbody.
    eapply denot_ty_in_ctx_under_comma_bind_to_lvar_insert in Hbody;
      [| exact Hydom].
    exact Hbody.
Qed.

Lemma fundamental_fixd_case
    (Φ : primop_ctx) Σ Γ τx τ vf b t (L : aset) :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTWand τx τ) ->
  (forall y, y ∉ L ->
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf IH m Hctx.
  unfold denot_ty_in_ctx_under, denot_ty.
  eapply fixd_intro_denotation
    with (L := L ∪ dom (erase_ctx_under Σ Γ)); eauto.
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - intros y marg Hc Hy Harg.
    assert (HyL : y ∉ L) by set_solver.
    assert (Hydom : y ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
    pose proof (IH y HyL (res_product marg m Hc) ltac:(
      eapply denot_ctx_in_env_star_bind_from_arg_denotation; eauto))
      as Hbody.
    eapply denot_ty_in_ctx_under_star_bind_to_lvar_insert in Hbody;
      [| exact Hydom].
    exact Hbody.
Qed.

Lemma appop_context_typing_arg_lookup
    (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) ->
  context_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) ->
  erase_ctx_under Σ Γ !! x = Some (erase_ty (primop_arg_ty (Φ op))).
Proof.
  intros Hsig [_ Hbasic].
  rewrite cty_open_preserves_erasure in Hbasic.
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

Lemma fundamental_appop_case
    (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) ->
  context_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (primop_arg_ty (Φ op)) (tret (vfvar x))) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ ({0 ~> x} (primop_result_ty (Φ op)))
      (tprim op (vfvar x)).
Proof.
  intros Hsig Hwf IH m Hctx.
  pose proof (proj1 (wf_primop_semantic op (Φ op) Hsig x)) as Hop.
  pose proof (appop_context_typing_arg_lookup Φ Σ Γ op x Hsig Hwf)
    as Hlookup.
  pose proof (IH m Hctx) as Harg.
  unfold denot_ty_in_ctx_under, denot_ty in Harg.
  unfold denot_ty_in_ctx_under, denot_ty.
  eapply appop_intro_denotation.
  - reflexivity.
  - exact (wf_primop_arg_basic op (Φ op) Hsig).
  - exact (wf_primop_result_basic op (Φ op) Hsig).
  - exact Hlookup.
  - exact (proj2 Hwf).
  - exact Hop.
  - exact Harg.
Qed.

Lemma fundamental_match_both_case
    (Φ : primop_ctx) Σ Γt Γf v τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf) ->
  (denot_ctx_in_env Σ Γt ⊫
    denot_ty_in_ctx_under Σ Γt (bool_precise_ty true) (tret v)) ->
  (denot_ctx_in_env Σ Γf ⊫
    denot_ty_in_ctx_under Σ Γf (bool_precise_ty false) (tret v)) ->
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt τt et) ->
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf τf ef) ->
  denot_ctx_in_env Σ (CtxSum Γt Γf) ⊫
    denot_ty_in_ctx_under Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch v et ef).
Proof.
  intros Hwf IHtrue IHfalse IHt IHf m Hctx.
  destruct (denot_ctx_in_env_sum_elim Σ Γt Γf m Hctx)
    as [mt [mf [Hdef [Hle [Hctxt Hctxf]]]]].
  pose proof (IHtrue mt Hctxt) as Htrue.
  pose proof (IHfalse mf Hctxf) as Hfalse.
  pose proof (IHt mt Hctxt) as Ht.
  pose proof (IHf mf Hctxf) as Hf.
  unfold denot_ty_in_ctx_under, denot_ty in Htrue, Hfalse, Ht, Hf |- *.
  destruct Hwf as [Hwf_cty Hbasic].
  destruct Hwf_cty as [[Hbasic_ctx _] _].
  cbn [basic_ctx] in Hbasic_ctx.
  destruct Hbasic_ctx as [_ [_ [_ Herase]]].
  eapply match_both_intro_denotation with
    (mt := mt) (mf := mf) (Hdef := Hdef).
  - rewrite lvar_store_to_atom_store_atom_store. exact Hbasic.
  - exact Hle.
  - apply denot_ty_lvar_gas_sum_left_to_ctx. exact Htrue.
  - eapply denot_ty_lvar_gas_sum_right_to_ctx; eauto.
  - apply denot_ty_lvar_gas_sum_left_to_ctx. exact Ht.
  - eapply denot_ty_lvar_gas_sum_right_to_ctx; eauto.
Qed.

Lemma fundamental_match_true_case
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty true) (tret v)) ->
  branch_unreachable Σ Γ v false ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ et) ->
  erase_ctx_under Σ Γ ⊢ₑ ef ⋮ erase_ty τ ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof.
  intros Hwf IHtrue Hunreach IHt Hef m Hctx.
  pose proof (IHtrue m Hctx) as Htrue.
  pose proof (IHt m Hctx) as Het.
  pose proof (Hunreach m Hctx) as Hunreach_m.
  unfold denot_ty_in_ctx_under, denot_ty in Htrue, Het, Hunreach_m |- *.
  eapply match_true_intro_denotation.
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - exact Hunreach_m.
  - exact Htrue.
  - exact Het.
  - rewrite lvar_store_to_atom_store_atom_store. exact Hef.
Qed.

Lemma fundamental_match_false_case
    (Φ : primop_ctx) Σ Γ v τ et ef :
  context_typing_wf Σ Γ (tmatch v et ef) τ ->
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (bool_precise_ty false) (tret v)) ->
  branch_unreachable Σ Γ v true ->
  erase_ctx_under Σ Γ ⊢ₑ et ⋮ erase_ty τ ->
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ ef) ->
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof.
  intros Hwf IHfalse Hunreach Het IHf m Hctx.
  pose proof (IHfalse m Hctx) as Hfalse.
  pose proof (IHf m Hctx) as Hef.
  pose proof (Hunreach m Hctx) as Hunreach_m.
  unfold denot_ty_in_ctx_under, denot_ty in Hfalse, Hef, Hunreach_m |- *.
  eapply match_false_intro_denotation.
  - rewrite lvar_store_to_atom_store_atom_store. exact (proj2 Hwf).
  - exact Hunreach_m.
  - exact Hfalse.
  - rewrite lvar_store_to_atom_store_atom_store. exact Het.
  - exact Hef.
Qed.

(** ** Fundamental theorem *)

Theorem Fundamental
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) :
  wf_primop_ctx Φ ->
  has_context_type Φ Σ Γ e τ ->
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ e.
Proof.
  intros HΦ Hty.
  induction Hty; eauto using fundamental_var_case, fundamental_const_case.
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
