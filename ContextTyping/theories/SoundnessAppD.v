(** * ContextTyping.SoundnessAppD

    AppD proof support for the direct Fundamental theorem. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  DenotationSetMapFacts
  TypeEquivCore
  TypeEquivFiberTransport
  TypeEquivFiberBase
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase SoundnessApp.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma appd_wand_fun_basic_insert_env
    Γ1 τx τ v1 x (m : WfWorldT) :
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ basic_world_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1))) ->
  m ⊨ ty_denote_gas (cty_depth (CTWand τx τ))
        (atom_env_to_lty_env (erase_ctx Γ1))
        (CTWand τx τ) (tret v1) ->
  m ⊨ expr_basic_typing_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1)))
        (tret v1) (erase_ty τx →ₜ erase_ty (cty_open 0 x τ)).
Proof.
  intros Hfresh Hworld Hfun.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Σrel := relevant_env Δ1 (CTWand τx τ) (tret v1)).
  set (Σins := <[LVFree x := erase_ty τx]> Σrel).
  pose proof (ty_denote_gas_guard
    (cty_depth (CTWand τx τ)) Δ1 (CTWand τx τ)
    (tret v1) m Hfun) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [_ [Hbasic_rel _]]].
  apply expr_basic_typing_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
  apply expr_basic_typing_formula_models_iff in Hbasic_rel
    as [_ [_ Hty_rel]].
  split; [exact Hlc|]. split; [exact Hscope|].
  rewrite cty_open_preserves_erasure.
  change (erase_ty τx →ₜ erase_ty τ) with (erase_ty (CTWand τx τ)).
  subst Σins.
  eapply basic_tm_has_ltype_weaken; [exact Hty_rel|].
  apply map_subseteq_spec. intros v T Hlook.
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - exfalso.
    pose proof (relevant_env_wand_fresh_free
      Δ1 τx τ (tret v1) x) as Hrel_fresh.
    apply Hrel_fresh.
    + better_set_solver.
    + better_set_solver.
    + cbn [fv_tm fv_value]. better_set_solver.
    + apply elem_of_dom. eexists. exact Hlook.
  - rewrite lookup_insert_ne by (symmetry; exact Hvx).
    exact Hlook.
Qed.

Lemma appd_arg_singleton_env_to_wand_arg
    Σ Γ1 Γ2 τx τ v1 x (m2 : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m2 ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ2))
        τx (tret (vfvar x)) ->
  res_restrict m2 ({[x]} : aset) ⊨ formula_open 0 x
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros Hwf_fun Hfresh Harg.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δ2 := atom_env_to_lty_env (erase_ctx Γ2)) in *.
  assert (Hτx_closed : wf_context_ty_at 0 ∅ τx).
  { exact (context_typing_wf_wand_arg_global
      Σ Γ1 (tret v1) τx τ Hwf_fun). }
  pose proof (ty_denote_gas_restrict_ret_fvar_closed
    (cty_depth τx) Δ2 τx x m2 Hτx_closed Harg) as Hargx.
  assert (Hxlookup : Δ2 !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup
      (cty_depth τx) Δ2 τx x (res_restrict m2 ({[x]} : aset)) Hargx). }
  assert (Hopen_env_fresh :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ1 (CTWand τx τ) (tret v1)) (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_wand_fresh_free
      Δ1 τx τ (tret v1) x Hxτx Hxτ Hxv1 Hbad).
  }
  assert (Hopen_tm_fresh : x ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  assert (Hopen_ty_fresh : x ∉ fv_cty (cty_shift 0 τx)).
  {
    rewrite cty_shift_fv.
    pose proof (wf_context_ty_at_fv_subset 0 ∅ τx Hτx_closed).
    better_set_solver.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ1 (CTWand τx τ) (tret v1)) (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))
    Hopen_env_fresh Hopen_tm_fresh Hopen_ty_fresh).
  change (open_tm 0 (vfvar x) (tret (vbvar 0))) with (tret (vfvar x)).
  rewrite (cty_open_shift_from_lc_fresh 0 x τx).
  2:{
    eapply wf_context_ty_at_lc. exact Hτx_closed.
  }
  2:{
    pose proof (wf_context_ty_at_fv_subset 0 ∅ τx Hτx_closed).
    better_set_solver.
  }
  rewrite (typed_lty_env_bind_open_current
    x (relevant_env Δ1 (CTWand τx τ) (tret v1)) (erase_ty τx)).
  2:{
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_wand_fresh_free
      Δ1 τx τ (tret v1) x Hxτx Hxτ Hxv1).
  }
  2:{
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Harg_big :
      res_restrict m2 ({[x]} : aset) ⊨
        ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
          Δ2 τx (tret (vfvar x))).
  {
    rewrite ty_denote_gas_saturate by (cbn [cty_depth]; lia).
    exact Hargx.
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    Δ2
    (<[LVFree x := erase_ty τx]>
      (relevant_env Δ1 (CTWand τx τ) (tret v1)))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x)))
    (res_restrict m2 ({[x]} : aset))).
  - reflexivity.
  - eapply lty_env_restrict_relevant_ret_fvar_closed_eq.
    + exact Hτx_closed.
    + exact Hxlookup.
    + apply map_lookup_insert.
  - exact Harg_big.
Qed.

Lemma appd_wand_result_first_arg_antecedent
    Σ Γ1 Γ2 τx τ v1 x z (m2 : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  z ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪ world_dom (m2 : WorldT) ->
  m2 ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ2))
        τx (tret (vfvar x)) ->
  res_restrict m2 ({[x]} : aset) ⊨ formula_open 0 x
    (formula_open 1 z
      (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
              (CTWand τx τ) (tret v1))
            (erase_ty (CTWand τx τ)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))).
Proof.
  intros Hwf_fun Hfresh Hzfresh Harg.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δ2 := atom_env_to_lty_env (erase_ctx Γ2)) in *.
  set (Σrel := relevant_env Δ1 (CTWand τx τ) (tret v1)).
  set (Tfun := erase_ty (CTWand τx τ)).
  assert (Hτx_closed : wf_context_ty_at 0 ∅ τx).
  { exact (context_typing_wf_wand_arg_global
      Σ Γ1 (tret v1) τx τ Hwf_fun). }
  assert (Hargx :
      res_restrict m2 ({[x]} : aset) ⊨
        ty_denote_gas (cty_depth τx) Δ2 τx (tret (vfvar x))).
  {
    eapply ty_denote_gas_restrict_ret_fvar_closed; eauto.
  }
  assert (Hxlookup : Δ2 !! LVFree x = Some (erase_ty τx)).
  { exact (ty_denote_gas_ret_fvar_lookup
      (cty_depth τx) Δ2 τx x (res_restrict m2 ({[x]} : aset)) Hargx). }
  assert (Hx_m2 : x ∈ world_dom (m2 : WorldT)).
  { eapply ty_denote_gas_ret_fvar_world_dom. exact Harg. }
  assert (Hzx : z <> x).
  { intros ->. apply Hzfresh. apply elem_of_union_r. exact Hx_m2. }
  assert (HzΣrel : LVFree z ∉ dom Σrel).
  {
    subst Σrel. apply soundness_relevant_env_wand_value_fresh.
    soundness_fresh_solve.
  }
  assert (HxΣrel : LVFree x ∉ dom Σrel).
  {
    subst Σrel. apply soundness_relevant_env_wand_value_fresh.
    soundness_fresh_solve.
  }
  rewrite (formula_open_result_first_fun_arg_two
    (Nat.max (cty_depth τx) (cty_depth τ))
    Σrel τx Tfun z x).
  2:{ subst Σrel. apply relevant_env_closed.
      apply atom_store_to_lvar_store_closed. }
  2:{ exact HzΣrel. }
  2:{ intros Hxz. apply Hzx. symmetry. exact Hxz. }
  2:{
    rewrite dom_insert_L. intros Hbad.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. inversion Hbad. subst.
      exact (Hzx eq_refl).
    - exact (HxΣrel Hbad).
  }
  2:{
    eapply wf_context_ty_at_lc. exact Hτx_closed.
  }
  2:{ intros Hbad. apply Hzfresh. apply elem_of_union_l.
      apply elem_of_union_l. apply elem_of_union_r. exact Hbad. }
  2:{ intros Hbad. apply Hfresh. apply elem_of_union_l.
      apply elem_of_union_r. exact Hbad. }
  assert (Harg_big :
      res_restrict m2 ({[x]} : aset) ⊨
        ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
          Δ2 τx (tret (vfvar x))).
  {
    rewrite ty_denote_gas_saturate by (cbn [cty_depth]; lia).
    exact Hargx.
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    Δ2
    (<[LVFree x := erase_ty τx]> (<[LVFree z := Tfun]> Σrel))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x)))
    (res_restrict m2 ({[x]} : aset))).
  - reflexivity.
  - eapply lty_env_restrict_relevant_ret_fvar_closed_eq.
    + exact Hτx_closed.
    + exact Hxlookup.
    + rewrite lookup_insert.
      destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
        [reflexivity|contradiction].
  - exact Harg_big.
Qed.

Lemma appd_wand_outer_value_open
    Σ Γ1 τx τ v1 (A : aset) (m : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  m ⊨ ty_denote_gas (cty_depth (CTWand τx τ))
        (atom_env_to_lty_env (erase_ctx Γ1))
        (CTWand τx τ) (tret v1) ->
  exists (z : atom) (Fz : fiber_extension) (mz : WfWorldT),
    z ∉ A ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
        world_dom (m : WorldT) /\
    expr_result_extension_witness_on (world_dom (m : WorldT))
      (tret v1) z Fz /\
    res_extend_by m Fz mz /\
    world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} /\
    res_restrict mz (world_dom (m : WorldT)) = m /\
    mz ⊨ expr_result_formula (tret v1) (LVFree z) /\
    mz ⊨ formula_open 0 z
      (wand_value_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1))
          (erase_ty (CTWand τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))).
Proof.
  intros Hwf_fun Hfun.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Σrel := relevant_env Δ1 (CTWand τx τ) (tret v1)).
  set (z := fresh_for
    (A ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
     world_dom (m : WorldT) ∪ lvars_fv (dom Σrel))).
  pose proof (fresh_for_not_in
    (A ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
     world_dom (m : WorldT) ∪ lvars_fv (dom Σrel))) as Hzfresh_all.
  assert (Hzfresh :
      z ∉ A ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
        world_dom (m : WorldT)).
  { subst z. better_set_solver. }
  assert (HzΣrel : z ∉ lvars_fv (dom Σrel)).
  { subst z. better_set_solver. }
  assert (Hguard :
      m ⊨ ty_guard_formula Σrel (CTWand τx τ) (tret v1)).
  {
    subst Σrel.
    apply ty_denote_gas_guard_formula with
      (gas := cty_depth (CTWand τx τ)).
    exact Hfun.
  }
  assert (Hzero :
      m ⊨ ty_denote_gas 0 Δ1 (CTWand τx τ) (tret v1)).
  { apply ty_denote_gas_zero_of_guard_formula. exact Hguard. }
  assert (Htotal : expr_total_on_atom_world (tret v1) m).
  { eapply ty_denote_gas_zero_total_atom_world; exact Hzero. }
  assert (Hfv_v1_m : fv_tm (tret v1) ⊆ world_dom (m : WorldT)).
  { eapply ty_denote_gas_fv_tm_subset; exact Hfun. }
  destruct (expr_result_extension_witness_on_exists
    (world_dom (m : WorldT)) (tret v1) z Hfv_v1_m
    ltac:(subst z; better_set_solver)) as [Fz HFz].
  destruct (expr_result_extension_witness_on_shape _ _ _ _ HFz)
    as [HFz_in HFz_out].
  unfold ext_in, ext_out in HFz_in, HFz_out.
  assert (Happ : extension_applicable Fz m).
  {
    constructor.
    - rewrite HFz_in. set_solver.
    - rewrite HFz_out. subst z. better_set_solver.
  }
  destruct (res_extend_by_exists m Fz Happ) as [mz Hext].
  pose proof (res_extend_by_singleton_output_open_world
    m mz Fz z Hext HFz_out) as [Hmz_dom Hmz_restrict].
  assert (Hbody_outer :
      m ⊨ FForall
        (FImpl
          (expr_result_formula_at (lvars_shift_from 0 (dom Σrel))
            (tm_shift 0 (tret v1)) (LVBound 0))
          (wand_value_denote_gas
            (Nat.max (cty_depth τx) (cty_depth τ))
            (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
            (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))))).
  {
    subst Σrel.
    cbn [cty_depth ty_denote_gas] in Hfun.
    repeat rewrite res_models_and_iff in Hfun.
    exact (proj2 Hfun).
  }
  pose proof (res_models_forall_open_named_fresh
    m mz z
    (FImpl
      (expr_result_formula_at (lvars_shift_from 0 (dom Σrel))
        (tm_shift 0 (tret v1)) (LVBound 0))
      (wand_value_denote_gas
        (Nat.max (cty_depth τx) (cty_depth τ))
        (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
        (cty_shift 0 τx) (cty_shift 1 τ) (tret (vbvar 0))))
    Hbody_outer ltac:(subst z; better_set_solver)
    Hmz_dom Hmz_restrict) as Houter_open.
  cbn [formula_open] in Houter_open.
	  assert (Hres_at :
	      mz ⊨ expr_result_formula_at (dom Σrel) (tret v1) (LVFree z)).
	  {
	    eapply expr_result_formula_at_env_of_result_extends_from_ty_guard_on.
	    - exact HFz.
	    - exact Hext.
	    - subst Σrel. exact Hguard.
	  }
	  rewrite (formula_open_result_first_expr_result_formula_at_shift0
	    z (dom Σrel) (tret v1)) in Houter_open.
	  2:{ subst Σrel. apply relevant_env_closed.
	      apply atom_store_to_lvar_store_closed. }
	  2:{ exact HzΣrel. }
	  2:{ constructor. eapply context_typing_wf_ret_lc_value.
	      exact Hwf_fun. }
	  2:{ cbn [fv_tm fv_value]. clear -Hzfresh; better_set_solver. }
	  pose proof (res_models_impl_elim _ _ _ Houter_open Hres_at)
	    as Hvalue.
	  assert (Hres_expr :
	      mz ⊨ expr_result_formula (tret v1) (LVFree z)).
	  {
	    eapply expr_result_formula_of_result_extends_on_from_ty_guard.
	    - exact HFz.
	    - exact Hext.
	    - subst Σrel. exact Hguard.
	  }
  exists z, Fz, mz.
  split; [exact Hzfresh|].
  split; [exact HFz|].
  split; [exact Hext|].
  split; [exact Hmz_dom|].
  split; [exact Hmz_restrict|].
  split; [exact Hres_expr|].
  exact Hvalue.
Qed.

Lemma appd_arg_product_to_star_env
    Σ Γ1 Γ2 τx τ v1 x (m1 m2 : WfWorldT)
    (Hc : world_compat (res_restrict m2 ({[x]} : aset)) m1) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  m2 ⊨ ty_denote_gas (cty_depth τx)
        (atom_env_to_lty_env (erase_ctx Γ2))
        τx (tret (vfvar x)) ->
  res_product (res_restrict m2 ({[x]} : aset)) m1 Hc ⊨
    ty_denote_gas (cty_depth τx)
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
      τx (tret (vfvar x)).
Proof.
  intros Hwf_fun Hwf_app Harg.
  pose proof (context_typing_wf_wand_arg_global
    Σ Γ1 (tret v1) τx τ Hwf_fun) as Hτx_closed.
  pose proof (ty_denote_gas_restrict_ret_fvar_closed
    (cty_depth τx) (atom_env_to_lty_env (erase_ctx Γ2))
    τx x m2 Hτx_closed Harg) as Hargx.
  assert (Hargx_prod :
      res_product (res_restrict m2 ({[x]} : aset)) m1 Hc ⊨
        ty_denote_gas (cty_depth τx)
          (atom_env_to_lty_env (erase_ctx Γ2))
          τx (tret (vfvar x))).
  {
    eapply res_models_kripke; [apply res_product_le_l|exact Hargx].
  }
  eapply (res_models_ty_denote_gas_env_agree_on
    (cty_depth τx)
    (atom_env_to_lty_env (erase_ctx Γ2))
    (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
    τx (tret (vfvar x))
    (relevant_lvars τx (tret (vfvar x)))
    (res_product (res_restrict m2 ({[x]} : aset)) m1 Hc)).
  - reflexivity.
  - pose proof (ty_denote_gas_ret_fvar_lookup
      (cty_depth τx) (atom_env_to_lty_env (erase_ctx Γ2))
      τx x m2 Harg) as HxΓ2.
    eapply lty_env_restrict_relevant_ret_fvar_closed_eq.
    + exact Hτx_closed.
    + exact HxΓ2.
    + rewrite atom_store_to_lvar_store_lookup_free.
      pose proof (context_typing_wf_ctx Σ (CtxStar Γ1 Γ2)
        (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hwfctx.
      pose proof (wf_ctx_under_basic Σ (CtxStar Γ1 Γ2) Hwfctx) as Hbasic.
      cbn [basic_ctx] in Hbasic.
      destruct Hbasic as [Hbasic1 [Hbasic2 Hdisj]].
      rewrite atom_store_to_lvar_store_lookup_free in HxΓ2.
      eapply erase_ctx_star_lookup_r_of_basic; eauto.
  - exact Hargx_prod.
Qed.

Lemma appd_open_result_env_agree
    Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  lty_env_restrict_lvars
    (<[LVFree x := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ1)))
    (relevant_lvars (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x))) =
  lty_env_restrict_lvars
    (<[LVFree x := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))))
    (relevant_lvars (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x))).
Proof.
  intros Hwf_fun Hwf_app.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ1 v1 (CTWand τx τ) Hwf_fun) as Hlc_v1.
  pose proof (context_typing_wf_context_ty Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hτopen_wf.
  change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτopen_wf.
  pose proof (wf_context_ty_at_lc 0 (dom (erase_ctx (CtxStar Γ1 Γ2)))
    (cty_open 0 x τ) Hτopen_wf) as Hlcτopen.
  assert (Hresult_rel_lc :
      lc_lvars (relevant_lvars (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)))).
  {
    apply lc_lvars_relevant_lvars.
    - exact Hlcτopen.
    - apply lc_tapp_tm; [constructor; exact Hlc_v1|constructor].
  }
  assert (Hrel_lc :
      lc_lvars (relevant_lvars (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)))).
  {
    unfold relevant_lvars. intros u Hu.
    apply elem_of_union in Hu as [Huτ|Hue].
    - pose proof (context_typing_wf_context_ty Σ (CtxStar Γ1 Γ2)
        (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hτwf.
      change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτwf.
      pose proof (cty_lc_at_lvars_bv_empty 0 (cty_open 0 x τ)
        (wf_context_ty_at_lc 0 (dom (erase_ctx (CtxStar Γ1 Γ2)))
          (cty_open 0 x τ) Hτwf)) as Hbv.
      destruct u as [k|a]; [|exact I].
      exfalso.
      assert (k ∈ lvars_bv (context_ty_lvars (cty_open 0 x τ)))
        by (apply lvars_bv_elem; exact Huτ).
      change (context_ty_lvars (cty_open 0 x τ))
        with (context_ty_lvars_at 0 (cty_open 0 x τ)) in H.
      rewrite Hbv in H. set_solver.
    - pose proof (tm_lvars_lc (tapp_tm (tret v1) (vfvar x))
        ltac:(apply lc_tapp_tm; [constructor; exact Hlc_v1|constructor])) as Hlc_tm.
      exact (Hlc_tm u Hue).
  }
  rewrite <- !lty_env_restrict_open_one_bind_as_insert
    by exact Hresult_rel_lc.
  eapply lty_env_restrict_open_one_bind_agree_on.
  - exact Hrel_lc.
  - intros y HyD Hyx.
    rewrite !atom_store_to_lvar_store_lookup_free.
    destruct (decide (y ∈ fv_value v1 ∪ fv_cty τ)) as [Hyrel|Hyrel].
    + assert (HyΓ1 : y ∈ dom (erase_ctx Γ1)).
        {
          pose proof (context_typing_wf_basic_typing Σ Γ1
            (tret v1) (CTWand τx τ) Hwf_fun) as Hbasic_fun.
          pose proof (basic_tm_has_ltype_of_atom_env_typing
            (erase_ctx Γ1) (tret v1) (erase_ty (CTWand τx τ))
            Hbasic_fun) as Hbasic_fun_lty.
          pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_fun_lty)
            as Hfun_lvars.
          pose proof (context_typing_wf_context_ty Σ Γ1
            (tret v1) (CTWand τx τ) Hwf_fun) as Hτwf_fun.
          cbn [wf_context_ty_at] in Hτwf_fun.
          destruct Hτwf_fun as [_ Hτwf_res].
          pose proof (wf_context_ty_at_fv_subset 1 (dom (erase_ctx Γ1))
            τ Hτwf_res) as Hτfv.
          apply elem_of_union in Hyrel as [Hyv|Hyτ].
          - assert (LVFree y ∈ lvars_of_atoms (fv_tm (tret v1))).
            {
              cbn [fv_tm].
              unfold lvars_of_atoms.
              apply elem_of_map.
              exists y. split; [reflexivity|exact Hyv].
            }
            pose proof (Hfun_lvars (LVFree y) H) as Hy_lvar.
            apply lvars_fv_elem in Hy_lvar.
            rewrite atom_store_to_lvar_store_dom in Hy_lvar.
            rewrite lvars_fv_of_atoms in Hy_lvar.
            exact Hy_lvar.
          - apply Hτfv. exact Hyτ.
        }
      assert (HyΓ2none : (erase_ctx Γ2 : gmap atom ty) !! y = None).
        {
          pose proof (context_typing_wf_ctx Σ (CtxStar Γ1 Γ2)
            (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hwfctx.
          pose proof (wf_ctx_under_basic Σ (CtxStar Γ1 Γ2) Hwfctx) as Hbasic.
          cbn [basic_ctx] in Hbasic.
          destruct Hbasic as [Hbasic1 [Hbasic2 Hdisj]].
          pose proof (basic_ctx_erase_dom (dom Σ) Γ1 Hbasic1) as Hdom1.
          pose proof (basic_ctx_erase_dom (dom Σ) Γ2 Hbasic2) as Hdom2.
          apply not_elem_of_dom. intros HyΓ2.
          rewrite Hdom1 in HyΓ1.
          rewrite Hdom2 in HyΓ2.
          better_set_solver.
        }
      apply elem_of_dom in HyΓ1 as [T HT].
      change ((erase_ctx Γ1 : gmap atom ty) !! y =
        (erase_ctx (CtxStar Γ1 Γ2) : gmap atom ty) !! y)
        with ((erase_ctx Γ1 : gmap atom ty) !! y =
          ((erase_ctx Γ1 ∪ erase_ctx Γ2) : gmap atom ty) !! y).
      rewrite <- (lookup_union_l' (M:=gmap atom) (A:=ty)
        (erase_ctx Γ1) (erase_ctx Γ2) y ltac:(eexists; exact HT)).
      reflexivity.
    + assert (Hy_not_R : LVFree y ∉ relevant_lvars (cty_open 0 x τ)
          (tapp_tm (tret v1) (vfvar x))).
        {
          intros HyR.
          apply lvars_fv_elem in HyR.
          rewrite relevant_lvars_fv in HyR.
          rewrite fv_tapp_tm in HyR.
          cbn [fv_tm fv_value] in HyR.
          pose proof (cty_open_fv_subset 0 x τ) as Hτopen.
          better_set_solver.
        }
      contradiction.
Qed.

Lemma appd_wand_result_to_arrow_open_result
    Σ Γ1 Γ2 τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree x := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
        (CTWand τx τ) (tret v1)))
    (cty_open 0 x τ)
    (tapp_tm (tret v1) (vfvar x)) ->
  m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree x := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
        (CTArrow τx τ) (tret v1)))
    (cty_open 0 x τ)
    (tapp_tm (tret v1) (vfvar x)).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hsrc.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δstar := atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))) in *.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ1 v1 (CTWand τx τ) Hwf_fun) as Hlc_v1.
	  pose proof (context_typing_wf_context_ty Σ (CtxStar Γ1 Γ2)
	    (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hτopen_wf_result.
	  change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτopen_wf_result.
	  pose proof (wf_context_ty_at_lc 0 (dom (erase_ctx (CtxStar Γ1 Γ2)))
	    (cty_open 0 x τ) Hτopen_wf_result) as Hlcτopen_result.
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  {
    pose proof (context_typing_wf_context_ty Σ Γ1
      (tret v1) (CTWand τx τ) Hwf_fun) as Hτ_wf.
    cbn [wf_context_ty_at] in Hτ_wf.
    eapply wf_context_ty_at_lc. exact (proj2 Hτ_wf).
  }
  assert (Hresult_rel_lc :
      lc_lvars (relevant_lvars (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)))).
  {
    apply lc_lvars_relevant_lvars.
    - exact Hlcτopen_result.
    - apply lc_tapp_tm; [constructor; exact Hlc_v1|constructor].
  }
  assert (Hmid1 :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (<[LVFree x := erase_ty τx]> Δ1)
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    assert (Hsrc_inserted :
        m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
          (<[LVFree x := erase_ty τx]>
            (relevant_env Δ1 (CTWand τx τ) (tret v1)))
          (cty_open 0 x τ)
          (tapp_tm (tret v1) (vfvar x))).
	    {
	      exact Hsrc.
	    }
	    eapply ty_equiv_wand_result_src_mid.
	    - constructor. exact Hlc_v1.
	    - better_set_solver.
	    - eapply cty_lvars_open_body_closed_no_fresh.
	      + apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
	        exact Hτ_lc1.
	      + intros HxD.
	        apply lvars_fv_elem in HxD.
	        rewrite context_ty_lvars_fv_at in HxD.
	        clear -Hfresh HxD. better_set_solver.
	      + reflexivity.
	    - exact Hsrc_inserted.
	  }
  assert (Hmidstar :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (<[LVFree x := erase_ty τx]> Δstar)
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    eapply res_models_ty_denote_gas_env_agree_on.
    - reflexivity.
    - subst Δ1 Δstar.
      exact (appd_open_result_env_agree Σ Γ1 Γ2 τx τ v1 x
        Hwf_fun Hwf_app).
    - exact Hmid1.
  }
  assert (Hgoal_inserted :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (<[LVFree x := erase_ty τx]>
          (relevant_env Δstar (CTArrow τx τ) (tret v1)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
	  {
	    eapply ty_equiv_arrow_result_tgt_goal_inserted_lc.
	    - constructor. exact Hlc_v1.
	    - better_set_solver.
	    - exact Hτ_lc1.
	    - exact Hresult_rel_lc.
	    - exact Hmidstar.
	  }
  exact Hgoal_inserted.
Qed.

Lemma appd_wand_basic_world_insert_env
    Γ1 Δarg τx τ v1 x (m : WfWorldT) :
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth (CTWand τx τ))
        (atom_env_to_lty_env (erase_ctx Γ1))
        (CTWand τx τ) (tret v1) ->
  m ⊨ ty_denote_gas (cty_depth τx)
        Δarg τx (tret (vfvar x)) ->
  m ⊨ basic_world_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1))).
Proof.
  intros Hfresh Hfun Harg.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Σrel := relevant_env Δ1 (CTWand τx τ) (tret v1)).
  pose proof (ty_denote_gas_guard
    (cty_depth (CTWand τx τ)) Δ1 (CTWand τx τ)
    (tret v1) m Hfun) as Hfun_guard.
  repeat rewrite res_models_and_iff in Hfun_guard.
  destruct Hfun_guard as [_ [Hworld_rel [_ _]]].
  pose proof (ty_denote_gas_ret_fvar_basic_world_singleton
    (cty_depth τx) Δarg τx x m Harg) as Hworld_x.
  pose proof (basic_world_formula_union
    (<[LVFree x := erase_ty τx]> (∅ : lty_env)) Σrel m
    Hworld_x Hworld_rel) as Hunion.
  eapply basic_world_formula_subenv; [|exact Hunion].
  intros v T Hlook.
  change ((<[LVFree x := erase_ty τx]> (Σrel : gmap logic_var ty))
    !! v = Some T) in Hlook.
  change (((<[LVFree x := erase_ty τx]> (∅ : lty_env)) ∪ Σrel
    : gmap logic_var ty) !! v = Some T).
  destruct (decide (v = LVFree x)) as [->|Hvx].
  - apply map_lookup_union_Some_raw. left.
    rewrite !lookup_insert in Hlook |- *.
    destruct (decide (LVFree x = LVFree x)) as [_|Hneq] in Hlook |- *;
      [exact Hlook|contradiction].
  - apply map_lookup_union_Some_raw. right. split.
    + rewrite lookup_insert_ne by (symmetry; exact Hvx).
      apply lookup_empty.
    + rewrite lookup_insert_ne in Hlook by (symmetry; exact Hvx).
      exact Hlook.
Qed.

Lemma appd_wand_context_wf_insert_env
    Σ Γ1 Γ2 τx τ v1 x (m : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ basic_world_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1))) ->
  m ⊨ context_ty_wf_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1)))
        (cty_open 0 x τ).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hworld.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)).
  set (Σins := <[LVFree x := erase_ty τx]>
    (relevant_env Δ1 (CTWand τx τ) (tret v1))).
  apply context_ty_wf_formula_models_iff.
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hscope _]].
  split; [exact Hlc|]. split; [exact Hscope|].
  pose proof (context_typing_wf_context_ty
    Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)
    Hwf_app) as Hτopen_wf.
  change ({0 ~> x} τ) with (cty_open 0 x τ) in Hτopen_wf.
  pose proof (wf_context_ty_at_to_lvars_shape
    0 (dom (erase_ctx (CtxStar Γ1 Γ2))) (cty_open 0 x τ)
    Hτopen_wf) as [_ Hshape].
  split; [|exact Hshape].
  intros v Hv.
  destruct v as [k|y].
  - exfalso.
    pose proof (wf_context_ty_at_lc 0
      (dom (erase_ctx (CtxStar Γ1 Γ2)))
      (cty_open 0 x τ) Hτopen_wf) as Hlcτ.
    pose proof (cty_lc_at_lvars_bv_empty 0
      (cty_open 0 x τ) Hlcτ) as Hbv.
    apply lvars_bv_elem in Hv.
    change (context_ty_lvars (cty_open 0 x τ))
      with (context_ty_lvars_at 0 (cty_open 0 x τ)) in Hv.
    rewrite Hbv in Hv. set_solver.
  - subst Σins Δ1.
    rewrite dom_insert_L.
    apply elem_of_union.
    destruct (decide (y = x)) as [->|Hyx].
    + left. set_solver.
    + right.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_dom.
      apply elem_of_intersection. split.
      * pose proof (context_typing_wf_context_ty
          Σ Γ1 (tret v1) (CTWand τx τ) Hwf_fun) as Hτfun_wf.
        cbn [wf_context_ty_at] in Hτfun_wf.
        destruct Hτfun_wf as [_ Hτ_body_wf].
        pose proof (wf_context_ty_at_fv_subset
          1 (dom (erase_ctx Γ1)) τ Hτ_body_wf) as Hτ_fv.
        assert (Hy_fv_open : y ∈ fv_cty (cty_open 0 x τ)).
        { apply lvars_fv_elem. exact Hv. }
        pose proof (cty_open_fv_subset 0 x τ y Hy_fv_open)
          as Hy_fv.
        apply elem_of_union in Hy_fv as [Hyτ|Hyx_single].
        -- rewrite atom_store_to_lvar_store_dom.
           unfold lvars_of_atoms. apply elem_of_map.
           exists y. split; [reflexivity|exact (Hτ_fv y Hyτ)].
        -- exfalso. apply Hyx.
           apply elem_of_singleton in Hyx_single. exact Hyx_single.
      * unfold relevant_lvars.
        cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
          context_ty_lvars context_ty_lvars_at].
        assert (Hy_fv_open : y ∈ fv_cty (cty_open 0 x τ)).
        { apply lvars_fv_elem. exact Hv. }
        pose proof (cty_open_fv_subset 0 x τ y Hy_fv_open)
          as Hy_fv.
        apply elem_of_union in Hy_fv as [Hyτ|Hyx_single].
        -- rewrite <- (context_ty_lvars_fv_at 1 τ) in Hyτ.
           apply elem_of_union_l. apply elem_of_union_r.
           apply lvars_fv_elem. exact Hyτ.
        -- exfalso. apply Hyx.
           apply elem_of_singleton in Hyx_single. exact Hyx_single.
Qed.

Lemma appd_wand_mid_static_guard
    Σ Γ1 Γ2 τx τ v1 x Δarg (m : WfWorldT) :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  m ⊨ ty_denote_gas (cty_depth (CTWand τx τ))
        (atom_env_to_lty_env (erase_ctx Γ1))
        (CTWand τx τ) (tret v1) ->
  m ⊨ ty_denote_gas (cty_depth τx)
        Δarg τx (tret (vfvar x)) ->
  m ⊨ ty_static_guard_formula
        (<[LVFree x := erase_ty τx]>
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
            (CTWand τx τ) (tret v1)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x)).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hfun Harg.
  pose proof (appd_wand_basic_world_insert_env
    Γ1 Δarg τx τ v1 x m Hfresh Hfun Harg) as Hworld.
  eapply (ty_static_guard_tapp_fun_result_base
    (<[LVFree x := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
        (CTWand τx τ) (tret v1)))
    (cty_open 0 x τ) v1 x (erase_ty τx) m).
  - rewrite lookup_insert.
    destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
      [reflexivity|contradiction].
  - eapply appd_wand_context_wf_insert_env; eauto.
  - exact Hworld.
  - eapply appd_wand_fun_basic_insert_env; eauto.
Qed.

Lemma fundamental_appd_case Σ Γ1 Γ2 τx τ v1 x :
  context_typing_wf Σ Γ1 (tret v1) (CTWand τx τ) ->
  context_typing_wf Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) ->
  x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
  (ctx_denote_under Σ Γ1 ⊫
    ty_denote_under Σ Γ1 (CTWand τx τ) (tret v1)) ->
  (ctx_denote_under Σ Γ2 ⊫
    ty_denote_under Σ Γ2 τx (tret (vfvar x))) ->
  ctx_denote_under Σ (CtxStar Γ1 Γ2) ⊫
    ty_denote_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ)
      (tapp v1 (vfvar x)).
Proof.
  intros Hwf_fun Hwf_app Hfresh HfunIH HargIH m Hctx.
  unfold ty_denote_under, ty_denote.
  pose proof (context_typing_wf_ctx Σ (CtxStar Γ1 Γ2)
    (tapp v1 (vfvar x)) ({0 ~> x} τ) Hwf_app) as Hwfctx_star.
  pose proof (wf_ctx_under_basic Σ (CtxStar Γ1 Γ2) Hwfctx_star)
    as Hbasic_star.
  cbn [basic_ctx] in Hbasic_star.
  destruct Hbasic_star as [HbasicΓ1 [HbasicΓ2 HdisjΓ12]].
  destruct (ctx_denote_under_star_elim Σ Γ1 Γ2 m Hctx)
    as [m1 [m2 [Hc12 [Hle12 [HΓ1 HΓ2]]]]].
  pose proof (HfunIH m1 HΓ1) as Hfun_m1.
  pose proof (HargIH m2 HΓ2) as Harg_m2.
  unfold ty_denote_under, ty_denote in Hfun_m1, Harg_m2.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δstar := atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))) in *.
  set (Σrel := relevant_env Δ1 (CTWand τx τ) (tret v1)).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (argX := res_restrict m2 ({[x]} : aset)).
  set (m1d := res_restrict m1 (world_dom (m1 : WorldT) ∖ {[x]})).
  assert (Hfun_m1d :
      m1d ⊨ ty_denote_gas (cty_depth (CTWand τx τ))
        Δ1 (CTWand τx τ) (tret v1)).
  {
    subst m1d Δ1.
    apply (ty_denote_gas_restrict_delete_fresh
      (cty_depth (CTWand τx τ))
      (atom_env_to_lty_env (erase_ctx Γ1))
      (CTWand τx τ) (tret v1) x m1).
    + cbn [fv_tm fv_value]. cty_fv_syntax_norm.
      rewrite !context_ty_lvars_fv_at.
      clear -Hfresh. better_set_solver.
    + exact Hfun_m1.
  }
  assert (Hx_m2 : x ∈ world_dom (m2 : WorldT)).
  { eapply ty_denote_gas_ret_fvar_world_dom. exact Harg_m2. }
  destruct (res_product_comm_eq m1 m2 Hc12) as [Hc21 Heq21].
  assert (Hc_arg_m1d : world_compat argX m1d).
  {
    subst argX m1d.
    eapply world_compat_restrict_overlap
      with (S := world_dom (m1 : WorldT)) (n := m2) (m := m1).
    - set_solver.
    - rewrite (res_restrict_eq_of_le m1 m1 ltac:(apply raw_le_refl)).
      exact Hc21.
  }
  destruct (appd_wand_outer_value_open
    Σ Γ1 τx τ v1
    (world_dom (m2 : WorldT) ∪ world_dom (m1 : WorldT))
    m1d Hwf_fun Hfun_m1d)
    as (z & Fz & m1z & Hzfresh & HFz & Hext_z &
      Hm1z_dom & Hm1z_restrict & Hres_v1_z_m1z & Hvalue).
  assert (Hz_m2 : z ∉ world_dom (m2 : WorldT)).
  { clear -Hzfresh. better_set_solver. }
  assert (Hz_m1 : z ∉ world_dom (m1 : WorldT)).
  { clear -Hzfresh. better_set_solver. }
  assert (Hzx : z <> x).
  { intros ->. exact (Hz_m2 Hx_m2). }
  destruct (expr_result_extension_witness_on_shape _ _ _ _ HFz)
    as [HFz_in HFz_out].
  assert (Hout_arg : extA_out Fz ## world_dom (argX : WorldT)).
  {
    change (ext_out Fz ## world_dom (argX : WorldT)).
    rewrite HFz_out. subst argX.
    rewrite res_restrict_dom.
    clear -Hz_m2. set_solver.
  }
  destruct (res_extend_by_product_frame_l
    m1d m1z argX Fz Hc_arg_m1d Hext_z Hout_arg)
    as [Hc_arg_m1z Hext_prod].
  set (psmall := res_product argX m1d Hc_arg_m1d).
  set (pz := res_product argX m1z Hc_arg_m1z).
  assert (Hx_not_m1z : x ∉ world_dom (m1z : WorldT)).
  {
    rewrite Hm1z_dom. subst m1d.
    rewrite res_restrict_dom.
    clear -Hzx. set_solver.
  }
  assert (Hdom_pz :
      world_dom (pz : WorldT) =
      world_dom (m1z : WorldT) ∪ {[x]}).
  {
    subst pz argX.
    change (world_dom
      (res_product (res_restrict m2 ({[x]} : aset)) m1z Hc_arg_m1z
        : WorldT) =
      world_dom (m1z : WorldT) ∪ {[x]}).
    assert (Hsingle : world_dom (m2 : WorldT) ∩ ({[x]} : aset) =
        ({[x]} : aset)).
    {
      apply set_eq. intros a. split.
      - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
      - intros Ha. apply elem_of_intersection. split; [|exact Ha].
        apply elem_of_singleton in Ha. subst a. exact Hx_m2.
    }
    rewrite res_product_dom, res_restrict_dom.
    rewrite Hsingle. clear -Hx_not_m1z. set_solver.
  }
  assert (Harg_open :
      argX ⊨ formula_open 0 x
        (formula_open 1 z
          (ty_denote_gas gas
            (typed_lty_env_bind
              (typed_lty_env_bind Σrel
                (erase_ty (CTWand τx τ)))
              (erase_ty (cty_shift 0 τx)))
            (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))))).
  {
    subst argX gas Σrel Δ1.
    eapply appd_wand_result_first_arg_antecedent; eauto.
    clear -Hzfresh. better_set_solver.
  }
  pose proof (res_models_fbwand_open_one_named_fresh
    m1z argX x
    (formula_open 1 z
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))))
    (formula_open 1 z
      (ty_denote_gas gas
        (typed_lty_env_bind
          (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τ)
        (tapp_tm (tret (vbvar 1)) (vbvar 0))))
    Hc_arg_m1z Hvalue Hx_not_m1z Hdom_pz Harg_open) as Hres_raw.
  assert (Hres_norm :
      pz ⊨ ty_denote_gas gas
        (<[LVFree x := erase_ty τx]>
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        (cty_open 0 x τ)
        (tapp_tm (tret (vfvar z)) (vfvar x))).
  {
    change (pz ⊨ formula_open 0 x
      (formula_open 1 z
        (ty_denote_gas gas
          (typed_lty_env_bind
            (typed_lty_env_bind Σrel (erase_ty (CTWand τx τ)))
            (erase_ty (cty_shift 0 τx)))
          (cty_shift 1 τ)
          (tapp_tm (tret (vbvar 1)) (vbvar 0))))) in Hres_raw.
    rewrite (formula_open_result_first_fun_result_two
      gas Σrel τx τ (erase_ty (CTWand τx τ)) z x) in Hres_raw.
    - exact Hres_raw.
    - subst Σrel Δ1. apply relevant_env_closed.
      apply atom_store_to_lvar_store_closed.
    - subst Σrel Δ1. apply relevant_env_wand_fresh_free;
        cbn [fv_tm fv_value]; clear -Hzfresh; better_set_solver.
    - intros Hxz. subst x. exact (Hz_m2 Hx_m2).
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. inversion Hin. subst.
        exact (Hz_m2 Hx_m2).
      + subst Σrel Δ1. apply relevant_env_wand_fresh_free in Hin;
          cbn [fv_tm fv_value]; clear -Hfresh Hin; better_set_solver.
    - pose proof (context_typing_wf_context_ty
        Σ Γ1 (tret v1) (CTWand τx τ) Hwf_fun) as Hτwf.
      cbn [wf_context_ty_at] in Hτwf.
      eapply wf_context_ty_at_lc. exact (proj2 Hτwf).
    - clear -Hzfresh. better_set_solver.
    - clear -Hfresh. better_set_solver.
  }
  assert (Hfun_pz :
      pz ⊨ ty_denote_gas (cty_depth (CTWand τx τ))
        Δ1 (CTWand τx τ) (tret v1)).
  {
    subst pz.
    eapply res_models_kripke; [apply res_product_le_r|].
    eapply res_models_kripke; [|exact Hfun_m1d].
    rewrite <- Hm1z_restrict.
    apply res_restrict_le.
  }
  assert (Harg_pz_star :
      pz ⊨ ty_denote_gas (cty_depth τx)
        Δstar τx (tret (vfvar x))).
  {
    subst pz argX Δstar.
    eapply appd_arg_product_to_star_env; eauto.
  }
  assert (Hstatic_pz :
      pz ⊨ ty_static_guard_formula
        (<[LVFree x := erase_ty τx]> Σrel)
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    subst Σrel Δ1 gas.
    eapply appd_wand_mid_static_guard; eauto.
  }
  pose proof Hstatic_pz as Hstatic_parts.
  unfold ty_static_guard_formula in Hstatic_parts.
  repeat rewrite res_models_and_iff in Hstatic_parts.
  destruct Hstatic_parts as [_ [Hworld_insert _]].
  pose proof (appd_wand_fun_basic_insert_env
    Γ1 τx τ v1 x pz Hfresh Hworld_insert Hfun_pz)
    as Hbasic_fun_pz.
  assert (Hres_alias_src :
      pz ⊨ ty_denote_gas gas
        (<[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 x τ)]>
          (<[LVFree x := erase_ty τx]> Σrel))
        (cty_open 0 x τ)
        (tapp_tm (tret (vfvar z)) (vfvar x))).
  {
    eapply res_models_ty_denote_gas_env_agree_on
      with (Σ1 := <[LVFree x := erase_ty τx]>
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        (X := relevant_lvars (cty_open 0 x τ)
          (tapp_tm (tret (vfvar z)) (vfvar x))).
    - reflexivity.
    - rewrite cty_open_preserves_erasure.
      rewrite lty_env_insert_free_commute by
        (intros ->; exact (Hz_m2 Hx_m2)).
      reflexivity.
    - exact Hres_norm.
  }
  assert (Hz_base_env :
      LVFree z ∉ dom (<[LVFree x := erase_ty τx]> Σrel)).
  {
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst.
      exact (Hz_m2 Hx_m2).
    - subst Σrel Δ1. apply relevant_env_wand_fresh_free in Hin;
        cbn [fv_tm fv_value]; clear -Hzfresh Hin; better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value v1 ∪ {[x]} ∪ fv_cty (cty_open 0 x τ)).
  {
    pose proof (cty_open_fv_subset 0 x τ z) as Hopen_fv.
    clear -Hzfresh Hopen_fv Hzx. better_set_solver.
  }
  assert (Hres_v1_z_pz :
      pz ⊨ expr_result_formula (tret v1) (LVFree z)).
  {
    subst pz.
    eapply res_models_kripke; [apply res_product_le_r|].
    exact Hres_v1_z_m1z.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_back_from_static
    gas (<[LVFree x := erase_ty τx]> Σrel)
    (cty_open 0 x τ) v1 x z (erase_ty τx) pz
    Hz_base_env Hz_alias_fresh
    ltac:(rewrite lookup_insert;
          destruct (decide (LVFree x = LVFree x));
          [reflexivity|contradiction])
    ltac:(eapply context_typing_wf_ret_lc_value; exact Hwf_fun)
    Hres_v1_z_pz Hbasic_fun_pz Hstatic_pz Hres_alias_src)
    as Htarget_pz.
	  assert (Htarget_opened_wand :
	      pz ⊨ ty_denote_gas gas
	        (<[LVFree x := erase_ty τx]> Σrel)
	        (cty_open 0 x τ)
	        (tapp_tm (tret v1) (vfvar x))).
	  {
	    exact Htarget_pz.
	  }
	  pose proof (appd_wand_result_to_arrow_open_result
	    Σ Γ1 Γ2 τx τ v1 x pz Hwf_fun Hwf_app Hfresh
	    Htarget_opened_wand) as Htarget_opened_arrow.
	  assert (Htarget_arrow_norm :
      pz ⊨ ty_denote_gas gas
	        (<[LVFree x := erase_ty τx]>
	          (relevant_env Δstar (CTArrow τx τ) (tret v1)))
	        (cty_open 0 x τ) (tapp_tm (tret v1) (vfvar x))).
	  {
	    exact Htarget_opened_arrow.
	  }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  {
    pose proof (context_typing_wf_context_ty
      Σ Γ1 (tret v1) (CTWand τx τ) Hwf_fun) as Hτfun.
    cbn [wf_context_ty_at] in Hτfun.
    exact (wf_context_ty_at_lc 1 (dom (erase_ctx Γ1)) τ (proj2 Hτfun)).
  }
	  pose proof (app_arrow_result_to_target
	    Σ (CtxStar Γ1 Γ2) τx τ v1 x pz Hwf_app Hτ_lc1 Hfresh
	    Harg_pz_star Htarget_arrow_norm) as Htarget_pz_final.
  assert (Htarget_psmall :
      psmall ⊨ ty_denote_gas (cty_depth ({0 ~> x} τ))
        Δstar ({0 ~> x} τ) (tapp v1 (vfvar x))).
  {
    assert (Hfv_target :
        formula_fv (ty_denote_gas (cty_depth ({0 ~> x} τ))
          Δstar ({0 ~> x} τ) (tapp v1 (vfvar x))) ⊆
        world_dom (psmall : WorldT)).
    {
      pose proof (res_models_scoped _ _ Htarget_pz_final) as Hscope.
      pose proof (formula_fv_ty_denote_gas_subset_relevant
        (cty_depth ({0 ~> x} τ)) Δstar ({0 ~> x} τ)
        (tapp v1 (vfvar x))) as Hfv.
      intros a Ha.
      pose proof (Hscope a Ha) as Ha_pz.
      subst pz psmall.
      pose proof (res_extend_by_dom
        (res_product argX m1d Hc_arg_m1d) Fz
        (res_product argX m1z Hc_arg_m1z) Hext_prod) as Hdom_ext.
      change (world_dom
        (res_product argX m1z Hc_arg_m1z : WorldT) =
        world_dom (res_product argX m1d Hc_arg_m1d : WorldT) ∪
          ext_out Fz) in Hdom_ext.
      rewrite Hdom_ext in Ha_pz.
      destruct (expr_result_extension_witness_on_shape _ _ _ _ HFz)
        as [_ Hout].
      rewrite Hout in Ha_pz.
      apply elem_of_union in Ha_pz as [Ha_small|Ha_z]; [exact Ha_small|].
      exfalso. apply elem_of_singleton in Ha_z. subst a.
      apply Hfv in Ha.
      cbn [fv_tm fv_value] in Ha.
      pose proof (cty_open_fv_subset 0 x τ z) as Hopen_fv.
      apply elem_of_union in Ha as [Hzv1|Hzτopen].
      + apply Hzfresh. better_set_solver.
      + pose proof (Hopen_fv Hzτopen) as Hzτ.
        apply Hzfresh. better_set_solver.
    }
    pose proof (proj1 (res_models_minimal_on
      (world_dom (psmall : WorldT)) pz
      (ty_denote_gas (cty_depth ({0 ~> x} τ))
        Δstar ({0 ~> x} τ) (tapp v1 (vfvar x)))
      Hfv_target) Htarget_pz_final) as Hmin.
    subst pz psmall.
    rewrite (res_extend_by_restrict_base
      (res_product argX m1d Hc_arg_m1d) Fz
      (res_product argX m1z Hc_arg_m1z) Hext_prod) in Hmin.
    exact Hmin.
  }
  assert (Hpsmall_le_m : psmall ⊑ m).
  {
    subst psmall argX m1d.
    etransitivity.
    - eapply res_product_le_mono.
      + apply res_restrict_le.
      + apply res_restrict_le.
    - rewrite <- Heq21. exact Hle12.
  }
  subst Δstar.
  eapply res_models_kripke; [exact Hpsmall_le_m|].
  exact Htarget_psmall.
Qed.
