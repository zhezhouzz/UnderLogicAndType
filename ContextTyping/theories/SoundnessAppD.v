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
  TypeEquivCore
  TypeEquivFiberTransport
  TypeEquivFiberBase
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessApp.

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
    subst Σrel. apply relevant_env_wand_fresh_free.
    - intros Hbad. apply Hzfresh. apply elem_of_union_l.
      apply elem_of_union_l. apply elem_of_union_r. exact Hbad.
    - intros Hbad. apply Hzfresh. apply elem_of_union_l.
      apply elem_of_union_r. exact Hbad.
    - cbn [fv_tm fv_value]. intros Hbad.
      apply Hzfresh. apply elem_of_union_l.
      apply elem_of_union_l. apply elem_of_union_l. exact Hbad.
  }
  assert (HxΣrel : LVFree x ∉ dom Σrel).
  {
    subst Σrel. apply relevant_env_wand_fresh_free.
    - intros Hbad. apply Hfresh. apply elem_of_union_l.
      apply elem_of_union_r. exact Hbad.
    - intros Hbad. apply Hfresh. apply elem_of_union_r. exact Hbad.
    - cbn [fv_tm fv_value]. intros Hbad.
      apply Hfresh. apply elem_of_union_l.
      apply elem_of_union_l. exact Hbad.
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
  exists (z : atom) (mz : WfWorldT),
    z ∉ A ∪ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ∪
        world_dom (m : WorldT) /\
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
  assert (Hmz_dom :
      world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]}).
  {
    pose proof (res_extend_by_dom m Fz mz Hext) as Hdom.
    rewrite Hdom, HFz_out. reflexivity.
  }
  assert (Hmz_restrict :
      res_restrict mz (world_dom (m : WorldT)) = m).
  { exact (res_extend_by_restrict_base m Fz mz Hext). }
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
    eapply expr_result_formula_at_of_result_extends_on_coarsen
      with (X := world_dom (m : WorldT)) (F := Fz) (m := m).
    - subst Σrel. apply relevant_env_closed.
      apply atom_store_to_lvar_store_closed.
    - pose proof Hguard as Hguard_parts.
      unfold ty_guard_formula in Hguard_parts.
      repeat rewrite res_models_and_iff in Hguard_parts.
      destruct Hguard_parts as [_ [_ [Hbasic _]]].
      apply expr_basic_typing_formula_models_iff in Hbasic
        as [_ [_ Hty]].
      rewrite (tm_lvars_lc_eq_atoms (tret v1)).
      2:{ constructor. eapply context_typing_wf_ret_lc_value.
          exact Hwf_fun. }
      eapply basic_tm_has_ltype_lvars. exact Hty.
    - pose proof Hguard as Hguard_parts.
      unfold ty_guard_formula in Hguard_parts.
      repeat rewrite res_models_and_iff in Hguard_parts.
      destruct Hguard_parts as [_ [Hworld [_ _]]].
      apply basic_world_formula_models_iff in Hworld
        as [HlcD [HdomD _]].
      intros v Hv.
      destruct v as [k|a].
      + exfalso. exact (HlcD (LVBound k) Hv).
      + unfold lvars_of_atoms. apply elem_of_map.
        exists a. split; [reflexivity|].
        apply HdomD. apply lvars_fv_elem. exact Hv.
    - unfold lvars_of_atoms. intros HzD.
      apply elem_of_map in HzD as [a [Ha HaD]].
      inversion Ha. subst a.
      subst z. better_set_solver.
    - set_solver.
    - exact HFz.
    - exact Hext.
    - exact Htotal.
  }
  assert (Hres_open :
      mz ⊨ formula_open 0 z
        (expr_result_formula_at
          (lvars_shift_from 0 (dom Σrel))
          (tm_shift 0 (tret v1)) (LVBound 0))).
  {
    subst Σrel.
    eapply result_first_outer_result_ret_value_at_open.
    - apply atom_store_to_lvar_store_closed.
    - eapply context_typing_wf_ret_lc_value. exact Hwf_fun.
    - subst z. better_set_solver.
    - exact HzΣrel.
    - exact Hres_at.
  }
  pose proof (res_models_impl_elim _ _ _ Houter_open Hres_open)
    as Hvalue.
  assert (Hres_expr :
      mz ⊨ expr_result_formula (tret v1) (LVFree z)).
  {
    unfold expr_result_formula.
    eapply expr_result_formula_at_of_result_extends_on_coarsen
      with (X := world_dom (m : WorldT)) (F := Fz) (m := m).
    - rewrite (tm_lvars_lc_eq_atoms (tret v1)).
      + unfold lvars_of_atoms. intros v Hv.
        apply elem_of_map in Hv as [a [Ha _]]. inversion Ha. exact I.
      + constructor. eapply context_typing_wf_ret_lc_value.
        exact Hwf_fun.
    - reflexivity.
    - rewrite (tm_lvars_lc_eq_atoms (tret v1)).
      + unfold lvars_of_atoms. intros v Hv.
        apply elem_of_map in Hv as [a [Ha HaIn]].
        inversion Ha. subst v.
        apply elem_of_map. exists a. split; [reflexivity|].
        apply Hfv_v1_m. exact HaIn.
      + constructor. eapply context_typing_wf_ret_lc_value.
        exact Hwf_fun.
    - unfold lvars_of_atoms. intros HzD.
      apply elem_of_map in HzD as [a [Ha HaD]].
      inversion Ha. subst a.
      subst z. better_set_solver.
    - set_solver.
    - exact HFz.
    - exact Hext.
    - exact Htotal.
  }
  exists z, mz.
  split; [exact Hzfresh|].
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
    (lty_env_open_one 0 x
      (typed_lty_env_bind
        (atom_env_to_lty_env (erase_ctx Γ1)) (erase_ty τx)))
    (relevant_lvars (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 x
      (typed_lty_env_bind
        (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))) (erase_ty τx)))
    (relevant_lvars (cty_open 0 x τ)
      (tapp_tm (tret v1) (vfvar x))).
Proof.
  intros Hwf_fun Hwf_app.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ1 v1 (CTWand τx τ) Hwf_fun) as Hlc_v1.
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
  m ⊨ formula_open 0 x
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ1))
          (CTWand τx τ) (tret v1))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))) ->
  m ⊨ formula_open 0 x
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2)))
          (CTArrow τx τ) (tret v1))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))).
Proof.
  intros Hwf_fun Hwf_app Hfresh Hsrc.
  set (Δ1 := atom_env_to_lty_env (erase_ctx Γ1)) in *.
  set (Δstar := atom_env_to_lty_env (erase_ctx (CtxStar Γ1 Γ2))) in *.
  pose proof (context_typing_wf_ret_lc_value
    Σ Γ1 v1 (CTWand τx τ) Hwf_fun) as Hlc_v1.
  assert (Htmfresh :
      x ∉ fv_tm (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))).
  {
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value]. better_set_solver.
  }
  assert (HΣfresh_src :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δ1 (CTWand τx τ) (tret v1))
          (erase_ty τx)))).
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
  assert (HΣfresh_tgt :
      x ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Δstar (CTArrow τx τ) (tret v1))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    assert (Hxτx : x ∉ fv_cty τx) by better_set_solver.
    assert (Hxτ : x ∉ fv_cty τ) by better_set_solver.
    assert (Hxv1 : x ∉ fv_tm (tret v1)).
    { cbn [fv_tm fv_value]. better_set_solver. }
    exact (relevant_env_arrow_fresh_free
      Δstar τx τ (tret v1) x Hxτx Hxτ Hxv1 Hbad).
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δ1 (CTWand τx τ) (tret v1))
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0))) in Hsrc
    by (exact HΣfresh_src || exact Htmfresh || better_set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc in Hsrc
    by (constructor; exact Hlc_v1).
  rewrite (formula_open_ty_denote_gas_singleton 0 x
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env Δstar (CTArrow τx τ) (tret v1))
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 (tret v1)) (vbvar 0)))
    by (exact HΣfresh_tgt || exact Htmfresh || better_set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc
    by (constructor; exact Hlc_v1).
  assert (Hmid1 :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 x (typed_lty_env_bind Δ1 (erase_ty τx)))
        (cty_open 0 x τ)
        (tapp_tm (tret v1) (vfvar x))).
  {
    eapply ty_equiv_wand_result_src_mid; eauto.
    better_set_solver.
  }
  assert (Hmidstar :
      m ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 x (typed_lty_env_bind Δstar (erase_ty τx)))
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
  eapply ty_equiv_arrow_result_tgt_goal; eauto.
  better_set_solver.
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
  (* Result-first Wand denotation first opens a fresh slot for the function
     value produced by [ret v1], then opens the disjoint argument resource
     through [FBWand].  The old proof started directly from the [FBWand]
     body, so it must be refactored around the outer result graph. *)
Admitted.
