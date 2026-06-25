(** * Denotation.TypeEquivTLet

    TLet-specific type-denotation transport.

    This file intentionally proves/hosts the [tlete] transport separately from
    the general term-transport lemmas.  In particular, Arrow and Wand cases
    should use the gas IH under the freshly opened argument world, not a
    generic application congruence theorem: after application, equivalent
    function-valued terms need not remain equivalent in the nondeterministic
    setting. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberTransport
  TypeEquivFiberBase
  TypeEquivFiberBody
  TypeEquivBody
  TypeEquivArrow
  TypeEquivArrowResultFirst
  TypeEquivWandResultFirst
  ResultFirstOpen
  DenotationSetMapFacts.

Section TypeDenote.

Local Lemma tlet_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_guard_formula Σ τ e ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  eapply basic_world_formula_wfworld_closed_on_atoms;
    [eapply basic_tm_has_ltype_lvars; exact Hty|exact Hworld].
Qed.

Local Lemma ty_denote_gas_zero_fv_tm_world
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  fv_tm e ⊆ world_dom (m : WorldT).
Proof.
  intros Hzero a Ha.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty) as Hlvars.
  apply basic_world_formula_models_iff in Hworld as [_ [Hdom _]].
  apply Hdom.
  apply lvars_fv_elem.
  apply Hlvars.
  unfold lvars_of_atoms.
  apply elem_of_map. exists a. split; [reflexivity|exact Ha].
Qed.

Local Lemma typed_fiber_equiv_tlet_body_extension
    (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  typed_fiber_equiv_on Σ τ mx (e2 ^^ x) (tlete e1 e2).
Proof.
  intros Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet.
  apply typed_fiber_equiv_intro.
  - eapply (tm_fiber_equiv_tlete_body_extension
      m mx (lvars_fv (context_ty_lvars τ)) e1 e2 x Fx).
    + exact Hxe2.
    + intros Hbad. apply Hxτ.
      rewrite context_ty_lvars_fv in Hbad. exact Hbad.
    + pose proof (ty_denote_gas_guard_of_zero
        Σ τ (tlete e1 e2) mx Hzero_tlet) as Hguard_tlet.
      unfold ty_guard_formula in Hguard_tlet.
      repeat rewrite res_models_and_iff in Hguard_tlet.
      destruct Hguard_tlet as [_ [_ [Hbasic_tlet _]]].
      apply expr_basic_typing_formula_models_iff in Hbasic_tlet
        as [HlcΣ [_ Hty_tlet]].
      eapply basic_tm_has_ltype_lc; [exact HlcΣ|exact Hty_tlet].
    + eapply tlet_guard_wfworld_closed_on_term.
      eapply ty_denote_gas_guard_of_zero. exact Hzero_tlet.
    + eapply ty_denote_gas_zero_fv_tm_world. exact Hzero_body.
    + pose proof (ty_denote_gas_guard_of_zero
        Σ τ (tlete e1 e2) mx Hzero_tlet) as Hguard_tlet.
      unfold ty_guard_formula in Hguard_tlet.
      repeat rewrite res_models_and_iff in Hguard_tlet.
      destruct Hguard_tlet as [_ [_ [_ Htotal_tlet]]].
      eapply expr_total_formula_to_atom_world. exact Htotal_tlet.
    + exact HFx.
    + exact Hext.
  - exact Hzero_body.
  - exact Hzero_tlet.
Qed.

Local Lemma tlet_arrow_open_arg_env
	  gas (Σ : lty_env) τx τr e_src e_tgt
	  (my : WfWorldT) y :
	  y ∉ fv_cty τx ->
	  lc_context_ty τx ->
	  lty_env_closed (relevant_env Σ (CTArrow τx τr) e_src) ->
	  lty_env_closed (relevant_env Σ (CTArrow τx τr) e_tgt) ->
	  y ∉ lvars_fv
	    (dom (typed_lty_env_bind
	      (relevant_env Σ (CTArrow τx τr) e_src) (erase_ty τx))) ->
	  y ∉ lvars_fv
	    (dom (typed_lty_env_bind
	      (relevant_env Σ (CTArrow τx τr) e_tgt) (erase_ty τx))) ->
	  my ⊨ ty_denote_gas gas
	    (<[LVFree y := erase_ty τx]>
	      (relevant_env Σ (CTArrow τx τr) e_tgt))
	    τx (tret (vfvar y)) ->
	  my ⊨ ty_denote_gas gas
	    (<[LVFree y := erase_ty τx]>
	      (relevant_env Σ (CTArrow τx τr) e_src))
	    τx (tret (vfvar y)).
Proof.
  intros Hyτx Hτx_lc Hsrc_closed Htgt_closed HyΣsrc HyΣtgt Htgt.
  assert (Hyrel_src : LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e_src : lty_env)).
  {
    intros Hbad. apply HyΣsrc. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTArrow τx τr) e_src)) Hsrc_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hyrel_tgt : LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e_tgt : lty_env)).
  {
    intros Hbad. apply HyΣtgt. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTArrow τx τr) e_tgt)) Htgt_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Htgt_raw :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e_tgt)
            (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current
      by (exact Hyrel_tgt || exact Htgt_closed).
    rewrite cty_open_shift_from_lc_fresh
      by (exact Hτx_lc || exact Hyτx).
    exact Htgt.
  }
  assert (Hsrc_raw :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e_src)
            (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
	  set (τa := cty_open 0 y (cty_shift 0 τx)).
	  set (ea := tret (vfvar y)).
    fold τa ea in Htgt_raw |- *.
	  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e_src) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (context_ty_lvars τa ∪ tm_lvars ea)
    ltac:(set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e_src Hyτx)) as Hsrc_mid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e_tgt) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (context_ty_lvars τa ∪ tm_lvars ea)
    ltac:(set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e_tgt Hyτx)) as Htgt_mid.
	  rewrite Hsrc_mid.
	  rewrite Htgt_mid in Htgt_raw.
	  exact Htgt_raw.
  }
  rewrite typed_lty_env_bind_open_current in Hsrc_raw
    by (exact Hyrel_src || exact Hsrc_closed).
  rewrite cty_open_shift_from_lc_fresh in Hsrc_raw
    by (exact Hτx_lc || exact Hyτx).
  exact Hsrc_raw.
Qed.

Local Lemma tlet_wand_open_arg_env
	  gas (Σ : lty_env) τx τr e_src e_tgt
	  (my : WfWorldT) y :
	  y ∉ fv_cty τx ->
	  lc_context_ty τx ->
	  lty_env_closed (relevant_env Σ (CTWand τx τr) e_src) ->
	  lty_env_closed (relevant_env Σ (CTWand τx τr) e_tgt) ->
	  y ∉ lvars_fv
	    (dom (typed_lty_env_bind
	      (relevant_env Σ (CTWand τx τr) e_src) (erase_ty τx))) ->
	  y ∉ lvars_fv
	    (dom (typed_lty_env_bind
	      (relevant_env Σ (CTWand τx τr) e_tgt) (erase_ty τx))) ->
	  my ⊨ ty_denote_gas gas
	    (<[LVFree y := erase_ty τx]>
	      (relevant_env Σ (CTWand τx τr) e_tgt))
	    τx (tret (vfvar y)) ->
	  my ⊨ ty_denote_gas gas
	    (<[LVFree y := erase_ty τx]>
	      (relevant_env Σ (CTWand τx τr) e_src))
	    τx (tret (vfvar y)).
Proof.
  intros Hyτx Hτx_lc Hsrc_closed Htgt_closed HyΣsrc HyΣtgt Htgt.
  assert (Hyrel_src : LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e_src : lty_env)).
  {
    intros Hbad. apply HyΣsrc. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e_src)) Hsrc_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hyrel_tgt : LVFree y ∉ dom (relevant_env Σ (CTWand τx τr) e_tgt : lty_env)).
  {
    intros Hbad. apply HyΣtgt. apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e_tgt)) Htgt_closed).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Htgt_raw :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e_tgt)
            (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current
      by (exact Hyrel_tgt || exact Htgt_closed).
    rewrite cty_open_shift_from_lc_fresh
      by (exact Hτx_lc || exact Hyτx).
    exact Htgt.
  }
  assert (Hsrc_raw :
      my ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e_src)
            (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
    set (τa := cty_open 0 y (cty_shift 0 τx)).
    set (ea := tret (vfvar y)).
    fold τa ea in Htgt_raw |- *.
	  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e_src) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (context_ty_lvars τa ∪ tm_lvars ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e_src Hyτx)) as Hsrc_mid.
  pose proof (ty_denote_gas_env_agree_on gas
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e_tgt) (erase_ty τx)))
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    τa ea (context_ty_lvars τa ∪ tm_lvars ea)
    ltac:(set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      Σ (erase_ty τx) y τx τr e_tgt Hyτx)) as Htgt_mid.
	  rewrite Hsrc_mid.
	  rewrite Htgt_mid in Htgt_raw.
	  exact Htgt_raw.
  }
  rewrite typed_lty_env_bind_open_current in Hsrc_raw
    by (exact Hyrel_src || exact Hsrc_closed).
  rewrite cty_open_shift_from_lc_fresh in Hsrc_raw
    by (exact Hτx_lc || exact Hyτx).
  exact Hsrc_raw.
Qed.

Local Lemma tlet_arrow_value_body_env
    gas (Σ : lty_env) τx τr e_src e_tgt
    (mf : WfWorldT) f :
  lty_env_closed (relevant_env Σ (CTArrow τx τr) e_src) ->
  lty_env_closed (relevant_env Σ (CTArrow τx τr) e_tgt) ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∈ world_dom (mf : WorldT) ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  f ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e_src) (erase_ty τx))) ->
  f ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e_tgt) (erase_ty τx))) ->
  formula_scoped_in_world mf
    (formula_open 0 f
      (arrow_value_denote_gas_with ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e_tgt)
          (erase_ty (CTArrow τx τr)))
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0)))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e_src)
        (erase_ty (CTArrow τx τr)))
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e_tgt)
        (erase_ty (CTArrow τx τr)))
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))).
Proof.
  intros HlcΣ_src HlcΣ_tgt Hlcτx Hlcτr Hf_world Hfτ HfΣsrc HfΣtgt
    Hscope_tgt Hvalue_src.
  cbn [formula_open arrow_value_denote_gas_with] in Hscope_tgt.
  cbn [formula_open arrow_value_denote_gas_with] in Hvalue_src |- *.
  eapply res_models_forall_full_world_map;
    [exact Hscope_tgt| |exact Hvalue_src].
  exists (world_dom (mf : WorldT) ∪ fv_cty τx ∪ fv_cty τr ∪
    lvars_fv (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e_src) (erase_ty τx))) ∪
    lvars_fv (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e_tgt) (erase_ty τx)))).
  intros y Hy my Hdom_y Hrestrict_y Hopened_src.
  cbn [formula_open] in Hopened_src |- *.
  pose proof (formula_scoped_forall_open_res_le mf my y
    _ Hscope_tgt
    ltac:(rewrite <- Hrestrict_y; apply res_restrict_le)
    ltac:(rewrite Hdom_y; clear; set_solver)) as Htarget_impl_scope.
  cbn [formula_open] in Htarget_impl_scope.
  eapply res_models_impl_intro; [exact Htarget_impl_scope|].
  intros Harg_tgt.
  assert (Hyτx : y ∉ fv_cty τx) by (clear -Hy; set_solver).
  assert (Hyτr : y ∉ fv_cty τr) by (clear -Hy; set_solver).
  assert (HyΣsrc : y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e_src) (erase_ty τx))))
    by (clear -Hy; set_solver).
  assert (HyΣtgt : y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTArrow τx τr) e_tgt) (erase_ty τx))))
    by (clear -Hy; set_solver).
  assert (Hfy : f <> y).
  { intros ->. apply Hy. clear -Hf_world. set_solver. }
  assert (Hf_rel_src :
      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e_src : lty_env)).
  {
    intros Hbad. apply HfΣsrc.
    apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTArrow τx τr) e_src)) HlcΣ_src).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hf_rel_tgt :
      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e_tgt : lty_env)).
  {
    intros Hbad. apply HfΣtgt.
    apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTArrow τx τr) e_tgt)) HlcΣ_tgt).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hy_rel_src :
      LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e_src : lty_env)).
  {
    intros Hbad. apply HyΣsrc.
    apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTArrow τx τr) e_src)) HlcΣ_src).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Hy_rel_tgt :
      LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e_tgt : lty_env)).
  {
    intros Hbad. apply HyΣtgt.
    apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTArrow τx τr) e_tgt)) HlcΣ_tgt).
    apply elem_of_union_l. exact Hbad.
  }
	  assert (Harg_tgt_regular :
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]>
	          (relevant_env Σ (CTArrow τx τr) e_tgt))
	        τx (tret (vfvar y))).
	  {
	    eapply arrow_result_first_arg_to_regular_open.
    - exact HlcΣ_tgt.
    - exact Hf_rel_tgt.
    - exact Hy_rel_tgt.
    - exact Hfy.
    - exact Hlcτx.
    - clear -Hfτ. set_solver.
    - exact Hyτx.
	    - exact Harg_tgt.
	  }
	  assert (Harg_src_regular :
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]>
	          (relevant_env Σ (CTArrow τx τr) e_src))
	        τx (tret (vfvar y))).
	  {
	    eapply tlet_arrow_open_arg_env.
	    - exact Hyτx.
	    - exact Hlcτx.
	    - exact HlcΣ_src.
	    - exact HlcΣ_tgt.
	    - exact HyΣsrc.
	    - exact HyΣtgt.
	    - exact Harg_tgt_regular.
	  }
  assert (Harg_src_formula :
      my ⊨ formula_open 0 y
        (formula_open 1 f
          (ty_denote_gas gas
            (typed_lty_env_bind
              (typed_lty_env_bind
                (relevant_env Σ (CTArrow τx τr) e_src)
                (erase_ty (CTArrow τx τr)))
              (erase_ty (cty_shift 0 τx)))
            (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))))).
  {
    eapply arrow_result_first_regular_to_arg_open.
    - exact HlcΣ_src.
    - exact Hf_rel_src.
    - exact Hy_rel_src.
    - exact Hfy.
    - exact Hlcτx.
    - clear -Hfτ. set_solver.
    - exact Hyτx.
    - exact Harg_src_regular.
  }
  change (my ⊨
    FImpl
      (formula_open 0 y
        (formula_open 1 f
          (ty_denote_gas gas
            (typed_lty_env_bind
              (typed_lty_env_bind
                (relevant_env Σ (CTArrow τx τr) e_src)
                (erase_ty (CTArrow τx τr)))
              (erase_ty (cty_shift 0 τx)))
            (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0)))))
      (formula_open 0 y
        (formula_open 1 f
          (ty_denote_gas gas
            (typed_lty_env_bind
              (typed_lty_env_bind
                (relevant_env Σ (CTArrow τx τr) e_src)
                (erase_ty (CTArrow τx τr)))
              (erase_ty (cty_shift 0 τx)))
            (cty_shift 1 τr)
            (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0)))))) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Harg_src_formula)
    as Hres_src_inner.
  assert (Hres_src_regular :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree f := erase_ty (CTArrow τx τr)]>
            (relevant_env Σ (CTArrow τx τr) e_src)))
        (cty_open 0 y τr)
        (tapp_tm (tret (vfvar f)) (vfvar y))).
  {
    eapply arrow_result_first_result_to_regular_open.
    - exact HlcΣ_src.
    - exact Hf_rel_src.
    - exact Hy_rel_src.
    - exact Hfy.
    - exact Hlcτr.
    - exact Hfτ.
    - clear -Hyτx Hyτr. set_solver.
    - exact Hres_src_inner.
  }
  assert (Hres_tgt_regular :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree f := erase_ty (CTArrow τx τr)]>
            (relevant_env Σ (CTArrow τx τr) e_tgt)))
        (cty_open 0 y τr)
        (tapp_tm (tret (vfvar f)) (vfvar y))).
  {
    eapply arrow_result_first_result_env_agree.
    - exact Hlcτr.
    - apply lc_tapp_tm; constructor; constructor.
    - exact Hfy.
    - exact Hfτ.
    - clear -Hyτx Hyτr. set_solver.
    - exact Hres_src_regular.
  }
  eapply arrow_result_first_regular_to_result_open.
  - exact HlcΣ_tgt.
  - exact Hf_rel_tgt.
  - exact Hy_rel_tgt.
  - exact Hfy.
  - exact Hlcτr.
  - exact Hfτ.
  - clear -Hyτx Hyτr. set_solver.
  - exact Hres_tgt_regular.
Qed.

Local Lemma tlet_arrow_result_first_body_transport
    gas (Σ : lty_env) τx τr e_src e_tgt (mx : WfWorldT) :
  mx ⊨ ty_denote_gas 0 Σ (CTArrow τx τr) e_src ->
  mx ⊨ ty_denote_gas 0 Σ (CTArrow τx τr) e_tgt ->
  tm_result_refines_projected_on mx
    (context_ty_lvars (CTArrow τx τr)) e_tgt e_src ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e_src)))
          (tm_shift 0 e_src) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e_src)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e_tgt)))
          (tm_shift 0 e_tgt) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e_tgt)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
Proof.
  intros Hzero_src Hzero_tgt Hproj Hsrc.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e_src mx Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e_tgt mx Hzero_tgt) as Hguard_tgt.
  cbn [ty_guard_formula] in Hguard_src, Hguard_tgt.
  repeat rewrite res_models_and_iff in Hguard_src, Hguard_tgt.
  destruct Hguard_src as [Hwf_src [Hworld_src [Hbasic_src _]]].
  destruct Hguard_tgt as [_ [Hworld_tgt [Hbasic_tgt _]]].
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_arrow_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTArrow τx τr) e_src)) _
    HlcΣ_wf_src Hbasic_arrow_src) as Hlc_arrow.
  cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
  destruct Hlc_arrow as [Hlcτx Hlcτr].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  apply expr_basic_typing_formula_models_iff in Hbasic_src
    as [HlcΣ_basic_src [_ Hty_src]].
  apply expr_basic_typing_formula_models_iff in Hbasic_tgt
    as [HlcΣ_basic_tgt [_ Hty_tgt]].
  pose proof (basic_tm_has_ltype_lc _ e_src
    (erase_ty (CTArrow τx τr)) HlcΣ_basic_src Hty_src) as Hlc_src_tm.
  pose proof (basic_tm_has_ltype_lc _ e_tgt
    (erase_ty (CTArrow τx τr)) HlcΣ_basic_tgt Hty_tgt) as Hlc_tgt_tm.
  pose proof (ty_denote_gas_scope_from_zero_any
    (S gas) Σ (CTArrow τx τr) e_tgt mx Hzero_tgt)
    as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (mx : WorldT) ∪
    fv_tm e_src ∪ fv_tm e_tgt ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e_src)) ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e_tgt)) ∪
    lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪
    fv_cty τx ∪ fv_cty τr).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (mx : WorldT) ∪ fv_tm e_tgt ∪ fv_tm e_src ∪
        lvars_fv (context_ty_lvars (CTArrow τx τr))).
  { clear -Hf. set_solver. }
  assert (Hf_src : f ∉ Lsrc) by (clear -Hf; set_solver).
  assert (Hfτ : f ∉ fv_cty τx ∪ fv_cty τr) by (clear -Hf; set_solver).
  assert (HfΣsrc :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e_src) (erase_ty τx)))).
  { clear -Hf. rewrite typed_lty_env_bind_lvars_fv_dom. set_solver. }
  assert (HfΣtgt :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e_tgt) (erase_ty τx)))).
  { clear -Hf. rewrite typed_lty_env_bind_lvars_fv_dom. set_solver. }
  assert (Hf_world : f ∈ world_dom (mf : WorldT)).
  {
    rewrite Hdom.
    apply elem_of_union_r.
    apply elem_of_singleton.
    reflexivity.
  }
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTArrow τx τr) e_tgt)))
              (tm_shift 0 e_tgt) (LVBound 0))
            (arrow_value_denote_gas_with ty_denote_gas gas
              (typed_lty_env_bind
                (relevant_env Σ (CTArrow τx τr) e_tgt)
                (erase_ty (CTArrow τx τr)))
              (cty_shift 0 τx) (cty_shift 1 τr)
              (tret (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. clear. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (first
      [ exact Hlc_tgt_tm
      | apply lvars_shift_from_lc; exact HlcΣ_tgt
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hf; set_solver ]).
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTArrow τx τr) e_tgt)) HlcΣ_tgt)
    in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTArrow τx τr) e_tgt mx Hzero_tgt) in Hres_tgt.
  destruct (Hproj f mf Hf_proj Hdom Hrestrict Hres_tgt)
    as [mf_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev f Hf_src mf_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (first
      [ exact Hlc_src_tm
      | apply lvars_shift_from_lc; exact HlcΣ_src
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hf; set_solver ]).
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTArrow τx τr) e_src)) HlcΣ_src)
    in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTArrow τx τr) e_src mx Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hvalue_tgt_src :
      mf_src ⊨ formula_open 0 f
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e_tgt)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
  {
    eapply tlet_arrow_value_body_env.
    - exact HlcΣ_src.
    - exact HlcΣ_tgt.
    - exact Hlcτx.
    - exact Hlcτr.
    - rewrite Hdom_src.
      apply elem_of_union_r.
      apply elem_of_singleton.
      reflexivity.
    - exact Hfτ.
    - exact HfΣsrc.
    - exact HfΣtgt.
    - eapply formula_scoped_open_arrow_value_body_obs.
      pose proof (ty_denote_gas_zero_type_fv_world
        Σ (CTArrow τx τr) e_src mx Hzero_src) as Hτworld.
      rewrite Hdom_src.
      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      + apply elem_of_union_l. exact (Hτworld a Ha).
      + apply elem_of_union_r. exact Ha.
    - exact Hvalue_src.
  }
  eapply res_models_projection; [|exact Hvalue_tgt_src].
  eapply res_restrict_eq_subset; [|exact Hproj_obs].
  etransitivity; [apply formula_open_fv_subset|].
  unfold formula_fv, formula_lvars, arrow_value_denote_gas_with.
  cbn [formula_lvars_at].
  rewrite lvars_fv_union.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e_tgt)
        (erase_ty (CTArrow τx τr)))
      (erase_ty (cty_shift 0 τx)))
    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg_fv.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e_tgt)
        (erase_ty (CTArrow τx τr)))
      (erase_ty (cty_shift 0 τx)))
    (cty_shift 1 τr)
    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))) as Hres_fv.
  apply lvars_fv_mono in Harg_fv.
  apply lvars_fv_mono in Hres_fv.
  rewrite !lvars_fv_union in Harg_fv, Hres_fv.
  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg_fv, Hres_fv.
  rewrite !cty_shift_fv in Harg_fv, Hres_fv.
  rewrite fv_tapp_tm, tm_shift_fv in Hres_fv.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at]
    in Harg_fv, Hres_fv |- *.
  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [[Ha_arg | Ha_res] | Ha_f].
  - specialize (Harg_fv a Ha_arg). rewrite cty_shift_fv in Harg_fv.
    clear -Harg_fv. set_solver.
  - specialize (Hres_fv a Ha_res). try rewrite cty_shift_fv in Hres_fv.
    clear -Hres_fv. set_solver.
  - clear -Ha_f. set_solver.
Qed.

Local Lemma tlet_wand_value_body_env
    gas (Σ : lty_env) τx τr e_src e_tgt
    (mf : WfWorldT) f :
  lty_env_closed (relevant_env Σ (CTWand τx τr) e_src) ->
  lty_env_closed (relevant_env Σ (CTWand τx τr) e_tgt) ->
  lc_context_ty τx ->
  cty_lc_at 1 τr ->
  f ∈ world_dom (mf : WorldT) ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  f ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e_src) (erase_ty τx))) ->
  f ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e_tgt) (erase_ty τx))) ->
  formula_scoped_in_world mf
    (formula_open 0 f
      (wand_value_denote_gas_with ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e_tgt)
          (erase_ty (CTWand τx τr)))
        (cty_shift 0 τx) (cty_shift 1 τr)
        (tret (vbvar 0)))) ->
  mf ⊨ formula_open 0 f
    (wand_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e_src)
        (erase_ty (CTWand τx τr)))
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))) ->
  mf ⊨ formula_open 0 f
    (wand_value_denote_gas_with ty_denote_gas gas
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e_tgt)
        (erase_ty (CTWand τx τr)))
      (cty_shift 0 τx) (cty_shift 1 τr)
      (tret (vbvar 0))).
Proof.
  intros HlcΣ_src HlcΣ_tgt Hlcτx Hlcτr Hf_world Hfτ HfΣsrc HfΣtgt
    Hscope_tgt Hvalue_src.
  cbn [formula_open wand_value_denote_gas_with] in Hscope_tgt.
  cbn [formula_open wand_value_denote_gas_with] in Hvalue_src |- *.
  eapply res_models_fbwand_intro; [exact Hscope_tgt|].
  destruct (res_models_fbwand_rev _ _ _ _ Hvalue_src) as [Lwand Hwand_src].
  exists (Lwand ∪ world_dom (mf : WorldT) ∪
    fv_cty τx ∪ fv_cty τr ∪
    lvars_fv (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e_src) (erase_ty τx))) ∪
    lvars_fv (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e_tgt) (erase_ty τx)))).
  intros η n Hc Hbind Hηfresh Hdom_prod Harg_tgt.
  destruct (open_env_binds_one_inv η Hbind) as [a ->].
  rewrite formula_open_env_singleton in Harg_tgt |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
  rewrite open_env_atoms_empty in Hdom_prod.
  assert (Haτx : a ∉ fv_cty τx) by (clear -Hηfresh; set_solver).
  assert (Haτr : a ∉ fv_cty τr) by (clear -Hηfresh; set_solver).
  assert (HaΣsrc : a ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e_src) (erase_ty τx))))
    by (clear -Hηfresh; set_solver).
  assert (HaΣtgt : a ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTWand τx τr) e_tgt) (erase_ty τx))))
    by (clear -Hηfresh; set_solver).
  assert (Hfa : f <> a).
  {
    intros ->.
    rewrite elem_of_disjoint in Hηfresh.
    assert (Ha : a ∈ ({[a]} ∪ ∅ : aset)).
    { apply elem_of_union_l. rewrite elem_of_singleton. reflexivity. }
    specialize (Hηfresh a Ha).
    apply Hηfresh. clear -Hf_world. set_solver.
  }
  assert (Hf_rel_tgt :
      LVFree f ∉ dom (relevant_env Σ (CTWand τx τr) e_tgt : lty_env)).
  {
    intros Hbad. apply HfΣtgt.
    apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e_tgt)) HlcΣ_tgt).
    apply elem_of_union_l. exact Hbad.
  }
  assert (Ha_rel_tgt :
      LVFree a ∉ dom (relevant_env Σ (CTWand τx τr) e_tgt : lty_env)).
  {
    intros Hbad. apply HaΣtgt.
    apply lvars_fv_elem.
    rewrite typed_lty_env_bind_dom.
    rewrite (lvars_shift_from_lc_eq 0
      (dom (relevant_env Σ (CTWand τx τr) e_tgt)) HlcΣ_tgt).
    apply elem_of_union_l. exact Hbad.
  }
	  assert (Harg_tgt_regular :
	      n ⊨ ty_denote_gas gas
	        (<[LVFree a := erase_ty τx]>
	          (relevant_env Σ (CTWand τx τr) e_tgt))
	        τx (tret (vfvar a))).
  {
    eapply wand_result_first_arg_to_regular_open.
    - exact HlcΣ_tgt.
    - exact Hf_rel_tgt.
    - exact Ha_rel_tgt.
    - exact Hfa.
    - exact Hlcτx.
    - clear -Hfτ. set_solver.
	    - exact Haτx.
	    - exact Harg_tgt.
	  }
	  assert (Hf_rel_src :
	      LVFree f ∉ dom (relevant_env Σ (CTWand τx τr) e_src : lty_env)).
	  {
	    intros Hbad. apply HfΣsrc.
	    apply lvars_fv_elem.
	    rewrite typed_lty_env_bind_dom.
	    rewrite (lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTWand τx τr) e_src)) HlcΣ_src).
	    apply elem_of_union_l. exact Hbad.
	  }
	  assert (Ha_rel_src :
	      LVFree a ∉ dom (relevant_env Σ (CTWand τx τr) e_src : lty_env)).
	  {
	    intros Hbad. apply HaΣsrc.
	    apply lvars_fv_elem.
	    rewrite typed_lty_env_bind_dom.
	    rewrite (lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTWand τx τr) e_src)) HlcΣ_src).
	    apply elem_of_union_l. exact Hbad.
	  }
	  assert (Harg_src_regular :
	      n ⊨ ty_denote_gas gas
	        (<[LVFree a := erase_ty τx]>
	          (relevant_env Σ (CTWand τx τr) e_src))
	        τx (tret (vfvar a))).
	  {
	    eapply tlet_wand_open_arg_env.
	    - exact Haτx.
	    - exact Hlcτx.
	    - exact HlcΣ_src.
	    - exact HlcΣ_tgt.
	    - exact HaΣsrc.
	    - exact HaΣtgt.
	    - exact Harg_tgt_regular.
	  }
	  assert (Harg_src_formula :
      n ⊨ formula_open 0 a
        (formula_open 1 f
          (ty_denote_gas gas
            (typed_lty_env_bind
              (typed_lty_env_bind
                (relevant_env Σ (CTWand τx τr) e_src)
                (erase_ty (CTWand τx τr)))
              (erase_ty (cty_shift 0 τx)))
            (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))))).
  {
    eapply wand_result_first_regular_to_arg_open.
    - exact HlcΣ_src.
    - exact Hf_rel_src.
    - exact Ha_rel_src.
    - exact Hfa.
    - exact Hlcτx.
    - clear -Hfτ. set_solver.
    - exact Haτx.
    - exact Harg_src_regular.
  }
  pose proof (Hwand_src _ n Hc Hbind
    ltac:(rewrite open_env_atoms_insert by apply lookup_empty;
          rewrite open_env_atoms_empty;
          clear -Hηfresh; set_solver)
    Hdom_prod Harg_src_formula) as Hres_src_inner.
  assert (Hres_src_regular :
      res_product n mf Hc ⊨ ty_denote_gas gas
        (<[LVFree a := erase_ty τx]>
          (<[LVFree f := erase_ty (CTWand τx τr)]>
            (relevant_env Σ (CTWand τx τr) e_src)))
        (cty_open 0 a τr)
        (tapp_tm (tret (vfvar f)) (vfvar a))).
  {
    eapply wand_result_first_result_to_regular_open.
    - exact HlcΣ_src.
    - exact Hf_rel_src.
    - exact Ha_rel_src.
    - exact Hfa.
    - exact Hlcτr.
    - exact Hfτ.
    - clear -Haτx Haτr. set_solver.
    - exact Hres_src_inner.
  }
  assert (Hres_tgt_regular :
      res_product n mf Hc ⊨ ty_denote_gas gas
        (<[LVFree a := erase_ty τx]>
          (<[LVFree f := erase_ty (CTWand τx τr)]>
            (relevant_env Σ (CTWand τx τr) e_tgt)))
        (cty_open 0 a τr)
        (tapp_tm (tret (vfvar f)) (vfvar a))).
  {
    eapply wand_result_first_result_env_agree.
    - exact Hlcτr.
    - apply lc_tapp_tm; constructor; constructor.
    - exact Hfa.
    - exact Hfτ.
    - clear -Haτx Haτr. set_solver.
    - exact Hres_src_regular.
  }
  eapply wand_result_first_regular_to_result_open.
  - exact HlcΣ_tgt.
  - exact Hf_rel_tgt.
  - exact Ha_rel_tgt.
  - exact Hfa.
  - exact Hlcτr.
  - exact Hfτ.
  - clear -Haτx Haτr. set_solver.
  - exact Hres_tgt_regular.
Qed.

Local Lemma tlet_wand_result_first_body_transport
    gas (Σ : lty_env) τx τr e_src e_tgt (mx : WfWorldT) :
  mx ⊨ ty_denote_gas 0 Σ (CTWand τx τr) e_src ->
  mx ⊨ ty_denote_gas 0 Σ (CTWand τx τr) e_tgt ->
  tm_result_refines_projected_on mx
    (context_ty_lvars (CTWand τx τr)) e_tgt e_src ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) e_src)))
          (tm_shift 0 e_src) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e_src)
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) e_tgt)))
          (tm_shift 0 e_tgt) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e_tgt)
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
Proof.
  intros Hzero_src Hzero_tgt Hproj Hsrc.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e_src mx Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTWand τx τr) e_tgt mx Hzero_tgt) as Hguard_tgt.
  cbn [ty_guard_formula] in Hguard_src, Hguard_tgt.
  repeat rewrite res_models_and_iff in Hguard_src, Hguard_tgt.
  destruct Hguard_src as [Hwf_src [Hworld_src [Hbasic_src _]]].
  destruct Hguard_tgt as [_ [Hworld_tgt [Hbasic_tgt _]]].
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_wand_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTWand τx τr) e_src)) _
    HlcΣ_wf_src Hbasic_wand_src) as Hlc_wand.
  cbn [lc_context_ty cty_lc_at] in Hlc_wand.
  destruct Hlc_wand as [Hlcτx Hlcτr].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  apply expr_basic_typing_formula_models_iff in Hbasic_src
    as [HlcΣ_basic_src [_ Hty_src]].
  apply expr_basic_typing_formula_models_iff in Hbasic_tgt
    as [HlcΣ_basic_tgt [_ Hty_tgt]].
  pose proof (basic_tm_has_ltype_lc _ e_src
    (erase_ty (CTWand τx τr)) HlcΣ_basic_src Hty_src) as Hlc_src_tm.
  pose proof (basic_tm_has_ltype_lc _ e_tgt
    (erase_ty (CTWand τx τr)) HlcΣ_basic_tgt Hty_tgt) as Hlc_tgt_tm.
  pose proof (ty_denote_gas_scope_from_zero_any
    (S gas) Σ (CTWand τx τr) e_tgt mx Hzero_tgt)
    as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (mx : WorldT) ∪
    fv_tm e_src ∪ fv_tm e_tgt ∪
    lvars_fv (dom (relevant_env Σ (CTWand τx τr) e_src)) ∪
    lvars_fv (dom (relevant_env Σ (CTWand τx τr) e_tgt)) ∪
    lvars_fv (context_ty_lvars (CTWand τx τr)) ∪
    fv_cty τx ∪ fv_cty τr).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (mx : WorldT) ∪ fv_tm e_tgt ∪ fv_tm e_src ∪
        lvars_fv (context_ty_lvars (CTWand τx τr))).
  { clear -Hf. set_solver. }
  assert (Hf_src : f ∉ Lsrc) by (clear -Hf; set_solver).
  assert (Hfτ : f ∉ fv_cty τx ∪ fv_cty τr) by (clear -Hf; set_solver).
  assert (HfΣsrc :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e_src) (erase_ty τx)))).
  { clear -Hf. rewrite typed_lty_env_bind_lvars_fv_dom. set_solver. }
  assert (HfΣtgt :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTWand τx τr) e_tgt) (erase_ty τx)))).
  { clear -Hf. rewrite typed_lty_env_bind_lvars_fv_dom. set_solver. }
  assert (Hf_world : f ∈ world_dom (mf : WorldT)).
  {
    rewrite Hdom.
    apply elem_of_union_r.
    apply elem_of_singleton.
    reflexivity.
  }
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTWand τx τr) e_tgt)))
              (tm_shift 0 e_tgt) (LVBound 0))
            (wand_value_denote_gas_with ty_denote_gas gas
              (typed_lty_env_bind
                (relevant_env Σ (CTWand τx τr) e_tgt)
                (erase_ty (CTWand τx τr)))
              (cty_shift 0 τx) (cty_shift 1 τr)
              (tret (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. clear. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (first
      [ exact Hlc_tgt_tm
      | apply lvars_shift_from_lc; exact HlcΣ_tgt
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hf; set_solver ]).
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTWand τx τr) e_tgt)) HlcΣ_tgt)
    in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTWand τx τr) e_tgt mx Hzero_tgt) in Hres_tgt.
  destruct (Hproj f mf Hf_proj Hdom Hrestrict Hres_tgt)
    as [mf_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev f Hf_src mf_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (first
      [ exact Hlc_src_tm
      | apply lvars_shift_from_lc; exact HlcΣ_src
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hf; set_solver ]).
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTWand τx τr) e_src)) HlcΣ_src)
    in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTWand τx τr) e_src mx Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hvalue_tgt_src :
      mf_src ⊨ formula_open 0 f
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e_tgt)
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
  {
    eapply tlet_wand_value_body_env.
    - exact HlcΣ_src.
    - exact HlcΣ_tgt.
    - exact Hlcτx.
    - exact Hlcτr.
    - rewrite Hdom_src.
      apply elem_of_union_r.
      apply elem_of_singleton.
      reflexivity.
    - exact Hfτ.
    - exact HfΣsrc.
    - exact HfΣtgt.
    - eapply formula_scoped_open_wand_value_body_obs.
      pose proof (ty_denote_gas_zero_type_fv_world
        Σ (CTWand τx τr) e_src mx Hzero_src) as Hτworld.
      rewrite Hdom_src.
      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      + apply elem_of_union_l. exact (Hτworld a Ha).
      + apply elem_of_union_r. exact Ha.
    - exact Hvalue_src.
  }
  eapply res_models_projection; [|exact Hvalue_tgt_src].
  eapply res_restrict_eq_subset; [|exact Hproj_obs].
  etransitivity; [apply formula_open_fv_subset|].
  unfold formula_fv, formula_lvars, wand_value_denote_gas_with.
  cbn [formula_lvars_at].
  rewrite lvars_fv_union.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e_tgt)
        (erase_ty (CTWand τx τr)))
      (erase_ty (cty_shift 0 τx)))
    (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg_fv.
  pose proof (ty_denote_gas_lvars_subset gas 1
    (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e_tgt)
        (erase_ty (CTWand τx τr)))
      (erase_ty (cty_shift 0 τx)))
    (cty_shift 1 τr)
    (tapp_tm (tm_shift 0 (tret (vbvar 0))) (vbvar 0))) as Hres_fv.
  apply lvars_fv_mono in Harg_fv.
  apply lvars_fv_mono in Hres_fv.
  rewrite !lvars_fv_union in Harg_fv, Hres_fv.
  rewrite !tm_lvars_at_fv, !context_ty_lvars_fv_at in Harg_fv, Hres_fv.
  rewrite !cty_shift_fv in Harg_fv, Hres_fv.
  rewrite fv_tapp_tm, tm_shift_fv in Hres_fv.
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at]
    in Harg_fv, Hres_fv |- *.
  rewrite lvars_fv_union, !context_ty_lvars_fv_at.
  intros a Ha.
  repeat rewrite elem_of_union in Ha.
  repeat rewrite elem_of_union.
  destruct Ha as [[Ha_arg | Ha_res] | Ha_f].
  - specialize (Harg_fv a Ha_arg). rewrite cty_shift_fv in Harg_fv.
    clear -Harg_fv. set_solver.
  - specialize (Hres_fv a Ha_res). try rewrite cty_shift_fv in Hres_fv.
    clear -Hres_fv. set_solver.
  - clear -Ha_f. set_solver.
Qed.

Local Lemma tlet_intro_denotation_arrow_body
    gas
    (IH : forall (Σ : lty_env) (τ : context_ty)
             (e1 e2 : tm) (x : atom) (Fx : FiberExtensionT)
             (m mx : WfWorldT),
      x ∉ fv_tm e2 ->
      x ∉ fv_cty τ ->
      expr_result_extension_witness e1 x Fx ->
      res_extend_by m Fx mx ->
      mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
      mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
      mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) ->
      mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2))
    (Σ : lty_env) τx τr e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty (CTArrow τx τr) ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ (CTArrow τx τr) (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ (CTArrow τx τr) (tlete e1 e2) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) (e2 ^^ x))))
          (tm_shift 0 (e2 ^^ x)) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) (e2 ^^ x))
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) (tlete e1 e2))))
          (tm_shift 0 (tlete e1 e2)) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) (tlete e1 e2))
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
Proof.
  intros Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Hbody.
  pose proof (typed_fiber_equiv_tlet_body_extension
    Σ (CTArrow τx τr) e1 e2 x Fx m mx
    Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet) as Hequiv.
  pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hequiv)
    as [_ Htlet_to_body].
  eapply tlet_arrow_result_first_body_transport.
  - exact Hzero_body.
  - exact Hzero_tlet.
  - exact Htlet_to_body.
  - exact Hbody.
Qed.

Local Lemma tlet_intro_denotation_arrow_body_reverse
    gas
    (IH : forall (Σ : lty_env) (τ : context_ty)
             (e1 e2 : tm) (x : atom) (Fx : FiberExtensionT)
             (m mx : WfWorldT),
      x ∉ fv_tm e2 ->
      x ∉ fv_cty τ ->
      expr_result_extension_witness e1 x Fx ->
      res_extend_by m Fx mx ->
      mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
      mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
      mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2) ->
      mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x))
    (Σ : lty_env) τx τr e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty (CTArrow τx τr) ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ (CTArrow τx τr) (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ (CTArrow τx τr) (tlete e1 e2) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) (tlete e1 e2))))
          (tm_shift 0 (tlete e1 e2)) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) (tlete e1 e2))
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) (e2 ^^ x))))
          (tm_shift 0 (e2 ^^ x)) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) (e2 ^^ x))
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
Proof.
  intros Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Htlet.
  pose proof (typed_fiber_equiv_tlet_body_extension
    Σ (CTArrow τx τr) e1 e2 x Fx m mx
    Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet) as Hequiv.
  pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hequiv)
    as [Hbody_to_tlet _].
  eapply tlet_arrow_result_first_body_transport.
  - exact Hzero_tlet.
  - exact Hzero_body.
  - exact Hbody_to_tlet.
  - exact Htlet.
Qed.

Local Lemma tlet_intro_denotation_wand_body
    gas
    (IH : forall (Σ : lty_env) (τ : context_ty)
             (e1 e2 : tm) (x : atom) (Fx : FiberExtensionT)
             (m mx : WfWorldT),
      x ∉ fv_tm e2 ->
      x ∉ fv_cty τ ->
      expr_result_extension_witness e1 x Fx ->
      res_extend_by m Fx mx ->
      mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
      mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
      mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) ->
      mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2))
    (Σ : lty_env) τx τr e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty (CTWand τx τr) ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ (CTWand τx τr) (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ (CTWand τx τr) (tlete e1 e2) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) (e2 ^^ x))))
          (tm_shift 0 (e2 ^^ x)) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) (e2 ^^ x))
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) (tlete e1 e2))))
          (tm_shift 0 (tlete e1 e2)) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) (tlete e1 e2))
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
Proof.
  intros Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Hbody.
  pose proof (typed_fiber_equiv_tlet_body_extension
    Σ (CTWand τx τr) e1 e2 x Fx m mx
    Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet) as Hequiv.
  pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hequiv)
    as [_ Htlet_to_body].
  eapply tlet_wand_result_first_body_transport.
  - exact Hzero_body.
  - exact Hzero_tlet.
  - exact Htlet_to_body.
  - exact Hbody.
Qed.

Local Lemma tlet_intro_denotation_wand_body_reverse
    gas
    (IH : forall (Σ : lty_env) (τ : context_ty)
             (e1 e2 : tm) (x : atom) (Fx : FiberExtensionT)
             (m mx : WfWorldT),
      x ∉ fv_tm e2 ->
      x ∉ fv_cty τ ->
      expr_result_extension_witness e1 x Fx ->
      res_extend_by m Fx mx ->
      mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
      mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
      mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2) ->
      mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x))
    (Σ : lty_env) τx τr e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty (CTWand τx τr) ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ (CTWand τx τr) (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ (CTWand τx τr) (tlete e1 e2) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) (tlete e1 e2))))
          (tm_shift 0 (tlete e1 e2)) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) (tlete e1 e2))
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) (e2 ^^ x))))
          (tm_shift 0 (e2 ^^ x)) (LVBound 0))
        (wand_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) (e2 ^^ x))
            (erase_ty (CTWand τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))).
Proof.
  intros Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Htlet.
  pose proof (typed_fiber_equiv_tlet_body_extension
    Σ (CTWand τx τr) e1 e2 x Fx m mx
    Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet) as Hequiv.
  pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hequiv)
    as [Hbody_to_tlet _].
  eapply tlet_wand_result_first_body_transport.
  - exact Hzero_tlet.
  - exact Hzero_body.
  - exact Hbody_to_tlet.
  - exact Htlet.
Qed.

Local Lemma tlet_persist_value_body_env_eq
    gas (Σ : lty_env) τ e_src e_tgt :
  lty_env_closed (relevant_env Σ (CTPersist τ) e_src) ->
  lty_env_closed (relevant_env Σ (CTPersist τ) e_tgt) ->
  lc_context_ty τ ->
  ty_denote_gas gas
    (typed_lty_env_bind (relevant_env Σ (CTPersist τ) e_src)
      (erase_ty (CTPersist τ)))
    (cty_shift 0 τ) (tret (vbvar 0)) =
  ty_denote_gas gas
    (typed_lty_env_bind (relevant_env Σ (CTPersist τ) e_tgt)
      (erase_ty (CTPersist τ)))
    (cty_shift 0 τ) (tret (vbvar 0)).
Proof.
  intros HlcΣsrc HlcΣtgt Hlcτ.
  eapply ty_denote_gas_env_agree_on
    with (X := relevant_lvars (cty_shift 0 τ) (tret (vbvar 0))).
  - reflexivity.
  - unfold relevant_env, relevant_lvars.
    apply map_eq. intros v.
    change ((storeA_restrict
      (typed_lty_env_bind
        (storeA_restrict Σ
          (context_ty_lvars (CTPersist τ) ∪ tm_lvars e_src))
        (erase_ty (CTPersist τ)))
      (context_ty_lvars (cty_shift 0 τ) ∪ tm_lvars (tret (vbvar 0)))) !! v =
    (storeA_restrict
      (typed_lty_env_bind
        (storeA_restrict Σ
          (context_ty_lvars (CTPersist τ) ∪ tm_lvars e_tgt))
        (erase_ty (CTPersist τ)))
      (context_ty_lvars (cty_shift 0 τ) ∪ tm_lvars (tret (vbvar 0)))) !! v).
    rewrite (storeA_restrict_lookup
      (typed_lty_env_bind
        (storeA_restrict Σ
          (context_ty_lvars (CTPersist τ) ∪ tm_lvars e_src))
        (erase_ty (CTPersist τ)))
      (context_ty_lvars (cty_shift 0 τ) ∪ tm_lvars (tret (vbvar 0))) v).
    rewrite (storeA_restrict_lookup
      (typed_lty_env_bind
        (storeA_restrict Σ
          (context_ty_lvars (CTPersist τ) ∪ tm_lvars e_tgt))
        (erase_ty (CTPersist τ)))
      (context_ty_lvars (cty_shift 0 τ) ∪ tm_lvars (tret (vbvar 0))) v).
    destruct (decide (v ∈ context_ty_lvars (cty_shift 0 τ) ∪
      tm_lvars (tret (vbvar 0)))) as [Hv|Hv]; cbn.
    + destruct v as [n|a].
      * destruct n as [|n].
        -- unfold typed_lty_env_bind, lvar_store_bind.
           rewrite !lookup_insert. repeat (destruct decide; [|congruence]).
           reflexivity.
        -- clear -HlcΣsrc HlcΣtgt.
           (* The outer restrict has kept this branch only if the lookup is
              demanded, but a closed environment shifted under the binder has
              no positive bound lookup. *)
           unfold typed_lty_env_bind, lvar_store_bind in *.
           rewrite !lookup_insert_ne by discriminate.
           rewrite !lvar_store_shift_closed by assumption.
           rewrite !lty_env_closed_lookup_bound_none by assumption.
           reflexivity.
      * rewrite !typed_lty_env_bind_lookup_free.
        change (relevant_env Σ (CTPersist τ) e_src !! LVFree a =
          relevant_env Σ (CTPersist τ) e_tgt !! LVFree a).
        change ((storeA_restrict Σ (context_ty_lvars τ ∪ tm_lvars e_src)
          : gmap logic_var ty) !! LVFree a =
          (storeA_restrict Σ (context_ty_lvars τ ∪ tm_lvars e_tgt)
          : gmap logic_var ty) !! LVFree a).
        assert (Haτ : LVFree a ∈ context_ty_lvars τ).
        {
          cbn [tm_lvars tm_lvars_at value_lvars_at bvar_lvars_at] in Hv.
          apply (proj1 (lvars_fv_elem (context_ty_lvars τ) a)).
          change (a ∈ fv_cty τ).
          rewrite <- (cty_shift_fv 0 τ).
          apply (proj2 (lvars_fv_elem
            (context_ty_lvars (cty_shift 0 τ)) a)).
          set_solver.
        }
        destruct (Σ !! LVFree a) eqn:HaΣ.
        -- transitivity (Some t).
           ++ apply (storeA_restrict_lookup_some_2 _ _ _ _ HaΣ). set_solver.
           ++ symmetry. apply (storeA_restrict_lookup_some_2 _ _ _ _ HaΣ). set_solver.
        -- transitivity (@None ty).
           ++ apply storeA_restrict_lookup_none_l. exact HaΣ.
           ++ symmetry. apply storeA_restrict_lookup_none_l. exact HaΣ.
    + reflexivity.
Qed.

Lemma tlet_persist_body_transport
    gas (Σ : lty_env) τ e_src e_tgt (mx : WfWorldT) :
  mx ⊨ ty_denote_gas 0 Σ (CTPersist τ) e_src ->
  mx ⊨ ty_denote_gas 0 Σ (CTPersist τ) e_tgt ->
  tm_result_refines_projected_on mx
    (context_ty_lvars (CTPersist τ)) e_tgt e_src ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTPersist τ) e_src)))
          (tm_shift 0 e_src) (LVBound 0))
        (FPersist
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTPersist τ) e_src)
              (erase_ty (CTPersist τ)))
            (cty_shift 0 τ) (tret (vbvar 0))))) ->
  mx ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTPersist τ) e_tgt)))
          (tm_shift 0 e_tgt) (LVBound 0))
        (FPersist
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTPersist τ) e_tgt)
              (erase_ty (CTPersist τ)))
            (cty_shift 0 τ) (tret (vbvar 0))))).
Proof.
  intros Hzero_src Hzero_tgt Hproj Hsrc.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTPersist τ) e_src mx Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTPersist τ) e_tgt mx Hzero_tgt) as Hguard_tgt.
  cbn [ty_guard_formula] in Hguard_src, Hguard_tgt.
  repeat rewrite res_models_and_iff in Hguard_src, Hguard_tgt.
  destruct Hguard_src as [Hwf_src [Hworld_src [Hbasic_src _]]].
  destruct Hguard_tgt as [_ [Hworld_tgt [Hbasic_tgt _]]].
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_persist_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTPersist τ) e_src)) _
    HlcΣ_wf_src Hbasic_persist_src) as Hlc_persist.
  cbn [lc_context_ty cty_lc_at] in Hlc_persist.
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  apply expr_basic_typing_formula_models_iff in Hbasic_src
    as [HlcΣ_basic_src [_ Hty_src]].
  apply expr_basic_typing_formula_models_iff in Hbasic_tgt
    as [HlcΣ_basic_tgt [_ Hty_tgt]].
  pose proof (basic_tm_has_ltype_lc _ e_src
    (erase_ty (CTPersist τ)) HlcΣ_basic_src Hty_src) as Hlc_src_tm.
  pose proof (basic_tm_has_ltype_lc _ e_tgt
    (erase_ty (CTPersist τ)) HlcΣ_basic_tgt Hty_tgt) as Hlc_tgt_tm.
  pose proof (ty_denote_gas_scope_from_zero_any
    (S gas) Σ (CTPersist τ) e_tgt mx Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (mx : WorldT) ∪
    fv_tm e_src ∪ fv_tm e_tgt ∪
    lvars_fv (dom (relevant_env Σ (CTPersist τ) e_src)) ∪
    lvars_fv (dom (relevant_env Σ (CTPersist τ) e_tgt)) ∪
    lvars_fv (context_ty_lvars (CTPersist τ)) ∪ fv_cty τ).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (mx : WorldT) ∪ fv_tm e_tgt ∪ fv_tm e_src ∪
        lvars_fv (context_ty_lvars (CTPersist τ))).
  { clear -Hf. set_solver. }
  assert (Hf_src : f ∉ Lsrc) by (clear -Hf; set_solver).
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTPersist τ) e_tgt)))
              (tm_shift 0 e_tgt) (LVBound 0))
            (FPersist
              (ty_denote_gas gas
                (typed_lty_env_bind
                  (relevant_env Σ (CTPersist τ) e_tgt)
                  (erase_ty (CTPersist τ)))
                (cty_shift 0 τ) (tret (vbvar 0))))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. clear. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (first
      [ exact Hlc_tgt_tm
      | apply lvars_shift_from_lc; exact HlcΣ_tgt
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hf; set_solver ]).
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTPersist τ) e_tgt)) HlcΣ_tgt)
    in Hres_tgt.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTPersist τ) e_tgt mx Hzero_tgt) in Hres_tgt.
  destruct (Hproj f mf Hf_proj Hdom Hrestrict Hres_tgt)
    as [mf_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev f Hf_src mf_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (first
      [ exact Hlc_src_tm
      | apply lvars_shift_from_lc; exact HlcΣ_src
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hf; set_solver ]).
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTPersist τ) e_src)) HlcΣ_src)
    in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTPersist τ) e_src mx Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hvalue_tgt_src :
      mf_src ⊨ formula_open 0 f
        (FPersist
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTPersist τ) e_tgt)
              (erase_ty (CTPersist τ)))
            (cty_shift 0 τ) (tret (vbvar 0))))).
  {
    rewrite <- (tlet_persist_value_body_env_eq
      gas Σ τ e_src e_tgt HlcΣ_src HlcΣ_tgt Hlc_persist).
    exact Hvalue_src.
  }
  eapply res_models_projection; [|exact Hvalue_tgt_src].
  eapply res_restrict_eq_subset; [|exact Hproj_obs].
  rewrite <- (formula_fv_open_persist_value_body_obs gas
    (relevant_env Σ (CTPersist τ) e_tgt) τ f).
  reflexivity.
Qed.

Local Lemma tlet_intro_denotation_forward
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2).
Proof.
  revert Σ τ e1 e2 x Fx m mx.
  induction gas as [|gas IH]; intros Σ τ e1 e2 x Fx m mx
    Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Hbody.
  - exact Hzero_tlet.
  - pose proof (typed_fiber_equiv_tlet_body_extension
      Σ τ e1 e2 x Fx m mx Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet)
      as Hfib.
    pose proof (ty_denote_gas_guard_of_zero
      Σ τ (tlete e1 e2) mx Hzero_tlet) as Hguard_tlet.
    pose proof (ty_denote_gas_scope_from_zero_any
      (S gas) Σ τ (tlete e1 e2) mx Hzero_tlet) as Hscope_tlet_full.
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr|τ1];
      cbn [ty_denote_gas] in Hbody |- *;
      rewrite res_models_and_iff in Hbody |- *;
      destruct Hbody as [_ Hbody].
    + split; [exact Hguard_tlet|].
      exact (ty_denote_gas_tm_fiber_equiv_over_body
        gas Σ b φ (e2 ^^ x) (tlete e1 e2) mx Hfib Hbody).
    + split; [exact Hguard_tlet|].
      exact (ty_denote_gas_tm_fiber_equiv_under_body
        gas Σ b φ (e2 ^^ x) (tlete e1 e2) mx Hfib Hbody).
    + split; [exact Hguard_tlet|].
      apply res_models_and_iff in Hbody as [H1 H2].
      apply res_models_and_iff. split.
      * eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_inter_l. exact Hzero_body.
        -- eapply ty_denote_gas_zero_inter_l. exact Hzero_tlet.
      * eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_inter_r. exact Hzero_body.
        -- eapply ty_denote_gas_zero_inter_r. exact Hzero_tlet.
    + split; [exact Hguard_tlet|].
      pose proof (res_models_scoped _ _ Hbody) as Hscope_src.
      apply (res_models_or_iff _ _ _ Hscope_src) in Hbody as [H1|H2].
      * pose proof Hscope_tlet_full as Hscope_tgt.
        cbn [ty_denote_gas] in Hscope_tgt.
        pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hscope_body_tgt.
        apply (res_models_or_iff _ _ _ Hscope_body_tgt).
        left. eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_union_l. exact Hzero_body.
        -- eapply ty_denote_gas_zero_union_l. exact Hzero_tlet.
      * pose proof Hscope_tlet_full as Hscope_tgt.
        cbn [ty_denote_gas] in Hscope_tgt.
        pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hscope_body_tgt.
        apply (res_models_or_iff _ _ _ Hscope_body_tgt).
        right. eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_union_r. exact Hzero_body.
        -- eapply ty_denote_gas_zero_union_r. exact Hzero_tlet.
    + split; [exact Hguard_tlet|].
      exact (ty_denote_gas_tm_fiber_equiv_sum_body
        gas Σ τ1 τ2 (e2 ^^ x) (tlete e1 e2) mx Hfib Hbody).
    + split; [exact Hguard_tlet|].
      exact (tlet_intro_denotation_arrow_body
        gas IH Σ τx τr e1 e2 x Fx m mx
        Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Hbody).
    + split; [exact Hguard_tlet|].
      exact (tlet_intro_denotation_wand_body
        gas IH Σ τx τr e1 e2 x Fx m mx
        Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Hbody).
    + split; [exact Hguard_tlet|].
      pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hfib)
        as [_ Htlet_to_body].
      eapply (tlet_persist_body_transport
        gas Σ τ1 (e2 ^^ x) (tlete e1 e2) mx);
        [exact Hzero_body|exact Hzero_tlet|exact Htlet_to_body|exact Hbody].
Qed.

Local Lemma tlet_intro_denotation_reverse
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x).
Proof.
  revert Σ τ e1 e2 x Fx m mx.
  induction gas as [|gas IH]; intros Σ τ e1 e2 x Fx m mx
    Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Htlet.
  - exact Hzero_body.
  - pose proof (typed_fiber_equiv_tlet_body_extension
      Σ τ e1 e2 x Fx m mx Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet)
      as Hfib.
    pose proof (typed_fiber_equiv_sym _ _ _ _ _ Hfib) as Hfib_sym.
    pose proof (ty_denote_gas_guard_of_zero
      Σ τ (e2 ^^ x) mx Hzero_body) as Hguard_body.
    pose proof (ty_denote_gas_scope_from_zero_any
      (S gas) Σ τ (e2 ^^ x) mx Hzero_body) as Hscope_body_full.
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr|τ1];
      cbn [ty_denote_gas] in Htlet |- *;
      rewrite res_models_and_iff in Htlet |- *;
      destruct Htlet as [_ Htlet].
    + split; [exact Hguard_body|].
      exact (ty_denote_gas_tm_fiber_equiv_over_body
        gas Σ b φ (tlete e1 e2) (e2 ^^ x) mx Hfib_sym Htlet).
    + split; [exact Hguard_body|].
      exact (ty_denote_gas_tm_fiber_equiv_under_body
        gas Σ b φ (tlete e1 e2) (e2 ^^ x) mx Hfib_sym Htlet).
    + split; [exact Hguard_body|].
      apply res_models_and_iff in Htlet as [H1 H2].
      apply res_models_and_iff. split.
      * eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_inter_l. exact Hzero_body.
        -- eapply ty_denote_gas_zero_inter_l. exact Hzero_tlet.
      * eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_inter_r. exact Hzero_body.
        -- eapply ty_denote_gas_zero_inter_r. exact Hzero_tlet.
    + split; [exact Hguard_body|].
      pose proof (res_models_scoped _ _ Htlet) as Hscope_src.
      apply (res_models_or_iff _ _ _ Hscope_src) in Htlet as [H1|H2].
      * pose proof Hscope_body_full as Hscope_tgt.
        cbn [ty_denote_gas] in Hscope_tgt.
        pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hscope_body_tgt.
        apply (res_models_or_iff _ _ _ Hscope_body_tgt).
        left. eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_union_l. exact Hzero_body.
        -- eapply ty_denote_gas_zero_union_l. exact Hzero_tlet.
      * pose proof Hscope_body_full as Hscope_tgt.
        cbn [ty_denote_gas] in Hscope_tgt.
        pose proof (formula_scoped_and_r _ _ _ Hscope_tgt) as Hscope_body_tgt.
        apply (res_models_or_iff _ _ _ Hscope_body_tgt).
        right. eapply IH; eauto.
        -- clear -Hxτ. unfold fv_cty, context_ty_lvars in Hxτ |- *.
           cbn [context_ty_lvars_at] in Hxτ.
           rewrite lvars_fv_union, !context_ty_lvars_fv_at in Hxτ.
           set_solver.
        -- eapply ty_denote_gas_zero_union_r. exact Hzero_body.
        -- eapply ty_denote_gas_zero_union_r. exact Hzero_tlet.
    + split; [exact Hguard_body|].
      exact (ty_denote_gas_tm_fiber_equiv_sum_body
        gas Σ τ1 τ2 (tlete e1 e2) (e2 ^^ x) mx Hfib_sym Htlet).
    + split; [exact Hguard_body|].
      exact (tlet_intro_denotation_arrow_body_reverse
        gas IH Σ τx τr e1 e2 x Fx m mx
        Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Htlet).
    + split; [exact Hguard_body|].
      exact (tlet_intro_denotation_wand_body_reverse
        gas IH Σ τx τr e1 e2 x Fx m mx
        Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet Htlet).
    + split; [exact Hguard_body|].
      pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hfib_sym)
        as [_ Hbody_to_tlet].
      eapply (tlet_persist_body_transport
        gas Σ τ1 (tlete e1 e2) (e2 ^^ x) mx);
        [exact Hzero_tlet|exact Hzero_body|exact Hbody_to_tlet|exact Htlet].
Qed.

Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ ty_denote_gas gas Σ τ (e2 ^^ x) <->
  mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2).
Proof.
  intros Hxe2 Hxτ HFx Hext Hzero_body Hzero_tlet.
  split.
  - eapply tlet_intro_denotation_forward; eauto.
  - intros Htlet.
    eapply tlet_intro_denotation_reverse; eauto.
Qed.

End TypeDenote.
