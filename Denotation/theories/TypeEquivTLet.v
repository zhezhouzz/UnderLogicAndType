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
  TypeEquivBody.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
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
    destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
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

(** Result alias is intentionally delegated to the TLet transport layer in the
    nondeterministic-ready semantics.  The proof route is to instantiate the
    let body with [ret #0], so the explicit result graph for [e] supplies the
    same result world as [ret x].  The remaining hard work is exactly the
    result-first Arrow/Wand TLet transport above. *)
Lemma tlet_result_alias_denotation_at
    gas (Σ : lty_env) τ e x D (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula_at D e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
Admitted.

Lemma tlet_result_alias_denotation
    gas (Σ : lty_env) τ e x (m : WfWorldT) :
  lty_env_closed Σ ->
  Σ !! LVFree x = Some (erase_ty τ) ->
  m ⊨ expr_result_formula e (LVFree x) ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar x)).
Proof.
  intros Hclosed Hlookup Hres Hden.
  unfold expr_result_formula in Hres.
  eapply tlet_result_alias_denotation_at; eauto.
Qed.

End TypeDenote.
