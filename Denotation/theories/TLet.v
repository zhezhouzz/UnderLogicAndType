(** * Denotation.TLet

    TLet introduction via term-result equivalence. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition
  ContextTypeDenotationSaturateCore ContextTypeDenotationSaturateMain.

Section TLetDenotation.

Lemma tlet_intro_denotation
    gas (Σ : lty_env) τ e1 e2 x Fx m mx :
  x ∉ fv_tm e2 ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_lvar_gas 0 Σ τ (e2 ^^ x) ->
  mx ⊨ denot_ty_lvar_gas 0 Σ τ (tlete e1 e2) ->
  mx ⊨ denot_ty_lvar_gas gas Σ τ (e2 ^^ x) ->
  mx ⊨ denot_ty_lvar_gas gas Σ τ (tlete e1 e2).
Proof.
  intros Hx_e2 HFx Hext Hzero_body Hzero_tlet Hbody.
  pose proof (denot_ty_lvar_gas_guard_of_zero
    Σ τ (tlete e1 e2) mx Hzero_tlet) as Hguard_tlet.
  pose proof Hguard_tlet as Hguard_tlet_parts.
  repeat rewrite res_models_and_iff in Hguard_tlet_parts.
  destruct Hguard_tlet_parts as [_ [_ [Hbasic_tlet Htotal_tlet]]].
  apply expr_basic_typing_formula_models_iff in Hbasic_tlet
    as [HlcΣ [_ Hty_tlet]].
  pose proof (basic_tm_has_ltype_lc _ _ _ HlcΣ Hty_tlet) as Hlc_tlet.
  pose proof (denot_ty_lvar_guard_wfworld_closed_on_term
    Σ τ (tlete e1 e2) mx Hguard_tlet) as Hclosed_tlet.
  eapply denot_ty_lvar_gas_tm_result_equiv.
  - split.
    + eapply tm_result_equiv_on_tlete_body_extension; eauto.
    + split; [exact Hzero_body|exact Hzero_tlet].
  - exact Hbody.
Qed.

End TLetDenotation.
