(** * Denotation.TypeEquivFiber

    The fiber-equality term transport theorem for type denotation.

    This file is intentionally kept as a small interface while the new
    nondeterministic result-graph semantics settles.  The previous proof
    attempt decomposed Over/Under/Sum/Arrow/Wand into several body lemmas whose
    statements mentioned the old [expr_result_formula] and [relevant_env]
    shapes.  Those old helper proofs are no longer on the compile path; use
    git history for the detailed script when reproving this theorem. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import TypeEquivCore TypeEquivTerm.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Lemma relevant_env_dom_project_context
    (Σ : lty_env) τsmall τbig e :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  context_ty_lvars τbig ⊆ dom (relevant_env Σ τbig e) ->
  context_ty_lvars τsmall ⊆ dom (relevant_env Σ τsmall e).
Proof.
  intros Hsmall Hbig v Hv.
  pose proof (Hbig v (Hsmall v Hv)) as Hbigdom.
  pose proof (relevant_env_dom_subset_direct Σ τbig e v Hbigdom)
    as HΣv.
  apply elem_of_dom in HΣv as [T HΣv].
  apply elem_of_dom. exists T.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  apply storeA_restrict_lookup_some_2; [exact HΣv|].
  set_solver.
Qed.

Lemma relevant_env_agree_on_tm_lvars
    (Σ : lty_env) τ1 τ2 e :
  storeA_restrict (relevant_env Σ τ1 e) (tm_lvars e) =
  storeA_restrict (relevant_env Σ τ2 e) (tm_lvars e).
Proof.
  unfold relevant_env, lty_env_restrict_lvars, relevant_lvars.
  rewrite !storeA_restrict_twice_subset by set_solver.
  reflexivity.
Qed.

Lemma ty_denote_gas_zero_project_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  erase_ty τsmall = erase_ty τbig ->
  context_ty_shape_ok τsmall ->
  m ⊨ ty_denote_gas 0 Σ τbig e ->
  m ⊨ ty_denote_gas 0 Σ τsmall e.
Proof.
  intros Hlv Herase Hshape Hzero.
  apply ty_denote_gas_zero_of_guard.
  pose proof (ty_denote_gas_guard_of_zero Σ τbig e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard |- *.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf_big [Hworld [Hbasic Htotal]]].
  pose proof (relevant_env_dom_mono_context Σ τsmall τbig e Hlv)
    as Hdom_mono.
  split.
  - apply context_ty_wf_formula_models_iff.
    apply context_ty_wf_formula_models_iff in Hwf_big
      as [HlcΣ [HscopeΣ Hwf_big]].
    split.
    + intros v Hv. apply HlcΣ. exact (Hdom_mono v Hv).
    + split.
      * intros x Hx. apply HscopeΣ.
        apply lvars_fv_elem in Hx.
        apply lvars_fv_elem. exact (Hdom_mono (LVFree x) Hx).
      * destruct Hwf_big as [Hlv_big _].
        split; [|exact Hshape].
        eapply relevant_env_dom_project_context; eauto.
  - split.
    + eapply basic_world_relevant_mono_context; eauto.
    + split; [|exact Htotal].
      apply expr_basic_typing_formula_models_iff.
      apply expr_basic_typing_formula_models_iff in Hbasic
        as [HlcΣ [HscopeΣ Hty]].
      split.
      * intros v Hv. apply HlcΣ. exact (Hdom_mono v Hv).
      * split.
        -- intros x Hx. apply HscopeΣ.
           apply lvars_fv_elem in Hx.
           apply lvars_fv_elem. exact (Hdom_mono (LVFree x) Hx).
        -- rewrite Herase.
           eapply basic_tm_has_ltype_env_agree_lc; [exact Hty| |].
           ++ eapply basic_tm_has_ltype_lc; [exact HlcΣ|exact Hty].
           ++ apply relevant_env_agree_on_tm_lvars.
Qed.

Lemma ty_denote_gas_zero_inter_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (ty_denote_gas_zero_project_context
    Σ τ1 (CTInter τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply ty_denote_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma ty_denote_gas_zero_inter_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTInter τ1 τ2)).
  {
    apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (ty_denote_gas_zero_project_context
    Σ τ2 (CTInter τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma ty_denote_gas_zero_union_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (ty_denote_gas_zero_project_context
    Σ τ1 (CTUnion τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply ty_denote_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma ty_denote_gas_zero_union_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTUnion τ1 τ2)).
  {
    apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (ty_denote_gas_zero_project_context
    Σ τ2 (CTUnion τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma ty_denote_gas_scope_from_zero_any
    gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  formula_scoped_in_world m (ty_denote_gas gas Σ τ e).
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  unfold formula_scoped_in_world.
  eapply ty_denote_gas_scope_of_guard.
  - reflexivity.
  - exact Hguard.
Qed.

Lemma ty_denote_gas_zero_lc_relevant_env
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  lc_lvars (dom (relevant_env Σ τ e)).
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld _]].
  apply basic_world_formula_models_iff in Hworld as [Hlc _].
  exact Hlc.
Qed.

Lemma ty_denote_gas_zero_relevant_env_world
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  lvars_fv (dom (relevant_env Σ τ e)) ⊆ world_dom (m : WorldT).
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld _]].
  apply basic_world_formula_models_iff in Hworld as [_ [Hscope _]].
  exact Hscope.
Qed.

Lemma ty_denote_gas_zero_context_lvars_dom
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  context_ty_lvars τ ⊆ dom (relevant_env Σ τ e).
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf _].
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [Hlv _]]].
  exact Hlv.
Qed.

Lemma ty_denote_gas_zero_tm_lvars_dom
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  tm_lvars e ⊆ dom (relevant_env Σ τ e).
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e m Hzero) as Hguard.
  unfold ty_guard_formula in Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [_ [Hbasic _]]].
  apply expr_basic_typing_formula_models_iff in Hbasic
    as [HlcΣ [_ Hty]].
  rewrite (tm_lvars_lc_eq_atoms e).
  - eapply basic_tm_has_ltype_lvars; eauto.
  - eapply basic_tm_has_ltype_lc; eauto.
Qed.

Lemma ty_denote_gas_zero_relevant_env_dom_eq
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  dom (relevant_env Σ τ e) = context_ty_lvars τ ∪ tm_lvars e.
Proof.
  intros Hzero.
  apply set_eq. intros v. split.
  - intros Hv.
    unfold relevant_env, lty_env_restrict_lvars in Hv.
    rewrite storeA_restrict_dom in Hv.
    apply elem_of_intersection in Hv as [_ Hrel].
    unfold relevant_lvars in Hrel. exact Hrel.
  - intros Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + eapply ty_denote_gas_zero_context_lvars_dom; [exact Hzero|exact Hv].
    + eapply ty_denote_gas_zero_tm_lvars_dom; [exact Hzero|exact Hv].
Qed.

Lemma ty_denote_gas_zero_relevant_lvars_world
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  lvars_fv (context_ty_lvars τ ∪ tm_lvars e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hzero a Ha.
  apply (ty_denote_gas_zero_relevant_env_world Σ τ e m Hzero).
  apply lvars_fv_elem.
  rewrite lvars_fv_union in Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - eapply ty_denote_gas_zero_context_lvars_dom; [exact Hzero|].
    apply lvars_fv_elem. exact Ha.
  - eapply ty_denote_gas_zero_tm_lvars_dom; [exact Hzero|].
    apply lvars_fv_elem. exact Ha.
Qed.

Lemma ty_denote_gas_zero_lc_relevant_lvars
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  lc_lvars (context_ty_lvars τ ∪ tm_lvars e).
Proof.
  intros Hzero v Hv.
  eapply ty_denote_gas_zero_lc_relevant_env; [exact Hzero|].
  apply elem_of_union in Hv as [Hv|Hv].
  - eapply ty_denote_gas_zero_context_lvars_dom; [exact Hzero|exact Hv].
  - eapply ty_denote_gas_zero_tm_lvars_dom; [exact Hzero|exact Hv].
Qed.

Lemma ty_denote_gas_zero_total_atom_world
    Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  expr_total_on_atom_world e m.
Proof.
  intros Hzero.
  pose proof (ty_denote_gas_total_guard_of_zero Σ τ e m Hzero)
    as Htotal.
  apply expr_total_formula_to_atom_world. exact Htotal.
Qed.

Lemma ty_denote_gas_zero_sum_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (ty_denote_gas_zero_project_context
    Σ τ1 (CTSum τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply ty_denote_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma ty_denote_gas_zero_sum_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTSum τ1 τ2)).
  {
    apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (ty_denote_gas_zero_project_context
    Σ τ2 (CTSum τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.


End TypeDenote.
