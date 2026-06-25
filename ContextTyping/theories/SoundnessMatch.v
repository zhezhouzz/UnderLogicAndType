(** * ContextTyping.SoundnessMatch

    Match proof support for the direct Fundamental theorem. *)

From Stdlib Require Import Lia.
From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquiv
  ConstDenoteBase
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase SoundnessLamArrow
  SoundnessLamWand.

Lemma context_typing_wf_match_inv Σ Γ x et ef τ :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  erase_ctx Γ ⊢ᵥ vfvar x ⋮ TBase TBool /\
  erase_ctx Γ ⊢ₑ et ⋮ erase_ty τ /\
  erase_ctx Γ ⊢ₑ ef ⋮ erase_ty τ.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic.
  inversion Hbasic; subst; eauto.
Qed.

Lemma tm_equiv_match_true_var
    Σ Γ x et ef τ (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cbool true))) ->
  tm_equiv_on m (et) (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hlookup σ v Hσ.
  pose proof (context_typing_wf_match_inv Σ Γ x et ef τ Hwf)
    as [_ [Het Hef]].
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic_match.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx) as Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld _]].
  set (X := fv_tm (tmatch (vfvar x) et ef)).
  assert (HclosedX : wfworld_closed_on X m).
  {
    subst X.
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    pose proof (basic_tm_has_ltype_of_atom_env_typing
      (erase_ctx Γ) (tmatch (vfvar x) et ef) (erase_ty τ)
      Hbasic_match) as Hbasic_match_lty.
    exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_match_lty).
  }
  destruct (soundness_match_left_observation_facts x et ef X
    ltac:(subst X; reflexivity)) as [Hfv_et [Hfv_match HxX]].
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (HclosedX σ Hσ). }
  assert (HσX_lookup :
      store_restrict σ X !! x = Some (vconst (cbool true))).
  { apply storeA_restrict_lookup_some_2; [apply Hlookup; exact Hσ|exact HxX]. }
  split.
  - intros Het_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    apply (proj2 (tm_eval_in_store_match_true_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ et v X Hfv_et)).
    exact Het_eval.
  - intros Hmatch_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ et v X Hfv_et)).
    apply (proj1 (tm_eval_in_store_match_true_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    exact Hmatch_eval.
Qed.

Lemma tm_equiv_match_false_var
    Σ Γ x et ef τ (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cbool false))) ->
  tm_equiv_on m (ef) (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hlookup σ v Hσ.
  pose proof (context_typing_wf_match_inv Σ Γ x et ef τ Hwf)
    as [_ [Het Hef]].
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic_match.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx) as Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld _]].
  set (X := fv_tm (tmatch (vfvar x) et ef)).
  assert (HclosedX : wfworld_closed_on X m).
  {
    subst X.
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    pose proof (basic_tm_has_ltype_of_atom_env_typing
      (erase_ctx Γ) (tmatch (vfvar x) et ef) (erase_ty τ)
      Hbasic_match) as Hbasic_match_lty.
    exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_match_lty).
  }
  destruct (soundness_match_right_observation_facts x et ef X
    ltac:(subst X; reflexivity)) as [Hfv_ef [Hfv_match HxX]].
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (HclosedX σ Hσ). }
  assert (HσX_lookup :
      store_restrict σ X !! x = Some (vconst (cbool false))).
  { apply storeA_restrict_lookup_some_2; [apply Hlookup; exact Hσ|exact HxX]. }
  split.
  - intros Hef_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
    apply (proj2 (tm_eval_in_store_match_false_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ ef v X Hfv_ef)).
    exact Hef_eval.
  - intros Hmatch_eval.
    apply (proj1 (tm_eval_in_store_restrict_fv_subset
      σ ef v X Hfv_ef)).
    apply (proj1 (tm_eval_in_store_match_false_fvar
      (store_restrict σ X) x et ef v HσX_closed
      (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup)).
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tmatch (vfvar x) et ef) v X Hfv_match)).
	    exact Hmatch_eval.
Qed.

Lemma tm_total_equiv_match_true_var
    Σ Γ x et ef τ (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cbool true))) ->
  tm_total_equiv_on m et (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hlookup σ Hσ.
  pose proof (context_typing_wf_match_inv Σ Γ x et ef τ Hwf)
    as [_ [Het Hef]].
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic_match.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx) as Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld _]].
  set (X := fv_tm (tmatch (vfvar x) et ef)).
  assert (HclosedX : wfworld_closed_on X m).
  {
    subst X.
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    pose proof (basic_tm_has_ltype_of_atom_env_typing
      (erase_ctx Γ) (tmatch (vfvar x) et ef) (erase_ty τ)
      Hbasic_match) as Hbasic_match_lty.
    exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_match_lty).
  }
  destruct (soundness_match_left_observation_facts x et ef X
    ltac:(subst X; reflexivity)) as [Hfv_et [Hfv_match HxX]].
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (HclosedX σ Hσ). }
  assert (HσX_lookup :
      store_restrict σ X !! x = Some (vconst (cbool true))).
  { apply storeA_restrict_lookup_some_2; [apply Hlookup; exact Hσ|exact HxX]. }
  pose proof (tm_must_terminating_match_true_fvar
    (store_restrict σ X) x et ef HσX_closed
    (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup) as HeqX.
  assert (Hlc_match : lc_tm (tmatch (vfvar x) et ef)).
  { exact (typing_tm_lc _ _ _ Hbasic_match). }
  assert (Het_agree :
      store_restrict σ (fv_tm et) =
      store_restrict (store_restrict σ X) (fv_tm et)).
  { rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_et]. }
  assert (Hmatch_agree :
      store_restrict σ (fv_tm (tmatch (vfvar x) et ef)) =
      store_restrict (store_restrict σ X) (fv_tm (tmatch (vfvar x) et ef))).
  { rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_match]. }
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    et (typing_tm_lc _ _ _ Het) Het_agree) as Het_restrict.
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tmatch (vfvar x) et ef) Hlc_match Hmatch_agree) as Hmatch_restrict.
  split; intros Htotal.
  - apply (proj2 Hmatch_restrict).
    apply (proj2 HeqX).
    apply (proj1 Het_restrict). exact Htotal.
  - apply (proj2 Het_restrict).
    apply (proj1 HeqX).
    apply (proj1 Hmatch_restrict). exact Htotal.
Qed.

Lemma tm_total_equiv_match_false_var
    Σ Γ x et ef τ (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  (forall σ, (m : WorldT) σ -> σ !! x = Some (vconst (cbool false))) ->
  tm_total_equiv_on m ef (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hlookup σ Hσ.
  pose proof (context_typing_wf_match_inv Σ Γ x et ef τ Hwf)
    as [_ [Het Hef]].
  pose proof (context_typing_wf_basic_typing
    Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic_match.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx) as Hstatic.
  unfold ty_static_guard_formula in Hstatic.
  repeat rewrite res_models_and_iff in Hstatic.
  destruct Hstatic as [_ [Hworld _]].
  set (X := fv_tm (tmatch (vfvar x) et ef)).
  assert (HclosedX : wfworld_closed_on X m).
  {
    subst X.
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
    pose proof (basic_tm_has_ltype_of_atom_env_typing
      (erase_ctx Γ) (tmatch (vfvar x) et ef) (erase_ty τ)
      Hbasic_match) as Hbasic_match_lty.
    exact (basic_tm_has_ltype_lvars _ _ _ Hbasic_match_lty).
  }
  destruct (soundness_match_right_observation_facts x et ef X
    ltac:(subst X; reflexivity)) as [Hfv_ef [Hfv_match HxX]].
  assert (HσX_closed : store_closed (store_restrict σ X)).
  { exact (HclosedX σ Hσ). }
  assert (HσX_lookup :
      store_restrict σ X !! x = Some (vconst (cbool false))).
  { apply storeA_restrict_lookup_some_2; [apply Hlookup; exact Hσ|exact HxX]. }
  pose proof (tm_must_terminating_match_false_fvar
    (store_restrict σ X) x et ef HσX_closed
    (typing_tm_lc _ _ _ Het) (typing_tm_lc _ _ _ Hef) HσX_lookup) as HeqX.
  assert (Hlc_match : lc_tm (tmatch (vfvar x) et ef)).
  { exact (typing_tm_lc _ _ _ Hbasic_match). }
  assert (Hef_agree :
      store_restrict σ (fv_tm ef) =
      store_restrict (store_restrict σ X) (fv_tm ef)).
  { rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_ef]. }
  assert (Hmatch_agree :
      store_restrict σ (fv_tm (tmatch (vfvar x) et ef)) =
      store_restrict (store_restrict σ X) (fv_tm (tmatch (vfvar x) et ef))).
  { rewrite storeA_restrict_twice_subset; [reflexivity|exact Hfv_match]. }
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    ef (typing_tm_lc _ _ _ Hef) Hef_agree) as Hef_restrict.
  pose proof (tm_must_terminating_agree_on_fv σ (store_restrict σ X)
    (tmatch (vfvar x) et ef) Hlc_match Hmatch_agree) as Hmatch_restrict.
  split; intros Htotal.
  - apply (proj2 Hmatch_restrict).
    apply (proj2 HeqX).
    apply (proj1 Hef_restrict). exact Htotal.
  - apply (proj2 Hef_restrict).
    apply (proj1 HeqX).
    apply (proj1 Hmatch_restrict). exact Htotal.
Qed.

Lemma match_target_zero_from_branch
    Σ Γ x τ et ef ebranch (m : WfWorldT) :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  fv_tm ebranch ⊆ fv_tm (tmatch (vfvar x) et ef) ->
  tm_equiv_on m ebranch (tmatch (vfvar x) et ef) ->
  tm_total_equiv_on m ebranch (tmatch (vfvar x) et ef) ->
  m ⊨ ty_denote (erase_ctx Γ) τ ebranch ->
  m ⊨ ty_denote (erase_ctx Γ) τ (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hctx Hfv_branch Hequiv Htotal_equiv Hbranch.
  unfold ty_denote in Hbranch |- *.
  eapply ty_denote_gas_tm_equiv.
  - split; [exact Hequiv|split].
    + exact Htotal_equiv.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hbranch.
      * assert (Hstatic :
          m ⊨ ty_static_guard_formula
            (atom_env_to_lty_env (erase_ctx Γ))
            τ (tmatch (vfvar x) et ef)).
        {
          exact (context_typing_wf_denot_static_guard_full
            Σ Γ τ (tmatch (vfvar x) et ef) m Hwf Hctx).
        }
        assert (Htotal_branch : m ⊨ expr_total_formula ebranch).
        {
          pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch) as Hguard.
          repeat rewrite res_models_and_iff in Hguard.
          tauto.
        }
        assert (Hlc_match : lc_tm (tmatch (vfvar x) et ef)).
        {
          pose proof (context_typing_wf_basic_typing
            Σ Γ (tmatch (vfvar x) et ef) τ Hwf) as Hbasic.
          exact (typing_tm_lc _ _ _ Hbasic).
        }
        assert (Hfv_match :
            fv_tm (tmatch (vfvar x) et ef) ⊆ world_dom (m : WorldT)).
        {
          unfold ty_static_guard_formula in Hstatic.
          repeat rewrite res_models_and_iff in Hstatic.
          destruct Hstatic as [_ [Hworld Hbasic]].
          apply expr_basic_typing_formula_models_iff in Hbasic
            as [_ [_ Hbasic_lty]].
          apply basic_world_formula_models_iff in Hworld
            as [_ [Hworld_dom _]].
          pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_lty) as Hlvars.
          intros z Hz.
          apply Hworld_dom.
          apply lvars_fv_elem.
          apply Hlvars.
          unfold lvars_of_atoms. apply elem_of_map.
          exists z. split; [reflexivity|exact Hz].
        }
        apply ty_denote_gas_zero_of_guard.
        eapply ty_guard_relevant_of_static_full_total; [exact Hstatic|].
        eapply tm_equiv_total; eauto.
  - exact Hbranch.
Qed.

Lemma context_typing_wf_match_sum_l
    Σ Γt Γf x τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf)
    (tmatch (vfvar x) et ef) (CTSum τt τf) ->
  context_typing_wf Σ Γt (tmatch (vfvar x) et ef) τt.
Proof.
  intros Hwf.
  destruct Hwf as [Hbasic_sum [Hty_sum Htm]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [Hbasic_t [_ [_ _]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [Hty_t [_ _]].
  cbn [erase_ctx erase_ty] in Htm.
  split.
  - exact Hbasic_t.
  - split; [exact Hty_t|exact Htm].
Qed.

Lemma context_typing_wf_match_sum_r
    Σ Γt Γf x τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf)
    (tmatch (vfvar x) et ef) (CTSum τt τf) ->
  context_typing_wf Σ Γf (tmatch (vfvar x) et ef) τf.
Proof.
  intros Hwf.
  destruct Hwf as [Hbasic_sum [Hty_sum Htm]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [Hbasic_f [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [Hty_f Herase_ty]].
  cbn [erase_ctx erase_ty] in Htm.
  split.
  - exact Hbasic_f.
  - split.
    + replace (dom (erase_ctx Γf)) with (dom (erase_ctx Γt)).
      * exact Hty_f.
      * rewrite Herase_ctx. reflexivity.
    + rewrite <- Herase_ctx.
      rewrite <- Herase_ty.
      exact Htm.
Qed.

Lemma expr_total_formula_sum_intro e
    (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2) :
  m1 ⊨ expr_total_formula e ->
  m2 ⊨ expr_total_formula e ->
  res_sum m1 m2 Hdef ⊨ expr_total_formula e.
Proof.
  intros Htotal1 Htotal2.
  apply expr_total_formula_to_atom_world in Htotal1.
  apply expr_total_formula_to_atom_world in Htotal2.
  apply expr_total_atom_world_to_formula.
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal1 as [Hdom1 Hstores1].
  destruct Htotal2 as [_ Hstores2].
  split.
  - rewrite !res_lift_free_dom in Hdom1 |- *.
    simpl. exact Hdom1.
  - intros τ Hτ.
    unfold res_lift_free in Hτ.
    cbn [worldA_stores] in Hτ.
    destruct Hτ as [σ [Hσsum ->]].
    cbn [res_sum raw_sum worldA_stores] in Hσsum.
    destruct Hσsum as [Hσ1 | Hσ2].
    + apply Hstores1.
      exists σ. split; [exact Hσ1|reflexivity].
    + apply Hstores2.
      exists σ. split; [exact Hσ2|reflexivity].
Qed.

Lemma sum_branch_source_env_agree
    Σ τ1 τ2 e y T :
  lc_context_ty τ1 ->
  lc_context_ty τ2 ->
  lc_tm e ->
  y ∉ fv_cty τ1 ∪ fv_cty τ2 ∪ fv_tm e ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e) T))
    (relevant_lvars τ1 e) =
  lty_env_restrict_lvars Σ (relevant_lvars τ1 e).
Proof.
  intros Hlcτ1 Hlcτ2 He Hy.
  rewrite typed_lty_env_bind_open_current.
  2:{
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    intros HyD. apply elem_of_intersection in HyD as [_ HyD].
    apply Hy.
    apply lvars_fv_elem in HyD.
    rewrite relevant_lvars_fv in HyD.
    replace (fv_cty (CTSum τ1 τ2)) with
      (fv_cty τ1 ∪ fv_cty τ2) in HyD.
    { clear -HyD. set_solver. }
    unfold fv_cty.
    cbn [context_ty_lvars context_ty_lvars_at].
    rewrite lvars_fv_union. reflexivity.
  }
  2:{
    unfold lty_env_closed, relevant_env, lty_env_restrict_lvars.
    intros v Hv.
    rewrite storeA_restrict_dom in Hv.
    apply elem_of_intersection in Hv as [_ Hv].
    eapply (lc_lvars_relevant_lvars (CTSum τ1 τ2) e).
    - exact (conj Hlcτ1 Hlcτ2).
    - exact He.
    - exact Hv.
  }
  unfold relevant_env, lty_env_restrict_lvars.
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars τ1 e)) as [Hv|Hv];
    [|reflexivity].
  assert (Hvy : v <> LVFree y).
  {
    intros ->. apply Hy.
    apply lvars_fv_elem in Hv.
    rewrite relevant_lvars_fv in Hv.
    clear -Hv. set_solver.
  }
  rewrite lookup_insert_ne by congruence.
  rewrite storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars (CTSum τ1 τ2) e)) as [_|Hbad].
  - reflexivity.
  - exfalso. apply Hbad.
    unfold relevant_lvars in *.
    cbn [context_ty_lvars context_ty_lvars_at].
    set_solver.
Qed.

Lemma relevant_env_sum_closed_of_lc Σ τ1 τ2 e :
  lc_context_ty τ1 ->
  lc_context_ty τ2 ->
  lc_tm e ->
  lty_env_closed (relevant_env Σ (CTSum τ1 τ2) e).
Proof.
  intros Hlcτ1 Hlcτ2 He.
  unfold lty_env_closed, relevant_env, lty_env_restrict_lvars.
  intros v Hv.
  rewrite storeA_restrict_dom in Hv.
  apply elem_of_intersection in Hv as [_ Hv].
  eapply (lc_lvars_relevant_lvars (CTSum τ1 τ2) e).
  - exact (conj Hlcτ1 Hlcτ2).
  - exact He.
  - exact Hv.
Qed.

Lemma relevant_env_sum_fresh_of_fv Σ τ1 τ2 e y :
  y ∉ fv_cty τ1 ∪ fv_cty τ2 ∪ fv_tm e ->
  LVFree y ∉ dom (relevant_env Σ (CTSum τ1 τ2) e).
Proof.
  intros Hy HyD.
  unfold relevant_env, lty_env_restrict_lvars in HyD.
  rewrite storeA_restrict_dom in HyD.
  apply elem_of_intersection in HyD as [_ HyD].
  apply Hy.
  apply lvars_fv_elem in HyD.
  rewrite relevant_lvars_fv in HyD.
  replace (fv_cty (CTSum τ1 τ2)) with
    (fv_cty τ1 ∪ fv_cty τ2) in HyD.
  - exact HyD.
  - unfold fv_cty.
    cbn [context_ty_lvars context_ty_lvars_at].
    rewrite lvars_fv_union. reflexivity.
Qed.

Lemma relevant_env_sum_branch_union_fresh
    Σ τ1 τ2 e y :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  LVFree y ∉
    dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e).
Proof.
  intros Hy HyD.
  apply Hy.
  apply elem_of_union_l. apply elem_of_union_l.
  apply elem_of_union_r.
  apply lvars_fv_elem.
  relevant_env_norm_in HyD.
  relevant_env_norm.
  apply elem_of_union in HyD as [HyD|HyD].
  - apply elem_of_intersection in HyD as [Hdom Hrel].
    apply elem_of_intersection; split; [exact Hdom|].
    unfold relevant_lvars in Hrel |- *.
    cbn [context_ty_lvars context_ty_lvars_at] in Hrel |- *.
    clear -Hrel. set_solver.
  - apply elem_of_intersection in HyD as [Hdom Hrel].
    apply elem_of_intersection; split; [exact Hdom|].
    unfold relevant_lvars in Hrel |- *.
    cbn [context_ty_lvars context_ty_lvars_at] in Hrel |- *.
    clear -Hrel. set_solver.
Qed.

Lemma sum_branch_source_env_agree_right
    Σ τ1 τ2 e y T :
  lc_context_ty τ1 ->
  lc_context_ty τ2 ->
  lc_tm e ->
  y ∉ fv_cty τ1 ∪ fv_cty τ2 ∪ fv_tm e ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e) T))
    (relevant_lvars τ2 e) =
  lty_env_restrict_lvars Σ (relevant_lvars τ2 e).
Proof.
  intros Hlcτ1 Hlcτ2 He Hy.
  rewrite typed_lty_env_bind_open_current.
  2:{ apply relevant_env_sum_fresh_of_fv. exact Hy. }
  2:{ apply relevant_env_sum_closed_of_lc; assumption. }
  unfold relevant_env, lty_env_restrict_lvars.
  apply storeA_map_eq. intros v.
  rewrite !storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars τ2 e)) as [Hv|Hv];
    [|reflexivity].
  assert (Hvy : v <> LVFree y).
  {
    intros ->. apply Hy.
    apply lvars_fv_elem in Hv.
    rewrite relevant_lvars_fv in Hv.
    clear -Hv. set_solver.
  }
  rewrite lookup_insert_ne by congruence.
  rewrite storeA_restrict_lookup.
  destruct (decide (v ∈ relevant_lvars (CTSum τ1 τ2) e)) as [_|Hbad].
  - reflexivity.
  - exfalso. apply Hbad.
    unfold relevant_lvars in *.
    cbn [context_ty_lvars context_ty_lvars_at].
    set_solver.
Qed.

Lemma lvars_lc_at_zero_of_lc D :
  lc_lvars D ->
  lvars_lc_at 0 D.
Proof.
  exact (soundness_lam_lvars_lc_at_zero_of_lc D).
Qed.

Lemma lc_lvars_shift_from k D :
  lc_lvars D ->
  lc_lvars (lvars_shift_from k D).
Proof.
  exact (soundness_lam_lc_lvars_shift_from k D).
Qed.

Lemma ty_denote_gas_lc_context_ty
    gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e ->
  lc_context_ty τ.
Proof.
  intros Hden.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hden) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld _]].
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasic]].
  apply basic_world_formula_models_iff in Hworld as [HlcD _].
  eapply basic_context_ty_lvars_lc; eauto.
Qed.

Lemma ty_denote_gas_sum_open_left_branch_from_pulled
    gas Σ τ1 τ2 e (m1 my1 : WfWorldT) y :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  lc_context_ty τ2 ->
  cty_depth τ1 <= gas ->
  res_restrict my1 (world_dom (m1 : WorldT)) = m1 ->
  my1 ⊨ expr_result_formula_at
    (dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e))
    e (LVFree y) ->
  m1 ⊨ ty_denote_gas (S gas) Σ τ1 e ->
  my1 ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
        (erase_ty τ1))
      (cty_shift 0 τ1) (tret (vbvar 0))).
Proof.
  intros Hy Hlcτ2 Hdepth Hrestrict Hres Hbranch.
  rewrite (formula_open_ty_denote_gas_singleton 0 y) by
    (rewrite ?typed_lty_env_bind_lvars_fv_dom, ?lvars_shift_from_fv,
      ?cty_shift_fv; cbn [fv_tm fv_value]; set_solver).
  pose proof (res_models_lift_projection_eq m1 my1
    (ty_denote_gas (S gas) Σ τ1 e) Hrestrict Hbranch) as Hbranch_my.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch_my) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
  assert (Hlcτ1 : lc_context_ty τ1).
  {
    apply basic_world_formula_models_iff in Hworld as [HlcD [_ _]].
    eapply basic_context_ty_lvars_lc; eauto.
  }
  assert (Hlc_e : lc_tm e).
  {
    eapply basic_tm_has_ltype_lc.
    - apply basic_world_formula_models_iff in Hworld as [HlcΣ1 _].
      exact HlcΣ1.
    - apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      exact Hty.
  }
  set (Σy := lty_env_open_one 0 y
    (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
      (erase_ty τ1))).
  set (τy := cty_open 0 y (cty_shift 0 τ1)).
  assert (Hτy : τy = τ1).
  {
    subst τy. apply cty_open_shift_from_lc_fresh; [exact Hlcτ1|].
    clear -Hy. set_solver.
  }
  assert (Hsource : my1 ⊨ ty_denote_gas (cty_depth τ1) Σ τ1 e).
  {
    rewrite <- (ty_denote_gas_saturate (S gas) Σ τ1 e)
      by lia.
    exact Hbranch_my.
  }
  assert (Hsource_y : my1 ⊨ ty_denote_gas (cty_depth τ1) Σy τy e).
  {
    subst τy.
    rewrite Hτy.
    eapply (res_models_ty_denote_gas_env_agree_on
      (cty_depth τ1) Σ Σy τ1 e (relevant_lvars τ1 e) my1).
    - intros v Hv. exact Hv.
    - subst Σy.
      symmetry.
      apply sum_branch_source_env_agree.
      + exact Hlcτ1.
      + exact Hlcτ2.
      + exact Hlc_e.
      + intros Hin. apply Hy.
        apply elem_of_union in Hin as [Hin|He].
        * apply elem_of_union in Hin as [Hτ1|Hτ2].
          -- apply elem_of_union_l. apply elem_of_union_r. exact Hτ1.
          -- apply elem_of_union_r. exact Hτ2.
        * apply elem_of_union_l. apply elem_of_union_l.
          apply elem_of_union_l. exact He.
    - exact Hsource.
  }
  subst τy.
  rewrite Hτy.
  rewrite Hτy in Hsource_y.
  rewrite <- (ty_denote_gas_saturate gas Σy τ1 e)
    in Hsource_y by lia.
	  eapply (ty_denote_gas_result_alias_at gas Σy τ1 e y
	    (dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e)) my1).
	  - subst Σy.
	    rewrite typed_lty_env_bind_open_current.
	    + apply lty_env_closed_insert_free.
	      apply relevant_env_sum_closed_of_lc; assumption.
	    + apply relevant_env_sum_fresh_of_fv.
	      intros Hin. apply Hy.
	      apply elem_of_union in Hin as [Hin|He].
	      * apply elem_of_union in Hin as [Hτ1|Hτ2].
	        -- apply elem_of_union_l. apply elem_of_union_r. exact Hτ1.
	        -- apply elem_of_union_r. exact Hτ2.
	      * apply elem_of_union_l. apply elem_of_union_l.
	        apply elem_of_union_l. exact He.
	    + apply relevant_env_sum_closed_of_lc; assumption.
  - intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + unfold relevant_env, lty_env_restrict_lvars in Hv.
      rewrite storeA_restrict_dom in Hv.
      apply elem_of_intersection in Hv as [_ Hv].
      eapply lc_lvars_relevant_lvars; [exact Hlcτ1|exact Hlc_e|exact Hv].
    + unfold relevant_env, lty_env_restrict_lvars in Hv.
      rewrite storeA_restrict_dom in Hv.
      apply elem_of_intersection in Hv as [_ Hv].
      eapply lc_lvars_relevant_lvars; [exact Hlcτ2|exact Hlc_e|exact Hv].
	  - intros v Hv.
	    apply elem_of_union_l.
	    eapply ty_denote_gas_zero_tm_lvars_dom.
	    + apply ty_denote_gas_zero_of_guard.
	      eapply ty_denote_gas_guard. exact Hsource.
	    + exact Hv.
	  - intros v Hv.
	    apply elem_of_union_l.
	    eapply ty_denote_gas_zero_context_lvars_dom.
	    + apply ty_denote_gas_zero_of_guard.
	      eapply ty_denote_gas_guard. exact Hsource.
	    + exact Hv.
  - intros HyD.
    eapply relevant_env_sum_branch_union_fresh; [exact Hy|].
    exact HyD.
  - intros a Ha.
    pose proof (res_models_scoped _ _ Hres) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_expr_result_formula_at in Hscope.
    apply Hscope.
    apply elem_of_union_l. exact Ha.
	  - subst Σy.
	    rewrite typed_lty_env_bind_open_current.
	    + apply map_lookup_insert.
	    + apply relevant_env_sum_fresh_of_fv.
	      intros Hin. apply Hy.
	      apply elem_of_union in Hin as [Hin|He].
	      * apply elem_of_union in Hin as [Hτ1|Hτ2].
	        -- apply elem_of_union_l. apply elem_of_union_r. exact Hτ1.
	        -- apply elem_of_union_r. exact Hτ2.
	      * apply elem_of_union_l. apply elem_of_union_l.
	        apply elem_of_union_l. exact He.
	    + apply relevant_env_sum_closed_of_lc; assumption.
	  - exact Hres.
  - exact Hsource_y.
Qed.

Lemma ty_denote_gas_sum_open_right_branch_from_pulled
    gas Σ τ1 τ2 e (m2 my2 : WfWorldT) y :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  lc_context_ty τ1 ->
  erase_ty τ1 = erase_ty τ2 ->
  cty_depth τ2 <= gas ->
  res_restrict my2 (world_dom (m2 : WorldT)) = m2 ->
  my2 ⊨ expr_result_formula_at
    (dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e))
    e (LVFree y) ->
  m2 ⊨ ty_denote_gas (S gas) Σ τ2 e ->
  my2 ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
        (erase_ty τ1))
      (cty_shift 0 τ2) (tret (vbvar 0))).
Proof.
  intros Hy Hlcτ1 Herase Hdepth Hrestrict Hres Hbranch.
  rewrite (formula_open_ty_denote_gas_singleton 0 y) by
    (rewrite ?typed_lty_env_bind_lvars_fv_dom, ?lvars_shift_from_fv,
      ?cty_shift_fv; cbn [fv_tm fv_value]; set_solver).
  pose proof (res_models_lift_projection_eq m2 my2
    (ty_denote_gas (S gas) Σ τ2 e) Hrestrict Hbranch) as Hbranch_my.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch_my) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  apply context_ty_wf_formula_models_iff in Hwf as [_ [_ Hbasicτ]].
  assert (Hlcτ2 : lc_context_ty τ2).
  {
    apply basic_world_formula_models_iff in Hworld as [HlcD [_ _]].
    eapply basic_context_ty_lvars_lc; eauto.
  }
  assert (Hlc_e : lc_tm e).
  {
    eapply basic_tm_has_ltype_lc.
    - apply basic_world_formula_models_iff in Hworld as [HlcΣ2 _].
      exact HlcΣ2.
    - apply expr_basic_typing_formula_models_iff in Hbasic as [_ [_ Hty]].
      exact Hty.
  }
  set (Σy := lty_env_open_one 0 y
    (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
      (erase_ty τ1))).
  set (τy := cty_open 0 y (cty_shift 0 τ2)).
  assert (Hτy : τy = τ2).
  {
    subst τy. apply cty_open_shift_from_lc_fresh; [exact Hlcτ2|].
    clear -Hy. set_solver.
  }
  assert (Hsource : my2 ⊨ ty_denote_gas (cty_depth τ2) Σ τ2 e).
  {
    rewrite <- (ty_denote_gas_saturate (S gas) Σ τ2 e)
      by lia.
    exact Hbranch_my.
  }
  assert (Hsource_y : my2 ⊨ ty_denote_gas (cty_depth τ2) Σy τy e).
  {
    subst τy.
    rewrite Hτy.
    eapply (res_models_ty_denote_gas_env_agree_on
      (cty_depth τ2) Σ Σy τ2 e (relevant_lvars τ2 e) my2).
    - intros v Hv. exact Hv.
    - subst Σy. symmetry.
      apply sum_branch_source_env_agree_right.
      + exact Hlcτ1.
      + exact Hlcτ2.
      + exact Hlc_e.
      + intros Hin. apply Hy.
        apply elem_of_union in Hin as [Hin|He].
        * apply elem_of_union in Hin as [Hτ1|Hτ2].
          -- apply elem_of_union_l. apply elem_of_union_r. exact Hτ1.
          -- apply elem_of_union_r. exact Hτ2.
        * apply elem_of_union_l. apply elem_of_union_l.
          apply elem_of_union_l. exact He.
    - exact Hsource.
  }
  subst τy.
  rewrite Hτy.
  rewrite Hτy in Hsource_y.
  rewrite <- (ty_denote_gas_saturate gas Σy τ2 e)
    in Hsource_y by lia.
  eapply (ty_denote_gas_result_alias_at gas Σy τ2 e y
    (dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e)) my2).
  - subst Σy.
    rewrite typed_lty_env_bind_open_current.
    + apply lty_env_closed_insert_free.
      apply relevant_env_sum_closed_of_lc; assumption.
    + apply relevant_env_sum_fresh_of_fv.
      intros Hin. apply Hy.
      apply elem_of_union in Hin as [Hin|He].
      * apply elem_of_union in Hin as [Hτ1|Hτ2].
        -- apply elem_of_union_l. apply elem_of_union_r. exact Hτ1.
        -- apply elem_of_union_r. exact Hτ2.
	      * apply elem_of_union_l. apply elem_of_union_l.
	        apply elem_of_union_l. exact He.
	    + apply relevant_env_sum_closed_of_lc; assumption.
	  - intros v Hv.
	    apply elem_of_union in Hv as [Hv|Hv].
	    + unfold relevant_env, lty_env_restrict_lvars in Hv.
	      rewrite storeA_restrict_dom in Hv.
	      apply elem_of_intersection in Hv as [_ Hv].
	      eapply lc_lvars_relevant_lvars; [exact Hlcτ1|exact Hlc_e|exact Hv].
	    + unfold relevant_env, lty_env_restrict_lvars in Hv.
	      rewrite storeA_restrict_dom in Hv.
	      apply elem_of_intersection in Hv as [_ Hv].
	      eapply lc_lvars_relevant_lvars; [exact Hlcτ2|exact Hlc_e|exact Hv].
	  - intros v Hv.
	    apply elem_of_union_r.
	    eapply ty_denote_gas_zero_tm_lvars_dom.
	    + apply ty_denote_gas_zero_of_guard.
	      eapply ty_denote_gas_guard. exact Hsource.
	    + exact Hv.
	  - intros v Hv.
	    apply elem_of_union_r.
	    eapply ty_denote_gas_zero_context_lvars_dom.
	    + apply ty_denote_gas_zero_of_guard.
	      eapply ty_denote_gas_guard. exact Hsource.
	    + exact Hv.
	  - intros HyD.
	    eapply relevant_env_sum_branch_union_fresh; [exact Hy|].
	    exact HyD.
	  - intros a Ha.
	    pose proof (res_models_scoped _ _ Hres) as Hscope.
	    unfold formula_scoped_in_world in Hscope.
	    rewrite formula_fv_expr_result_formula_at in Hscope.
	    apply Hscope.
	    apply elem_of_union_l. exact Ha.
	  - subst Σy.
	    rewrite typed_lty_env_bind_open_current.
	    + rewrite <- Herase. apply map_lookup_insert.
    + apply relevant_env_sum_fresh_of_fv.
      intros Hin. apply Hy.
      apply elem_of_union in Hin as [Hin|He].
      * apply elem_of_union in Hin as [Hτ1|Hτ2].
        -- apply elem_of_union_l. apply elem_of_union_r. exact Hτ1.
        -- apply elem_of_union_r. exact Hτ2.
      * apply elem_of_union_l. apply elem_of_union_l.
        apply elem_of_union_l. exact He.
    + apply relevant_env_sum_closed_of_lc; assumption.
  - exact Hres.
  - exact Hsource_y.
Qed.

Lemma expr_result_formula_at_pullback_exact_domain
    D e y (my p : WfWorldT) Hsub :
  lc_lvars D ->
  tm_lvars e ⊆ D ->
  LVFree y ∉ D ->
  world_dom (p : WorldT) = lvars_fv D ->
  my ⊨ expr_result_formula_at D e (LVFree y) ->
  res_pullback_subset_projection my p Hsub ⊨
    expr_result_formula_at D e (LVFree y).
Proof.
  intros HlcD HeD HyD Hpdom Hres.
  pose proof Hres as Hscope_my.
  unfold expr_result_formula_at in Hscope_my.
  apply res_models_FFibVars_iff in Hscope_my
    as [Hscope_my _].
  eapply expr_result_formula_at_intro.
  - exact HlcD.
  - exact HeD.
  - exact HyD.
  - exact Hscope_my.
  - intros σ Hσ.
    apply expr_result_formula_at_models_elim with (m := my) (D := D); eauto.
    exact (proj1 Hσ).
  - intros σ v Hσ Heval.
    destruct Hσ as [Hσmy Hσp].
    destruct (expr_result_formula_at_fiber_witness
      D e y my HeD HyD Hres σ v Hσmy Heval)
      as [σv [Hσv_my [HσvD Hσvy]]].
    exists σv. split.
    + split; [exact Hσv_my|].
      change ((p : WorldT) (store_restrict σ (world_dom (p : WorldT)))) in Hσp.
      replace (world_dom (p : WorldT)) with (lvars_fv D) in Hσp
        by (symmetry; exact Hpdom).
      change ((p : WorldT) (store_restrict σv (world_dom (p : WorldT)))).
      replace (world_dom (p : WorldT)) with (lvars_fv D)
        by (symmetry; exact Hpdom).
      rewrite HσvD.
      exact Hσp.
    + split; [exact HσvD|exact Hσvy].
Qed.

Lemma ty_denote_gas_sum_open_result_split_from_pulled_branches
    gas Σ τ1 τ2 e (m1 m2 my1 my2 my : WfWorldT) y
    (Hdef : raw_sum_defined my1 my2) :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  res_sum my1 my2 Hdef ⊑ my ->
  res_restrict my1 (world_dom (m1 : WorldT)) = m1 ->
  res_restrict my2 (world_dom (m2 : WorldT)) = m2 ->
  erase_ty τ1 = erase_ty τ2 ->
  cty_depth τ1 <= gas ->
  cty_depth τ2 <= gas ->
  my1 ⊨ expr_result_formula_at
    (dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e))
    e (LVFree y) ->
  my2 ⊨ expr_result_formula_at
    (dom (relevant_env Σ τ1 e) ∪ dom (relevant_env Σ τ2 e))
    e (LVFree y) ->
  m1 ⊨ ty_denote_gas (S gas) Σ τ1 e ->
  m2 ⊨ ty_denote_gas (S gas) Σ τ2 e ->
  my ⊨ formula_open 0 y
    (FPlus
      (ty_denote_gas gas
        (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0)))
      (ty_denote_gas gas
        (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ2) (tret (vbvar 0)))).
Proof.
  intros Hy Hle Hrestrict1 Hrestrict2 Herase Hdepth1 Hdepth2
    Hres1 Hres2 Hbranch1 Hbranch2.
  rewrite formula_open_plus.
  eapply res_models_plus_intro with (m1 := my1) (m2 := my2) (Hdef := Hdef).
  - exact Hle.
  - eapply ty_denote_gas_sum_open_left_branch_from_pulled.
    + exact Hy.
    + eapply ty_denote_gas_lc_context_ty; exact Hbranch2.
    + exact Hdepth1.
    + exact Hrestrict1.
    + exact Hres1.
    + exact Hbranch1.
  - eapply ty_denote_gas_sum_open_right_branch_from_pulled.
    + exact Hy.
    + eapply ty_denote_gas_lc_context_ty; exact Hbranch1.
    + exact Herase.
    + exact Hdepth2.
    + exact Hrestrict2.
    + exact Hres2.
    + exact Hbranch2.
Qed.

Lemma ty_denote_gas_sum_open_result_split_from_branches
    gas Σ τ1 τ2 e (m1 m2 m my : WfWorldT) y
    (Hdef : raw_sum_defined m1 m2) :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  res_sum m1 m2 Hdef ⊑ m ->
  erase_ty τ1 = erase_ty τ2 ->
  cty_depth τ1 <= gas ->
  cty_depth τ2 <= gas ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTSum τ1 τ2) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  m1 ⊨ ty_denote_gas (S gas) Σ τ1 e ->
  m2 ⊨ ty_denote_gas (S gas) Σ τ2 e ->
  my ⊨ formula_open 0 y
    (FPlus
      (ty_denote_gas gas
        (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0)))
      (ty_denote_gas gas
        (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ2) (tret (vbvar 0)))).
Proof.
  intros Hy Hle Herase Hdepth1 Hdepth2 Hdom Hrestrict Hres Hbranch1 Hbranch2.
  set (Dsum := dom (relevant_env Σ (CTSum τ1 τ2) e)).
  set (D1 := dom (relevant_env Σ τ1 e)).
  set (D2 := dom (relevant_env Σ τ2 e)).
  set (D12 := D1 ∪ D2).
  set (S12 := lvars_fv D12).
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch1) as Hguard1.
  pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1, Hguard2.
  destruct Hguard1 as [Hwf1 [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [Hwf2 [Hworld2 [Hbasic2 _]]].
  apply basic_world_formula_models_iff in Hworld1 as [HlcD1 [HdomD1_m1 _]].
  apply basic_world_formula_models_iff in Hworld2 as [HlcD2 [HdomD2_m2 _]].
  assert (Hlc_e : lc_tm e).
  {
    eapply basic_tm_has_ltype_lc.
    - exact HlcD1.
    - apply expr_basic_typing_formula_models_iff in Hbasic1 as [_ [_ Hty]].
      exact Hty.
  }
  assert (Hres_sum : my ⊨ expr_result_formula_at Dsum e (LVFree y)).
  {
    subst Dsum.
    rewrite formula_open_expr_result_formula_at_shift0 in Hres.
    - rewrite lvars_shift_from_lc_at_id in Hres; [exact Hres|].
      apply lvars_lc_at_zero_of_lc.
      apply relevant_env_sum_closed_of_lc.
      + eapply ty_denote_gas_lc_context_ty; exact Hbranch1.
      + eapply ty_denote_gas_lc_context_ty; exact Hbranch2.
      + exact Hlc_e.
    - apply lc_lvars_shift_from.
      apply relevant_env_sum_closed_of_lc.
      + eapply ty_denote_gas_lc_context_ty; exact Hbranch1.
      + eapply ty_denote_gas_lc_context_ty; exact Hbranch2.
      + exact Hlc_e.
    - clear -Hy. rewrite lvars_shift_from_fv. set_solver.
    - exact Hlc_e.
    - clear -Hy. set_solver.
  }
  assert (HD1_sum : D1 ⊆ Dsum).
  {
    subst D1 Dsum.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite !storeA_restrict_dom.
    intros v Hv. apply elem_of_intersection in Hv as [Hv Hrel].
    apply elem_of_intersection. split; [exact Hv|].
    relevant_lvars_norm. relevant_lvars_norm_in Hrel. better_set_solver.
  }
  assert (HD2_sum : D2 ⊆ Dsum).
  {
    subst D2 Dsum.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite !storeA_restrict_dom.
    intros v Hv. apply elem_of_intersection in Hv as [Hv Hrel].
    apply elem_of_intersection. split; [exact Hv|].
    relevant_lvars_norm. relevant_lvars_norm_in Hrel. better_set_solver.
  }
  assert (HeD1 : tm_lvars e ⊆ D1).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic1 as [_ [_ Hty1]].
    intros v Hv.
    apply (basic_tm_has_ltype_lvars _ _ _ Hty1).
    apply tm_lvars_lc_subset_atoms_fv; [apply tm_lvars_lc; exact Hlc_e|].
    exact Hv.
  }
  assert (HeD2 : tm_lvars e ⊆ D2).
  {
    apply expr_basic_typing_formula_models_iff in Hbasic2 as [_ [_ Hty2]].
    intros v Hv.
    apply (basic_tm_has_ltype_lvars _ _ _ Hty2).
    apply tm_lvars_lc_subset_atoms_fv; [apply tm_lvars_lc; exact Hlc_e|].
    exact Hv.
  }
  assert (HyD1 : LVFree y ∉ D1).
  {
    subst D1. intros Hin. apply Hy.
    assert (HyDsum : y ∈ lvars_fv Dsum).
    { apply lvars_fv_elem. apply HD1_sum. exact Hin. }
    subst Dsum. set_solver.
  }
  assert (HyD2 : LVFree y ∉ D2).
  {
    subst D2. intros Hin. apply Hy.
    assert (HyDsum : y ∈ lvars_fv Dsum).
    { apply lvars_fv_elem. apply HD2_sum. exact Hin. }
    subst Dsum. set_solver.
  }
  assert (HyDsum : LVFree y ∉ Dsum).
  {
    intros Hin. apply Hy.
    apply lvars_fv_elem in Hin.
    subst Dsum. set_solver.
  }
  assert (HD12_sum : D12 ⊆ Dsum).
  {
    subst D12. intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    - apply HD1_sum. exact Hv.
    - apply HD2_sum. exact Hv.
  }
  assert (HeD12 : tm_lvars e ⊆ D12).
  {
    subst D12. intros v Hv. apply elem_of_union_l. apply HeD1. exact Hv.
  }
  assert (HyD12 : LVFree y ∉ D12).
  {
    subst D12. intros Hyin.
    apply elem_of_union in Hyin as [Hyin|Hyin];
      [exact (HyD1 Hyin)|exact (HyD2 Hyin)].
  }
  pose proof (expr_result_formula_at_coarsen_domain
    D12 Dsum e y my HD12_sum HeD12
    HyDsum Hres_sum) as Hres_sum12.
  assert (Hbranch1D : res_restrict m1 S12 ⊨ ty_denote_gas (S gas) Σ τ1 e).
  {
    subst S12.
    assert (Hfv1D :
        formula_fv (ty_denote_gas (S gas) Σ τ1 e) ⊆ lvars_fv D12).
    {
      pose proof (formula_fv_ty_denote_gas_subset_relevant (S gas) Σ τ1 e)
        as Hfv1.
      apply context_ty_wf_formula_models_iff in Hwf1 as [_ [_ Hcty1]].
      destruct Hcty1 as [Hcty1_vars _].
      apply expr_basic_typing_formula_models_iff in Hbasic1 as [_ [_ Hty1]].
      intros a Ha. pose proof (Hfv1 a Ha) as Hrel.
      apply lvars_fv_elem.
      subst D12.
      apply elem_of_union_l.
      apply elem_of_union in Hrel as [He | Hτ].
      - apply HeD1.
        rewrite tm_lvars_lc_eq_atoms by exact Hlc_e.
        apply elem_of_map. exists a. split; [reflexivity|exact He].
      - apply Hcty1_vars.
        apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hτ.
    }
    exact (proj1 (res_models_minimal_on (lvars_fv D12) m1
      (ty_denote_gas (S gas) Σ τ1 e) Hfv1D) Hbranch1).
  }
  assert (Hbranch2D : res_restrict m2 S12 ⊨ ty_denote_gas (S gas) Σ τ2 e).
  {
    subst S12.
    assert (Hfv2D :
        formula_fv (ty_denote_gas (S gas) Σ τ2 e) ⊆ lvars_fv D12).
    {
      pose proof (formula_fv_ty_denote_gas_subset_relevant (S gas) Σ τ2 e)
        as Hfv2.
      apply context_ty_wf_formula_models_iff in Hwf2 as [_ [_ Hcty2]].
      destruct Hcty2 as [Hcty2_vars _].
      apply expr_basic_typing_formula_models_iff in Hbasic2 as [_ [_ Hty2]].
      intros a Ha. pose proof (Hfv2 a Ha) as Hrel.
      apply lvars_fv_elem.
      subst D12.
      apply elem_of_union_r.
      apply elem_of_union in Hrel as [He | Hτ].
      - apply HeD2.
        rewrite tm_lvars_lc_eq_atoms by exact Hlc_e.
        apply elem_of_map. exists a. split; [reflexivity|exact He].
      - apply Hcty2_vars.
        apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hτ.
    }
    exact (proj1 (res_models_minimal_on (lvars_fv D12) m2
      (ty_denote_gas (S gas) Σ τ2 e) Hfv2D) Hbranch2).
  }
  destruct (res_sum_restrict_same_le m m1 m2 S12 Hdef Hle)
    as [HdefD HleD].
  assert (Hsum_myD :
      res_sum (res_restrict m1 S12) (res_restrict m2 S12)
        HdefD ⊑ my).
  {
    transitivity (res_restrict m S12); [exact HleD|].
    rewrite <- Hrestrict.
    rewrite res_restrict_restrict_eq.
    apply res_restrict_le.
  }
  destruct (res_sum_pullback_subset_projection_full my
    (res_restrict m1 S12) (res_restrict m2 S12)
    HdefD Hsum_myD) as [Hsub1 [Hsub2 [Hdef_full Hle_full]]].
  set (my1 := res_pullback_subset_projection my
    (res_restrict m1 S12) Hsub1).
  set (my2 := res_pullback_subset_projection my
    (res_restrict m2 S12) Hsub2).
  assert (HlcD12 : lc_lvars D12).
  {
    subst D12. intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    - exact (HlcD1 v Hv).
    - exact (HlcD2 v Hv).
  }
  assert (Hres1 : my1 ⊨ expr_result_formula_at D12 e (LVFree y)).
  {
    subst my1.
    eapply expr_result_formula_at_pullback_exact_domain.
    - exact HlcD12.
    - exact HeD12.
    - exact HyD12.
    - subst S12.
      change (world_dom (res_restrict m1 (lvars_fv D12) : WorldT) =
        lvars_fv D12).
      rewrite res_restrict_dom.
      apply set_eq. intros a. rewrite elem_of_intersection. split.
      + intros [_ Ha]. exact Ha.
      + intros Ha. split; [|exact Ha].
        subst D12. rewrite lvars_fv_union in Ha.
        apply elem_of_union in Ha as [Ha|Ha].
        * apply HdomD1_m1. exact Ha.
        * change (a ∈ world_dom (m1 : WorldT)).
          change (world_dom (m1 : WorldT) =
            world_dom (m2 : WorldT)) in Hdef.
          rewrite Hdef. apply HdomD2_m2. exact Ha.
    - exact Hres_sum12.
  }
  assert (Hres2 : my2 ⊨ expr_result_formula_at D12 e (LVFree y)).
  {
    subst my2.
    eapply expr_result_formula_at_pullback_exact_domain.
    - exact HlcD12.
    - exact HeD12.
    - exact HyD12.
    - subst S12.
      change (world_dom (res_restrict m2 (lvars_fv D12) : WorldT) =
        lvars_fv D12).
      rewrite res_restrict_dom.
      apply set_eq. intros a. rewrite elem_of_intersection. split.
      + intros [_ Ha]. exact Ha.
      + intros Ha. split; [|exact Ha].
        subst D12. rewrite lvars_fv_union in Ha.
        apply elem_of_union in Ha as [Ha|Ha].
        * change (a ∈ world_dom (m2 : WorldT)).
          change (world_dom (m1 : WorldT) =
            world_dom (m2 : WorldT)) in Hdef.
          rewrite <- Hdef. apply HdomD1_m1. exact Ha.
        * apply HdomD2_m2. exact Ha.
    - exact Hres_sum12.
  }
  eapply ty_denote_gas_sum_open_result_split_from_pulled_branches
    with (m1 := res_restrict m1 S12)
         (m2 := res_restrict m2 S12)
         (my1 := my1) (my2 := my2) (Hdef := Hdef_full); eauto.
  - subst my1. apply res_pullback_subset_projection_restrict.
  - subst my2. apply res_pullback_subset_projection_restrict.
Qed.

Lemma ty_denote_gas_sum_result_body_from_branch_refinement
    gas Σ τ1 τ2 e (m1 m2 m : WfWorldT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m ->
  erase_ty τ1 = erase_ty τ2 ->
  cty_depth τ1 <= gas ->
  cty_depth τ2 <= gas ->
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m1 ⊨ ty_denote_gas (S gas) Σ τ1 e ->
  m2 ⊨ ty_denote_gas (S gas) Σ τ2 e ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTSum τ1 τ2) e)))
          (tm_shift 0 e) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
              (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
              (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))).
Proof.
  intros Hle Herase Hdepth1 Hdepth2 Hzero Hbranch1 Hbranch2.
  pose proof (ty_denote_gas_scope_from_zero_any
    (S gas) Σ (CTSum τ1 τ2) e m Hzero) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_body.
  eapply res_models_forall_rev_intro; [exact Hscope_body|].
  exists
    (world_dom (m : WorldT) ∪ fv_tm e ∪
      lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
      lvars_fv (context_ty_lvars (CTSum τ1 τ2))).
  intros y Hy my Hdom Hrestrict.
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ (CTSum τ1 τ2) e)))
              (tm_shift 0 e) (LVBound 0))
            (FPlus
              (ty_denote_gas gas
                (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
                  (erase_ty τ1))
                (cty_shift 0 τ1) (tret (vbvar 0)))
              (ty_denote_gas gas
                (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
                  (erase_ty τ1))
                (cty_shift 0 τ2) (tret (vbvar 0))))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_body.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres.
  assert (Hfresh_split :
      y ∉ fv_tm e ∪
        lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
        fv_cty τ1 ∪ fv_cty τ2).
  {
    intros Hbad. apply Hy.
    repeat rewrite elem_of_union in Hbad.
    destruct Hbad as [[[He | Hrel] | Hτ1] | Hτ2].
    - apply elem_of_union_l. apply elem_of_union_l.
      apply elem_of_union_r. exact He.
    - apply elem_of_union_l. apply elem_of_union_r. exact Hrel.
    - apply elem_of_union_r.
      apply lvars_fv_elem.
      cbn [context_ty_lvars context_ty_lvars_at].
      apply elem_of_union_l.
      apply lvars_fv_elem. exact Hτ1.
    - apply elem_of_union_r.
      apply lvars_fv_elem.
      cbn [context_ty_lvars context_ty_lvars_at].
      apply elem_of_union_r.
      apply lvars_fv_elem. exact Hτ2.
  }
  apply (ty_denote_gas_sum_open_result_split_from_branches
    gas Σ τ1 τ2 e m1 m2 m my y Hdef Hfresh_split Hle
    Herase Hdepth1 Hdepth2 Hdom Hrestrict Hres Hbranch1 Hbranch2).
Qed.

Lemma ty_denote_gas_sum_intro_from_branch_refinement
    gas Σ τ1 τ2 e (m1 m2 m : WfWorldT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m ->
  erase_ty τ1 = erase_ty τ2 ->
  cty_depth τ1 < gas ->
  cty_depth τ2 < gas ->
  m ⊨ ty_static_guard_formula Σ (CTSum τ1 τ2) e ->
  m ⊨ expr_total_formula e ->
  m1 ⊨ ty_denote_gas gas Σ τ1 e ->
  m2 ⊨ ty_denote_gas gas Σ τ2 e ->
  m ⊨ ty_denote_gas gas Σ (CTSum τ1 τ2) e.
Proof.
  intros Hle Herase Hdepth1 Hdepth2 Hstatic Htotal Hbranch1 Hbranch2.
  destruct gas as [|gas].
  - apply ty_denote_gas_zero_of_guard.
    eapply ty_guard_relevant_of_static_full_total; eauto.
  - assert (Hzero_m : m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e).
    {
      apply ty_denote_gas_zero_of_guard.
      eapply ty_guard_relevant_of_static_full_total; eauto.
    }
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch1) as Hguard1.
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hbranch2) as Hguard2.
    repeat rewrite res_models_and_iff in Hguard1, Hguard2.
    destruct Hguard1 as [_ [_ [_ Htotal1]]].
    destruct Hguard2 as [_ [_ [_ Htotal2]]].
    cbn [ty_denote_gas].
    rewrite res_models_and_iff.
    split.
    + eapply ty_guard_relevant_of_static_full_total; eauto.
    + eapply ty_denote_gas_sum_result_body_from_branch_refinement; eauto; lia.
Qed.

Lemma fundamental_match_both_case Σ Γt Γf x τt τf et ef :
  context_typing_wf Σ (CtxSum Γt Γf)
    (tmatch (vfvar x) et ef) (CTSum τt τf) ->
  (ctx_denote_under Σ Γt ⊫
    ty_denote_under Σ Γt (bool_precise_ty true) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γf ⊫
    ty_denote_under Σ Γf (bool_precise_ty false) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γt ⊫ ty_denote_under Σ Γt τt et) ->
  (ctx_denote_under Σ Γf ⊫ ty_denote_under Σ Γf τf ef) ->
  ctx_denote_under Σ (CtxSum Γt Γf) ⊫
    ty_denote_under Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hbool_t Hbool_f HIHt HIHf m Hctx.
  pose proof Hwf as Hwf_for_eqs.
  destruct Hwf_for_eqs as [Hbasic_sum [Hty_sum _]].
  cbn [basic_ctx] in Hbasic_sum.
  destruct Hbasic_sum as [_ [_ [_ Herase_ctx]]].
  cbn [wf_context_ty_at] in Hty_sum.
  destruct Hty_sum as [_ [_ Herase_ty]].
  destruct (ctx_denote_under_sum_elim Σ Γt Γf m Hctx)
    as [mt [mf [Hdef [Hle [HΓt HΓf]]]]].
  pose proof (Hbool_t mt HΓt) as Hbt.
  pose proof (Hbool_f mf HΓf) as Hbf.
  pose proof (HIHt mt HΓt) as Het.
  pose proof (HIHf mf HΓf) as Hef.
  pose proof (context_typing_wf_match_sum_l
    Σ Γt Γf x τt τf et ef Hwf) as Hwf_t.
  pose proof (context_typing_wf_match_sum_r
    Σ Γt Γf x τt τf et ef Hwf) as Hwf_f.
  pose proof (bool_precise_true_ret_fvar_lookup Γt x mt) as Hlookup_t.
  pose proof (tm_equiv_match_true_var
    Σ Γt x et ef τt mt Hwf_t HΓt
    (fun σ Hσ => Hlookup_t σ Hbt Hσ)) as Heq_t.
  pose proof (tm_total_equiv_match_true_var
    Σ Γt x et ef τt mt Hwf_t HΓt
    (fun σ Hσ => Hlookup_t σ Hbt Hσ)) as Htotal_eq_t.
  pose proof (match_target_zero_from_branch
    Σ Γt x τt et ef et mt Hwf_t HΓt
    ltac:(cbn [fv_tm]; better_set_solver) Heq_t Htotal_eq_t Het)
    as Hmatch_t.
  pose proof (bool_precise_false_ret_fvar_lookup Γf x mf) as Hlookup_f.
  pose proof (tm_equiv_match_false_var
    Σ Γf x et ef τf mf Hwf_f HΓf
    (fun σ Hσ => Hlookup_f σ Hbf Hσ)) as Heq_f.
  pose proof (tm_total_equiv_match_false_var
    Σ Γf x et ef τf mf Hwf_f HΓf
    (fun σ Hσ => Hlookup_f σ Hbf Hσ)) as Htotal_eq_f.
  pose proof (match_target_zero_from_branch
    Σ Γf x τf et ef ef mf Hwf_f HΓf
    ltac:(cbn [fv_tm]; better_set_solver) Heq_f Htotal_eq_f Hef)
    as Hmatch_f.
  unfold ty_denote_under, ty_denote in Hmatch_t, Hmatch_f |- *.
  rewrite <- (ty_denote_gas_saturate
      (cty_depth (CTSum τt τf))
      (atom_env_to_lty_env (erase_ctx Γt)) τt
      (tmatch (vfvar x) et ef)) in Hmatch_t by (cbn [cty_depth]; lia).
  rewrite <- (ty_denote_gas_saturate
      (cty_depth (CTSum τt τf))
      (atom_env_to_lty_env (erase_ctx Γf)) τf
      (tmatch (vfvar x) et ef)) in Hmatch_f by (cbn [cty_depth]; lia).
  replace (atom_env_to_lty_env (erase_ctx Γf))
    with (atom_env_to_lty_env (erase_ctx Γt)) in Hmatch_f
    by (rewrite Herase_ctx; reflexivity).
  assert (Htotal_t : mt ⊨ expr_total_formula (tmatch (vfvar x) et ef)).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_t) as Hguard_t.
    repeat rewrite res_models_and_iff in Hguard_t.
    tauto.
  }
  assert (Htotal_f : mf ⊨ expr_total_formula (tmatch (vfvar x) et ef)).
  {
    pose proof (ty_denote_gas_guard _ _ _ _ _ Hmatch_f) as Hguard_f.
    repeat rewrite res_models_and_iff in Hguard_f.
    tauto.
  }
  assert (Htotal_m : m ⊨ expr_total_formula (tmatch (vfvar x) et ef)).
  {
    eapply res_models_kripke; [exact Hle|].
    eapply expr_total_formula_sum_intro; eauto.
  }
  assert (Hstatic :
      m ⊨ ty_static_guard_formula
        (atom_env_to_lty_env (erase_ctx (CtxSum Γt Γf)))
        (CTSum τt τf) (tmatch (vfvar x) et ef)).
  {
    exact (context_typing_wf_denot_static_guard_full
      Σ (CtxSum Γt Γf) (CTSum τt τf)
      (tmatch (vfvar x) et ef) m Hwf Hctx).
  }
  replace (atom_env_to_lty_env (erase_ctx (CtxSum Γt Γf)))
    with (atom_env_to_lty_env (erase_ctx Γt)) in Hstatic |- *
    by (cbn [erase_ctx]; reflexivity).
  eapply ty_denote_gas_sum_intro_from_branch_refinement
    with (m1 := mt) (m2 := mf) (Hdef := Hdef).
  - exact Hle.
  - exact Herase_ty.
  - cbn [cty_depth]. lia.
  - cbn [cty_depth]. lia.
  - exact Hstatic.
  - exact Htotal_m.
  - exact Hmatch_t.
  - exact Hmatch_f.
Qed.

Lemma fundamental_match_true_case Σ Γ x τ et ef :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (bool_precise_ty true) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ et) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hbool HIH m Hctx.
  pose proof (Hbool m Hctx) as Hbt.
  pose proof (HIH m Hctx) as Het.
  pose proof (bool_precise_true_ret_fvar_lookup Γ x m) as Hlookup.
  pose proof (tm_equiv_match_true_var
    Σ Γ x et ef τ m Hwf Hctx
    (fun σ Hσ => Hlookup σ Hbt Hσ)) as Heq.
  pose proof (tm_total_equiv_match_true_var
    Σ Γ x et ef τ m Hwf Hctx
    (fun σ Hσ => Hlookup σ Hbt Hσ)) as Htotal_eq.
  exact (match_target_zero_from_branch
    Σ Γ x τ et ef et m Hwf Hctx
    ltac:(cbn [fv_tm]; better_set_solver) Heq Htotal_eq Het).
Qed.

Lemma fundamental_match_false_case Σ Γ x τ et ef :
  context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ ->
  (ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (bool_precise_ty false) (tret (vfvar x))) ->
  (ctx_denote_under Σ Γ ⊫ ty_denote_under Σ Γ τ ef) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ τ (tmatch (vfvar x) et ef).
Proof.
  intros Hwf Hbool HIH m Hctx.
  pose proof (Hbool m Hctx) as Hbf.
  pose proof (HIH m Hctx) as Hef.
  pose proof (bool_precise_false_ret_fvar_lookup Γ x m) as Hlookup.
  pose proof (tm_equiv_match_false_var
    Σ Γ x et ef τ m Hwf Hctx
    (fun σ Hσ => Hlookup σ Hbf Hσ)) as Heq.
  pose proof (tm_total_equiv_match_false_var
    Σ Γ x et ef τ m Hwf Hctx
    (fun σ Hσ => Hlookup σ Hbf Hσ)) as Htotal_eq.
  exact (match_target_zero_from_branch
    Σ Γ x τ et ef ef m Hwf Hctx
    ltac:(cbn [fv_tm]; better_set_solver) Heq Htotal_eq Hef).
Qed.
