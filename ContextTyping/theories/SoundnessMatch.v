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
From ContextTyping Require Import Typing SoundnessLam.

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
  assert (Hfv_et : fv_tm et ⊆ X) by (subst X; cbn [fv_tm]; better_set_solver).
  assert (Hfv_match : fv_tm (tmatch (vfvar x) et ef) ⊆ X)
    by (subst X; better_set_solver).
  assert (HxX : x ∈ X) by (subst X; cbn [fv_tm fv_value]; better_set_solver).
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
  assert (Hfv_ef : fv_tm ef ⊆ X) by (subst X; cbn [fv_tm]; better_set_solver).
  assert (Hfv_match : fv_tm (tmatch (vfvar x) et ef) ⊆ X)
    by (subst X; better_set_solver).
  assert (HxX : x ∈ X) by (subst X; cbn [fv_tm fv_value]; better_set_solver).
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
  assert (Hfv_et : fv_tm et ⊆ X) by (subst X; cbn [fv_tm]; better_set_solver).
  assert (Hfv_match : fv_tm (tmatch (vfvar x) et ef) ⊆ X)
    by (subst X; better_set_solver).
  assert (HxX : x ∈ X) by (subst X; cbn [fv_tm fv_value]; better_set_solver).
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
  assert (Hfv_ef : fv_tm ef ⊆ X) by (subst X; cbn [fv_tm]; better_set_solver).
  assert (Hfv_match : fv_tm (tmatch (vfvar x) et ef) ⊆ X)
    by (subst X; better_set_solver).
  assert (HxX : x ∈ X) by (subst X; cbn [fv_tm fv_value]; better_set_solver).
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

Lemma ty_denote_gas_sum_open_left_branch_from_pulled
    gas Σ τ1 τ2 e (m1 my1 : WfWorldT) y :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  res_restrict my1 (world_dom (m1 : WorldT)) = m1 ->
  my1 ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTSum τ1 τ2) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  m1 ⊨ ty_denote_gas (S gas) Σ τ1 e ->
  my1 ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
        (erase_ty τ1))
      (cty_shift 0 τ1) (tret (vbvar 0))).
Proof.
  (* Branch-local alias obligation for the left summand.

     Use the pulled projection [my1 ↾ m1 = m1] to lift the branch denotation to
     [my1], coarsen the opened branch result graph as needed, then call
     [ty_denote_gas_result_alias] and normalize the opened branch environment
     using [sum_branch_relevant_env_agree_open_one_core]. *)
Admitted.

Lemma ty_denote_gas_sum_open_right_branch_from_pulled
    gas Σ τ1 τ2 e (m2 my2 : WfWorldT) y :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  res_restrict my2 (world_dom (m2 : WorldT)) = m2 ->
  my2 ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTSum τ1 τ2) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  m2 ⊨ ty_denote_gas (S gas) Σ τ2 e ->
  my2 ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
        (erase_ty τ1))
      (cty_shift 0 τ2) (tret (vbvar 0))).
Proof.
  (* Branch-local alias obligation for the right summand.

     This is analogous to the left branch, but also uses the CTSum shape/guard
     information to align the result slot typed with [erase_ty τ1] against
     [τ2]'s erased type. *)
Admitted.

Lemma ctsum_open_result_graph_pullback_branches
    Σ τ1 τ2 e (my1 my2 my : WfWorldT) y
    (Hdef : raw_sum_defined my1 my2) :
  res_sum my1 my2 Hdef ⊑ my ->
  my ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTSum τ1 τ2) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  my1 ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTSum τ1 τ2) e)))
      (tm_shift 0 e) (LVBound 0)) /\
  my2 ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTSum τ1 τ2) e)))
      (tm_shift 0 e) (LVBound 0)).
Proof.
  (* Exact result graphs are not ordinary Kripke-downward facts.  This lemma is
     the precise place where the global result witness must be pulled back to
     the already-constructed branch result worlds.  Proving it should use the
     fact that [my1] and [my2] are pullbacks of [my] along the branch base
     worlds, not a generic formula restriction argument. *)
Admitted.

Lemma ty_denote_gas_sum_open_result_split_from_pulled_branches
    gas Σ τ1 τ2 e (m1 m2 my1 my2 my : WfWorldT) y
    (Hdef : raw_sum_defined my1 my2) :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  res_sum my1 my2 Hdef ⊑ my ->
  res_restrict my1 (world_dom (m1 : WorldT)) = m1 ->
  res_restrict my2 (world_dom (m2 : WorldT)) = m2 ->
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
  intros Hy Hle Hrestrict1 Hrestrict2 Hres Hbranch1 Hbranch2.
  destruct (ctsum_open_result_graph_pullback_branches
    Σ τ1 τ2 e my1 my2 my y Hdef Hle Hres) as [Hres1 Hres2].
  rewrite formula_open_plus.
  eapply res_models_plus_intro with (m1 := my1) (m2 := my2) (Hdef := Hdef).
  - exact Hle.
  - eapply ty_denote_gas_sum_open_left_branch_from_pulled; eauto.
  - eapply ty_denote_gas_sum_open_right_branch_from_pulled; eauto.
Qed.

Lemma ty_denote_gas_sum_open_result_split_from_branches
    gas Σ τ1 τ2 e (m1 m2 m my : WfWorldT) y
    (Hdef : raw_sum_defined m1 m2) :
  y ∉ fv_tm e ∪
    lvars_fv (dom (relevant_env Σ (CTSum τ1 τ2) e)) ∪
    fv_cty τ1 ∪ fv_cty τ2 ->
  res_sum m1 m2 Hdef ⊑ m ->
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
  intros Hy Hle Hdom Hrestrict Hres Hbranch1 Hbranch2.
  assert (Hsum_my : res_sum m1 m2 Hdef ⊑ my).
  {
    eapply res_le_of_restrict_eq; [exact Hle|exact Hrestrict].
  }
  destruct (res_sum_pullback_subset_projection_full my m1 m2 Hdef Hsum_my)
    as [Hsub1 [Hsub2 [Hdef_full Hle_full]]].
  eapply ty_denote_gas_sum_open_result_split_from_pulled_branches; eauto.
  - apply res_pullback_subset_projection_restrict.
  - apply res_pullback_subset_projection_restrict.
Qed.

Lemma ty_denote_gas_sum_result_body_from_branch_refinement
    gas Σ τ1 τ2 e (m1 m2 m : WfWorldT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m ->
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
  intros Hle Hzero Hbranch1 Hbranch2.
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
    gas Σ τ1 τ2 e m1 m2 m my y Hdef Hfresh_split Hle Hdom Hrestrict Hres
    Hbranch1 Hbranch2).
Qed.

Lemma ty_denote_gas_sum_intro_from_branch_refinement
    gas Σ τ1 τ2 e (m1 m2 m : WfWorldT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m ->
  m ⊨ ty_static_guard_formula Σ (CTSum τ1 τ2) e ->
  m ⊨ expr_total_formula e ->
  m1 ⊨ ty_denote_gas gas Σ τ1 e ->
  m2 ⊨ ty_denote_gas gas Σ τ2 e ->
  m ⊨ ty_denote_gas gas Σ (CTSum τ1 τ2) e.
Proof.
  intros Hle Hstatic Htotal Hbranch1 Hbranch2.
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
    + eapply ty_denote_gas_sum_result_body_from_branch_refinement; eauto.
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
