(** * ContextTyping.SoundnessLamBase

    Lam and LamD proof support for the direct Fundamental theorem.
    These lemmas are kept out of [Soundness.v] so the Fundamental dispatch file
    does not re-check the large Arrow/Wand transport proofs on every edit. *)

From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeDenote
  TypeEquivCore
  DenotationSetMapFacts
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Lemma soundness_lam_lc_lvars_shift_from k D :
  lc_lvars D ->
  lc_lvars (lvars_shift_from k D).
Proof.
  exact (denotation_open_lvars_shift_from_lc k D).
Qed.

Lemma soundness_lam_lvars_lc_at_zero_of_lc D :
  lc_lvars D ->
  lvars_lc_at 0 D.
Proof.
  exact (denotation_open_lvars_lc_at_zero_of_lc D).
Qed.

Lemma soundness_lam_lc_lvars_context_ty_lvars_at_of_lc d τ :
  cty_lc_at d τ ->
  lc_lvars (context_ty_lvars_at d τ).
Proof.
  intros Hlc v Hv.
  destruct v as [k|a]; [|exact I].
  pose proof (cty_lc_at_lvars_bv_empty d τ Hlc) as Hempty.
  assert (Hk : k ∈ lvars_bv (context_ty_lvars_at d τ))
    by (rewrite lvars_bv_elem; exact Hv).
  rewrite Hempty in Hk.
  rewrite elem_of_empty in Hk.
  exact Hk.
Qed.

Lemma lam_lty_env_restrict_result_first_arg_eq
    (Δ : lty_env) τx τ vf y :
  lc_context_ty τx ->
  y ∉ fv_value vf ∪ fv_cty τx ∪ fv_cty τ ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (relevant_env Δ (CTArrow τx τ) (tret vf)))
    (relevant_lvars τx (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]> Δ)
	    (relevant_lvars τx (tret (vfvar y))).
Proof.
  intros Hτx Hy.
  apply storeA_map_eq. intros u.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (u ∈ relevant_lvars τx (tret (vfvar y)))) as [Hu|Hu];
    [|reflexivity].
  destruct u as [k|a].
  - exfalso.
    assert (Hlc_rel :
        lc_lvars (relevant_lvars τx (tret (vfvar y)))).
    {
      apply lc_lvars_relevant_lvars; [exact Hτx|constructor; constructor].
    }
    exact (Hlc_rel (LVBound k) Hu).
  - destruct (decide (a = y)) as [->|Hay].
    + rewrite !lookup_insert.
      repeat rewrite decide_True by reflexivity.
      reflexivity.
    + rewrite !lookup_insert_ne by congruence.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide
        (LVFree a ∈ relevant_lvars (CTArrow τx τ) (tret vf)))
        as [_|Hbad]; [reflexivity|].
      exfalso. apply Hbad.
      unfold relevant_lvars in Hu |- *.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
        context_ty_lvars context_ty_lvars_at] in Hu |- *.
      apply elem_of_union in Hu as [Haτx|Hay_single].
      * better_set_solver.
      * apply elem_of_singleton in Hay_single.
        inversion Hay_single. congruence.
Qed.

Lemma lamd_lty_env_restrict_result_first_arg_eq
    (Δ : lty_env) τx τ vf y :
  lc_context_ty τx ->
  y ∉ fv_value vf ∪ fv_cty τx ∪ fv_cty τ ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (relevant_env Δ (CTWand τx τ) (tret vf)))
    (relevant_lvars τx (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]> Δ)
	    (relevant_lvars τx (tret (vfvar y))).
Proof.
  intros Hτx Hy.
  apply storeA_map_eq. intros u.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (u ∈ relevant_lvars τx (tret (vfvar y)))) as [Hu|Hu];
    [|reflexivity].
  destruct u as [k|a].
  - exfalso.
    assert (Hlc_rel :
        lc_lvars (relevant_lvars τx (tret (vfvar y)))).
    {
      apply lc_lvars_relevant_lvars; [exact Hτx|constructor; constructor].
    }
    exact (Hlc_rel (LVBound k) Hu).
  - destruct (decide (a = y)) as [->|Hay].
    + rewrite !lookup_insert.
      repeat rewrite decide_True by reflexivity.
      reflexivity.
    + rewrite !lookup_insert_ne by congruence.
      unfold relevant_env, lty_env_restrict_lvars.
      rewrite storeA_restrict_lookup.
      destruct (decide
        (LVFree a ∈ relevant_lvars (CTWand τx τ) (tret vf)))
        as [_|Hbad]; [reflexivity|].
      exfalso. apply Hbad.
      unfold relevant_lvars in Hu |- *.
      cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
        context_ty_lvars context_ty_lvars_at] in Hu |- *.
      apply elem_of_union in Hu as [Haτx|Hay_single].
      * better_set_solver.
      * apply elem_of_singleton in Hay_single.
        inversion Hay_single. congruence.
Qed.

Lemma lam_lty_env_restrict_result_first_result_eq
    (Δ : lty_env) τx τ vf y z :
  lty_env_closed Δ ->
  context_ty_lvars (cty_open 0 y τ) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τ ->
  y <> z ->
  y ∉ fv_cty τ ->
  z ∉ fv_value vf ∪ fv_cty τx ∪ fv_cty τ ->
  lty_env_restrict_lvars
    (<[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
      (<[LVFree y := erase_ty τx]> Δ))
    (relevant_lvars (cty_open 0 y τ)
      (tapp_tm (tret (vfvar z)) (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (<[LVFree z := erase_ty (CTArrow τx τ)]>
        (relevant_env Δ (CTArrow τx τ) (tret vf))))
    (relevant_lvars (cty_open 0 y τ)
      (tapp_tm (tret (vfvar z)) (vfvar y))).
Proof.
  intros HΔclosed Hτopen Hyz Hyτ Hz.
  rewrite cty_open_preserves_erasure.
  apply storeA_map_eq. intros u.
  unfold lty_env_restrict_lvars.
  rewrite !storeA_restrict_lookup.
  destruct (decide (u ∈ relevant_lvars (cty_open 0 y τ)
      (tapp_tm (tret (vfvar z)) (vfvar y)))) as [Hu|Hu];
    [|reflexivity].
  try rewrite !decide_True by exact Hu.
  destruct u as [k|a].
  - repeat rewrite lookup_insert_ne by congruence.
    change ((Δ : gmap logic_var ty) !! LVBound k =
      (relevant_env Δ (CTArrow τx τ) (tret vf) : gmap logic_var ty)
        !! LVBound k).
	    pose proof (lty_env_closed_lookup_bound_none Δ k HΔclosed)
	      as HΔk.
	    rewrite HΔk.
	    pose proof (lty_env_closed_lookup_bound_none
	      (relevant_env Δ (CTArrow τx τ) (tret vf)) k
	      ltac:(apply relevant_env_closed; exact HΔclosed)) as Hrelk.
	    rewrite Hrelk. reflexivity.
	  - destruct (decide (a = y)) as [->|Hay].
	    + repeat rewrite lookup_insert.
	      destruct (decide (LVFree y = LVFree y)); [|congruence].
	      destruct (decide (LVFree z = LVFree y)); [congruence|reflexivity].
	    + destruct (decide (a = z)) as [->|Haz].
	      * repeat rewrite lookup_insert_ne by congruence.
	        repeat rewrite lookup_insert.
	        destruct (decide (LVFree z = LVFree z)); [|congruence].
	        destruct (decide (LVFree y = LVFree z)); [congruence|].
	        destruct (decide (LVFree z = LVFree z)); [reflexivity|congruence].
	      * repeat rewrite lookup_insert_ne by congruence.
	        unfold relevant_env, lty_env_restrict_lvars.
	        rewrite storeA_restrict_lookup.
	        destruct (decide
	          (LVFree a ∈ relevant_lvars (CTArrow τx τ) (tret vf)))
	          as [_|Hbad]; [reflexivity|].
	        exfalso. apply Hbad.
	        unfold relevant_lvars in Hu |- *.
	        cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys
	          context_ty_lvars context_ty_lvars_at] in Hu |- *.
	        apply elem_of_union in Hu as [Huτ|Hu_tm].
	        -- apply elem_of_union_l.
	           apply elem_of_union_r.
	           apply Hτopen.
	           apply elem_of_difference. split; [exact Huτ|].
	           intros Hyin. apply elem_of_singleton in Hyin.
	           inversion Hyin. congruence.
	        -- clear -Hu_tm Hay Haz.
	           rewrite tm_lvars_tapp_tm_fvar in Hu_tm.
	           cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys] in Hu_tm.
		           set_solver.
Qed.

Lemma lam_lty_env_restrict_result_first_result_closed_eq
    (Δ : lty_env) τx τ vf y z :
  lty_env_closed Δ ->
  lc_context_ty τ ->
  y <> z ->
  y ∉ fv_cty τ ->
  z ∉ fv_value vf ∪ fv_cty τx ∪ fv_cty τ ->
  lty_env_restrict_lvars
    (<[LVFree z := erase_ty (CTArrow τx τ)]>
      (<[LVFree y := erase_ty τx]> Δ))
    (relevant_lvars τ (tapp_tm (tret (vfvar z)) (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (<[LVFree z := erase_ty (CTArrow τx τ)]>
        (relevant_env Δ (CTArrow τx τ) (tret vf))))
    (relevant_lvars τ (tapp_tm (tret (vfvar z)) (vfvar y))).
Proof.
  intros HΔ Hτ Hyz Hyτ Hz.
  pose proof (lam_lty_env_restrict_result_first_result_eq
    Δ τx τ vf y z HΔ
    ltac:(eapply cty_lvars_open_body_closed_no_fresh;
      [apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc;
       eapply (cty_lc_at_mono_depth 0 1); [lia|exact Hτ]
      |intros HyD; apply lvars_fv_elem in HyD;
       rewrite context_ty_lvars_fv_at in HyD; exact (Hyτ HyD)
      |reflexivity])
    Hyz Hyτ Hz) as Heq.
  rewrite (cty_open_above_lc_fresh 0 0 y τ) in Heq
    by (lia || exact Hτ || exact Hyτ).
  exact Heq.
Qed.

Lemma lamd_lty_env_restrict_result_first_result_eq
    (Δ : lty_env) τx τ vf y z :
  lty_env_closed Δ ->
  context_ty_lvars (cty_open 0 y τ) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τ ->
  y <> z ->
  y ∉ fv_cty τ ->
  z ∉ fv_value vf ∪ fv_cty τx ∪ fv_cty τ ->
  lty_env_restrict_lvars
    (<[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
      (<[LVFree y := erase_ty τx]> Δ))
    (relevant_lvars (cty_open 0 y τ)
      (tapp_tm (tret (vfvar z)) (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (<[LVFree z := erase_ty (CTWand τx τ)]>
        (relevant_env Δ (CTWand τx τ) (tret vf))))
    (relevant_lvars (cty_open 0 y τ)
      (tapp_tm (tret (vfvar z)) (vfvar y))).
Proof.
  intros HΔclosed Hτopen Hyz Hyτ Hz.
  change (erase_ty (CTWand τx τ)) with (erase_ty (CTArrow τx τ)).
  change (relevant_env Δ (CTWand τx τ) (tret vf))
    with (relevant_env Δ (CTArrow τx τ) (tret vf)).
  eapply lam_lty_env_restrict_result_first_result_eq; eauto.
Qed.

Lemma context_typing_wf_denot_static_guard_full
    (Σ : gmap atom ty) Γ τ e (m : WfWorldT) :
  context_typing_wf Σ Γ e τ ->
  m ⊨ ctx_denote_under Σ Γ ->
  m ⊨ ty_static_guard_formula
    (atom_env_to_lty_env (erase_ctx Γ))
    τ e.
Proof.
  intros Hwf Hctx.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as Hbasicctx.
  assert (Hworld :
      m ⊨ basic_world_formula
        (atom_env_to_lty_env (erase_ctx Γ))).
  {
    eapply basic_world_formula_subenv.
    - intros v T Hv.
      destruct v as [k|x].
      + rewrite atom_store_to_lvar_store_lookup_bound_none in Hv.
        discriminate.
      + rewrite atom_store_to_lvar_store_lookup_free in Hv |- *.
        assert (HxΓ : x ∈ dom (erase_ctx Γ)).
        { apply elem_of_dom. eauto. }
        exact (eq_trans
          (eq_sym (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
            Σ Γ x Hbasicctx HxΓ)) Hv).
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
    rewrite atom_store_to_lvar_store_dom.
    apply basic_context_ty_to_lvars. exact Hτ.
  - rewrite res_models_and_iff. split.
    + apply basic_world_formula_models_iff.
      split; [exact Hlc|]. split; [exact Hscope|exact Htyped_world].
    + apply expr_basic_typing_formula_models_iff.
	      split; [exact Hlc|]. split; [exact Hscope|].
	      apply basic_tm_has_ltype_of_atom_typing.
	      * apply atom_store_to_lvar_store_closed.
	      * rewrite lvar_store_to_atom_store_atom_store.
	        exact (context_typing_wf_basic_typing Σ Γ e τ Hwf).
Qed.

Lemma context_typing_wf_denot_static_guard_comma_bind_insert
    (Σ : gmap atom ty) Γ y τx τ e (m : WfWorldT) :
  y ∉ dom (erase_ctx Γ) ->
  context_typing_wf Σ (CtxComma Γ (CtxBind y τx)) e τ ->
  m ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  m ⊨ ty_static_guard_formula
    (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))
    τ e.
Proof.
  intros Hy Hwf Hctx.
  pose proof (context_typing_wf_denot_static_guard_full
    Σ (CtxComma Γ (CtxBind y τx)) τ e m Hwf Hctx) as Hstatic.
  assert (Henv :
      atom_env_to_lty_env (erase_ctx (CtxComma Γ (CtxBind y τx))) =
      (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))).
  {
    rewrite erase_ctx_comma_bind_fresh.
    - apply atom_store_to_lvar_store_insert.
    - exact Hy.
  }
  rewrite Henv in Hstatic.
  exact Hstatic.
Qed.

Lemma ctx_erasure_under_agree_union_on_ty
    (Σ : gmap atom ty) Γ e τ :
  context_typing_wf Σ Γ e τ ->
  ty_env_agree_on (fv_cty τ) (Σ ∪ erase_ctx Γ) (ctx_erasure_under Σ Γ).
Proof.
  intros Hwf.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom
    Σ Γ e τ Hwf) as Hτ.
  unfold ty_env_agree_on. intros y Hy.
  assert (HyΓ : y ∈ dom (erase_ctx Γ)) by (apply Hτ; exact Hy).
  pose proof (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
    Σ Γ y HbasicΓ HyΓ) as Herase.
  assert (HΣnone : Σ !! y = None).
  { eapply basic_ctx_erase_dom_fresh_none; eauto. }
  transitivity ((erase_ctx Γ : gmap atom ty) !! y).
  - apply lookup_union_r. exact HΣnone.
  - exact Herase.
Qed.

Lemma lam_arrow_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
      * apply basic_ctx_bind.
        -- ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ. better_set_solver.
        -- eapply (wf_context_ty_at_mono_env
             0 (dom (erase_ctx Γ)) (dom Σ ∪ ctx_dom Γ)).
           ++ rewrite HdomΓ. set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ.
        better_set_solver.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_comma_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxComma Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
        -- symmetry. apply erase_ctx_comma_bind_fresh.
           ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  pose proof (context_typing_wf_denot_static_guard_full
    Σ (CtxComma Γ (CtxBind y τx)) (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))
    my Hwf_app Hctx_comma) as Hstatic.
  assert (Henv :
      atom_env_to_lty_env (erase_ctx (CtxComma Γ (CtxBind y τx))) =
      (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))).
  {
    rewrite erase_ctx_comma_bind_fresh.
    - apply atom_store_to_lvar_store_insert.
    - ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  rewrite Henv in Hstatic.
  exact Hstatic.
Qed.

Lemma lam_wand_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_star.
  assert (Hwf_app :
      context_typing_wf Σ (CtxStar Γ (CtxBind y τx))
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
      * apply basic_ctx_bind.
        -- ctx_erasure_under_norm_in Hy. better_set_solver.
        -- eapply (wf_context_ty_at_mono_env
             0 ∅ (dom Σ)).
           ++ better_set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ.
        better_set_solver.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxStar Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_star_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxStar Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
        -- symmetry. apply erase_ctx_star_bind_fresh.
           ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  pose proof (context_typing_wf_denot_static_guard_full
    Σ (CtxStar Γ (CtxBind y τx)) (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))
    my Hwf_app Hctx_star) as Hstatic.
  assert (Henv :
      atom_env_to_lty_env (erase_ctx (CtxStar Γ (CtxBind y τx))) =
      (<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ)))).
  {
    rewrite erase_ctx_star_bind_fresh.
    - apply atom_store_to_lvar_store_insert.
    - ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  rewrite Henv in Hstatic.
  exact Hstatic.
Qed.
