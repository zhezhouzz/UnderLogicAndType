(** * ContextTyping.SoundnessLam

    Lam and LamD proof support for the direct Fundamental theorem.
    These lemmas are kept out of [Soundness.v] so the Fundamental dispatch file
    does not re-check the large Arrow/Wand transport proofs on every edit. *)

From CoreLang Require Import BasicTyping BasicTypingProps InstantiationProps
  SmallStep StrongNormalization.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface ResourceExtension.
From ContextTypeLanguage Require Import WF.
From ContextBasicDenotation Require Import StoreTyping TermExtension TermTLet Qualifier
  BasicTypingFormula RelevantEnv.
From Denotation Require Import Context
  TypeDenote TypeDenoteRegular
  TypeEquivCore
  DenotationSetMapFacts
  TypeEquivTermBase TypeEquivTermResult
  TypeEquivFiberBaseCore TypeEquivFiberBaseProjected
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing TypingRegular.

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
  apply context_ty_lvars_at_lc_of_cty_lc.
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
	        (LVFree a ∈ context_ty_lvars (CTArrow τx τ) ∪ tm_lvars (tret vf)))
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
	        (LVFree a ∈ context_ty_lvars (CTWand τx τ) ∪ tm_lvars (tret vf)))
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
			          (LVFree a ∈ context_ty_lvars (CTArrow τx τ) ∪ tm_lvars (tret vf)))
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

(** Arrow/Lam proof support. *)

Lemma lam_arrow_open_arg_mid_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Hmid.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hτx_fv : fv_cty τx ⊆ dom (erase_ctx Γ)).
  {
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    eapply wf_context_ty_at_fv_subset. exact Hτx.
  }
  eapply ty_denote_gas_ret_fvar_insert_ctx_erasure_under; eauto.
Qed.

Lemma lam_arrow_open_arg_normalize
  (Σ : tyctx) Γ τx τ e
  (my : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  lc_context_ty τx ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)).
Proof.
  intros Hy Hlcτx Harg.
  rewrite formula_open_ty_denote_gas_bind_ret_bvar0 in Harg.
  2:{ apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  2:{
    apply relevant_env_arrow_fresh_free.
    - clear -Hy. better_set_solver.
    - clear -Hy. better_set_solver.
    - cbn [fv_tm fv_value]. clear -Hy. better_set_solver.
  }
  2:{ clear -Hy. better_set_solver. }
  2:{ exact Hlcτx. }
  exact (arrow_open_arg_to_inserted_env
    (Nat.max (cty_depth τx) (cty_depth τ))
    (atom_env_to_lty_env (erase_ctx Γ)) τx τ
    (tret (vlam (erase_ty τx) e)) my y Harg).
Qed.

Lemma lam_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  rewrite ty_denote_gas_saturate in Harg by lia.
  eapply lam_arrow_open_arg_mid_to_bind_denotation; eauto.
Qed.

Lemma lam_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ e
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (lam_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ e my y Hwf Hy Harg)
    as Hbind_den.
  eapply ctx_bind_from_inserted_erasure_arg_denotation.
  - ctx_erasure_under_norm_in Hy. better_set_solver.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    destruct Hτwf as [Hτx _].
    pose proof (wf_context_ty_at_fv_subset 0 (dom (erase_ctx Γ)) τx Hτx)
      as Hτxfv.
    unfold ty_env_agree_on. intros z Hz.
    assert (HzΓ : z ∈ dom (erase_ctx Γ)).
    { apply Hτxfv. exact Hz. }
    pose proof (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
      Σ Γ z HbasicΓ HzΓ) as Herase.
    assert (HΣnone : Σ !! z = None).
    { eapply basic_ctx_erase_dom_fresh_none; eauto. }
    transitivity ((erase_ctx Γ : gmap atom ty) !! z).
    + apply lookup_union_r. exact HΣnone.
    + exact Herase.
  - exact Hctx_my.
  - exact Hbind_den.
Qed.

Lemma lam_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ e
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hwf Hctx Hdom Hrestrict Hy Harg.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  assert (Hctx_my : my ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_my|].
  eapply lam_arrow_open_arg_to_bind_ctx; eauto.
Qed.

Lemma lam_body_to_arrow_result_mid
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
    ({0 ~> y} τ) (e ^^ y) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ) (e ^^ y).
Proof.
  intros _ Hy Hbody.
  pose proof (ty_denote_under_comma_bind_to_lvar_insert
    Σ Γ τx (cty_open 0 y τ) (e ^^ y) y my
    ltac:(ctx_erasure_under_norm_in Hy; better_set_solver) Hbody) as Hinsert.
  rewrite ty_denote_gas_saturate
    by (rewrite cty_open_preserves_depth; lia).
  rewrite cty_open_preserves_depth.
  rewrite cty_open_preserves_depth in Hinsert.
  exact Hinsert.
Qed.

Lemma lam_arrow_result_mid_app_guard
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas 0
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_guard_formula
    (relevant_env
      ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y τ)
      (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
		Proof.
		  intros Hwf Hy Hzero_body Hstatic.
	  pose proof (ty_static_guard_relevant_of_full _ _ _ _ Hstatic)
	    as Hstatic_rel.
	  unfold ty_guard_formula.
	  pose proof (ty_static_guard_context_wf _ _ _ _ Hstatic_rel)
	    as Hwf_app.
	  pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_rel)
	    as Hworld_app.
	  pose proof (ty_static_guard_basic_typing _ _ _ _ Hstatic_rel)
	    as Hbasic_app.
	  repeat rewrite res_models_and_iff.
	  split; [exact Hwf_app|].
	  split; [exact Hworld_app|].
	  split; [exact Hbasic_app|].
	  pose proof (ty_denote_gas_guard_of_zero _ _ _ _ Hzero_body)
	    as Hguard_body.
	  unfold ty_guard_formula in Hguard_body.
	  repeat rewrite res_models_and_iff in Hguard_body.
	  destruct Hguard_body as [_ [_ [_ Htotal_body]]].
	  apply expr_basic_typing_formula_models_iff in Hbasic_app
	    as [HlcΣ_app [_ Hbasic_ltype_app]].
	  pose proof (basic_tm_has_ltype_lc _ _ _
	    HlcΣ_app Hbasic_ltype_app) as Hlc_app.
	  pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
	    as Hfv_lvars_app.
	  assert (Hfv_app :
	      fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ⊆
	      world_dom (my : WorldT)).
	  {
	    apply basic_world_formula_models_iff in Hworld_app
	      as [_ [Hscope_app _]].
	    intros x Hx.
	    apply Hscope_app.
	    apply (proj2 (lvars_fv_elem _ x)).
	    apply Hfv_lvars_app.
	    unfold lvars_of_atoms.
	    apply elem_of_map. exists x. split; [reflexivity|exact Hx].
	  }
	  pose proof (context_typing_wf_lam_body
	    Σ Γ (erase_ty τx) e (CTArrow τx τ) Hwf) as Hbody.
		  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
		  {
		    apply Hfv_app.
		    cbn [fv_tm fv_value].
		    set_solver.
		  }
	  assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
	  {
	    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
	    eapply ty_denote_gas_guard_of_zero. exact Hzero_body.
	  }
	  assert (Hclosed_app :
	      wfworld_closed_on
	        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))) my).
	  {
	    eapply basic_world_formula_wfworld_closed_on_atoms;
	      [exact Hfv_lvars_app|exact Hworld_app].
	  }
	  assert (Hclosed :
	      wfworld_closed_on
	        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ∪
	         fv_tm (e ^^ y)) my).
	  { apply wfworld_closed_on_union; assumption. }
	  assert (Heq :
	      tm_equiv_on my (e ^^ y)
	        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
	  {
	    intros σ v Hσ.
	    pose proof (tm_equiv_lam_app_body (erase_ty τx) e y my
	      Hclosed Hbody ltac:(ctx_erasure_under_norm_in Hy; better_set_solver)
	      Hy_dom σ v Hσ) as [Happ_body Hbody_app].
		    split; [exact Hbody_app|exact Happ_body].
		  }
		  pose proof (tm_total_equiv_lam_app_body
		    (erase_ty τx) e y my Hclosed Hbody
		    ltac:(ctx_erasure_under_norm_in Hy; better_set_solver)
		    Hy_dom) as Htotal_eq.
		  eapply tm_equiv_total;
		    [ exact Htotal_eq
		    | exact Hlc_app
		    | exact Hfv_app
		    | exact Htotal_body ].
		Qed.

Lemma lam_arrow_result_mid_app_zero
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas 0
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_denote_gas 0
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hzero_body Hstatic.
	  apply ty_denote_gas_zero_of_guard.
	  eapply lam_arrow_result_mid_app_guard; eauto.
Qed.

Lemma lam_arrow_result_mid_app_denotation
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hmid Hstatic.
  assert (Hzero_body :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ) (e ^^ y)).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hmid.
  }
  assert (Hzero_app :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
	  { eapply lam_arrow_result_mid_app_zero; eauto. }
  assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard. exact Hmid.
  }
  assert (Hclosed_app :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard_of_zero. exact Hzero_app.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ∪
         fv_tm (e ^^ y)) my).
  { apply wfworld_closed_on_union; assumption. }
  pose proof (context_typing_wf_lam_body
    Σ Γ (erase_ty τx) e (CTArrow τx τ) Hwf) as Hbody.
	  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
	  {
	    pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic)
	      as Hworld_app.
	    pose proof (ty_static_guard_basic_typing _ _ _ _ Hstatic)
	      as Hbasic_app.
	    apply expr_basic_typing_formula_models_iff in Hbasic_app
	      as [HlcΣ_app [_ Hbasic_ltype_app]].
	    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
	      as Hfv_lvars_app.
	    apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope_app _]].
	    apply Hscope_app.
	    apply (proj2 (lvars_fv_elem _ y)).
	    apply Hfv_lvars_app.
	    unfold lvars_of_atoms.
	    apply elem_of_map. exists y. split; [reflexivity|].
	    cbn [fv_tm fv_value].
	    set_solver.
	  }
  eapply lam_intro_denotation; eauto.
  ctx_erasure_under_norm_in Hy. better_set_solver.
Qed.

Lemma lam_arrow_result_mid_to_opened_goal
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
		  intros Hwf Hy Hmid Hstatic.
  set (elam := tret (vlam (erase_ty τx) e)).
		  pose proof (lam_arrow_result_mid_app_denotation
		    Σ Γ τx τ e my y Hwf Hy Hmid Hstatic) as Happ_mid.
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  {
    apply (context_typing_wf_arrow_result_lc1 Σ Γ
      (tret (vlam (erase_ty τx) e)) τx τ).
    exact Hwf.
  }
  subst elam.
	  eapply ty_equiv_arrow_result_tgt_goal.
  - set_solver.
  - apply arrow_result_open_vars_subset; [exact Hτ_lc1|set_solver].
  - exact Happ_mid.
Qed.

Lemma lam_opened_arrow_result
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
	  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
			  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
			      ((<[LVFree y := erase_ty τx]>
	            (atom_env_to_lty_env (erase_ctx Γ))))
		      τx (tret (vfvar y)) ->
		  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree y := erase_ty τx]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
      (cty_open 0 y τ)
      (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf IH Hctx Hdom Hrestrict Hy Harg.
  assert (Hy_rest :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
  {
    intros Hin.
    clear -Hy Hin. better_set_solver.
  }
  assert (HyL : y ∉ L).
  {
    intros Hin.
    clear -Hy Hin. better_set_solver.
  }
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (lam_arrow_open_arg_to_comma_ctx Σ Γ τx τ e m my y).
    - exact Hwf.
    - exact Hctx.
    - exact Hdom.
    - exact Hrestrict.
    - exact Hy_rest.
    - exact Harg.
  }
		  pose proof (IH y HyL my Hctx_comma) as Hbody.
		  pose proof (lam_arrow_opened_app_static_guard_full
			    Σ Γ τx τ e my y Hwf Hy_rest Hctx_comma) as Hstatic_app.
  pose proof (lam_body_to_arrow_result_mid
    Σ Γ τx τ e my y Hwf Hy_rest Hbody) as Hmid.
  eapply lam_arrow_result_mid_to_opened_goal; eauto.
Qed.

Lemma lam_result_first_outer_result_plain
    (Σ : tyctx) Γ τx τ e
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))))
      (tm_shift 0 (tret (vlam (erase_ty τx) e))) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret (vlam (erase_ty τx) e)) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))))).
		  {
		    rewrite lvars_shift_from_fv.
		    intros Hzbad.
		    apply lvars_fv_elem in Hzbad.
		    pose proof (soundness_relevant_env_arrow_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver))
		      as Hnot.
		    exact (Hnot Hzbad).
		  }
  assert (Hlc_elam :
      lc_tm (tret (vlam (erase_ty τx) e))).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  }
  assert (Hz_elam :
      z ∉ fv_tm (tret (vlam (erase_ty τx) e))).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_elam || exact Hz_elam).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret (vlam (erase_ty τx) e)))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
        as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
          as Hlc.
        exfalso.
        pose proof (tm_lvars_lc _ Hlc (LVBound k) Hv) as [].
	      * rewrite atom_store_to_lvar_store_dom.
	        apply elem_of_map. exists a. split; [reflexivity|].
	        apply Hfv.
	        rewrite <- tm_lvars_fv.
	        apply (proj2 (lvars_fv_elem _ _)).
	        exact Hv.
    + unfold relevant_lvars. set_solver.
	  - set_solver.
		  - intros Hzbad.
		    pose proof (soundness_relevant_env_arrow_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
		    exact (Hnot Hzbad).
	  - exact Hres.
  Qed.

Lemma lamd_result_first_outer_result_plain
    (Σ : tyctx) Γ τx τ e
    (mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  z ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  mz ⊨ formula_open 0 z
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))))
      (tm_shift 0 (tret (vlam (erase_ty τx) e))) (LVBound 0)) ->
  mz ⊨ expr_result_formula
    (tret (vlam (erase_ty τx) e)) (LVFree z).
Proof.
  intros Hwf Hz Hres.
  assert (Hlc_Dshift :
      lc_lvars
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))))).
  {
    apply soundness_lam_lc_lvars_shift_from.
    apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  assert (Hz_Dshift :
      z ∉ lvars_fv
        (lvars_shift_from 0
          (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))))).
		  {
		    rewrite lvars_shift_from_fv.
		    intros Hzbad.
		    apply lvars_fv_elem in Hzbad.
		    pose proof (soundness_relevant_env_wand_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver))
		      as Hnot.
		    exact (Hnot Hzbad).
		  }
  assert (Hlc_elam :
      lc_tm (tret (vlam (erase_ty τx) e))).
  {
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  }
  assert (Hz_elam :
      z ∉ fv_tm (tret (vlam (erase_ty τx) e))).
  {
    cbn [fv_tm fv_value].
    clear -Hz. better_set_solver.
  }
  rewrite formula_open_expr_result_formula_at_shift0 in Hres
    by (exact Hlc_Dshift || exact Hz_Dshift ||
        exact Hlc_elam || exact Hz_elam).
  rewrite (lvars_shift_from_lc_at_id 0
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))))) in Hres
    by (apply soundness_lam_lvars_lc_at_zero_of_lc;
        apply relevant_env_closed; apply atom_store_to_lvar_store_closed).
  unfold expr_result_formula.
  eapply (expr_result_formula_at_coarsen_domain
    (tm_lvars (tret (vlam (erase_ty τx) e)))
    (dom (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))))).
  - intros v Hv.
    unfold relevant_env, lty_env_restrict_lvars.
    rewrite storeA_restrict_dom.
    apply elem_of_intersection. split.
    + pose proof (context_typing_wf_fv_tm_subset
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf)
        as Hfv.
      destruct v as [k|a].
      * pose proof (context_typing_wf_lc_tm
          Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf)
          as Hlc.
        exfalso.
        pose proof (tm_lvars_lc _ Hlc (LVBound k) Hv) as [].
	      * rewrite atom_store_to_lvar_store_dom.
	        apply elem_of_map. exists a. split; [reflexivity|].
	        apply Hfv.
	        rewrite <- tm_lvars_fv.
	        apply (proj2 (lvars_fv_elem _ _)).
	        exact Hv.
    + unfold relevant_lvars. set_solver.
	  - set_solver.
		  - intros Hzbad.
		    pose proof (soundness_relevant_env_wand_value_fresh
		      (atom_env_to_lty_env (erase_ctx Γ)) τx τ
		      (vlam (erase_ty τx) e) z
		      ltac:(cbn [fv_value]; clear -Hz; better_set_solver)) as Hnot.
		    exact (Hnot Hzbad).
  - exact Hres.
Qed.

Lemma lam_result_first_arrow_value_denotation
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (arrow_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTArrow τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
      τx τ (tret (vfvar z))) ->
  mz ⊨ expr_result_formula (tret (vlam (erase_ty τx) e)) (LVFree z) ->
  mz ⊨ arrow_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTArrow τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e))))
      τx τ (tret (vfvar z)).
Proof.
  intros Hwf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (vf := vlam (erase_ty τx) e).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTArrow τx τ) (tret vf)).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf)
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  assert (HΣrel_closed : lty_env_closed Σrel).
  { subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed. }
  assert (HzΣrel : LVFree z ∉ dom Σrel).
  {
    subst Σrel. apply soundness_relevant_env_arrow_value_fresh.
    subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
  }
  eapply res_models_forall_rev_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  intros y Hy my Hdomy Hrestricty.
  assert (Hle_mz_my : mz ⊑ my).
  { rewrite <- Hrestricty. apply res_restrict_le. }
  assert (Hy_world : y ∈ world_dom (my : WorldT)).
  { rewrite Hdomy. apply elem_of_union_r. apply elem_of_singleton_2. reflexivity. }
	  cbn [arrow_value_denote_gas_with] in Hscope_value |- *.
  pose proof (formula_scoped_forall_open_res_le
    mz my y _ Hscope_value Hle_mz_my Hy_world) as Hopened_scope.
  cbn [formula_open] in Hopened_scope |- *.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Harg_raw.
  assert (Hy_fresh :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
  {
    clear -Hy. better_set_solver.
  }
	  assert (Harg_norm :
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]>
	          (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
	        τx (tret (vfvar y))).
	  {
	    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
	      y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel) τx)
	      in Harg_raw.
	    - exact Harg_raw.
	    - apply lty_env_closed_insert_free. exact HΣrel_closed.
	    - rewrite dom_insert_L. intros Hin.
	      apply elem_of_union in Hin as [Hin|Hin].
	      + apply elem_of_singleton in Hin. inversion Hin. subst.
	        clear -Hy. set_solver.
	      + exfalso.
	        subst Σrel.
	        eapply (soundness_relevant_env_arrow_value_fresh
	          (atom_env_to_lty_env (erase_ctx Γ)) τx τ vf y).
	        * subst vf. cbn [fv_value]. clear -Hy. better_set_solver.
	        * exact Hin.
	    - clear -Hy. better_set_solver.
	    - exact Hτx_lc.
	  }
	  assert (Harg_old :
	      my ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]> Δ)
	        τx (tret (vfvar y))).
	  {
	    eapply res_models_ty_denote_gas_env_agree_on
	      with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by (clear -Hy; set_solver).
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTArrow τx τ)) Hz_rel_arg).
      apply lam_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst vf. clear -Hy. cbn [fv_value]. better_set_solver.
    - exact Harg_norm.
  }
	  assert (Hctx_comma :
	      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
	  {
	    eapply (lam_arrow_open_arg_to_comma_ctx Σ Γ τx τ e mz my y).
	    - exact Hwf.
    - exact Hctx_mz.
    - exact Hdomy.
	    - exact Hrestricty.
	    - exact Hy_fresh.
	    - exact Harg_old.
	  }
  assert (HyL : y ∉ L) by (clear -Hy; better_set_solver).
  pose proof (IH y HyL my Hctx_comma) as Hbody.
  pose proof (lam_arrow_opened_app_static_guard_full
    Σ Γ τx τ e my y Hwf Hy_fresh Hctx_comma) as Hstatic_app.
  pose proof (lam_body_to_arrow_result_mid
    Σ Γ τx τ e my y Hwf Hy_fresh Hbody) as Hmid.
  pose proof (lam_arrow_result_mid_app_denotation
    Σ Γ τx τ e my y Hwf Hy_fresh Hmid Hstatic_app) as Happ_src.
  assert (Hres_my :
      my ⊨ expr_result_formula (tret vf) (LVFree z)).
  {
    subst vf.
    eapply res_models_kripke; [exact Hle_mz_my|exact Hres_z].
  }
	  assert (Hfun_basic :
	      my ⊨ expr_basic_typing_formula
	        (<[LVFree y := erase_ty τx]> Δ)
	        (tret vf) (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
  {
    apply expr_basic_typing_formula_models_iff.
    split.
    - apply lty_env_closed_insert_free. apply atom_store_to_lvar_store_closed.
    - split.
      + pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_app)
          as Hworld_app.
        apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope _]].
        exact Hscope.
      + rewrite cty_open_preserves_erasure.
        eapply basic_tm_has_ltype_weaken.
        * subst Δ vf.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
	        * apply insert_subseteq. apply not_elem_of_dom.
		          apply atom_env_to_lty_env_dom_free_notin.
		          eapply soundness_fresh_erase_ctx_from_context_union.
              exact Hy_fresh.
	  }
  assert (Hlc_vf : lc_value vf).
  {
    subst vf.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    subst Δ. apply
      (ctx_erasure_under_inserted_erase_ctx_lty_env_fresh
        Σ Γ z y (erase_ty τx)).
    - clear -Hy. set_solver.
    - clear -Hz. better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value vf ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    apply value_open_result_alias_fresh.
    subst vf. cbn [fv_value].
    clear -Hy Hz. better_set_solver.
  }
	  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
		    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
		    vf y z (erase_ty τx) my
	    Hz_insert_env
	    Hz_alias_fresh
		    ltac:(apply map_lookup_insert)
		    Hlc_vf
		    Hres_my Hfun_basic Hstatic_app Happ_src) as Htarget_alias.
	  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
	    y gas (<[LVFree z := erase_ty (CTArrow τx τ)]> Σrel)
	    τ (erase_ty τx) (tret (vfvar z))).
	  2:{ apply lty_env_closed_insert_free. exact HΣrel_closed. }
	  2:{
	    rewrite dom_insert_L. intros Hin.
	    apply elem_of_union in Hin as [Hin|Hin].
	    - apply elem_of_singleton in Hin. inversion Hin. subst.
	      clear -Hy. set_solver.
	    - exfalso.
	      subst Σrel.
	      eapply (soundness_relevant_env_arrow_value_fresh
	        (atom_env_to_lty_env (erase_ctx Γ)) τx τ vf y).
	      + subst vf. cbn [fv_value]. clear -Hy. better_set_solver.
	      + exact Hin.
	  }
	  2:{ cbn [fv_tm fv_value]. clear -Hy. set_solver. }
	  2:{ clear -Hy. better_set_solver. }
	  2:{ constructor. constructor. }
	  eapply res_models_ty_denote_gas_env_agree_on
	    with (Σ1 := <[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
	        (<[LVFree y := erase_ty τx]> Δ))
      (X := relevant_lvars (cty_open 0 y τ)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  - reflexivity.
  - apply lam_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
	      * intros HyD.
	        apply lvars_fv_elem in HyD.
	        rewrite context_ty_lvars_fv_at in HyD.
          clear -Hy_fresh HyD. better_set_solver.
      * reflexivity.
    + clear -Hy. set_solver.
    + clear -Hy. better_set_solver.
    + subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.

(** Wand/LamD proof support. *)

Lemma lamd_wand_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  n ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env
      (<[y := erase_ty τx]> (store_restrict Σ (fv_cty τx))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret (vlam (erase_ty τx) e)) τx τ Hwf) as Hτx_global.
  rewrite ty_denote_gas_saturate in Harg by lia.
  eapply ty_denote_gas_ret_fvar_insert_closed_atom_env; eauto.
Qed.

Lemma lamd_wand_open_arg_normalize
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  lc_context_ty τx ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTWand τx τ) (tret (vlam (erase_ty τx) e))))
    τx (tret (vfvar y)) ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)).
Proof.
  intros Hy Hlcτx Harg.
  eapply wand_open_arg_to_inserted_env.
  exact Harg.
Qed.

Lemma lamd_open_arg_to_star_ctx
    (Σ : tyctx) Γ τx τ e
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	      ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
	      τx (tret (vfvar y)) ->
	  res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)).
	Proof.
  intros Hwf Hctx Hdom Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret (vlam (erase_ty τx) e)) τx τ Hwf) as Hτx_global.
  pose proof (lamd_wand_open_arg_to_bind_denotation
    Σ Γ τx τ e n y Hwf Hy Harg) as Harg_den.
  assert (Hbind_cropped :
      n ⊨ ctx_denote_under (store_restrict Σ (fv_cty τx))
        (CtxBind y τx)).
  {
    eapply ctx_bind_from_base_denotation.
    - eapply wf_context_ty_at_mono_env; [|exact Hτx_global].
      better_set_solver.
    - intros HyΣ.
      apply Hy.
      rewrite storeA_restrict_dom in HyΣ.
      better_set_solver.
    - exact Harg_den.
  }
  assert (Hbind : n ⊨ ctx_denote_under Σ (CtxBind y τx)).
  {
    rewrite ctx_denote_under_minimal.
    exact Hbind_cropped.
  }
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  destruct (res_product_comm_eq n m Hc) as [Hcmn Heq].
  rewrite Heq.
  eapply ctx_denote_under_star_intro_product; eauto.
Qed.

Lemma lamd_body_to_wand_result_mid
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
	    ({0 ~> y} τ) (e ^^ y) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf Hy Hbody Hstatic.
  set (elam := tret (vlam (erase_ty τx) e)).
  assert (HyΓ : y ∉ dom (erase_ctx Γ)).
  { eapply soundness_fresh_erase_ctx_from_context_union. exact Hy. }
  pose proof (ty_denote_under_star_bind_to_lvar_insert_direct
    Σ Γ τx ({0 ~> y} τ) (e ^^ y) y my HyΓ Hbody) as Hbody_insert.
  assert (Hmid_body :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ) (e ^^ y)).
  {
    replace ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
      with (<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))).
	    2:{ lty_env_open_bind_norm. reflexivity. }
    change (cty_open 0 y τ) with ({0 ~> y} τ).
    rewrite ty_denote_gas_saturate by
      (rewrite cty_open_preserves_depth; lia).
    exact Hbody_insert.
  }
  assert (Hzero_body :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ) (e ^^ y)).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hmid_body.
  }
  assert (Hfull_guard :
      my ⊨ ty_guard_formula
        (relevant_env
          ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
          (cty_open 0 y τ)
          (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
	  {
	    unfold ty_guard_formula.
	    pose proof (ty_static_guard_relevant_of_full _ _ _ _ Hstatic)
	      as Hstatic_rel.
	    pose proof (ty_static_guard_context_wf _ _ _ _ Hstatic_rel)
	      as Hwf_app.
	    pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_rel)
	      as Hworld_app.
	    pose proof (ty_static_guard_basic_typing _ _ _ _ Hstatic_rel)
	      as Hbasic_app.
    repeat rewrite res_models_and_iff.
    split; [exact Hwf_app|].
    split; [exact Hworld_app|].
    split; [exact Hbasic_app|].
    pose proof (ty_denote_gas_guard_of_zero _ _ _ _ Hzero_body)
      as Hguard_body.
    unfold ty_guard_formula in Hguard_body.
    repeat rewrite res_models_and_iff in Hguard_body.
    destruct Hguard_body as [_ [_ [_ Htotal_body]]].
    apply expr_basic_typing_formula_models_iff in Hbasic_app
      as [HlcΣ_app [_ Hbasic_ltype_app]].
    pose proof (basic_tm_has_ltype_lc _ _ _
      HlcΣ_app Hbasic_ltype_app) as Hlc_app.
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
      as Hfv_lvars_app.
    assert (Hfv_app :
        fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ⊆
        world_dom (my : WorldT)).
    {
      apply basic_world_formula_models_iff in Hworld_app
        as [_ [Hscope_app _]].
      intros x Hx.
      apply Hscope_app.
      apply (proj2 (lvars_fv_elem _ x)).
      apply Hfv_lvars_app.
      unfold lvars_of_atoms.
      apply elem_of_map. exists x. split; [reflexivity|exact Hx].
    }
    pose proof (context_typing_wf_lam_body
      Σ Γ (erase_ty τx) e (CTWand τx τ) Hwf) as Hbody_lc.
    assert (Hy_dom : y ∈ world_dom (my : WorldT)).
    {
      apply Hfv_app.
      cbn [fv_tm fv_value]. better_set_solver.
    }
    assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
    {
      eapply denot_ty_lvar_guard_wfworld_closed_on_term.
      eapply ty_denote_gas_guard_of_zero. exact Hzero_body.
    }
    assert (Hclosed_app :
        wfworld_closed_on
          (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))) my).
    {
      eapply basic_world_formula_wfworld_closed_on_atoms;
        [exact Hfv_lvars_app|exact Hworld_app].
    }
	    assert (Hclosed :
	        wfworld_closed_on
	          (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ∪
	           fv_tm (e ^^ y)) my).
	    { apply wfworld_closed_on_union; assumption. }
			    pose proof (tm_total_equiv_lam_app_body
			      (erase_ty τx) e y my Hclosed Hbody_lc
			      ltac:(clear -Hy; soundness_fresh_solve)
			      Hy_dom) as Htotal_eq.
	    eapply tm_equiv_total;
	      [ exact Htotal_eq
	      | exact Hlc_app
	      | exact Hfv_app
	      | exact Htotal_body ].
	  }
  assert (Hzero_app :
      my ⊨ ty_denote_gas 0
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
  { apply ty_denote_gas_zero_of_guard. exact Hfull_guard. }
  assert (Hclosed_body : wfworld_closed_on (fv_tm (e ^^ y)) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard. exact Hmid_body.
  }
  assert (Hclosed_app :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard_of_zero. exact Hzero_app.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ∪
         fv_tm (e ^^ y)) my).
  { apply wfworld_closed_on_union; assumption. }
  pose proof (context_typing_wf_lam_body
    Σ Γ (erase_ty τx) e (CTWand τx τ) Hwf) as Hbody_lc.
  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
  {
    pose proof Hfull_guard as Hguard_app.
    unfold ty_guard_formula in Hguard_app.
    repeat rewrite res_models_and_iff in Hguard_app.
    destruct Hguard_app as [_ [Hworld_app [Hbasic_app _]]].
    apply expr_basic_typing_formula_models_iff in Hbasic_app
      as [_ [_ Hbasic_ltype_app]].
    pose proof (basic_tm_has_ltype_lvars _ _ _ Hbasic_ltype_app)
      as Hfv_lvars_app.
    apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope_app _]].
    apply Hscope_app.
    apply (proj2 (lvars_fv_elem _ y)).
    apply Hfv_lvars_app.
    unfold lvars_of_atoms.
    apply elem_of_map. exists y. split; [reflexivity|].
    cbn [fv_tm fv_value]. better_set_solver.
  }
  assert (Happ_mid :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
		  {
		    eapply lam_intro_denotation; eauto.
		    clear -Hy. soundness_fresh_solve.
		  }
  exact Happ_mid.
Qed.

Lemma lamd_wand_result_mid_to_opened_goal
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTWand τx τ) (tret (vlam (erase_ty τx) e))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf Hy Happ_mid.
  set (elam := tret (vlam (erase_ty τx) e)).
  assert (Hτ_body_lc1 : cty_lc_at 1 τ).
  {
    apply (context_typing_wf_wand_result_lc1 Σ Γ
      (tret (vlam (erase_ty τx) e)) τx τ).
    exact Hwf.
  }
  subst elam.
  eapply ty_equiv_wand_result_tgt_goal.
  - better_set_solver.
  - eapply cty_lvars_open_body_closed_no_fresh.
    + apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
      exact Hτ_body_lc1.
    + intros HyD.
      apply lvars_fv_elem in HyD.
      rewrite context_ty_lvars_fv_at in HyD.
      clear -Hy HyD. better_set_solver.
    + reflexivity.
  - exact Happ_mid.
Qed.

Lemma lamd_opened_wand_result
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m n : WfWorldT) y (Hc : world_compat n m) :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ ({[y]} : aset) ->
	  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	      ((<[LVFree y := erase_ty τx]>
	        (atom_env_to_lty_env (erase_ctx Γ))))
	      τx (tret (vfvar y)) ->
  res_product n m Hc ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTWand τx τ) (tret (vlam (erase_ty τx) e))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)).
Proof.
  intros Hwf IH Hctx Hdom Hy Harg.
  assert (Hy_rest :
      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
  {
    intros Hin.
    clear -Hy Hin. better_set_solver.
  }
  assert (HyL : y ∉ L).
  {
    intros Hin.
    clear -Hy Hin. better_set_solver.
  }
  assert (Hctx_star :
      res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx))).
  {
    eapply (lamd_open_arg_to_star_ctx Σ Γ τx τ e m n y Hc).
    - exact Hwf.
    - exact Hctx.
    - exact Hdom.
    - exact Hy_rest.
    - exact Harg.
  }
  pose proof (IH y HyL (res_product n m Hc) Hctx_star) as Hbody.
		  pose proof (lam_wand_opened_app_static_guard_full
		    Σ Γ τx τ e (res_product n m Hc) y
		    Hwf Hy_rest Hctx_star) as Hstatic_app.
  pose proof (lamd_body_to_wand_result_mid
    Σ Γ τx τ e (res_product n m Hc) y
    Hwf Hy_rest Hbody Hstatic_app) as Happ_mid.
  eapply (lamd_wand_result_mid_to_opened_goal
    Σ Γ τx τ e (res_product n m Hc) y).
  - exact Hwf.
  - exact Hy_rest.
  - exact Happ_mid.
Qed.

Lemma lam_result_first_wand_value_denotation
    (Σ : tyctx) Γ τx τ e (L : aset)
    (m mz : WfWorldT) z :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxStar Γ (CtxBind y τx)) ⊫
      ty_denote_under Σ (CtxStar Γ (CtxBind y τx))
        ({0 ~> y} τ) (e ^^ y)) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (mz : WorldT) = world_dom (m : WorldT) ∪ {[z]} ->
  res_restrict mz (world_dom (m : WorldT)) = m ->
  z ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
    fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  formula_scoped_in_world mz
    (wand_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTWand τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e))))
      τx τ (tret (vfvar z))) ->
  mz ⊨ expr_result_formula (tret (vlam (erase_ty τx) e)) (LVFree z) ->
  mz ⊨ wand_value_denote_gas_with ty_denote_gas
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree z := erase_ty (CTWand τx τ)]>
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e))))
      τx τ (tret (vfvar z)).
Proof.
  intros Hwf IH Hctx Hdomz Hrestrictz Hz Hscope_value Hres_z.
  set (Δ := atom_env_to_lty_env (erase_ctx Γ)).
  set (vf := vlam (erase_ty τx) e).
  set (gas := Nat.max (cty_depth τx) (cty_depth τ)).
  set (Σrel := relevant_env Δ (CTWand τx τ) (tret vf)).
  assert (Hle_m_mz : m ⊑ mz).
  { rewrite <- Hrestrictz. apply res_restrict_le. }
  assert (Hctx_mz : mz ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  pose proof (context_typing_wf_context_ty
    Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf)
    as Hτwf.
  cbn [wf_context_ty_at] in Hτwf.
  destruct Hτwf as [Hτx_wf Hτ_wf].
  assert (Hτx_lc : lc_context_ty τx).
  { eapply wf_context_ty_at_lc. exact Hτx_wf. }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  { eapply wf_context_ty_at_lc. exact Hτ_wf. }
  cbn [wand_value_denote_gas_with] in Hscope_value |- *.
  eapply res_models_fbwand_intro; [exact Hscope_value|].
  exists (L ∪ world_dom (mz : WorldT) ∪ dom Σ ∪
    dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  intros η n Hc Hbind Hηfresh Hdom_prod Harg_raw.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite formula_open_env_singleton in Harg_raw |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
  rewrite open_env_atoms_empty in Hdom_prod.
	  assert (Hdom_y :
	      world_dom (res_product n mz Hc : WorldT) =
	        world_dom (mz : WorldT) ∪ ({[y]} : aset)).
	  {
	    rewrite Hdom_prod. apply union_singleton_empty_r.
	  }
  assert (Hy_fresh :
      y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
        fv_tm e ∪ fv_cty τx ∪ fv_cty τ ∪ {[z]}).
  {
    clear -Hηfresh. set_solver.
  }
	  assert (Hy_rest :
	      y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪
	        fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
	  { clear -Hy_fresh. better_set_solver. }
		  assert (Hy_eraseΓ : y ∉ dom (erase_ctx Γ)).
		  { eapply soundness_fresh_erase_ctx_from_context_union. exact Hy_rest. }
	  assert (HyΔ : LVFree y ∉ dom Δ).
	  {
	    subst Δ. apply atom_env_to_lty_env_dom_free_notin.
	    exact Hy_eraseΓ.
	  }
	  assert (HyL : y ∉ L) by (clear -Hy_fresh; better_set_solver).
  assert (Hyz : y <> z) by (clear -Hy_fresh; set_solver).
  assert (Harg_norm :
      n ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]>
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        τx (tret (vfvar y))).
  {
    change (n ⊨ formula_open 0 y
      (ty_denote_gas gas
        (typed_lty_env_bind
          (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel)
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))) in Harg_raw.
    rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
      y gas (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel) τx)
      in Harg_raw.
    - exact Harg_raw.
    - apply lty_env_closed_insert_free.
      subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
    - rewrite dom_insert_L. intros Hin.
      apply elem_of_union in Hin as [Hin|Hin].
      + apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hyz. congruence.
      + subst Σrel. apply relevant_env_wand_fresh_free in Hin;
          cbn [fv_tm fv_value]; clear -Hy_fresh Hin; better_set_solver.
    - clear -Hy_fresh. better_set_solver.
    - exact Hτx_lc.
  }
	  assert (Harg_old :
	      n ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]> Δ)
	        τx (tret (vfvar y))).
	  {
	    eapply res_models_ty_denote_gas_env_agree_on
	      with (Σ1 := <[LVFree y := erase_ty τx]>
        (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel))
        (X := relevant_lvars τx (tret (vfvar y))).
    - reflexivity.
    - rewrite lty_env_insert_free_commute by exact Hyz.
      assert (Hz_rel_arg :
          LVFree z ∉ relevant_lvars τx (tret (vfvar y)))
        by (intros Hzbad; apply lvars_fv_elem in Hzbad;
            rewrite relevant_lvars_fv in Hzbad;
            cbn [fv_tm fv_value] in Hzbad;
            clear -Hz Hy_fresh Hzbad; better_set_solver).
      rewrite (lty_env_restrict_lvars_insert_fresh
        (<[LVFree y := erase_ty τx]> Σrel)
        (relevant_lvars τx (tret (vfvar y))) z
        (erase_ty (CTWand τx τ)) Hz_rel_arg).
      apply lamd_lty_env_restrict_result_first_arg_eq.
      + exact Hτx_lc.
      + subst vf. clear -Hy_fresh. cbn [fv_value]. better_set_solver.
    - exact Harg_norm.
  }
  pose proof (lamd_opened_wand_result
    Σ Γ τx τ e L mz n y Hc
    Hwf IH Hctx_mz Hdom_y
    ltac:(clear -Hy_fresh; better_set_solver)
    Harg_old) as Hopened_src.
  assert (Hopened_norm :
      res_product n mz Hc ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τx]> Σrel)
        (cty_open 0 y τ)
        (tapp_tm (tret vf) (vfvar y))).
  {
    subst gas Σrel vf.
    exact Hopened_src.
  }
	  assert (Hsrc :
	      res_product n mz Hc ⊨ ty_denote_gas gas
	        (<[LVFree y := erase_ty τx]> Δ)
	        (cty_open 0 y τ)
        (tapp_tm (tret vf) (vfvar y))).
  {
    eapply ty_equiv_wand_result_src_mid.
	    - clear -Hy_rest. better_set_solver.
    - eapply cty_lvars_open_body_closed_no_fresh.
      + apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      + intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_rest HyD. better_set_solver.
      + reflexivity.
		    - exact Hopened_norm.
	  }
	  assert (Hctx_star :
	      res_product n mz Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx))).
	  {
	    eapply (lamd_open_arg_to_star_ctx Σ Γ τx τ e mz n y Hc).
	    - exact Hwf.
	    - exact Hctx_mz.
	    - exact Hdom_y.
	    - exact Hy_rest.
	    - exact Harg_old.
	  }
  pose proof (lam_wand_opened_app_static_guard_full
    Σ Γ τx τ e (res_product n mz Hc) y
    Hwf Hy_rest Hctx_star) as Hstatic_app.
  assert (Hres_prod :
      res_product n mz Hc ⊨ expr_result_formula (tret vf) (LVFree z)).
  {
    subst vf.
    eapply res_models_kripke; [apply res_product_le_r|exact Hres_z].
  }
  assert (Hfun_basic :
      res_product n mz Hc ⊨ expr_basic_typing_formula
        (<[LVFree y := erase_ty τx]> Δ)
        (tret vf) (erase_ty τx →ₜ erase_ty (cty_open 0 y τ))).
  {
    apply expr_basic_typing_formula_models_iff.
    split.
    - apply lty_env_closed_insert_free. apply atom_store_to_lvar_store_closed.
    - split.
      + pose proof (ty_static_guard_basic_world _ _ _ _ Hstatic_app)
          as Hworld_app.
        apply basic_world_formula_models_iff in Hworld_app as [_ [Hscope _]].
        exact Hscope.
      + rewrite cty_open_preserves_erasure.
        eapply basic_tm_has_ltype_weaken.
        * subst Δ vf.
          apply basic_tm_has_ltype_of_atom_env_typing.
          exact (context_typing_wf_basic_typing
            Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
	        * apply insert_subseteq. apply not_elem_of_dom.
	          exact HyΔ.
  }
  assert (Hlc_vf : lc_value vf).
  {
    subst vf.
    apply lc_ret_iff_value.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  }
  assert (Hz_insert_env :
      LVFree z ∉ dom (<[LVFree y := erase_ty τx]> Δ)).
  {
    subst Δ. apply
      (ctx_erasure_under_inserted_erase_ctx_lty_env_fresh
        Σ Γ z y (erase_ty τx)).
    - clear -Hyz. congruence.
    - clear -Hz. better_set_solver.
  }
  assert (Hz_alias_fresh :
      z ∉ fv_value vf ∪ {[y]} ∪ fv_cty (cty_open 0 y τ)).
  {
    apply value_open_result_alias_fresh.
    subst vf. cbn [fv_value].
    clear -Hy_fresh Hz Hyz. better_set_solver.
  }
  pose proof (ty_denote_gas_tapp_fun_result_alias_from_static
    gas (<[LVFree y := erase_ty τx]> Δ) (cty_open 0 y τ)
    vf y z (erase_ty τx) (res_product n mz Hc)
    Hz_insert_env
    Hz_alias_fresh
    ltac:(apply map_lookup_insert)
    Hlc_vf
    Hres_prod Hfun_basic Hstatic_app Hsrc) as Htarget_alias.
  change (res_product n mz Hc ⊨ formula_open 0 y
    (ty_denote_gas gas
      (typed_lty_env_bind
        (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel)
        (erase_ty τx))
      τ (tapp_tm (tm_shift 0 (tret (vfvar z))) (vbvar 0)))).
  rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
    y gas (<[LVFree z := erase_ty (CTWand τx τ)]> Σrel)
    τ (erase_ty τx) (tret (vfvar z))).
  2:{
    apply lty_env_closed_insert_free.
    subst Σrel. apply relevant_env_closed. apply atom_store_to_lvar_store_closed.
  }
  2:{
    rewrite dom_insert_L. intros Hin.
    apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. inversion Hin. subst. clear -Hyz. congruence.
    - subst Σrel. apply relevant_env_wand_fresh_free in Hin;
        cbn [fv_tm fv_value]; clear -Hy_fresh Hin; better_set_solver.
  }
  2:{ cbn [fv_tm fv_value]. clear -Hyz. set_solver. }
  2:{ clear -Hy_fresh. better_set_solver. }
  2:{ constructor. constructor. }
  eapply res_models_ty_denote_gas_env_agree_on
    with (Σ1 := <[LVFree z := erase_ty τx →ₜ erase_ty (cty_open 0 y τ)]>
        (<[LVFree y := erase_ty τx]> Δ))
      (X := relevant_lvars (cty_open 0 y τ)
        (tapp_tm (tret (vfvar z)) (vfvar y))).
  - reflexivity.
  - apply lamd_lty_env_restrict_result_first_result_eq.
    + apply atom_store_to_lvar_store_closed.
    + eapply cty_lvars_open_body_closed_no_fresh.
      * apply soundness_lam_lc_lvars_context_ty_lvars_at_of_lc.
        exact Hτ_lc1.
      * intros HyD.
        apply lvars_fv_elem in HyD.
        rewrite context_ty_lvars_fv_at in HyD.
        clear -Hy_rest HyD. better_set_solver.
      * reflexivity.
    + exact Hyz.
    + clear -Hy_rest. better_set_solver.
    + subst vf. cbn [fv_value]. clear -Hz. better_set_solver.
  - exact Htarget_alias.
Qed.
