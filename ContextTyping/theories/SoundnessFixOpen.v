(** * ContextTyping.SoundnessFixOpen

    Opened-argument and unfolded-result support for the Fix case. *)

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
  TypeEquivArrow
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLamBase SoundnessLamArrow
  SoundnessLamWand SoundnessFixBase.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

Local Lemma fix_open_fresh_erase_ctx_from_fix_union
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (erase_ctx Γ).
Proof.
  intros Hy.
  eapply ctx_erasure_under_notin_erase_ctx.
  intros Hyctx.
  apply Hy.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_l.
  apply elem_of_union_r.
  exact Hyctx.
Qed.

Local Lemma fix_open_fresh_ctx_erasure_under_from_fix_union
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom (ctx_erasure_under Σ Γ).
Proof.
  intros Hy Hyctx.
  apply Hy.
  clear -Hyctx. set_solver.
Qed.

Local Lemma fix_open_fresh_env_erase_ctx_from_fix_union
    (Σ : tyctx) Γ y A B C :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ A ∪ B ∪ C ->
  y ∉ dom Σ ∪ dom (erase_ctx Γ).
Proof.
  intros Hy Hin.
  apply elem_of_union in Hin as [HyΣ|HyΓ].
  - apply Hy. clear -HyΣ. set_solver.
  - eapply fix_open_fresh_erase_ctx_from_fix_union; eauto.
Qed.

Lemma fix_arrow_opened_app_static_guard_full
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)).
Proof.
  intros Hwf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx Hτ].
    split.
    + unfold wf_ctx_under. cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
      * apply basic_ctx_bind.
        -- rewrite <- HdomΓ.
           eapply fix_open_fresh_env_erase_ctx_from_fix_union. exact Hy.
        -- eapply (wf_context_ty_at_mono_env
             0 (dom (erase_ctx Γ)) (dom Σ ∪ ctx_dom Γ)).
           ++ rewrite HdomΓ. better_set_solver.
           ++ exact Hτx.
      * cbn [ctx_dom]. rewrite <- HdomΓ.
        apply elem_of_disjoint. intros a Ha Hay.
        apply elem_of_singleton in Hay. subst a.
        eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy. exact Ha.
    + split.
      * eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        -- rewrite erase_ctx_comma_bind_dom. reflexivity.
        -- apply wf_context_ty_at_open_at.
           ++ eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
           ++ exact Hτ.
      * rewrite cty_open_preserves_erasure.
        replace (erase_ctx (CtxComma Γ (CtxBind y τx)))
          with (<[y := erase_ty τx]> (erase_ctx Γ)).
        -- apply basic_typing_tapp_tm_fvar_insert.
           ++ eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
           ++ exact (context_typing_wf_basic_typing Σ Γ
                (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf).
        -- symmetry. apply erase_ctx_comma_bind_fresh.
           eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
  }
  eapply context_typing_wf_denot_static_guard_comma_bind_insert; eauto.
  eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
Qed.

Lemma fix_arrow_open_arg_normalize
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  assert (Hlcτx : lc_context_ty τx).
  {
    apply (context_typing_wf_arrow_arg_lc Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) τx τ).
    exact Hwf.
  }
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
    (tret (vfix (TBase b →ₜ t) vf)) my y Harg).
Qed.

Lemma fix_arrow_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Harg.
  eapply ty_denote_gas_ret_fvar_insert_ctx_erasure_under.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
    exact (wf_ctx_under_basic Σ Γ Hwfctx).
  - pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτ.
    cbn [wf_context_ty_at] in Hτ.
    destruct Hτ as [Hτx _].
    eapply wf_context_ty_at_fv_subset. exact Hτx.
  - exact Harg.
Qed.

Lemma fix_arrow_open_arg_to_bind_ctx
    (Σ : tyctx) Γ τx τ vf b t
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  my ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (fix_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ vf b t my y Hwf Harg)
    as Hbind_den.
  assert (Hworld_bind :
      my ⊨ basic_world_formula
        (atom_env_to_lty_env (<[y := erase_ty τx]> (ctx_erasure_under Σ Γ)))).
  {
    replace (atom_env_to_lty_env (<[y := erase_ty τx]> (ctx_erasure_under Σ Γ)))
      with (<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (ctx_erasure_under Σ Γ))).
    2:{ symmetry. apply atom_store_to_lvar_store_insert. }
    eapply (basic_world_insert_of_arg
      (atom_env_to_lty_env (ctx_erasure_under Σ Γ)) τx y
      (erase_ty τx) (cty_depth τx)); eauto.
    - apply atom_env_to_lty_env_dom_free_notin.
      eapply fix_open_fresh_ctx_erasure_under_from_fix_union. exact Hy.
    - exact (ctx_denote_under_basic_world Σ Γ my Hctx_my).
    - rewrite <- atom_store_to_lvar_store_insert.
      exact Hbind_den.
  }
	  eapply ctx_bind_from_inserted_erasure_denotation.
	  - eapply fix_open_fresh_ctx_erasure_under_from_fix_union. exact Hy.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτwf.
    cbn [wf_context_ty_at] in Hτwf.
    destruct Hτwf as [Hτx _].
    eapply ty_env_agree_ctx_erasure_under_of_basic_ctx.
    + exact HbasicΓ.
    + eapply wf_context_ty_at_fv_subset. exact Hτx.
  - exact Hworld_bind.
  - exact Hbind_den.
Qed.

Lemma fix_arrow_open_arg_to_comma_ctx
    (Σ : tyctx) Γ τx τ vf b t
    (m my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (cty_depth τx)
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      τx (tret (vfvar y)) ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)).
Proof.
  intros Hwf Hctx Hdom Hrestrict Hy Harg.
  pose proof (context_typing_wf_ctx Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  assert (Hle : m ⊑ my).
  { rewrite <- Hrestrict. apply res_restrict_le. }
  assert (Hctx_my : my ⊨ ctx_denote_under Σ Γ).
  { eapply res_models_kripke; eauto. }
  eapply ctx_denote_under_comma_intro; [exact HbasicΓ|exact Hctx_my|].
  eapply fix_arrow_open_arg_to_bind_ctx; eauto.
Qed.

Lemma fix_tapp_unfold_tm_equiv_on
    b t vf y (my : WfWorldT) :
  body_val vf ->
  y ∈ world_dom (my : WorldT) ->
  wfworld_closed_on
    (fv_tm (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) ∪
     fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
       (vfix (TBase b →ₜ t) vf))) my ->
  tm_equiv_on my
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))
    (tapp_tm (tret (open_value 0 (vfvar y) vf))
      (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hbody Hy_dom Hclosed σ v Hσ.
  pose proof (tm_equiv_fix_unfold (TBase b →ₜ t) vf y my
    Hclosed Hbody Hy_dom σ v Hσ) as [Hfix_unfold Hunfold_fix].
  split; [exact Hfix_unfold|exact Hunfold_fix].
Qed.

Lemma fix_unfolded_result_to_opened_goal
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (open_value 0 (vfvar y) vf))
      (vfix (TBase b →ₜ t) vf)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    (<[LVFree y := erase_ty τx]>
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret (vfix (TBase b →ₜ t) vf))))
    (cty_open 0 y τ)
    (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)).
Proof.
  intros Hwf Hy Hunfolded Hstatic.
  set (efix := tret (vfix (TBase b →ₜ t) vf)).
  assert (Hlc_efix : lc_tm efix).
  {
    subst efix.
    exact (context_typing_wf_lc_tm
      Σ Γ (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf).
  }
  assert (Hbody_vf : body_val vf).
  {
    subst efix.
    apply lc_ret_iff_value in Hlc_efix.
    apply lc_fix_iff_body in Hlc_efix.
    exact Hlc_efix.
  }
  assert (Hτ_lc1 : cty_lc_at 1 τ).
  {
    apply (context_typing_wf_arrow_result_lc1 Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) τx τ).
    exact Hwf.
  }
  assert (Hzero_unfolded :
      my ⊨ ty_denote_gas 0
        (<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        (cty_open 0 y τ)
        (tapp_tm (tret (open_value 0 (vfvar y) vf))
          (vfix (TBase b →ₜ t) vf))).
  {
    apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hunfolded.
  }
  assert (Hclosed_fix :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))) my).
  { eapply ty_static_guard_wfworld_closed_on_term. exact Hstatic. }
  assert (Hclosed_unfolded :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
          (vfix (TBase b →ₜ t) vf))) my).
  {
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    eapply ty_denote_gas_guard_of_zero. exact Hzero_unfolded.
  }
  assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) ∪
         fv_tm (tapp_tm (tret (open_value 0 (vfvar y) vf))
           (vfix (TBase b →ₜ t) vf))) my).
  { apply wfworld_closed_on_union; assumption. }
  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
  {
    pose proof (ty_static_guard_fv_tm_subset _ _ _ _ Hstatic)
      as Hfv_app.
    apply Hfv_app.
    rewrite fv_tapp_tm. cbn [fv_tm fv_value]. better_set_solver.
  }
  pose proof (fix_tapp_unfold_tm_equiv_on
    b t vf y my Hbody_vf Hy_dom Hclosed) as Heq.
  assert (Hzero_fix :
      my ⊨ ty_denote_gas 0
        (<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))).
  {
	    pose proof (ty_denote_gas_guard_of_zero
	      (<[LVFree y := erase_ty τx]>
	        (atom_env_to_lty_env (erase_ctx Γ)))
	      (cty_open 0 y τ)
	      (tapp_tm (tret (open_value 0 (vfvar y) vf))
	        (vfix (TBase b →ₜ t) vf)) my Hzero_unfolded)
	      as Hguard_unfolded.
	    repeat rewrite res_models_and_iff in Hguard_unfolded.
	    destruct Hguard_unfolded as [_ [_ [_ Htotal_unfolded]]].
	    assert (Heq_unfold_fix :
	        tm_equiv_on my
	          (tapp_tm (tret (open_value 0 (vfvar y) vf))
	            (vfix (TBase b →ₜ t) vf))
	          (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))).
	    {
	      intros σ v Hσ.
	      specialize (Heq σ v Hσ) as [Hfix_unfold Hunfold_fix].
	      split; [exact Hunfold_fix|exact Hfix_unfold].
	    }
			    eapply ty_denote_gas_zero_transport_static_tm_equiv.
		    - exact Heq_unfold_fix.
		    - intros σ Hσ.
		      pose proof (tm_total_equiv_fix_unfold (TBase b →ₜ t) vf y my
		        Hclosed Hbody_vf Hy_dom σ Hσ) as Htotal_fix_unfold.
		      split; [exact (proj2 Htotal_fix_unfold)|exact (proj1 Htotal_fix_unfold)].
			    - exact Hstatic.
		    - apply lc_tapp_tm; [exact Hlc_efix|constructor].
		    - eapply ty_static_guard_fv_tm_subset. exact Hstatic.
		    - exact Hzero_unfolded.
	  }
	  assert (Hfix_open :
	      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
	        (<[LVFree y := erase_ty τx]>
	          (atom_env_to_lty_env (erase_ctx Γ)))
	        (cty_open 0 y τ)
	        (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y))).
		  {
		    pose proof (ty_denote_gas_guard_of_zero
		      (<[LVFree y := erase_ty τx]>
		        (atom_env_to_lty_env (erase_ctx Γ)))
		      (cty_open 0 y τ)
		      (tapp_tm (tret (open_value 0 (vfvar y) vf))
		        (vfix (TBase b →ₜ t) vf)) my Hzero_unfolded)
		      as Hguard_unfolded.
		    pose proof (ty_denote_gas_guard_of_zero
		      (<[LVFree y := erase_ty τx]>
		        (atom_env_to_lty_env (erase_ctx Γ)))
		      (cty_open 0 y τ)
		      (tapp_tm (tret (vfix (TBase b →ₜ t) vf)) (vfvar y)) my
	      Hzero_fix) as Hguard_fix.
	    repeat rewrite res_models_and_iff in Hguard_unfolded.
	    repeat rewrite res_models_and_iff in Hguard_fix.
	    destruct Hguard_unfolded as [_ [_ [_ Htotal_unfolded]]].
		    destruct Hguard_fix as [_ [_ [_ Htotal_fix]]].
				    eapply ty_denote_gas_tm_equiv.
				    - refine (conj _ (conj _ (conj _ _))).
					      + intros σ0 v0 Hσ0. symmetry. exact (Heq σ0 v0 Hσ0).
						      + eapply tm_total_equiv_of_total_formulas; eauto.
						      + exact Hzero_unfolded.
					      + exact Hzero_fix.
				    - exact Hunfolded.
		  }
	  eapply ty_equiv_arrow_result_tgt_goal.
	  - exact Hlc_efix.
	  - clear -Hy. set_solver.
	  - apply arrow_result_open_vars_subset; [exact Hτ_lc1|clear -Hy; set_solver].
	  - exact Hfix_open.
Qed.

Lemma fix_unfolded_app_static_guard_full
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  context_typing_wf Σ
    (CtxComma Γ (CtxBind y τx))
    (tret ({0 ~> vfvar y} vf))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ)) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_static_guard_formula
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
    (tapp_tm (tret (open_value 0 (vfvar y) vf))
      (vfix (TBase b →ₜ t) vf)).
Proof.
  intros Hτx Hτ Hwf Hbody_wf Hy Hctx_comma.
  assert (Hwf_app :
      context_typing_wf Σ (CtxComma Γ (CtxBind y τx))
        (tapp_tm (tret (open_value 0 (vfvar y) vf))
          (vfix (TBase b →ₜ t) vf))
        (cty_open 0 y τ)).
  {
    unfold context_typing_wf.
    pose proof (context_typing_wf_ctx Σ
      (CtxComma Γ (CtxBind y τx))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
      Hbody_wf) as Hwfctx_body.
    pose proof (context_typing_wf_context_ty Σ Γ
      (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf) as Hτ_outer.
    cbn [wf_context_ty_at] in Hτ_outer.
    destruct Hτ_outer as [_ Hτres_outer].
    split.
    - exact Hwfctx_body.
    - split.
      + eapply (wf_context_ty_at_mono_env
          0 (dom (erase_ctx Γ) ∪ {[y]})
          (dom (erase_ctx (CtxComma Γ (CtxBind y τx))))).
        * rewrite erase_ctx_comma_bind_dom. reflexivity.
        * apply wf_context_ty_at_open_at.
          -- eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
          -- exact Hτres_outer.
      + rewrite cty_open_preserves_erasure.
        eapply basic_typing_tapp_tm.
        * pose proof (context_typing_wf_basic_typing Σ
            (CtxComma Γ (CtxBind y τx))
            (tret ({0 ~> vfvar y} vf))
            (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
            Hbody_wf) as Hbody_basic.
          change (erase_ctx (CtxComma Γ (CtxBind y τx)) ⊢ₑ
            tret (open_value 0 (vfvar y) vf)
            ⋮ (erase_ty (fix_rec_call_ty b y τx τ) →ₜ
               erase_ty (cty_open 0 y τ))) in Hbody_basic.
          rewrite cty_open_preserves_erasure in Hbody_basic.
          exact Hbody_basic.
        * pose proof (context_typing_wf_basic_typing Σ Γ
            (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) Hwf)
            as Hfix_basic_tm.
          inversion Hfix_basic_tm; subst.
          match goal with
          | Hfix_val : erase_ctx Γ ⊢ᵥ
              vfix _ vf ⋮ _ |- _ =>
              eapply basic_typing_weaken_value; [exact Hfix_val|]
          end.
          rewrite erase_ctx_comma_bind_fresh.
          -- apply insert_subseteq.
             apply not_elem_of_dom.
             eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
          -- eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
  }
  eapply context_typing_wf_denot_static_guard_comma_bind_insert; eauto.
  eapply fix_open_fresh_erase_ctx_from_fix_union. exact Hy.
Qed.
