(** * ContextTyping.SoundnessLam

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
  TypeEquivCore
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing.

Local Notation LStoreOnT := (LStoreOn (V := value)) (only parsing).

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

Lemma ctx_erasure_under_agree_union_on_ty
    (Σ : gmap atom ty) Γ e τ :
  context_typing_wf Σ Γ e τ ->
  ty_env_agree_on (fv_cty τ) (Σ ∪ erase_ctx Γ) (ctx_erasure_under Σ Γ).
Proof.
  intros Hwf.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hwf) as Hwfctx.
  pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
  pose proof (basic_ctx_dom_fresh (dom Σ) Γ HbasicΓ) as HfreshΓ.
  pose proof (context_typing_wf_fv_cty_subset_erase_dom
    Σ Γ e τ Hwf) as Hτ.
  unfold ty_env_agree_on. intros y Hy.
  assert (HyΓ : y ∈ dom (erase_ctx Γ)) by (apply Hτ; exact Hy).
  pose proof (erase_ctx_lookup_ctx_erasure_under_of_basic_ctx
    Σ Γ y HbasicΓ HyΓ) as Herase.
  assert (HΣnone : Σ !! y = None).
  {
    apply not_elem_of_dom. intros HΣy.
    rewrite HdomΓ in HyΓ. set_solver.
  }
  transitivity ((erase_ctx Γ : gmap atom ty) !! y).
  - apply lookup_union_r. exact HΣnone.
  - exact Herase.
Qed.

Lemma lam_arrow_arg_type_open_shift_eq
    (Σ : tyctx) Γ τx τ e y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  cty_open 0 y (cty_shift 0 τx) = τx.
Proof.
  intros Hwf Hy.
  pose proof (context_typing_wf_context_ty Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  destruct Hτ as [Hτx _].
  apply cty_open_shift_from_lc_fresh.
  - eapply wf_context_ty_at_lc. exact Hτx.
  - ctx_erasure_under_norm_in Hy. better_set_solver.
Qed.

Lemma lam_wand_arg_type_open_shift_eq
    (Σ : tyctx) Γ τx τ e y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  cty_open 0 y (cty_shift 0 τx) = τx.
Proof.
  intros Hwf Hy.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret (vlam (erase_ty τx) e)) τx τ Hwf) as Hτx.
  apply cty_open_shift_from_lc_fresh.
  - eapply wf_context_ty_at_lc. exact Hτx.
  - ctx_erasure_under_norm_in Hy. better_set_solver.
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
    + split.
      * cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
        -- apply basic_ctx_bind.
           ++ ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ. better_set_solver.
           ++ eapply (wf_context_ty_at_mono_env
                0 (dom (erase_ctx Γ)) (dom Σ ∪ ctx_dom Γ)).
              ** rewrite HdomΓ. set_solver.
              ** exact Hτx.
        -- cbn [ctx_dom]. ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ.
           better_set_solver.
      * exists my. exact Hctx_comma.
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
    + split.
      * cbn [basic_ctx]. split; [exact HbasicΓ|]. split.
        -- apply basic_ctx_bind.
           ++ ctx_erasure_under_norm_in Hy. better_set_solver.
           ++ eapply (wf_context_ty_at_mono_env
                0 ∅ (dom Σ)).
              ** better_set_solver.
              ** exact Hτx.
        -- cbn [ctx_dom]. ctx_erasure_under_norm_in Hy. rewrite <- HdomΓ.
           better_set_solver.
      * exists my. exact Hctx_star.
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
  rewrite <- atom_store_to_lvar_store_insert in Hmid.
  eapply (ty_denote_gas_ret_fvar_insert_atom_env_agree_on
    (cty_depth τx) (erase_ctx Γ) (ctx_erasure_under Σ Γ) τx y my);
    [|exact Hmid].
  unfold ty_env_agree_on. intros z Hz.
  destruct (decide (z = y)) as [->|Hzy].
  - setoid_rewrite lookup_insert.
    repeat case_decide; congruence.
  - assert (HzΓ : z ∈ dom (erase_ctx Γ)).
    { set_solver. }
    transitivity ((erase_ctx Γ : gmap atom ty) !! z).
    + apply map_lookup_insert_ne. congruence.
    + transitivity ((ctx_erasure_under Σ Γ : gmap atom ty) !! z).
      * apply erase_ctx_lookup_ctx_erasure_under_of_basic_ctx; assumption.
      * symmetry. apply map_lookup_insert_ne. congruence.
Qed.

Lemma lam_arrow_open_arg_normalize
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
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
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros Hy Harg.
  assert (HΣarg_fresh :
      y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_dom_subset_direct
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
    intros Hyfv.
    apply lvars_fv_elem in Hyfv.
    pose proof (Hrel _ Hyfv) as Hatom.
    rewrite atom_store_to_lvar_store_dom in Hatom.
    rewrite <- lvars_fv_elem in Hatom.
    rewrite lvars_fv_of_atoms in Hatom.
    ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  assert (Hτarg_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. ctx_erasure_under_norm_in Hy. better_set_solver. }
  assert (Hearg_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  change (my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0)))) in Harg.
  rewrite (formula_open_ty_denote_gas_singleton 0 y
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact HΣarg_fresh || exact Hτarg_fresh || exact Hearg_fresh).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg.
  pose proof (ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx)))
    (lty_env_open_one 0 y
      (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ))
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y)))
    ltac:(better_set_solver)
    (arrow_arg_relevant_env_agree_open_one_core
      (atom_env_to_lty_env (erase_ctx Γ)) (erase_ty τx)
      y τx τ (tret (vlam (erase_ty τx) e))
      ltac:(ctx_erasure_under_norm_in Hy; better_set_solver))) as Hagree.
  rewrite Hagree in Harg.
  rewrite typed_lty_env_bind_open_current in Harg.
  2:{
    apply atom_env_to_lty_env_dom_free_notin.
    ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  2:{ apply atom_store_to_lvar_store_closed. }
  exact Harg.
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
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env (<[y:=erase_ty τx]> (ctx_erasure_under Σ Γ)))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  assert (Hmid :
      my ⊨ ty_denote_gas (cty_depth τx)
        ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
        τx (tret (vfvar y))).
  {
    rewrite ty_denote_gas_saturate in Harg by
      (rewrite cty_open_preserves_depth, cty_shift_preserves_depth; lia).
    rewrite cty_open_preserves_depth, cty_shift_preserves_depth in Harg.
    assert (Hτnorm :
        cty_open 0 y (cty_shift 0 τx) = τx).
    { eapply lam_arrow_arg_type_open_shift_eq; eauto. }
    rewrite Hτnorm in Harg.
    exact Harg.
  }
  clear Harg.
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
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  my ⊨ ctx_denote_under (Σ ∪ erase_ctx Γ) (CtxBind y τx).
Proof.
  intros Hwf Hctx_my Hdom Hrestrict Hy Harg.
  pose proof (lam_arrow_open_arg_to_bind_denotation
    Σ Γ τx τ e my y Hwf Hy Harg)
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
      ctx_erasure_under_norm_in Hy. better_set_solver.
    - exact (ctx_denote_under_basic_world Σ Γ my Hctx_my).
    - rewrite <- atom_store_to_lvar_store_insert.
      exact Hbind_den.
  }
  eapply ctx_bind_from_inserted_erasure_denotation.
  - ctx_erasure_under_norm_in Hy. better_set_solver.
  - pose proof (context_typing_wf_ctx Σ Γ
      (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf) as Hwfctx.
    pose proof (wf_ctx_under_basic Σ Γ Hwfctx) as HbasicΓ.
    pose proof (basic_ctx_erase_dom (dom Σ) Γ HbasicΓ) as HdomΓ.
    pose proof (basic_ctx_dom_fresh (dom Σ) Γ HbasicΓ) as HfreshΓ.
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
    {
      apply not_elem_of_dom. intros HΣz.
      rewrite HdomΓ in HzΓ. better_set_solver.
    }
    transitivity ((erase_ctx Γ : gmap atom ty) !! z).
    + apply lookup_union_r. exact HΣnone.
    + exact Herase.
  - exact Hworld_bind.
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
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
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
	  unfold ty_static_guard_formula in Hstatic_rel.
	  repeat rewrite res_models_and_iff in Hstatic_rel.
	  destruct Hstatic_rel as [Hwf_app [Hworld_app Hbasic_app]].
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
	  assert (Hbody : body_tm e).
	  {
	    pose proof (typing_tm_lc _ _ _
	      (context_typing_wf_basic_typing
	        Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf))
	      as Hlc_lam.
	    inversion Hlc_lam; subst.
	    apply lc_lam_iff_body in H0. exact H0.
	  }
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
	  eapply tm_equiv_total; eauto.
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
  assert (Hbody : body_tm e).
  {
    pose proof (typing_tm_lc _ _ _
      (context_typing_wf_basic_typing
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf))
      as Hlc_lam.
    inversion Hlc_lam; subst.
    apply lc_lam_iff_body in H0. exact H0.
  }
	  assert (Hy_dom : y ∈ world_dom (my : WorldT)).
	  {
	    pose proof Hstatic as Hstatic_app.
	    unfold ty_static_guard_formula in Hstatic_app.
	    repeat rewrite res_models_and_iff in Hstatic_app.
	    destruct Hstatic_app as [_ [Hworld_app Hbasic_app]].
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
	  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
	      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
		  intros Hwf Hy Hmid Hstatic.
  set (elam := tret (vlam (erase_ty τx) e)).
		  pose proof (lam_arrow_result_mid_app_denotation
		    Σ Γ τx τ e my y Hwf Hy Hmid Hstatic) as Happ_mid.
  assert (Hlc_elam : lc_tm elam).
  {
    subst elam.
    eapply typing_tm_lc.
    exact (context_typing_wf_basic_typing
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) Hwf).
  }
  assert (HΣfresh :
      y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTArrow τx τ) elam)
          (erase_ty τx)))).
  {
    subst elam.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_dom_subset_direct
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTArrow τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
    intros Hyfv.
    apply lvars_fv_elem in Hyfv.
    pose proof (Hrel _ Hyfv) as Hatom.
    rewrite atom_store_to_lvar_store_dom in Hatom.
    rewrite <- lvars_fv_elem in Hatom.
    rewrite lvars_fv_of_atoms in Hatom.
    ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  assert (Htmfresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 elam) (vbvar 0))).
  {
    subst elam.
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value]. set_solver.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 y
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTArrow τx τ) elam)
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 elam) (vbvar 0)))
    by (exact HΣfresh || exact Htmfresh || set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc_elam.
  subst elam.
  assert (Happ_mid_open :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 y
          (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ))
            (erase_ty τx)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current.
    - exact Happ_mid.
    - apply atom_env_to_lty_env_dom_free_notin.
      ctx_erasure_under_norm_in Hy. better_set_solver.
    - apply atom_store_to_lvar_store_closed.
  }
  eapply ty_equiv_arrow_result_tgt_goal.
  - exact Hlc_elam.
  - set_solver.
  - exact Happ_mid_open.
Qed.

Lemma lam_body_to_opened_arrow_result
    (Σ : tyctx) Γ τx τ e
    (my : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
	  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
	    ({0 ~> y} τ) (e ^^ y) ->
	  my ⊨ ty_static_guard_formula
	    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
	    (cty_open 0 y τ)
	    (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y)) ->
	  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
		  intros Hwf Hy Hbody Hstatic.
		  pose proof (lam_body_to_arrow_result_mid
		    Σ Γ τx τ e my y Hwf Hy Hbody) as Hmid.
		  eapply lam_arrow_result_mid_to_opened_goal; eauto.
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
	      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
	  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
	      τ
	      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
  intros Hwf IH Hctx Hdom Hrestrict Hy Harg.
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (lam_arrow_open_arg_to_comma_ctx Σ Γ τx τ e m my y);
      eauto.
    set_solver.
  }
  assert (HyL : y ∉ L) by set_solver.
	  pose proof (IH y HyL my Hctx_comma) as Hbody.
	  pose proof (lam_arrow_opened_app_static_guard_full
		    Σ Γ τx τ e my y Hwf ltac:(set_solver) Hctx_comma) as Hstatic_app.
	  eapply (lam_body_to_opened_arrow_result Σ Γ τx τ e my y);
	    eauto.
  set_solver.
Qed.

Lemma lamd_wand_open_arg_to_bind_denotation
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  context_typing_wf Σ Γ
    (tret (vlam (erase_ty τx) e)) (CTWand τx τ) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  n ⊨ ty_denote_gas (cty_depth τx)
    (atom_env_to_lty_env
      (<[y := erase_ty τx]> (store_restrict Σ (fv_cty τx))))
    τx (tret (vfvar y)).
Proof.
  intros Hwf Hy Harg.
  pose proof (context_typing_wf_wand_arg_global Σ Γ
    (tret (vlam (erase_ty τx) e)) τx τ Hwf) as Hτx_global.
  rewrite ty_denote_gas_saturate in Harg by
    (rewrite cty_open_preserves_depth, cty_shift_preserves_depth; lia).
  rewrite cty_open_preserves_depth, cty_shift_preserves_depth in Harg.
  assert (Hτnorm :
      cty_open 0 y (cty_shift 0 τx) = τx).
  { eapply lam_wand_arg_type_open_shift_eq; eauto. }
  rewrite Hτnorm in Harg.
  rewrite <- atom_store_to_lvar_store_insert in Harg.
  eapply (ty_denote_gas_ret_fvar_insert_atom_env_agree_on
    (cty_depth τx) (erase_ctx Γ) (store_restrict Σ (fv_cty τx)) τx y n);
    [|exact Harg].
  unfold ty_env_agree_on. intros z Hz.
  destruct (decide (z = y)) as [->|Hzy].
  - setoid_rewrite lookup_insert.
    repeat case_decide; congruence.
  - exfalso.
    pose proof (basic_context_ty_fv_subset ∅ τx Hτx_global) as Hτxfv.
    assert (Hzτx : z ∈ fv_cty τx) by better_set_solver.
    pose proof (Hτxfv z Hzτx). better_set_solver.
Qed.

Lemma lamd_wand_open_arg_normalize
    (Σ : tyctx) Γ τx τ e
    (n : WfWorldT) y :
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ ->
  n ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)).
Proof.
  intros Hy Harg.
  assert (HΣarg_fresh :
      y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
          (erase_ty τx)))).
  {
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_dom_subset_direct
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
    intros Hyfv.
    apply lvars_fv_elem in Hyfv.
    pose proof (Hrel _ Hyfv) as Hatom.
    rewrite atom_store_to_lvar_store_dom in Hatom.
    rewrite <- lvars_fv_elem in Hatom.
    rewrite lvars_fv_of_atoms in Hatom.
    ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  assert (Hτarg_fresh : y ∉ fv_cty (cty_shift 0 τx)).
  { rewrite cty_shift_fv. ctx_erasure_under_norm_in Hy. better_set_solver. }
  assert (Hearg_fresh : y ∉ fv_tm (tret (vbvar 0))).
  { cbn [fv_tm fv_value]. better_set_solver. }
  change (n ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0)))) in Harg.
  rewrite (formula_open_ty_denote_gas_singleton 0 y
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
      (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg
    by (exact HΣarg_fresh || exact Hτarg_fresh || exact Hearg_fresh).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg.
  pose proof (ty_denote_gas_env_agree_on
    (Nat.max (cty_depth τx) (cty_depth τ))
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx)))
    (lty_env_open_one 0 y
      (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ))
        (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τx))
      (tret (vfvar y)))
    ltac:(better_set_solver)
    (wand_arg_relevant_env_agree_open_one_core
      (atom_env_to_lty_env (erase_ctx Γ)) (erase_ty τx)
      y τx τ (tret (vlam (erase_ty τx) e))
      ltac:(ctx_erasure_under_norm_in Hy; better_set_solver))) as Hagree.
  rewrite Hagree in Harg.
  rewrite typed_lty_env_bind_open_current in Harg.
  2:{
    apply atom_env_to_lty_env_dom_free_notin.
    ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  2:{ apply atom_store_to_lvar_store_closed. }
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
	      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
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
      apply elem_of_dom in HyΣ as [T HyΣ].
      apply storeA_restrict_lookup_some in HyΣ as [_ HyΣ].
      apply elem_of_dom_2 in HyΣ.
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
  { ctx_erasure_under_norm_in Hy. better_set_solver. }
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
	    unfold ty_static_guard_formula in Hstatic_rel.
	    repeat rewrite res_models_and_iff in Hstatic_rel.
	    destruct Hstatic_rel as [Hwf_app [Hworld_app Hbasic_app]].
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
    assert (Hbody_lc : body_tm e).
    {
      pose proof (typing_tm_lc _ _ _
        (context_typing_wf_basic_typing
          Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf))
        as Hlc_lam.
      inversion Hlc_lam; subst.
      apply lc_lam_iff_body in H0. exact H0.
    }
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
    eapply tm_equiv_total; eauto.
    intros σ v Hσ.
    pose proof (tm_equiv_lam_app_body (erase_ty τx) e y my
      Hclosed Hbody_lc ltac:(ctx_erasure_under_norm_in Hy; better_set_solver)
      Hy_dom σ v Hσ) as [Happ_body Hbody_app].
    split; [exact Hbody_app|exact Happ_body].
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
  assert (Hbody_lc : body_tm e).
  {
    pose proof (typing_tm_lc _ _ _
      (context_typing_wf_basic_typing
        Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf))
      as Hlc_lam.
    inversion Hlc_lam; subst.
    apply lc_lam_iff_body in H0. exact H0.
  }
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
    ctx_erasure_under_norm_in Hy. better_set_solver.
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
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
  intros Hwf Hy Happ_mid.
  set (elam := tret (vlam (erase_ty τx) e)).
  assert (Hlc_elam : lc_tm elam).
  {
    subst elam.
    eapply typing_tm_lc.
    exact (context_typing_wf_basic_typing
      Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) Hwf).
  }
  assert (HΣfresh :
      y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
            (CTWand τx τ) elam)
          (erase_ty τx)))).
  {
    subst elam.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    pose proof (relevant_env_dom_subset_direct
      (atom_env_to_lty_env (erase_ctx Γ))
      (CTWand τx τ) (tret (vlam (erase_ty τx) e))) as Hrel.
    intros Hyfv.
    apply lvars_fv_elem in Hyfv.
    pose proof (Hrel _ Hyfv) as Hatom.
    rewrite atom_store_to_lvar_store_dom in Hatom.
    rewrite <- lvars_fv_elem in Hatom.
    rewrite lvars_fv_of_atoms in Hatom.
    ctx_erasure_under_norm_in Hy. better_set_solver.
  }
  assert (Htmfresh :
      y ∉ fv_tm (tapp_tm (tm_shift 0 elam) (vbvar 0))).
  {
    subst elam.
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value]. better_set_solver.
  }
  rewrite (formula_open_ty_denote_gas_singleton 0 y
    (Nat.max (cty_depth τx) (cty_depth τ))
    (typed_lty_env_bind
      (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
        (CTWand τx τ) elam)
      (erase_ty τx))
    τ (tapp_tm (tm_shift 0 elam) (vbvar 0)))
    by (exact HΣfresh || exact Htmfresh || better_set_solver).
  rewrite open_tapp_tm_shift_bvar0_lc by exact Hlc_elam.
  subst elam.
  assert (Happ_mid_open :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        (lty_env_open_one 0 y
          (typed_lty_env_bind (atom_env_to_lty_env (erase_ctx Γ))
            (erase_ty τx)))
        (cty_open 0 y τ)
        (tapp_tm (tret (vlam (erase_ty τx) e)) (vfvar y))).
  {
    rewrite typed_lty_env_bind_open_current.
    - exact Happ_mid.
    - apply atom_env_to_lty_env_dom_free_notin.
      ctx_erasure_under_norm_in Hy. better_set_solver.
    - apply atom_store_to_lvar_store_closed.
  }
  eapply ty_equiv_wand_result_tgt_goal.
  - exact Hlc_elam.
  - better_set_solver.
  - exact Happ_mid_open.
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
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) ->
  res_product n m Hc ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTWand τx τ) (tret (vlam (erase_ty τx) e)))
        (erase_ty τx))
      τ
      (tapp_tm (tm_shift 0 (tret (vlam (erase_ty τx) e))) (vbvar 0))).
Proof.
  intros Hwf IH Hctx Hdom Hy Harg.
  assert (Hctx_star :
      res_product n m Hc ⊨ ctx_denote_under Σ (CtxStar Γ (CtxBind y τx))).
  {
    eapply (lamd_open_arg_to_star_ctx Σ Γ τx τ e m n y Hc);
      eauto.
    set_solver.
  }
  assert (HyL : y ∉ L) by set_solver.
  pose proof (IH y HyL (res_product n m Hc) Hctx_star) as Hbody.
	  pose proof (lam_wand_opened_app_static_guard_full
	    Σ Γ τx τ e (res_product n m Hc) y
	    Hwf ltac:(set_solver) Hctx_star) as Hstatic_app.
  pose proof (lamd_body_to_wand_result_mid
    Σ Γ τx τ e (res_product n m Hc) y
    Hwf ltac:(set_solver) Hbody Hstatic_app) as Happ_mid.
  eapply lamd_wand_result_mid_to_opened_goal; eauto.
  set_solver.
Qed.
