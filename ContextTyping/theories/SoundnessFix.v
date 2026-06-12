(** * ContextTyping.SoundnessFix

    Final Fix-case proof for the direct Fundamental theorem. *)

From Stdlib Require Import Lia.
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
From ContextTyping Require Import Typing SoundnessLam SoundnessFixBase
  SoundnessFixOpen SoundnessFixApply SoundnessFixSelf.

Local Ltac fix_union_left :=
  match goal with
  | H : ?x ∉ ?A ∪ ?B |- ?x ∉ ?A =>
      intros Hbad; apply H; apply elem_of_union_l; exact Hbad
  end.

Local Ltac fix_union_right :=
  match goal with
  | H : ?x ∉ ?A ∪ ?B |- ?x ∉ ?B =>
      intros Hbad; apply H; apply elem_of_union_r; exact Hbad
  end.

Local Ltac fix_build_union :=
  match goal with
  | H : ?x ∈ ?A |- ?x ∈ ?A => exact H
  | |- ?x ∈ ?A ∪ ?B =>
      first [apply elem_of_union_l; fix_build_union
            | apply elem_of_union_r; fix_build_union]
  end.

Local Ltac fix_union_side :=
  first
    [ assumption
    | fix_union_left
    | fix_union_right
    | intros Hbad;
      match goal with
      | H : ?x ∉ ?A ∪ ?B |- False => apply H
      | H : ?x ∉ ?A |- False => apply H
      end;
      repeat match goal with
      | H : _ ∈ _ ∪ _ |- _ => apply elem_of_union in H as [H|H]
      end;
      fix_build_union ].

Lemma fix_opened_arrow_result Σ Γ φx τ vf b t (L : aset)
    (m my : WfWorldT) y :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  m ⊨ ctx_denote_under Σ Γ ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ L ∪ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty (over_ty b φx) ∪ fv_cty τ ->
  my ⊨ ty_denote_gas
      (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      ((<[LVFree y := erase_ty (over_ty b φx)]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (over_ty b φx) (tret (vfvar y)) ->
  my ⊨ formula_open 0 y
    (ty_denote_gas (Nat.max (cty_depth (over_ty b φx)) (cty_depth τ))
      (typed_lty_env_bind
        (relevant_env (atom_env_to_lty_env (erase_ctx Γ))
          (CTArrow (over_ty b φx) τ) (tret (vfix (TBase b →ₜ t) vf)))
        (erase_ty (over_ty b φx)))
      τ
      (tapp_tm (tm_shift 0 (tret (vfix (TBase b →ₜ t) vf))) (vbvar 0))).
Proof.
  change (over_ty b φx) with (CTOver b φx) in *.
  intros Hτ Hwf Hbody_wf IH Hctx Hdom Hrestrict Hy Harg.
  set (τx := over_ty b φx) in *.
  assert (Hτx : erase_ty τx = TBase b) by (subst τx; reflexivity).
  assert (Harg_norm_full :
      my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
        ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
        τx (tret (vfvar y))).
  { change (CTOver b φx) with τx in Harg. exact Harg. }
  assert (Harg_norm_depth :
      my ⊨ ty_denote_gas (cty_depth τx)
        ((<[LVFree y := erase_ty τx]>
          (atom_env_to_lty_env (erase_ctx Γ))))
        τx (tret (vfvar y))).
  {
    rewrite <- (ty_denote_gas_saturate
      (Nat.max (cty_depth τx) (cty_depth τ))
      (<[LVFree y := erase_ty τx]> (atom_env_to_lty_env (erase_ctx Γ)))
      τx (tret (vfvar y))) by lia.
    exact Harg_norm_full.
  }
  assert (Hctx_comma :
      my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx))).
  {
    eapply (fix_arrow_open_arg_to_comma_ctx Σ Γ τx τ vf b t m my y);
      eauto using Harg_norm_depth.
    subst τx. fix_union_side.
  }
  assert (HyL : y ∉ L) by fix_union_side.
  pose proof (IH y HyL my Hctx_comma) as Hbody_arrow.
  pose proof (fix_self_rec_call_denotation
    Σ Γ φx τ vf b t L my y
    Hτ Hwf Hbody_wf IH ltac:(fix_union_side)
    Hctx_comma Harg_norm_full) as Hself.
  pose proof (fix_body_arrow_apply_self
    Σ Γ τx τ vf b t my y Hτx Hτ Hwf (Hbody_wf y HyL)
    ltac:(fix_union_side) Hctx_comma Hbody_arrow Hself) as Hunfolded.
  pose proof (fix_arrow_opened_app_static_guard_full
    Σ Γ τx τ vf b t my y Hwf ltac:(fix_union_side)
    Hctx_comma) as Hstatic_app.
  eapply fix_unfolded_result_to_opened_goal; eauto.
  fix_union_side.
Qed.

Lemma fundamental_fix_case Σ Γ φx τ vf b t (L : aset) :
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf))
    (CTArrow (over_ty b φx) τ) ->
  (forall y, y ∉ L ->
    context_typing_wf Σ
      (CtxComma Γ (CtxBind y (over_ty b φx)))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) ->
  (forall y, y ∉ L ->
    ctx_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx))) ⊫
      ty_denote_under Σ (CtxComma Γ (CtxBind y (over_ty b φx)))
        (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) ->
  ctx_denote_under Σ Γ ⊫
    ty_denote_under Σ Γ (CTArrow (over_ty b φx) τ)
      (tret (vfix (TBase b →ₜ t) vf)).
Proof.
Admitted.
