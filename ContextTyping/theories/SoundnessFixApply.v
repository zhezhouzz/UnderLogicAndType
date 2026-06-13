(** * ContextTyping.SoundnessFixApply

    Applying the opened Fix body arrow to the recursive self value. *)

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
  TypeEquivFiberTransport
  TypeEquivBody
  TypeEquivArrow
  TypeEquivWand
  TypeEquiv
  ConstDenote.
From ContextTyping Require Import Typing SoundnessLam SoundnessFixBase
  SoundnessFixOpen.

Local Ltac fix_apply_build_union :=
  first
    [ assumption
    | apply elem_of_union_l; fix_apply_build_union
    | apply elem_of_union_r; fix_apply_build_union
    | apply elem_of_singleton_2; reflexivity ].

Local Ltac fix_apply_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  match goal with
  | H : ?x ∉ _ |- False =>
      apply H; fix_apply_build_union
  end.

Local Lemma fix_apply_fresh_erase_ctx_from_fix_union
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

Lemma fix_body_arrow_apply_self
    (Σ : tyctx) Γ τx τ vf b t
    (my : WfWorldT) y :
  erase_ty τx = TBase b ->
  erase_ty τ = t ->
  context_typing_wf Σ Γ
    (tret (vfix (TBase b →ₜ t) vf)) (CTArrow τx τ) ->
  (context_typing_wf Σ
      (CtxComma Γ (CtxBind y τx))
      (tret ({0 ~> vfvar y} vf))
      (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))) ->
  y ∉ dom Σ ∪ dom (ctx_erasure_under Σ Γ) ∪ fv_value vf ∪
      fv_cty τx ∪ fv_cty τ ->
  my ⊨ ctx_denote_under Σ (CtxComma Γ (CtxBind y τx)) ->
  my ⊨ ty_denote_under Σ (CtxComma Γ (CtxBind y τx))
    (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))
    (tret ({0 ~> vfvar y} vf)) ->
  my ⊨ ty_denote_gas (cty_depth (fix_rec_call_ty b y τx τ))
      ((<[LVFree y := erase_ty τx]>
        (atom_env_to_lty_env (erase_ctx Γ))))
      (fix_rec_call_ty b y τx τ)
      (tret (vfix (TBase b →ₜ t) vf)) ->
  my ⊨ ty_denote_gas (Nat.max (cty_depth τx) (cty_depth τ))
    ((<[LVFree y := erase_ty τx]>
      (atom_env_to_lty_env (erase_ctx Γ))))
    (cty_open 0 y τ)
      (tapp_tm (tret (open_value 0 (vfvar y) vf))
        (vfix (TBase b →ₜ t) vf)).
Proof.
  (* Result-first Arrow denotation adds an outer function-result binder
     before the old argument binder. The old proof below opened the body
     arrow directly at the recursive self argument. The replacement proof
     should first bind the opened body value itself, then reuse the old
     recursive-self application argument inside [arrow_value_denote_gas]. *)
Admitted.
