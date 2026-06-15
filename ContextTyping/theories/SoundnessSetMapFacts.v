(** * ContextTyping.SoundnessSetMapFacts

    Small Soundness-local fresh/domain helpers.  These facts mention contexts
    and typing-layer erasure, so they live above Denotation rather than in the
    generic set/map facts file. *)

From ContextStore Require Import Store.
From ContextBasicDenotation Require Import RelevantEnv.
From Denotation Require Import Context.
From ContextTyping Require Import Typing.

Ltac soundness_build_union :=
  first
    [ assumption
    | apply elem_of_union_l; soundness_build_union
    | apply elem_of_union_r; soundness_build_union
    | apply elem_of_singleton_2; reflexivity ].

Ltac soundness_notin_union :=
  let Hbad := fresh "Hbad" in
  intros Hbad;
  match goal with
  | H : ?x ∉ _ |- False =>
      apply H; soundness_build_union
  end.

Ltac soundness_fresh_norm :=
  cbn [fv_tm fv_value context_ty_lvars context_ty_lvars_at] in *;
  rewrite ?dom_insert_L, ?dom_union_L, ?dom_empty_L, ?dom_singleton_L in *.

Ltac soundness_fresh_solve :=
  soundness_fresh_norm; better_set_solver.

Ltac soundness_ctx_dom_solve :=
  ctx_erasure_under_norm; soundness_fresh_solve.

Lemma soundness_fresh_erase_ctx_from_context_union
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

Lemma soundness_relevant_env_arrow_value_fresh
    (Δ : lty_env) τx τ v x :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  LVFree x ∉ dom (relevant_env Δ (CTArrow τx τ) (tret v) : lty_env).
Proof.
  intros Hfresh.
  apply relevant_env_arrow_fresh_free; cbn [fv_tm fv_value];
    soundness_fresh_solve.
Qed.

Lemma soundness_relevant_env_wand_value_fresh
    (Δ : lty_env) τx τ v x :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  LVFree x ∉ dom (relevant_env Δ (CTWand τx τ) (tret v) : lty_env).
Proof.
  intros Hfresh.
  apply relevant_env_wand_fresh_free; cbn [fv_tm fv_value];
    soundness_fresh_solve.
Qed.

Lemma soundness_typed_bind_arrow_value_fresh
    (Δ : lty_env) τx τ v x T :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  x ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Δ (CTArrow τx τ) (tret v)) T)).
Proof.
  intros Hfresh Hbad.
  rewrite typed_lty_env_bind_lvars_fv_dom in Hbad.
  apply lvars_fv_elem in Hbad.
  eapply soundness_relevant_env_arrow_value_fresh; eauto.
Qed.

Lemma soundness_typed_bind_wand_value_fresh
    (Δ : lty_env) τx τ v x T :
  x ∉ fv_value v ∪ fv_cty τx ∪ fv_cty τ ->
  x ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Δ (CTWand τx τ) (tret v)) T)).
Proof.
  intros Hfresh Hbad.
  rewrite typed_lty_env_bind_lvars_fv_dom in Hbad.
  apply lvars_fv_elem in Hbad.
  eapply soundness_relevant_env_wand_value_fresh; eauto.
Qed.
