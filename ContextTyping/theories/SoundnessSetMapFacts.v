(** * ContextTyping.SoundnessSetMapFacts

    Small Soundness-local fresh/domain helpers.  These facts mention contexts
    and typing-layer erasure, so they live above Denotation rather than in the
    generic set/map facts file. *)

From ContextStore Require Import Store.
From ContextBasicDenotation Require Import RelevantEnv BasicTypingFormula.
From Denotation Require Import Context.
From ContextTyping Require Import Typing.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).

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

(** ** Regular facts extracted from typing/soundness definitions

    These lemmas are intentionally not pure stdpp facts.  They turn
    repository-specific hypotheses, such as [context_typing_wf] and
    [ctx_denote_under], into the stdpp side conditions that later proof
    scripts hand to the folder-local set/map solvers. *)

Lemma soundness_wf_ret_persist_obs_subset
    Σ Γ τ v :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  fv_cty τ ∪ fv_value v ⊆ dom (erase_ctx Γ).
Proof.
  intros Hwf a Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - apply context_typing_wf_fv_cty_subset_erase_dom with
      (Σ := Σ) (e := tret v) (τ := CTPersist τ) in Hwf.
    cbn [fv_cty context_ty_lvars context_ty_lvars_at] in Hwf.
    exact (Hwf a Ha).
  - pose proof (context_typing_wf_fv_tm_subset Σ Γ (tret v)
      (CTPersist τ) Hwf) as Hfv.
    cbn [fv_tm] in Hfv.
    exact (Hfv a Ha).
Qed.

Lemma soundness_wf_ret_persist_observed_world
    Σ Γ τ v (m : WfWorldT) :
  context_typing_wf Σ Γ (tret v) (CTPersist τ) ->
  m ⊨ ctx_denote_under Σ Γ ->
  fv_cty τ ∪ fv_value v ⊆ world_dom (m : WorldT).
Proof.
  intros Hwf Hctx.
  pose proof (soundness_wf_ret_persist_obs_subset
    Σ Γ τ v Hwf) as Hobs.
  pose proof (ctx_denote_under_basic_world Σ Γ m Hctx) as Hworld.
  pose proof (basic_world_formula_atom_env_dom_subset
    (ctx_erasure_under Σ Γ) m Hworld) as Hctxdom.
  ctx_erasure_under_norm_in Hctxdom.
  intros a Ha.
  pose proof (Hobs a Ha) as Haobs.
  apply Hctxdom.
  ctx_erasure_under_norm.
  set_solver.
Qed.

Ltac soundness_regular_observed_world :=
  match goal with
  | Hwf : context_typing_wf ?Σ ?Γ (tret ?v) (CTPersist ?τ),
    Hctx : ?m ⊨ ctx_denote_under ?Σ ?Γ |- _ =>
      lazymatch goal with
      | H : fv_cty τ ∪ fv_value v ⊆ world_dom (m : WorldT) |- _ =>
          fail
      | _ =>
          let H := fresh "Hobs_world" in
          pose proof (soundness_wf_ret_persist_observed_world
            Σ Γ τ v m Hwf Hctx) as H
      end
  end.

Ltac soundness_regular_lc :=
  match goal with
  | Hwf : context_typing_wf ?Σ ?Γ (tret ?v) (CTPersist ?τ) |- _ =>
      lazymatch goal with
      | H : lc_value v |- _ => fail
      | _ =>
          let H := fresh "Hv" in
          pose proof (context_typing_wf_ret_lc_value
            Σ Γ v (CTPersist τ) Hwf) as H
      end
  end.

Ltac soundness_regular_obs_subset :=
  match goal with
  | Hwf : context_typing_wf ?Σ ?Γ (tret ?v) (CTPersist ?τ) |- _ =>
      lazymatch goal with
      | H : fv_cty τ ∪ fv_value v ⊆ dom (erase_ctx Γ) |- _ =>
          fail
      | _ =>
          let H := fresh "Hobs" in
          pose proof (soundness_wf_ret_persist_obs_subset
            Σ Γ τ v Hwf) as H
      end
  end.

Ltac soundness_regular :=
  try soundness_regular_observed_world;
  try soundness_regular_lc;
  try soundness_regular_obs_subset.

Lemma soundness_match_left_observation_facts x et ef X :
  X = fv_tm (tmatch (vfvar x) et ef) ->
  fv_tm et ⊆ X /\
  fv_tm (tmatch (vfvar x) et ef) ⊆ X /\
  x ∈ X.
Proof.
  intros ->.
  cbn [fv_tm fv_value].
  repeat split; better_set_solver.
Qed.

Lemma soundness_match_right_observation_facts x et ef X :
  X = fv_tm (tmatch (vfvar x) et ef) ->
  fv_tm ef ⊆ X /\
  fv_tm (tmatch (vfvar x) et ef) ⊆ X /\
  x ∈ X.
Proof.
  intros ->.
  cbn [fv_tm fv_value].
  repeat split; better_set_solver.
Qed.

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
