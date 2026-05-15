From CoreLang Require Import SmallStep BasicTypingProps LocallyNamelessProps
  LocallyNamelessExtra Instantiation InstantiationProps.
From LocallyNameless Require Import Tactics.

(** * Operational facts for CoreLang

    These are the direct-style counterparts of the regularity and multistep
    lemmas in HATs/UnderType. *)

Lemma head_step_regular e e' :
  head_step e e' → lc_tm e ∧ lc_tm e'.
Proof.
  intros Hstep.
  destruct Hstep as
    [v e Hlc | op c c' Heval Hlc | s body v Hlc
    | Tf vf v Hlc | et ef Hlc | et ef Hlc].
  - split.
    + assumption.
    + apply body_open_tm.
      * by apply lc_lete_iff_body in Hlc as [_ Hbody].
      * apply lc_lete_iff_body in Hlc as [Hret _].
        by apply lc_ret_iff_value.
  - split; [assumption|constructor; constructor].
  - split.
    + assumption.
    + apply body_open_tm.
      * apply lc_app_iff_values in Hlc as [Hlam _].
        by apply lc_lam_iff_body in Hlam.
      * by apply lc_app_iff_values in Hlc as [_ ?].
  - split.
    + assumption.
    + match goal with
      | H : lc_tm _ |- _ =>
          apply lc_app_iff_values in H as [Hfix Hv];
          apply lc_app_iff_values; split;
          [apply body_open_value; [by apply lc_fix_iff_body in Hfix | exact Hv] | exact Hfix]
      end.
  - split.
    + assumption.
    + by apply lc_match_iff_parts in Hlc as [_ [? _]].
  - split.
    + assumption.
    + by apply lc_match_iff_parts in Hlc as [_ [_ ?]].
Qed.

Lemma step_regular e e' :
  step e e' → lc_tm e ∧ lc_tm e'.
Proof.
  intros Hstep. induction Hstep.
  - by apply head_step_regular.
  - destruct IHHstep as [Hlc1 Hlc1'].
    split; auto.
    match goal with
    | Hlc : lc_tm (tlete _ _) |- _ =>
        apply lc_lete_iff_body in Hlc as [_ Hbody];
        apply lc_lete_iff_body; split; auto
    end.
Qed.

Lemma step_regular1 e e' :
  step e e' → lc_tm e.
Proof. intros H. exact (proj1 (step_regular e e' H)). Qed.

Lemma step_regular2 e e' :
  step e e' → lc_tm e'.
Proof. intros H. exact (proj2 (step_regular e e' H)). Qed.

Lemma steps_trans e1 e2 e3 :
  e1 →* e2 → e2 →* e3 → e1 →* e3.
Proof.
  intros H12 H23. induction H12; eauto using Steps_step.
Qed.

Lemma steps_R e e' :
  step e e' → e →* e'.
Proof.
  intros Hstep. eapply Steps_step; eauto.
  apply Steps_refl. eauto using step_regular2.
Qed.

Lemma steps_inv e z :
  e →* z →
  (e = z ∧ lc_tm e) ∨ ∃ y, step e y ∧ y →* z.
Proof.
  intros Hsteps. inversion Hsteps; subst; eauto.
Qed.

Lemma steps_regular e e' :
  e →* e' → lc_tm e'.
Proof.
  intros Hsteps. induction Hsteps; eauto using step_regular2.
Qed.

Lemma steps_regular1 e e' :
  e →* e' → lc_tm e.
Proof.
  intros Hsteps. induction Hsteps; eauto using step_regular1.
Qed.

Lemma steps_regular2 e e' :
  e →* e' → lc_tm e'.
Proof. apply steps_regular. Qed.

Definition closed_tm (e : tm) : Prop :=
  stale e = ∅ ∧ lc_tm e.

Definition closed_value (v : value) : Prop :=
  stale v = ∅ ∧ lc_value v.

Lemma head_step_fv_subset e e' :
  head_step e e' →
  fv_tm e' ⊆ fv_tm e.
Proof.
  intros Hstep. destruct Hstep; simpl.
  - pose proof (open_fv_tm e v 0) as Hopen. my_set_solver.
  - my_set_solver.
  - pose proof (open_fv_tm body v 0) as Hopen. my_set_solver.
  - pose proof (open_fv_value vf v 0) as Hopen. my_set_solver.
  - my_set_solver.
  - my_set_solver.
Qed.

Lemma step_fv_subset e e' :
  step e e' →
  fv_tm e' ⊆ fv_tm e.
Proof.
  intros Hstep. induction Hstep; simpl.
  - by apply head_step_fv_subset.
  - pose proof IHHstep. my_set_solver.
Qed.

Lemma steps_fv_subset e e' :
  e →* e' →
  fv_tm e' ⊆ fv_tm e.
Proof.
  intros Hsteps. induction Hsteps.
  - set_solver.
  - pose proof (step_fv_subset _ _ H) as Hfv.
    set_solver.
Qed.

Lemma steps_closed_result e v :
  closed_tm e →
  e →* tret v →
  closed_value v.
Proof.
  intros [Hclosed Hlc] Hsteps.
  split.
  - pose proof (steps_fv_subset _ _ Hsteps) as Hfv.
    simpl in Hfv. change (fv_tm e = ∅) in Hclosed.
    rewrite Hclosed in Hfv. set_solver.
  - pose proof (steps_regular2 _ _ Hsteps) as Hret.
    by apply lc_ret_iff_value in Hret.
Qed.

Lemma msubst_closed_tm σ e :
  store_closed σ →
  lc_tm e →
  stale e ⊆ dom σ →
  closed_tm (m{σ} e).
Proof.
  intros [Hclosed Hlc_env] Hlc Hcover.
  split.
  - pose proof (msubst_fv_delete_tm σ e Hclosed) as Hfv.
    apply leibniz_equiv. set_solver.
  - apply msubst_lc; assumption.
Qed.

Lemma value_steps_self v e :
  tret v →* e → e = tret v.
Proof. apply val_steps_self. Qed.

Lemma value_reduction_any_ctx v :
  lc_value v →
  tret v →* tret v.
Proof. intros Hlc. apply Steps_refl. by constructor. Qed.

Lemma value_no_step v e :
  ¬ step (tret v) e.
Proof. intro Hstep. eapply val_no_step; eauto. Qed.

Lemma basic_step_preservation Γ e e' T :
  Γ ⊢ₑ e ⋮ T → step e e' → Γ ⊢ₑ e' ⋮ T.
Proof. apply step_preserves_type. Qed.

Lemma basic_steps_preservation Γ e e' T :
  Γ ⊢ₑ e ⋮ T → e →* e' → Γ ⊢ₑ e' ⋮ T.
Proof. apply steps_preserves_type. Qed.

Lemma basic_steps_result_closed e v T :
  ∅ ⊢ₑ e ⋮ T →
  e →* tret v →
  stale v = ∅.
Proof.
  intros Hty Hsteps.
  pose proof (basic_steps_preservation ∅ e (tret v) T Hty Hsteps) as Hret.
  inversion Hret; subst.
  match goal with
  | H : ∅ ⊢ᵥ v ⋮ _ |- _ => exact (basic_typing_closed_value v _ H)
  end.
Qed.

Lemma beta_step_regular s body v :
  lc_tm (tapp (vlam s body) v) →
  lc_tm ({0 ~> v} body).
Proof.
  intros Hlc.
  pose proof (head_step_regular _ _ (HS_Beta s body v Hlc)) as [_ H].
  exact H.
Qed.

Lemma fix_step_regular Tf vf v :
  lc_tm (tapp (vfix Tf vf) v) →
  lc_tm (tapp ({0 ~> v} vf) (vfix Tf vf)).
Proof.
  intros Hlc.
  pose proof (head_step_regular _ _ (HS_Fix Tf vf v Hlc)) as [_ H].
  exact H.
Qed.

Lemma reduction_lete e1 e2 v :
  tlete e1 e2 →* tret v →
  ∃ vx, e1 →* tret vx ∧ open_tm 0 vx e2 →* tret v.
Proof.
  intros Hsteps.
  remember (tlete e1 e2) as e eqn:He.
  remember (tret v) as r eqn:Hr.
  revert e1 e2 v He Hr.
  induction Hsteps; intros e1' e2' v' He Hr; subst.
  - discriminate.
  - inversion H; subst.
    + inversion H0; subst; try discriminate.
      eexists. split; [|exact Hsteps].
      apply Steps_refl.
      match goal with
      | Hlc : lc_tm (tlete (tret _) _) |- _ =>
          apply lc_lete_iff_body in Hlc as [Hret _]; exact Hret
      end.
    + destruct (IHHsteps e1'0 e2' v' eq_refl eq_refl) as [vx [Hsteps1 Hsteps2]].
      exists vx. split; [|exact Hsteps2].
      eapply Steps_step; eauto.
Qed.

Lemma reduction_lete_intro e1 e2 vx v :
  body_tm e2 →
  e1 →* tret vx →
  open_tm 0 vx e2 →* tret v →
  tlete e1 e2 →* tret v.
Proof.
  intros Hbody Hsteps1.
  remember (tret vx) as r eqn:Hr.
  revert vx Hr e2 Hbody v.
  induction Hsteps1; intros vx Hr e2' Hbody v Hsteps2.
  - inversion Hr; subst.
    eapply steps_trans; [|exact Hsteps2].
    apply steps_R. apply Step_head. apply HS_Ret.
    apply lc_lete_iff_body. split; eauto.
  - eapply Steps_step.
    + apply Step_let; eauto.
      apply lc_lete_iff_body. split; eauto using step_regular1.
    + eapply IHHsteps1; eauto.
Qed.

Lemma reduction_lete_msubst_intro σ e1 e2 vx v :
  body_tm (msubst σ e2) →
  msubst σ e1 →* tret vx →
  open_tm 0 vx (msubst σ e2) →* tret v →
  msubst σ (tlete e1 e2) →* tret v.
Proof.
  intros Hbody Hsteps1 Hsteps2.
  rewrite msubst_lete.
  eapply reduction_lete_intro; eauto.
Qed.

Lemma reduction_lete_iff e1 e2 v :
  body_tm e2 →
  tlete e1 e2 →* tret v ↔
  ∃ vx, e1 →* tret vx ∧ open_tm 0 vx e2 →* tret v.
Proof.
  intros Hbody.
  split.
  - apply reduction_lete.
  - intros [vx [H1 H2]].
    eapply reduction_lete_intro; eauto.
Qed.

(** ** Result view of evaluation

    [steps e (tret v)] remains a relation even though primitive reduction is
    deterministic.  These helpers keep let-result reasoning relational, which
    avoids committing higher layers to a particular evaluator function. *)

Definition reaches_result (e : tm) (v : value) : Prop :=
  e →* tret v.

Definition result_set (e : tm) : value → Prop :=
  reaches_result e.

Definition all_results (e : tm) (P : value → Prop) : Prop :=
  ∀ v, reaches_result e v → P v.

Definition let_result_set (e1 e2 : tm) : value → Prop :=
  λ v, ∃ vx,
    reaches_result e1 vx ∧
    reaches_result (open_tm 0 vx e2) v.

Lemma let_result_decompose e1 e2 v :
  reaches_result (tlete e1 e2) v →
  let_result_set e1 e2 v.
Proof. apply reduction_lete. Qed.

Lemma let_result_compose e1 e2 v :
  body_tm e2 →
  let_result_set e1 e2 v →
  reaches_result (tlete e1 e2) v.
Proof.
  intros Hbody [vx [H1 H2]].
  eapply reduction_lete_intro; eauto.
Qed.

Lemma all_results_let_intro e1 e2 P :
  body_tm e2 →
  (∀ vx, reaches_result e1 vx →
    all_results (open_tm 0 vx e2) P) →
  all_results (tlete e1 e2) P.
Proof.
  intros _ Hall v Hlet.
  apply let_result_decompose in Hlet as [vx [H1 H2]].
  exact (Hall vx H1 v H2).
Qed.

Lemma reduction_beta s body vx v :
  lc_value vx →
  tapp (vlam s body) vx →* tret v →
  open_tm 0 vx body →* tret v.
Proof.
  intros _ Hsteps.
  destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
  - discriminate.
  - inversion Hstep; subst.
    + inversion H; subst; try discriminate. exact Hrest.
Qed.

Lemma reduction_beta_intro s body vx v :
  body_tm body →
  lc_value vx →
  open_tm 0 vx body →* tret v →
  tapp (vlam s body) vx →* tret v.
Proof.
  intros Hbody Hlc Hsteps.
  eapply steps_trans; [|exact Hsteps].
  apply steps_R. apply Step_head. apply HS_Beta.
  apply lc_app_iff_values. split; auto.
  by apply lc_lam_iff_body.
Qed.

Lemma reduction_beta_iff s body vx v :
  body_tm body →
  lc_value vx →
  tapp (vlam s body) vx →* tret v ↔
  open_tm 0 vx body →* tret v.
Proof.
  intros Hbody Hlc. split.
  - apply reduction_beta; auto.
  - apply reduction_beta_intro; auto.
Qed.

Lemma reduction_prim_intro op c c' :
  prim_step op c c' →
  tprim op (vconst c) →* tret (vconst c').
Proof.
  intros Hop.
  apply steps_R. apply Step_head. apply HS_Op; [exact Hop |].
  constructor. constructor.
Qed.

Lemma reduction_prim_const op c v :
  tprim op (vconst c) →* tret v →
  ∃ c', prim_step op c c' ∧ v = vconst c'.
Proof.
  intros Hsteps.
  destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
  - discriminate.
  - inversion Hstep; subst.
    inversion H; subst; try discriminate.
    apply val_steps_self in Hrest.
    inversion Hrest. subst. eauto.
Qed.

Lemma reduction_prim_fvar_msubst_const σ op x c v :
  closed_env σ →
  σ !! x = Some (vconst c) →
  m{σ} (tprim op (vfvar x)) →* tret v →
  ∃ c', prim_step op c c' ∧ v = vconst c'.
Proof.
  intros Hclosed Hlookup Hsteps.
  rewrite (msubst_prim_fvar_lookup_closed σ op x (vconst c) Hclosed Hlookup)
    in Hsteps.
  apply reduction_prim_const. exact Hsteps.
Qed.

Lemma reduction_fix Tf vf vx v :
  lc_value vx →
  tapp (vfix Tf vf) vx →* tret v →
  tapp (open_value 0 vx vf) (vfix Tf vf) →* tret v.
Proof.
  intros _ Hsteps.
  destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
  - discriminate.
  - inversion Hstep; subst.
    + inversion H; subst; try discriminate. exact Hrest.
Qed.

Lemma reduction_fix_intro Tf vf vx v :
  body_val vf →
  lc_value vx →
  tapp (open_value 0 vx vf) (vfix Tf vf) →* tret v →
  tapp (vfix Tf vf) vx →* tret v.
Proof.
  intros Hbody Hlc Hsteps.
  eapply steps_trans; [|exact Hsteps].
  apply steps_R. apply Step_head. apply HS_Fix.
  apply lc_app_iff_values. split; auto.
  by apply lc_fix_iff_body.
Qed.

Lemma reduction_fix_iff Tf vf vx v :
  body_val vf →
  lc_value vx →
  tapp (vfix Tf vf) vx →* tret v ↔
  tapp (open_value 0 vx vf) (vfix Tf vf) →* tret v.
Proof.
  intros Hbody Hlc. split.
  - apply reduction_fix; auto.
  - apply reduction_fix_intro; auto.
Qed.

Lemma reduction_match_true et ef v :
  tmatch (vconst (cbool true)) et ef →* tret v →
  et →* tret v.
Proof.
  intros Hsteps.
  destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
  - discriminate.
  - inversion Hstep; subst.
    + inversion H; subst; try discriminate. exact Hrest.
Qed.

Lemma reduction_match_true_intro et ef v :
  lc_tm et →
  lc_tm ef →
  et →* tret v →
  tmatch (vconst (cbool true)) et ef →* tret v.
Proof.
  intros Ht Hf Hsteps.
  eapply steps_trans; [|exact Hsteps].
  apply steps_R. apply Step_head. apply HS_MatchTrue.
  apply lc_match_iff_parts. repeat split; auto.
Qed.

Lemma reduction_match_true_iff et ef v :
  lc_tm et →
  lc_tm ef →
  tmatch (vconst (cbool true)) et ef →* tret v ↔
  et →* tret v.
Proof.
  intros Ht Hf. split.
  - apply reduction_match_true.
  - apply reduction_match_true_intro; auto.
Qed.

Lemma reduction_match_false et ef v :
  tmatch (vconst (cbool false)) et ef →* tret v →
  ef →* tret v.
Proof.
  intros Hsteps.
  destruct (steps_inv _ _ Hsteps) as [[Heq _] | [e' [Hstep Hrest]]].
  - discriminate.
  - inversion Hstep; subst.
    + inversion H; subst; try discriminate. exact Hrest.
Qed.

Lemma reduction_match_false_intro et ef v :
  lc_tm et →
  lc_tm ef →
  ef →* tret v →
  tmatch (vconst (cbool false)) et ef →* tret v.
Proof.
  intros Ht Hf Hsteps.
  eapply steps_trans; [|exact Hsteps].
  apply steps_R. apply Step_head. apply HS_MatchFalse.
  apply lc_match_iff_parts. repeat split; auto.
Qed.

Lemma reduction_match_false_iff et ef v :
  lc_tm et →
  lc_tm ef →
  tmatch (vconst (cbool false)) et ef →* tret v ↔
  ef →* tret v.
Proof.
  intros Ht Hf. split.
  - apply reduction_match_false.
  - apply reduction_match_false_intro; auto.
Qed.
