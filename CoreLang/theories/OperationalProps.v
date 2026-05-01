From CoreLang Require Import SmallStep BasicTypingProps LocallyNamelessProps.
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
Proof. apply rtc_trans. Qed.

Lemma steps_R e e' :
  step e e' → e →* e'.
Proof. apply rtc_once. Qed.

Lemma steps_regular e e' :
  e →* e' → lc_tm e → lc_tm e'.
Proof.
  intros Hsteps Hlc. induction Hsteps; eauto using step_regular2.
Qed.

Lemma steps_regular1 e e' :
  e →* e' → lc_tm e → lc_tm e.
Proof. eauto. Qed.

Lemma steps_regular2 e e' :
  e →* e' → lc_tm e → lc_tm e'.
Proof. apply steps_regular. Qed.

Lemma value_steps_self v e :
  tret v →* e → e = tret v.
Proof. apply val_steps_self. Qed.

Lemma value_no_step v e :
  ¬ step (tret v) e.
Proof. intro Hstep. eapply val_no_step; eauto. Qed.

Lemma head_step_deterministic e e1 e2 :
  head_step e e1 → head_step e e2 → e1 = e2.
Proof. apply head_step_det. Qed.

Lemma basic_step_preservation Γ e e' T :
  Γ ⊢ₑ e ⋮ T → step e e' → Γ ⊢ₑ e' ⋮ T.
Proof. apply step_preserves_type. Qed.

Lemma basic_steps_preservation Γ e e' T :
  Γ ⊢ₑ e ⋮ T → e →* e' → Γ ⊢ₑ e' ⋮ T.
Proof. apply steps_preserves_type. Qed.

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
Proof. Admitted.

Lemma reduction_lete_intro e1 e2 vx v :
  body_tm e2 →
  e1 →* tret vx →
  open_tm 0 vx e2 →* tret v →
  tlete e1 e2 →* tret v.
Proof. Admitted.

Lemma reduction_beta s body vx v :
  lc_value vx →
  tapp (vlam s body) vx →* tret v →
  open_tm 0 vx body →* tret v.
Proof. Admitted.

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

Lemma reduction_fix Tf vf vx v :
  lc_value vx →
  tapp (vfix Tf vf) vx →* tret v →
  tapp (open_value 0 vx vf) (vfix Tf vf) →* tret v.
Proof. Admitted.

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

Lemma reduction_match_true et ef v :
  tmatch (vconst (cbool true)) et ef →* tret v →
  et →* tret v.
Proof. Admitted.

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

Lemma reduction_match_false et ef v :
  tmatch (vconst (cbool false)) et ef →* tret v →
  ef →* tret v.
Proof. Admitted.

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
