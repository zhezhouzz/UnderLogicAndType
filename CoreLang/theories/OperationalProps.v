From CoreLang Require Import SmallStep BasicTypingProps.
From LocallyNameless Require Import Tactics.

(** * Operational facts for CoreLang

    These are the direct-style counterparts of the regularity and multistep
    lemmas in HATs/UnderType. *)

Lemma head_step_regular e e' :
  head_step e e' → lc_tm e ∧ lc_tm e'.
Proof. Admitted.

Lemma step_regular e e' :
  step e e' → lc_tm e ∧ lc_tm e'.
Proof. Admitted.

Lemma step_regular1 e e' :
  step e e' → lc_tm e.
Proof. intros H. exact (proj1 (step_regular e e' H)). Qed.

Lemma step_regular2 e e' :
  step e e' → lc_tm e'.
Proof. intros H. exact (proj2 (step_regular e e' H)). Qed.

Lemma steps_trans e1 e2 e3 :
  e1 →* e2 → e2 →* e3 → e1 →* e3.
Proof. Admitted.

Lemma steps_regular e e' :
  e →* e' → lc_tm e → lc_tm e'.
Proof.
  intros Hsteps Hlc. induction Hsteps; eauto using step_regular2.
Qed.

Lemma value_steps_self v e :
  tret v →* e → e = tret v.
Proof. apply val_steps_self. Qed.

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
