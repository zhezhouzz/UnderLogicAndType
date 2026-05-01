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
