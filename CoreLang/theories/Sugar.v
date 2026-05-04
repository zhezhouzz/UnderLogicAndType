(** * CoreLang.Sugar

    Small derived forms used by examples.  The core syntax remains ANF and
    boolean-only for matching; nondeterministic choice is encoded by drawing a
    boolean and matching on it. *)

From CoreLang Require Export SmallStep OperationalProps LocallyNamelessProps.

Definition vtrue : value := vconst (cbool true).
Definition vfalse : value := vconst (cbool false).
Definition vnat (n : nat) : value := vconst (cnat n).

Definition tbool_gen : tm :=
  tprim op_bool_gen vtrue.

Definition tnat_gen : tm :=
  tprim op_nat_gen vtrue.

Definition tchoice (etrue efalse : tm) : tm :=
  tlete tbool_gen (tmatch (vbvar 0) etrue efalse).

Lemma lc_tbool_gen : lc_tm tbool_gen.
Proof. repeat constructor. Qed.

Lemma lc_tnat_gen : lc_tm tnat_gen.
Proof. repeat constructor. Qed.

Lemma lc_tchoice et ef :
  lc_tm et →
  lc_tm ef →
  lc_tm (tchoice et ef).
Proof.
  intros Het Hef. unfold tchoice.
  eapply LC_lete with (L := ∅); [apply lc_tbool_gen |].
  intros x _. cbn.
  change (lc_tm (tmatch (vfvar x)
    (open_tm 0 (vfvar x) et) (open_tm 0 (vfvar x) ef))).
  rewrite (open_rec_lc_tm et Het 0 (vfvar x)).
  rewrite (open_rec_lc_tm ef Hef 0 (vfvar x)).
  apply LC_match; eauto.
Qed.

Lemma body_tchoice_body et ef :
  lc_tm et →
  lc_tm ef →
  body_tm (tmatch (vbvar 0) et ef).
Proof.
  intros Het Hef. exists ∅.
  intros x _. cbn.
  change (lc_tm (tmatch (vfvar x)
    (open_tm 0 (vfvar x) et) (open_tm 0 (vfvar x) ef))).
  rewrite (open_rec_lc_tm et Het 0 (vfvar x)).
  rewrite (open_rec_lc_tm ef Hef 0 (vfvar x)).
  apply LC_match; eauto.
Qed.

Lemma tbool_gen_true :
  tbool_gen →* tret vtrue.
Proof.
  unfold tbool_gen, vtrue.
  apply steps_R. apply Step_head. eapply HS_Op.
  - apply Prim_bool_gen_true.
  - repeat constructor.
Qed.

Lemma tbool_gen_false :
  tbool_gen →* tret vfalse.
Proof.
  unfold tbool_gen, vtrue, vfalse.
  apply steps_R. apply Step_head. eapply HS_Op.
  - apply Prim_bool_gen_false.
  - repeat constructor.
Qed.

Lemma tnat_gen_reaches n :
  tnat_gen →* tret (vnat n).
Proof.
  unfold tnat_gen, vtrue, vnat.
  apply steps_R. apply Step_head. eapply HS_Op.
  - apply Prim_nat_gen.
  - repeat constructor.
Qed.

Lemma tchoice_true_branch et ef :
  lc_tm et →
  lc_tm ef →
  tchoice et ef →* et.
Proof.
  intros Het Hef.
  unfold tchoice, tbool_gen, vtrue.
  eapply Steps_step.
  - apply Step_let.
    + apply Step_head. eapply HS_Op.
      * apply Prim_bool_gen_true.
      * repeat constructor.
    + apply lc_tchoice; eauto.
  - cbn.
    eapply Steps_step.
    + apply Step_head. apply HS_Ret.
      apply lc_lete_iff_body. split.
      * repeat constructor.
      * apply body_tchoice_body; eauto.
    + cbn.
      change (tmatch vtrue (open_tm 0 vtrue et) (open_tm 0 vtrue ef) →* et).
      rewrite (open_rec_lc_tm et Het 0 vtrue).
      rewrite (open_rec_lc_tm ef Hef 0 vtrue).
      apply steps_R. apply Step_head. apply HS_MatchTrue.
      apply LC_match; eauto.
Qed.

Lemma tchoice_false_branch et ef :
  lc_tm et →
  lc_tm ef →
  tchoice et ef →* ef.
Proof.
  intros Het Hef.
  unfold tchoice, tbool_gen, vtrue.
  eapply Steps_step.
  - apply Step_let.
    + apply Step_head. eapply HS_Op.
      * apply Prim_bool_gen_false.
      * repeat constructor.
    + apply lc_tchoice; eauto.
  - cbn.
    eapply Steps_step.
    + apply Step_head. apply HS_Ret.
      apply lc_lete_iff_body. split.
      * repeat constructor.
      * apply body_tchoice_body; eauto.
    + cbn.
      change (tmatch vfalse (open_tm 0 vfalse et) (open_tm 0 vfalse ef) →* ef).
      rewrite (open_rec_lc_tm et Het 0 vfalse).
      rewrite (open_rec_lc_tm ef Hef 0 vfalse).
      apply steps_R. apply Step_head. apply HS_MatchFalse.
      apply LC_match; eauto.
Qed.

Lemma tchoice_true_result et ef v :
  lc_tm et →
  lc_tm ef →
  et →* tret v →
  tchoice et ef →* tret v.
Proof.
  intros Het Hef Hsteps.
  unfold tchoice.
  eapply reduction_lete_intro.
  - apply body_tchoice_body; eauto.
  - apply tbool_gen_true.
  - change (tmatch vtrue (open_tm 0 vtrue et) (open_tm 0 vtrue ef) →* tret v).
    rewrite (open_rec_lc_tm et Het 0 vtrue).
    rewrite (open_rec_lc_tm ef Hef 0 vtrue).
    eapply reduction_match_true_intro; eauto.
Qed.

Lemma tchoice_false_result et ef v :
  lc_tm et →
  lc_tm ef →
  ef →* tret v →
  tchoice et ef →* tret v.
Proof.
  intros Het Hef Hsteps.
  unfold tchoice.
  eapply reduction_lete_intro.
  - apply body_tchoice_body; eauto.
  - apply tbool_gen_false.
  - change (tmatch vfalse (open_tm 0 vfalse et) (open_tm 0 vfalse ef) →* tret v).
    rewrite (open_rec_lc_tm et Het 0 vfalse).
    rewrite (open_rec_lc_tm ef Hef 0 vfalse).
    eapply reduction_match_false_intro; eauto.
Qed.
