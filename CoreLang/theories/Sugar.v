(** * CoreLang.Sugar

    Small derived forms used by examples.  The core syntax remains ANF and
    boolean-only for matching; nondeterministic choice is encoded by drawing a
    boolean and matching on it. *)

From CoreLang Require Export SmallStep OperationalProps LocallyNamelessProps.
From CoreLang Require Import BasicTypingProps.

Definition vtrue : value := vconst (cbool true).
Definition vfalse : value := vconst (cbool false).
Definition vnat (n : nat) : value := vconst (cnat n).

Definition tbool_gen : tm :=
  tprim op_bool_gen vtrue.

Definition tnat_gen : tm :=
  tprim op_nat_gen vtrue.

Definition tapp_tm (ef : tm) (vx : value) : tm :=
  tlete ef (tapp (vbvar 0) vx).

Definition tchoice (etrue efalse : tm) : tm :=
  tlete tbool_gen (tmatch (vbvar 0) etrue efalse).

Lemma lc_tbool_gen : lc_tm tbool_gen.
Proof. repeat constructor. Qed.

Lemma lc_tnat_gen : lc_tm tnat_gen.
Proof. repeat constructor. Qed.

Lemma fv_tapp_tm ef vx :
  fv_tm (tapp_tm ef vx) = fv_tm ef ∪ fv_value vx.
Proof.
  unfold tapp_tm. simpl. set_solver.
Qed.

Lemma body_tapp_tm_body vx :
  lc_value vx →
  body_tm (tapp (vbvar 0) vx).
Proof.
  intros Hvx. exists ∅. intros x _.
  change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
  rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
  repeat constructor. exact Hvx.
Qed.

Lemma lc_tapp_tm ef vx :
  lc_tm ef →
  lc_value vx →
  lc_tm (tapp_tm ef vx).
Proof.
  intros Hef Hvx. unfold tapp_tm.
  eapply LC_lete with (L := ∅); [exact Hef |].
  intros x _.
  change (lc_tm (tapp (vfvar x) (open_value 0 (vfvar x) vx))).
  rewrite (open_rec_lc_value vx Hvx 0 (vfvar x)).
  repeat constructor. exact Hvx.
Qed.

Lemma basic_typing_tapp_tm Γ ef vx Tx T :
  Γ ⊢ₑ ef ⋮ (Tx →ₜ T) →
  Γ ⊢ᵥ vx ⋮ Tx →
  Γ ⊢ₑ tapp_tm ef vx ⋮ T.
Proof.
  intros Hef Hvx. unfold tapp_tm.
  eapply TT_Let with (L := dom Γ ∪ fv_value vx).
  - exact Hef.
  - intros x Hx.
    change (<[x := Tx →ₜ T]> Γ ⊢ₑ
      tapp (vfvar x) (open_value 0 (vfvar x) vx) ⋮ T).
    rewrite (open_rec_lc_value vx (typing_value_lc _ _ _ Hvx) 0 (vfvar x)).
    eapply TT_App.
    + eapply VT_FVar. rewrite lookup_insert.
      destruct (decide (x = x)); [reflexivity | congruence].
    + eapply basic_typing_weaken_insert_value; [set_solver | exact Hvx].
Qed.

Lemma reduction_tapp_tm_intro ef vf vx v :
  lc_value vx →
  ef →* tret vf →
  tapp vf vx →* tret v →
  tapp_tm ef vx →* tret v.
Proof.
  intros Hvx Hef Happ.
  unfold tapp_tm.
  eapply reduction_lete_intro.
  - apply body_tapp_tm_body. exact Hvx.
  - exact Hef.
  - change (tapp vf (open_value 0 vf vx) →* tret v).
    rewrite (open_rec_lc_value vx Hvx 0 vf).
    exact Happ.
Qed.

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
