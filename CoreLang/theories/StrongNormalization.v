(** * CoreLang.StrongNormalization

    Step-indexed must-termination for the deterministic core language.  The
    fuel below measures the height of the reduction tree; in the deterministic
    setting that tree is at most a path, but the stronger formulation remains
    convenient for existing totality lemmas. *)

From Stdlib Require Import Lia.
From CoreLang Require Import SmallStep OperationalProps LocallyNamelessProps Sugar.

Definition result_tm (e : tm) : Prop :=
  exists v, e = tret v /\ lc_value v.

Definition can_step (e : tm) : Prop :=
  exists e', step e e'.

Fixpoint strongly_normalizing_fuel (n : nat) (e : tm) : Prop :=
  match n with
  | 0 => result_tm e
  | S n' =>
      result_tm e \/
      (can_step e /\ forall e', step e e' -> strongly_normalizing_fuel n' e')
  end.

Definition strongly_normalizing (e : tm) : Prop :=
  exists n, strongly_normalizing_fuel n e.

Inductive must_terminating : tm -> Prop :=
  | Must_result e :
      result_tm e ->
      must_terminating e
  | Must_step e :
      can_step e ->
      (forall e', step e e' -> must_terminating e') ->
      must_terminating e.

Lemma result_tm_tret v :
  lc_value v ->
  result_tm (tret v).
Proof. intros Hlc. exists v. split; [reflexivity | exact Hlc]. Qed.

Lemma strongly_normalizing_tret v :
  lc_value v ->
  strongly_normalizing (tret v).
Proof.
  intros Hlc. exists 0. apply result_tm_tret. exact Hlc.
Qed.

Lemma must_terminating_tret v :
  lc_value v ->
  must_terminating (tret v).
Proof.
  intros Hlc. apply Must_result. apply result_tm_tret. exact Hlc.
Qed.

Lemma must_terminating_step_inv e e' :
  must_terminating e ->
  step e e' ->
  must_terminating e'.
Proof.
  intros Hmt Hstep.
  inversion Hmt; subst.
  - destruct H as [v [-> _]].
    exfalso. eapply val_no_step; eauto.
  - eauto.
Qed.

Lemma must_terminating_reaches_result e :
  must_terminating e ->
  exists v, e →* tret v.
Proof.
  intros Hmt. induction Hmt as [e [v [-> Hlc]] | e [e' Hstep] _ IH].
  - exists v. apply Steps_refl. constructor. exact Hlc.
  - destruct (IH e' Hstep) as [v Hsteps].
    exists v. eapply Steps_step; eauto.
Qed.

Lemma must_terminating_steps_inv e e' :
  must_terminating e ->
  e →* e' ->
  must_terminating e'.
Proof.
  intros Hmt Hsteps. induction Hsteps.
  - exact Hmt.
  - apply IHHsteps. eapply must_terminating_step_inv; eauto.
Qed.

Lemma strongly_normalizing_fuel_step_inv n e e' :
  strongly_normalizing_fuel (S n) e ->
  step e e' ->
  strongly_normalizing_fuel n e'.
Proof.
  intros Hsn Hstep.
  destruct Hsn as [Hres | [_ Hnext]].
  - destruct Hres as [v [-> _]].
    exfalso. eapply val_no_step; eauto.
  - exact (Hnext e' Hstep).
Qed.

Lemma strongly_normalizing_step_inv e e' :
  strongly_normalizing e ->
  step e e' ->
  strongly_normalizing e'.
Proof.
  intros [n Hsn] Hstep.
  destruct n as [|n].
  - destruct Hsn as [v [-> _]].
    exfalso. eapply val_no_step; eauto.
  - exists n. eapply strongly_normalizing_fuel_step_inv; eauto.
Qed.

Lemma strongly_normalizing_reaches_result e :
  strongly_normalizing e ->
  exists v, e →* tret v.
Proof.
  intros [n Hsn]. induction n as [|n IH] in e, Hsn |- *.
  - destruct Hsn as [v [-> Hlc]].
    exists v. apply Steps_refl. constructor. exact Hlc.
  - destruct Hsn as [[v [-> Hlc]] | [[e' Hstep] Hnext]].
    + exists v. apply Steps_refl. constructor. exact Hlc.
    + destruct (IH e' (Hnext e' Hstep)) as [v Hsteps].
      exists v. eapply Steps_step; eauto.
Qed.

Lemma strongly_normalizing_fuel_weaken n e :
  strongly_normalizing_fuel n e ->
  strongly_normalizing_fuel (S n) e.
Proof.
  induction n as [|n IH] in e |- *; intros Hsn.
  - left. exact Hsn.
  - destruct Hsn as [Hres | Hstep].
    + left. exact Hres.
    + right. destruct Hstep as [Hcan Hnext].
      split; [exact Hcan |].
      intros e' Hstep. apply IH.
      exact (Hnext e' Hstep).
Qed.

Lemma strongly_normalizing_fuel_mono n m e :
  n <= m ->
  strongly_normalizing_fuel n e ->
  strongly_normalizing_fuel m e.
Proof.
  intros Hle Hsn.
  induction Hle; eauto using strongly_normalizing_fuel_weaken.
Qed.

Lemma strongly_normalizing_steps_inv e e' :
  strongly_normalizing e ->
  e →* e' ->
  strongly_normalizing e'.
Proof.
  intros Hsn Hsteps. induction Hsteps.
  - exact Hsn.
  - apply IHHsteps.
    eapply strongly_normalizing_step_inv; eauto.
Qed.

Lemma strongly_normalizing_fuel_steps_inv n e e' :
  strongly_normalizing_fuel n e ->
  e →* e' ->
  exists n', n' <= n /\ strongly_normalizing_fuel n' e'.
Proof.
  intros Hsn Hsteps.
  induction Hsteps in n, Hsn |- *.
  - exists n. split; [lia | exact Hsn].
  - destruct n as [|n].
    + destruct Hsn as [v [-> _]].
      exfalso. eapply val_no_step; eauto.
    + pose proof (strongly_normalizing_fuel_step_inv n e1 e2 Hsn H) as Hsn2.
      destruct (IHHsteps n Hsn2) as [n' [Hle Hsn']].
      exists n'. split; [lia | exact Hsn'].
Qed.

(** The tlet facts below are intentionally stated at the operational layer.
    They are the principles the ContextTyping totality proof should use.  Their
    proofs are independent of refinements/resources, so they belong here even
    when later proof engineering temporarily admits them. *)

Lemma strongly_normalizing_fuel_tlete_elim_e1 n e1 e2 :
  strongly_normalizing_fuel n (tlete e1 e2) ->
  strongly_normalizing_fuel n e1.
Proof.
  induction n as [|n IH] in e1, e2 |- *; intros Hsn.
  - destruct Hsn as [v [Hbad _]]. discriminate Hbad.
  - destruct Hsn as [[v [Hbad _]] | [Hcan Hnext]].
    + discriminate Hbad.
    + destruct Hcan as [e' Hstep_tlet].
      pose proof (step_regular1 _ _ Hstep_tlet) as Hlc_tlet.
      destruct e1 as [v|e1a e1b|op v|v1 v2|v et ef|root lft rgt|v el en].
      * left.
        apply lc_lete_iff_body in Hlc_tlet as [Hret _].
        apply lc_ret_iff_value in Hret.
        apply result_tm_tret. exact Hret.
      * right. split.
        -- inversion Hstep_tlet; subst.
           ++ inversion H; subst; try discriminate.
           ++ unfold can_step; eauto.
        -- intros e1' Hstep1.
           apply IH with (e2 := e2).
           apply Hnext. apply Step_let; assumption.
      * right. split.
        -- inversion Hstep_tlet; subst.
           ++ inversion H; subst; try discriminate.
           ++ unfold can_step; eauto.
        -- intros e1' Hstep1.
           apply IH with (e2 := e2).
           apply Hnext. apply Step_let; assumption.
      * right. split.
        -- inversion Hstep_tlet; subst.
           ++ inversion H; subst; try discriminate.
           ++ unfold can_step; eauto.
        -- intros e1' Hstep1.
           apply IH with (e2 := e2).
           apply Hnext. apply Step_let; assumption.
      * right. split.
        -- inversion Hstep_tlet; subst.
           ++ inversion H; subst; try discriminate.
           ++ unfold can_step; eauto.
        -- intros e1' Hstep1.
           apply IH with (e2 := e2).
           apply Hnext. apply Step_let; assumption.
      * right. split.
        -- inversion Hstep_tlet; subst.
           ++ inversion H; subst; try discriminate.
           ++ unfold can_step; eauto.
        -- intros e1' Hstep1.
           apply IH with (e2 := e2).
           apply Hnext. apply Step_let; assumption.
      * right. split.
        -- inversion Hstep_tlet; subst.
           ++ inversion H; subst; try discriminate.
           ++ unfold can_step; eauto.
        -- intros e1' Hstep1.
           apply IH with (e2 := e2).
           apply Hnext. apply Step_let; assumption.
Qed.

Lemma strongly_normalizing_tlete_elim_e1 e1 e2 :
  strongly_normalizing (tlete e1 e2) ->
  strongly_normalizing e1.
Proof.
  intros [n Hsn]. exists n.
  eapply strongly_normalizing_fuel_tlete_elim_e1; eauto.
Qed.

Lemma steps_tlete_to_body e1 e2 vx :
  body_tm e2 ->
  e1 →* tret vx ->
  tlete e1 e2 →* ({0 ~> vx} e2).
Proof.
  intros Hbody Hsteps.
  remember (tret vx) as r eqn:Hr.
  revert vx Hr e2 Hbody.
  induction Hsteps; intros vx Hr e2' Hbody; subst.
  - eapply Steps_step.
    + apply Step_head. apply HS_Ret.
      apply lc_lete_iff_body. split; [exact H | exact Hbody].
    + apply Steps_refl.
      apply body_open_tm; [exact Hbody |].
      apply lc_ret_iff_value in H. exact H.
  - eapply Steps_step.
    + apply Step_let.
      * exact H.
      * apply lc_lete_iff_body. split.
        -- exact (step_regular1 _ _ H).
        -- exact Hbody.
    + eapply IHHsteps; eauto.
Qed.

Lemma strongly_normalizing_tlete_elim_body e1 e2 vx :
  body_tm e2 ->
  e1 →* tret vx ->
  strongly_normalizing (tlete e1 e2) ->
  strongly_normalizing ({0 ~> vx} e2).
Proof.
  intros Hbody Hsteps Hsn.
  eapply strongly_normalizing_steps_inv.
  - exact Hsn.
  - eapply steps_tlete_to_body; eauto.
Qed.

Lemma strongly_normalizing_fuel_tlete_elim_body n e1 e2 vx :
  body_tm e2 ->
  e1 →* tret vx ->
  strongly_normalizing_fuel n (tlete e1 e2) ->
  strongly_normalizing_fuel n ({0 ~> vx} e2).
Proof.
  intros Hbody Hsteps Hsn.
  destruct (strongly_normalizing_fuel_steps_inv n (tlete e1 e2)
    ({0 ~> vx} e2) Hsn ltac:(eapply steps_tlete_to_body; eauto))
    as [n' [Hle Hsn']].
  eapply strongly_normalizing_fuel_mono; eauto.
Qed.

Lemma strongly_normalizing_fuel_tlete_intro n1 n2 e1 e2 :
  body_tm e2 ->
  strongly_normalizing_fuel n1 e1 ->
  (forall vx, e1 →* tret vx ->
    strongly_normalizing_fuel n2 ({0 ~> vx} e2)) ->
  strongly_normalizing_fuel (S (n1 + n2)) (tlete e1 e2).
Proof.
  intros Hbody Hsn1 Hbody_sn.
  induction n1 as [|n1 IH] in e1, Hsn1, Hbody_sn |- *.
  - destruct Hsn1 as [vx [-> Hlc_vx]].
    right. split.
    + exists ({0 ~> vx} e2).
      apply Step_head. apply HS_Ret.
      apply lc_lete_iff_body. split.
      * constructor. exact Hlc_vx.
      * exact Hbody.
    + intros e' Hstep.
      inversion Hstep; subst.
      * inversion H; subst; try discriminate.
        apply Hbody_sn.
        apply Steps_refl. constructor. exact Hlc_vx.
      * exfalso. eapply val_no_step; eauto.
  - destruct Hsn1 as [[vx [-> Hlc_vx]] | [Hcan1 Hnext1]].
    + right. split.
      * exists ({0 ~> vx} e2).
        apply Step_head. apply HS_Ret.
        apply lc_lete_iff_body. split.
        -- constructor. exact Hlc_vx.
        -- exact Hbody.
      * intros e' Hstep.
        inversion Hstep; subst.
        -- inversion H; subst; try discriminate.
           apply (strongly_normalizing_fuel_mono n2 (S n1 + n2)).
           ++ lia.
           ++ apply Hbody_sn.
              apply Steps_refl. constructor. exact Hlc_vx.
        -- exfalso. eapply val_no_step; eauto.
    + right. split.
      * destruct Hcan1 as [e1' Hstep1].
        exists (tlete e1' e2).
        apply Step_let.
        -- exact Hstep1.
        -- apply lc_lete_iff_body. split.
           ++ exact (step_regular1 _ _ Hstep1).
           ++ exact Hbody.
      * intros e' Hstep.
        inversion Hstep; subst.
        -- inversion H; subst; try discriminate.
           destruct Hcan1 as [e1' Hstep1].
           exfalso. eapply val_no_step; eauto.
	        -- apply IH.
	           ++ match goal with
	              | Hs : step e1 ?e1' |- _ => exact (Hnext1 _ Hs)
	              end.
	           ++ intros vx Hsteps.
              apply Hbody_sn.
              eapply Steps_step; eauto.
Qed.

Lemma strongly_normalizing_tlete_intro e1 e2 :
  body_tm e2 ->
  strongly_normalizing e1 ->
  (exists n2, forall vx, e1 →* tret vx ->
    strongly_normalizing_fuel n2 ({0 ~> vx} e2)) ->
  strongly_normalizing (tlete e1 e2).
Proof.
  intros Hbody [n1 Hsn1] [n2 Hbody_sn].
  exists (S (n1 + n2)).
  eapply strongly_normalizing_fuel_tlete_intro; eauto.
Qed.

Lemma must_terminating_tlete_intro e1 e2 :
  body_tm e2 ->
  must_terminating e1 ->
  (forall vx, e1 →* tret vx -> must_terminating ({0 ~> vx} e2)) ->
  must_terminating (tlete e1 e2).
Proof.
  intros Hbody Hmt1.
  induction Hmt1 as [e1 [vx [-> Hlc_vx]] | e1 Hcan Hnext IH];
    intros Hbody_mt.
  - apply Must_step.
    + exists ({0 ~> vx} e2).
      apply Step_head. apply HS_Ret.
      apply lc_lete_iff_body. split.
      * constructor. exact Hlc_vx.
      * exact Hbody.
    + intros e' Hstep.
      inversion Hstep; subst.
      * inversion H; subst; try discriminate.
        apply Hbody_mt.
        apply Steps_refl. constructor. exact Hlc_vx.
      * exfalso. eapply val_no_step; eauto.
  - apply Must_step.
    + destruct Hcan as [e1' Hstep1].
      exists (tlete e1' e2).
      apply Step_let.
      * exact Hstep1.
      * apply lc_lete_iff_body. split.
        -- exact (step_regular1 _ _ Hstep1).
        -- exact Hbody.
    + intros e' Hstep.
      inversion Hstep; subst.
      * inversion H; subst; try discriminate.
        destruct Hcan as [e1' Hstep1].
        exfalso. eapply val_no_step; eauto.
      * eapply IH.
        -- eassumption.
        -- intros vx Hsteps.
           apply Hbody_mt.
           eapply Steps_step; eauto.
Qed.

Lemma must_terminating_tlete_elim_e1 e1 e2 :
  must_terminating (tlete e1 e2) ->
  must_terminating e1.
Proof.
  intros Hmt.
  remember (tlete e1 e2) as e eqn:Heq.
  induction Hmt as [e Hres | e Hcan Hnext IH] in e1, e2, Heq |- *;
    subst e.
  - destruct Hres as [v [Hbad _]]. discriminate Hbad.
  - destruct Hcan as [e' Hstep_tlet].
    pose proof (step_regular1 _ _ Hstep_tlet) as Hlc_tlet.
    destruct e1 as [v|e1a e1b|op v|v1 v2|v et ef|root lft rgt|v el en].
    + apply lc_lete_iff_body in Hlc_tlet as [Hret _].
      apply lc_ret_iff_value in Hret.
      apply must_terminating_tret. exact Hret.
    + apply Must_step.
      * inversion Hstep_tlet; subst.
        -- inversion H; subst; try discriminate.
        -- unfold can_step. eauto.
      * intros e1' Hstep1.
        eapply IH.
        -- apply Step_let; [exact Hstep1|exact Hlc_tlet].
        -- reflexivity.
    + apply Must_step.
      * inversion Hstep_tlet; subst.
        -- inversion H; subst; try discriminate.
        -- unfold can_step. eauto.
      * intros e1' Hstep1.
        eapply IH.
        -- apply Step_let; [exact Hstep1|exact Hlc_tlet].
        -- reflexivity.
    + apply Must_step.
      * inversion Hstep_tlet; subst.
        -- inversion H; subst; try discriminate.
        -- unfold can_step. eauto.
      * intros e1' Hstep1.
        eapply IH.
        -- apply Step_let; [exact Hstep1|exact Hlc_tlet].
        -- reflexivity.
    + apply Must_step.
      * inversion Hstep_tlet; subst.
        -- inversion H; subst; try discriminate.
        -- unfold can_step. eauto.
      * intros e1' Hstep1.
        eapply IH.
        -- apply Step_let; [exact Hstep1|exact Hlc_tlet].
        -- reflexivity.
    + apply Must_step.
      * inversion Hstep_tlet; subst.
        -- inversion H; subst; try discriminate.
        -- unfold can_step. eauto.
      * intros e1' Hstep1.
        eapply IH.
        -- apply Step_let; [exact Hstep1|exact Hlc_tlet].
        -- reflexivity.
    + apply Must_step.
      * inversion Hstep_tlet; subst.
        -- inversion H; subst; try discriminate.
        -- unfold can_step. eauto.
      * intros e1' Hstep1.
        eapply IH.
        -- apply Step_let; [exact Hstep1|exact Hlc_tlet].
        -- reflexivity.
Qed.

Lemma must_terminating_tlete_elim_body e1 e2 vx :
  body_tm e2 ->
  e1 →* tret vx ->
  must_terminating (tlete e1 e2) ->
  must_terminating ({0 ~> vx} e2).
Proof.
  intros Hbody Hsteps Hmt.
  eapply must_terminating_steps_inv.
  - exact Hmt.
  - eapply steps_tlete_to_body; eauto.
Qed.

Lemma must_terminating_tapp_tm_fun_equiv e1 e2 vx :
  lc_tm e1 ->
  lc_tm e2 ->
  lc_value vx ->
  (forall vf, e1 →* tret vf <-> e2 →* tret vf) ->
  (must_terminating e1 <-> must_terminating e2) ->
  must_terminating (tapp_tm e1 vx) <->
  must_terminating (tapp_tm e2 vx).
Proof.
  intros Hlc1 Hlc2 Hvx Hresults Htotal.
  unfold tapp_tm.
  set (body := tapp (vbvar 0) (value_shift 0 vx)).
  assert (Hbody : body_tm body).
  { subst body. apply body_tapp_tm_body.
    rewrite value_shift_lc_id by exact Hvx. exact Hvx. }
  split; intros Happ.
  - eapply must_terminating_tlete_intro.
    + exact Hbody.
    + apply (proj1 Htotal).
      eapply must_terminating_tlete_elim_e1. exact Happ.
    + intros vf He2.
      eapply must_terminating_tlete_elim_body.
      * exact Hbody.
      * apply (proj2 (Hresults vf)). exact He2.
      * exact Happ.
  - eapply must_terminating_tlete_intro.
    + exact Hbody.
    + apply (proj2 Htotal).
      eapply must_terminating_tlete_elim_e1. exact Happ.
    + intros vf He1.
      eapply must_terminating_tlete_elim_body.
      * exact Hbody.
      * apply (proj1 (Hresults vf)). exact He1.
      * exact Happ.
Qed.

Lemma must_terminating_tapp_tm_ret_equiv vf vx :
  lc_value vf ->
  lc_value vx ->
  must_terminating (tapp_tm (tret vf) vx) <->
  must_terminating (tapp vf vx).
Proof.
  intros Hvf Hvx.
  split; intros Hmt.
  - unfold tapp_tm in Hmt.
    eapply must_terminating_tlete_elim_body in Hmt.
    + unfold open_one in Hmt.
      change (open_tm_inst 0 vf (tapp (vbvar 0) (value_shift 0 vx)))
        with (open_tm 0 vf (tapp (vbvar 0) (value_shift 0 vx))) in Hmt.
      cbn [open_tm open_value] in Hmt.
      rewrite value_shift_lc_id in Hmt by exact Hvx.
      unfold open_tm_inst in Hmt.
      cbn [open_tm open_value] in Hmt.
      rewrite open_rec_lc_value in Hmt by exact Hvx.
      rewrite decide_True in Hmt by lia.
      exact Hmt.
    + apply body_tapp_tm_body.
      rewrite value_shift_lc_id by exact Hvx. exact Hvx.
    + apply Steps_refl. constructor. exact Hvf.
  - unfold tapp_tm.
    eapply must_terminating_tlete_intro.
    + apply body_tapp_tm_body.
      rewrite value_shift_lc_id by exact Hvx. exact Hvx.
    + apply must_terminating_tret. exact Hvf.
    + intros vf' Hsteps.
      pose proof (value_steps_self vf (tret vf') Hsteps) as Heq.
      inversion Heq. subst vf'.
      unfold open_one.
      change (open_tm_inst 0 vf (tapp (vbvar 0) (value_shift 0 vx)))
        with (open_tm 0 vf (tapp (vbvar 0) (value_shift 0 vx))).
      cbn [open_tm open_value].
      rewrite value_shift_lc_id by exact Hvx.
      unfold open_tm_inst.
      cbn [open_tm open_value].
      rewrite open_rec_lc_value by exact Hvx.
      rewrite decide_True by lia.
      exact Hmt.
Qed.

Lemma must_terminating_tprim_const op c :
  lc_tm (tprim op (vconst c)) ->
  (exists c', prim_step op c c') ->
  must_terminating (tprim op (vconst c)).
Proof.
  intros Hlc [c' Hstep].
  apply Must_step.
  - exists (tret (vconst c')).
    apply Step_head. eapply HS_Op; eauto.
  - intros e' Hred.
    inversion Hred; subst.
    inversion H; subst; try solve [inversion H0].
    apply must_terminating_tret. constructor.
Qed.

Lemma must_terminating_lam_app_equiv T body v :
  lc_tm (tapp (vlam T body) v) ->
  must_terminating (tapp (vlam T body) v) <->
  must_terminating ({0 ~> v} body).
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_Beta. exact Hlc.
  - apply Must_step.
    + exists ({0 ~> v} body).
      apply Step_head. apply HS_Beta. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

Lemma must_terminating_fix_app_equiv Tf vf v :
  lc_tm (tapp (vfix Tf vf) v) ->
  must_terminating (tapp (vfix Tf vf) v) <->
  must_terminating (tapp ({0 ~> v} vf) (vfix Tf vf)).
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_Fix. exact Hlc.
  - apply Must_step.
    + exists (tapp ({0 ~> v} vf) (vfix Tf vf)).
      apply Step_head. apply HS_Fix. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

Lemma must_terminating_match_true_equiv et ef :
  lc_tm (tmatch (vconst (cbool true)) et ef) ->
  must_terminating (tmatch (vconst (cbool true)) et ef) <->
  must_terminating et.
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_MatchTrue. exact Hlc.
  - apply Must_step.
    + exists et. apply Step_head. apply HS_MatchTrue. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.

Lemma must_terminating_match_false_equiv et ef :
  lc_tm (tmatch (vconst (cbool false)) et ef) ->
  must_terminating (tmatch (vconst (cbool false)) et ef) <->
  must_terminating ef.
Proof.
  intros Hlc.
  split; intros Hmt.
  - eapply must_terminating_step_inv.
    + exact Hmt.
    + apply Step_head. apply HS_MatchFalse. exact Hlc.
  - apply Must_step.
    + exists ef. apply Step_head. apply HS_MatchFalse. exact Hlc.
    + intros e' Hstep.
      inversion Hstep; subst.
      inversion H; subst; try solve [inversion H0].
      exact Hmt.
Qed.
