(** * CoreLang.StrongNormalization

    Step-indexed must-termination for the deterministic core language.  The
    fuel below measures the height of the reduction tree; in the deterministic
    setting that tree is at most a path, but the stronger formulation remains
    convenient for existing totality lemmas. *)

From Stdlib Require Import Lia.
From CoreLang Require Import SmallStep OperationalProps LocallyNamelessProps.

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
    They are the principles the ChoiceTyping totality proof should use.  Their
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
      destruct e1 as [v|op v|v1 v2|e1a e1b|v et ef].
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
