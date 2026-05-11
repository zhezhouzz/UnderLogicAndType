(** * CoreLang.StrongNormalization

    Step-indexed must-termination for the nondeterministic core language.

    The old denotational "totality" helper only recorded that an expression had
    at least one result.  That is too weak in the presence of generators: a
    typed term should not merely have a successful branch, it should have no
    diverging branch.  The fuel below measures the height of the whole reduction
    tree. *)

From CoreLang Require Import SmallStep OperationalProps.

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

(** The tlet facts below are intentionally stated at the operational layer.
    They are the principles the ChoiceTyping totality proof should use.  Their
    proofs are independent of refinements/resources, so they belong here even
    when later proof engineering temporarily admits them. *)

Lemma strongly_normalizing_tlete_elim_e1 e1 e2 :
  strongly_normalizing (tlete e1 e2) ->
  strongly_normalizing e1.
Proof.
Admitted.

Lemma strongly_normalizing_tlete_elim_body e1 e2 vx :
  body_tm e2 ->
  e1 →* tret vx ->
  strongly_normalizing (tlete e1 e2) ->
  strongly_normalizing ({0 ~> vx} e2).
Proof.
Admitted.

Lemma strongly_normalizing_tlete_intro e1 e2 :
  body_tm e2 ->
  strongly_normalizing e1 ->
  (forall vx, e1 →* tret vx -> strongly_normalizing ({0 ~> vx} e2)) ->
  strongly_normalizing (tlete e1 e2).
Proof.
Admitted.
