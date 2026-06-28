(** * ContextTyping.SoundnessCaseTactics

    Deterministic proof-start tactics for split Fundamental/Soundness cases.

    These tactics only perform the common wrapper work shared by many case
    lemmas: opening an entailment goal, applying already-available entailment
    hypotheses to the current context model, running regular extraction, and
    normalizing denotation wrappers.  They deliberately do not solve the
    semantic core of any case. *)

From Denotation Require Import Context.
From ContextTyping Require Import Typing TypingRegular.

Ltac soundness_intro_entailment :=
  repeat match goal with
  | |- ?P ⊫ ?Q =>
      let m := fresh "m" in
      let Hctx := fresh "Hctx" in
      intros m Hctx
  end.

Ltac soundness_pose_entailment_once :=
  match goal with
  | Hent : ?P ⊫ ?Q,
    Hctx : ?m ⊨ ?P |- _ =>
      lazymatch goal with
      | H : m ⊨ Q |- _ => fail
      | _ =>
          let H := fresh "Hden" in
          pose proof (Hent m Hctx) as H
      end
  end.

Ltac soundness_pose_entailments :=
  repeat soundness_pose_entailment_once.

Ltac soundness_unfold_ty_denotes :=
  repeat match goal with
  | H : _ ⊨ ty_denote_under _ _ _ _ |- _ =>
      unfold ty_denote_under, ty_denote in H
  end;
  unfold ty_denote_under, ty_denote.

Ltac soundness_case_start :=
  intros;
  soundness_intro_entailment;
  soundness_pose_entailments;
  soundness_regular.

