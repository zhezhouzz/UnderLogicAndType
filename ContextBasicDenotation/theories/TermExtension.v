(** * BasicDenotation.TermExtension

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Import TermEval TermOpen.

Section TermDenotation.

Lemma expr_result_extension_shape e x Hfresh :
  ext_in (expr_result_extension e x Hfresh) = fv_tm e /\
  ext_out (expr_result_extension e x Hfresh) = {[x]}.
Proof.
  unfold expr_result_extension, ext_in, ext_out, mk_fiber_extension.
  simpl. split; reflexivity.
Qed.

Record expr_result_extension_witness
    (e : tm) (x : atom) (Fx : FiberExtensionT) : Prop := {
  expr_result_extension_witness_fresh : x ∉ fv_tm e;
  expr_result_extension_witness_shape :
    ext_in Fx = fv_tm e /\ ext_out Fx = {[x]};
  expr_result_extension_witness_rel :
    forall σ,
      dom σ = fv_tm e ->
      ext_rel Fx σ (expr_result_output_world e x σ);
}.

Lemma expr_result_extension_witness_exists e x :
  x ∉ fv_tm e ->
  exists Fx, expr_result_extension_witness e x Fx.
Proof.
  intros Hfresh.
  exists (expr_result_extension e x Hfresh).
  constructor.
  - exact Hfresh.
  - apply expr_result_extension_shape.
  - intros σ Hdom.
    unfold expr_result_extension, ext_rel, mk_fiber_extension,
      mk_fiber_extension_rel.
    simpl. reflexivity.
Qed.

Lemma expr_result_extension_apply_total_store e x F σ w v :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  expr_eval_in_atom_store σ e v ->
  (w : WorldT) ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Heval.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (proj2 (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) ({[x := v]} : StoreT)
    HdomF Hrel Hcanonical)) as Hto.
  apply Hto.
  unfold expr_result_output_world.
  destruct (excluded_middle_informative (exists v0, expr_eval_in_atom_store σ e v0))
    as [Hex | Hnone].
  - destruct (constructive_indefinite_description _ Hex) as [v0 Heval0].
    assert (v0 = v).
    {
      unfold expr_eval_in_atom_store, expr_eval_in_store in *.
      eapply steps_result_unique; eauto.
    }
    subst v0. simpl. reflexivity.
  - exfalso. apply Hnone. exists v. exact Heval.
Qed.

Lemma expr_result_extension_apply_total_iff e x F σ w :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  (exists v, expr_eval_in_atom_store σ e v) ->
  forall σout,
    (w : WorldT) σout <->
    exists v, expr_eval_in_atom_store σ e v /\ σout = ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Htotal σout.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) σout HdomF Hrel Hcanonical) as Hext.
  split.
  - intros Hw.
    apply Hext in Hw.
    unfold expr_result_output_world in Hw.
    destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
      as [Hex | Hnone].
    + destruct (constructive_indefinite_description _ Hex) as [v Hv].
      exists v. split; [exact Hv|].
      simpl in Hw. subst σout. reflexivity.
    + exfalso. apply Hnone. exact Htotal.
  - intros [v [Heval ->]].
    eapply expr_result_extension_apply_total_store; eauto.
	    constructor; [exact Hfresh|split; assumption|exact Hwrel].
Qed.

End TermDenotation.
