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

Definition expr_result_extension_on
    (X : aset) (e : tm) (x : atom)
    (Hfv : fv_tm e ⊆ X) (Hfresh : x ∉ X) : FiberExtensionT.
Proof.
  refine (mk_fiber_extension X {[x]}
    (fun σ => expr_result_output_world e x σ) _ _ _).
  - set_solver.
  - intros σ Hσ. unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
      as [Hex | _].
    + reflexivity.
    + unfold world_dom, singleton_world. simpl.
      apply dom_singleton_L.
  - intros σ Hσ. unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
      as [Hex | _].
    + destruct Hex as [v Heval].
      exists ({[x := v]} : StoreT).
      exists v. split; [exact Heval|reflexivity].
    + exists ({[x := inhabitant]} : StoreT). simpl. reflexivity.
Defined.

Lemma expr_result_extension_on_shape X e x Hfv Hfresh :
  ext_in (expr_result_extension_on X e x Hfv Hfresh) = X /\
  ext_out (expr_result_extension_on X e x Hfv Hfresh) = {[x]}.
Proof.
  unfold expr_result_extension_on, ext_in, ext_out, mk_fiber_extension.
  simpl. split; reflexivity.
Qed.

Record expr_result_extension_witness_on
    (X : aset) (e : tm) (x : atom) (Fx : FiberExtensionT) : Prop := {
  expr_result_extension_witness_on_fv : fv_tm e ⊆ X;
  expr_result_extension_witness_on_fresh : x ∉ X;
  expr_result_extension_witness_on_shape :
    ext_in Fx = X /\ ext_out Fx = {[x]};
  expr_result_extension_witness_on_rel :
    forall σ,
      dom σ = X ->
      ext_rel Fx σ (expr_result_output_world e x σ);
}.

Lemma expr_result_extension_witness_on_exists X e x :
  fv_tm e ⊆ X ->
  x ∉ X ->
  exists Fx, expr_result_extension_witness_on X e x Fx.
Proof.
  intros Hfv Hfresh.
  exists (expr_result_extension_on X e x Hfv Hfresh).
  constructor.
  - exact Hfv.
  - exact Hfresh.
  - apply expr_result_extension_on_shape.
  - intros σ Hdom.
    unfold expr_result_extension_on, ext_rel, mk_fiber_extension,
      mk_fiber_extension_rel.
    simpl. reflexivity.
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

Lemma expr_result_extension_witness_to_on e x Fx :
  expr_result_extension_witness e x Fx ->
  expr_result_extension_witness_on (fv_tm e) e x Fx.
Proof.
  intros [Hfresh Hshape Hrel].
  constructor.
  - set_solver.
  - exact Hfresh.
  - exact Hshape.
  - exact Hrel.
Qed.

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
  tm_eval_in_store σ e v ->
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
  destruct (excluded_middle_informative (exists v0, tm_eval_in_store σ e v0))
    as [Hex | Hnone].
  - exists v. split; [exact Heval|reflexivity].
  - exfalso. apply Hnone. exists v. exact Heval.
Qed.

Lemma expr_result_extension_apply_total_store_on X e x F σ w v :
  expr_result_extension_witness_on X e x F ->
  dom σ = X ->
  ext_rel F σ w ->
  tm_eval_in_store σ e v ->
  (w : WorldT) ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Heval.
  destruct Hwitness as [Hfv Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (proj2 (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) ({[x := v]} : StoreT)
    HdomF Hrel Hcanonical)) as Hto.
  apply Hto.
  unfold expr_result_output_world.
  destruct (excluded_middle_informative (exists v0, tm_eval_in_store σ e v0))
    as [Hex | Hnone].
  - exists v. split; [exact Heval|reflexivity].
  - exfalso. apply Hnone. exists v. exact Heval.
Qed.

Lemma expr_result_extension_apply_total_iff e x F σ w :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  (exists v, tm_eval_in_store σ e v) ->
  forall σout,
    (w : WorldT) σout <->
    exists v, tm_eval_in_store σ e v /\ σout = ({[x := v]} : StoreT).
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
    destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
      as [Hex | Hnone].
    + exact Hw.
    + exfalso. apply Hnone. exact Htotal.
  - intros [v [Heval ->]].
    apply Hext.
    unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v0, tm_eval_in_store σ e v0))
      as [Hex | Hnone].
    + exists v. split; [exact Heval|reflexivity].
    + exfalso. apply Hnone. exists v. exact Heval.
Qed.

Lemma expr_result_extension_apply_total_iff_on X e x F σ w :
  expr_result_extension_witness_on X e x F ->
  dom σ = X ->
  ext_rel F σ w ->
  (exists v, tm_eval_in_store σ e v) ->
  forall σout,
    (w : WorldT) σout <->
    exists v, tm_eval_in_store σ e v /\ σout = ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Htotal σout.
  destruct Hwitness as [Hfv Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) σout HdomF Hrel Hcanonical) as Hext.
  split.
  - intros Hw.
    apply Hext in Hw.
    unfold expr_result_output_world in Hw.
    destruct (excluded_middle_informative (exists v, tm_eval_in_store σ e v))
      as [Hex | Hnone].
    + exact Hw.
    + exfalso. apply Hnone. exact Htotal.
  - intros [v [Heval ->]].
    apply Hext.
    unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v0, tm_eval_in_store σ e v0))
      as [Hex | Hnone].
    + exists v. split; [exact Heval|reflexivity].
    + exfalso. apply Hnone. exists v. exact Heval.
Qed.

End TermDenotation.
