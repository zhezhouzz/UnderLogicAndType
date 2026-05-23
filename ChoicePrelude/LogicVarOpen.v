(** * ChoicePrelude.LogicVarOpen

    Opening operations for logic-variable sets. *)

From ChoicePrelude Require Export LogicVarCore.

Definition logic_var_open_onesided (k : nat) (x : atom) (v : logic_var) : logic_var :=
  match v with
  | LVBound j => if decide (j = k) then LVFree x else LVBound j
  | LVFree y => LVFree y
  end.

Definition logic_var_open (k : nat) (x : atom) : logic_var → logic_var :=
  swap (LVBound k) (LVFree x).

Definition lvars_open (k : nat) (x : atom) (D : lvset) : lvset :=
  swap (LVBound k) (LVFree x) D.

Lemma logic_var_open_unfold k x v :
  logic_var_open k x v = eq_swap (LVBound k) (LVFree x) v.
Proof. reflexivity. Qed.

Lemma lvars_open_unfold k x D :
  lvars_open k x D = gset_swap (LVBound k) (LVFree x) D.
Proof. reflexivity. Qed.

Lemma logic_var_open_involutive k x v :
  logic_var_open k x (logic_var_open k x v) = v.
Proof.
  unfold logic_var_open. apply swap_involutive.
Qed.

Lemma lvars_open_involutive k x D :
  lvars_open k x (lvars_open k x D) = D.
Proof.
  unfold lvars_open. apply swap_involutive.
Qed.

Lemma lvars_open_fresh_index k x D :
  k ∉ lvars_bv D ->
  x ∉ lvars_fv D ->
  lvars_open k x D = D.
Proof.
  intros Hk Hx.
  rewrite lvars_open_unfold.
  apply gset_swap_fresh.
  - intros Hbad. apply Hk. rewrite lvars_bv_elem. exact Hbad.
  - intros Hbad. apply Hx. apply lvars_fv_elem. exact Hbad.
Qed.

Lemma lvars_fv_open_prime_except k x D :
  lvars_fv D ∖ {[x]} ⊆ lvars_fv (lvars_open k x D).
Proof.
  intros y Hy.
  apply elem_of_difference in Hy as [HyD Hyx].
  apply lvars_fv_elem.
  rewrite lvars_open_unfold. apply elem_of_gset_swap.
  rewrite elem_of_singleton in Hyx.
  rewrite key_swap_fresh by congruence.
  apply lvars_fv_elem. exact HyD.
Qed.

Lemma lvars_fv_open_prime_fresh k x D :
  x ∉ lvars_fv D ->
  lvars_fv D ⊆ lvars_fv (lvars_open k x D).
Proof.
  intros Hfresh y Hy.
  apply lvars_fv_open_prime_except.
  apply elem_of_difference. split; [exact Hy|].
  intros Hyx. apply Hfresh. rewrite elem_of_singleton in Hyx. subst y. exact Hy.
Qed.

Lemma logic_var_open_sym k x v :
  logic_var_open k x v = swap (LVFree x) (LVBound k) v.
Proof.
  unfold logic_var_open. apply swap_sym.
Qed.

Lemma lvars_open_sym k x D :
  lvars_open k x D = swap (LVFree x) (LVBound k) D.
Proof.
  unfold lvars_open. apply swap_sym.
Qed.

Lemma logic_var_open_onesided_eq_swap_fresh k x v :
  x ∉ logic_var_fv v →
  logic_var_open_onesided k x v = logic_var_open k x v.
Proof.
  destruct v as [j|y]; simpl.
  - unfold logic_var_open, swap, swap_action_self, eq_swap.
    repeat destruct decide; congruence.
  - intros Hfresh.
    unfold logic_var_open, swap, swap_action_self, eq_swap.
    rewrite not_elem_of_singleton in Hfresh.
    repeat destruct decide; congruence.
Qed.

Definition lvars_open_onesided (k : nat) (x : atom) (D : lvset) : lvset :=
  set_map (logic_var_open_onesided k x) D.

Lemma lvars_open_onesided_eq_swap_fresh k x D :
  x ∉ lvars_fv D →
  lvars_open_onesided k x D = lvars_open k x D.
Proof.
  intros Hfresh.
  apply set_eq. intros v.
  unfold lvars_open_onesided.
  rewrite lvars_open_unfold.
  unfold gset_swap.
  rewrite !elem_of_map.
  split.
  - intros [u [Hv Hu]]. exists u. split; [|exact Hu].
    rewrite Hv. apply logic_var_open_onesided_eq_swap_fresh.
    intros Hbad. apply Hfresh. apply lvars_fv_elem.
    destruct u as [j|y]; cbn [logic_var_fv] in Hbad;
      [set_solver | rewrite elem_of_singleton in Hbad; subst; exact Hu].
  - intros [u [Hv Hu]]. exists u. split; [|exact Hu].
    rewrite Hv. symmetry. apply logic_var_open_onesided_eq_swap_fresh.
    intros Hbad. apply Hfresh. apply lvars_fv_elem.
    destruct u as [j|y]; cbn [logic_var_fv] in Hbad;
      [set_solver | rewrite elem_of_singleton in Hbad; subst; exact Hu].
Qed.
