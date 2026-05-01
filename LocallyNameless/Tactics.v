From CoreLang Require Export Syntax.

(** * Shared locally-nameless proof helpers

    This file intentionally stays small: it provides the lightweight proof
    automation used by the CoreLang proof files, while the larger theorem
    statements live next to the CoreLang definitions. *)

Ltac crush_binders :=
  repeat match goal with
  | H : context[decide (?x = ?x)] |- _ =>
      rewrite decide_True in H by reflexivity
  | |- context[decide (?x = ?x)] =>
      rewrite decide_True by reflexivity
  | H : context[decide (?x = ?y)] |- _ =>
      rewrite decide_False in H by congruence
  | |- context[decide (?x = ?y)] =>
      rewrite decide_False by congruence
  end.

Ltac inv_lc :=
  repeat match goal with
  | H : lc_value (vconst _) |- _ => inversion H; subst; clear H
  | H : lc_value (vfvar _) |- _ => inversion H; subst; clear H
  | H : lc_value (vbvar _) |- _ => inversion H; subst; clear H
  | H : lc_value (vlam _ _) |- _ => inversion H; subst; clear H
  | H : lc_value (vfix _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tret _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tlete _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tprim _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tapp _ _) |- _ => inversion H; subst; clear H
  | H : lc_tm (tmatch _ _ _) |- _ => inversion H; subst; clear H
  end.

Ltac ln_simpl :=
  simpl in *; crush_binders; try set_solver; try congruence; eauto.

(** ** Small set facts used by locally-nameless scripts *)

Lemma setunion_cons_cons (x : atom) (s1 s2 : aset) :
  {[x]} ∪ s1 ∪ ({[x]} ∪ s2) = {[x]} ∪ s1 ∪ s2.
Proof. set_solver. Qed.

Lemma setunion_empty_left (s : aset) :
  ∅ ∪ s = s.
Proof. set_solver. Qed.

Lemma subseteq_subtract_both (x : atom) (s1 s2 : aset) :
  x ∉ s1 →
  x ∉ s2 →
  {[x]} ∪ s1 ⊆ {[x]} ∪ s2 →
  s1 ⊆ s2.
Proof. set_solver. Qed.

Lemma setunion_cons_right (x : atom) (s : aset) :
  s ∪ ({[x]} ∪ ∅) = {[x]} ∪ s.
Proof. set_solver. Qed.

Lemma subseteq_subtract_both' (x : atom) (s1 s2 : aset) :
  x ∉ s1 →
  x ∉ s2 →
  {[x]} ∪ s1 ⊆ s2 ∪ ({[x]} ∪ ∅) →
  s1 ⊆ s2.
Proof. set_solver. Qed.

Lemma subseteq_trans_cons (x : atom) (s1 s2 s3 : aset) :
  {[x]} ∪ s1 ⊆ {[x]} ∪ s2 →
  s2 ⊆ {[x]} ∪ s3 →
  {[x]} ∪ s1 ⊆ {[x]} ∪ s3.
Proof. set_solver. Qed.

Ltac pose_fresh_from x s :=
  let Hfresh := fresh "Hfresh" in
  pose (x := fresh_for s);
  assert (Hfresh : x ∉ s) by (subst x; apply fresh_for_not_in).
