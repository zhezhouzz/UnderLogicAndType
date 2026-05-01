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

