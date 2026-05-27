(** * ContextLogic.FormulaSyntaxTactics

    Small normalization tactics for formula syntax proofs.  These live below
    formula semantics so lower-layer proofs can use them without importing the
    denotation-level automation. *)

From ContextLogic Require Import FormulaSyntax.

Ltac formula_fv_syntax_norm :=
  unfold formula_fv;
  cbn [formula_lvars];
  rewrite ?formula_fv_true, ?formula_fv_false, ?formula_fv_atom;
  rewrite ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl;
  rewrite ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus;
  rewrite ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under;
  rewrite ?formula_fv_fibvars;
  rewrite ?lvars_fv_union.

Ltac formula_fv_syntax_norm_in H :=
  unfold formula_fv in H;
  cbn [formula_lvars] in H;
  rewrite ?formula_fv_true in H;
  rewrite ?formula_fv_false in H;
  rewrite ?formula_fv_atom in H;
  rewrite ?formula_fv_and in H;
  rewrite ?formula_fv_or in H;
  rewrite ?formula_fv_impl in H;
  rewrite ?formula_fv_star in H;
  rewrite ?formula_fv_wand in H;
  rewrite ?formula_fv_plus in H;
  rewrite ?formula_fv_forall in H;
  rewrite ?formula_fv_over in H;
  rewrite ?formula_fv_under in H;
  rewrite ?formula_fv_fibvars in H;
  rewrite ?lvars_fv_union in H.

