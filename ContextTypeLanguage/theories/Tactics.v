(** * ContextTypeLanguage.Tactics

    Lightweight normalization helpers for the syntax/type-language layer. *)

From ContextTypeLanguage Require Export Notation.

Ltac mopen_norm :=
  rewrite ?mopen_insert_norm.

Ltac type_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X))
      | gmap logic_var ty => change (into_lvars X) with (dom X)
      end
  | H : context[into_lvars ?X] |- _ =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X in H
      | aset => change (into_lvars X) with (lvars_of_atoms X) in H
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X)) in H
      | gmap logic_var ty => change (into_lvars X) with (dom X) in H
      end
  end.

Ltac type_env_norm :=
  rewrite ?open_cty_env_empty in *;
  rewrite ?lty_env_atom_dom_shift in *.
