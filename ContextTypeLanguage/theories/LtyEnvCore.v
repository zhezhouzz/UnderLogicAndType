(** * ContextTypeLanguage.LtyEnvCore

    Thin TypeLanguage names for [ty]-valued lvar stores.  The operations and
    laws live in [ContextStore]; this file only fixes the value type and
    provides the TypeLanguage instances used by opening notation. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export TypeOpen.

Notation lty_env := (@StoreA ty logic_var _ _) (only parsing).

Notation lty_env_shift_from :=
  (@lvar_store_shift_from ty) (only parsing).
Notation lty_env_shift :=
  (@lvar_store_shift ty) (only parsing).
Notation lty_env_open_one :=
  (@lvar_store_open_one ty) (only parsing).
Notation lty_env_closed :=
  (@lvar_store_closed ty) (only parsing).
Notation atom_env_to_lty_env :=
  (@atom_store_to_lvar_store ty) (only parsing).
Notation lty_env_open :=
  (@lvar_store_open ty) (only parsing).
Notation lty_env_to_atom_env :=
  (@lvar_store_to_atom_store ty) (only parsing).
Notation lty_env_open_lvars :=
  (@lvar_store_open_lvars ty) (only parsing).
Notation lty_env_atom_dom :=
  (@lvar_store_atom_dom ty) (only parsing).
Notation lty_env_bvar_scope :=
  (@lvar_store_bvar_scope ty) (only parsing).
Notation lty_env_swap :=
  (@lvar_store_swap ty) (only parsing).

Definition typed_lty_env_bind (Σ : lty_env) (T : ty) : lty_env :=
  <[LVBound 0 := T]> (lvar_store_shift Σ).

#[global] Instance stale_lty_env : Stale lty_env := lvar_store_atom_dom.
Arguments stale_lty_env /.

#[global] Instance open_lty_env_atom_inst : Open atom lty_env :=
  lvar_store_open_one.

#[global] Instance mopen_lty_env_inst :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lvar_store_open.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.
