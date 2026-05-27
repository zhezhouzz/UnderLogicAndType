(** * Atom-key finite-map environments

    This module is intentionally below ContextPrelude's generic [StoreA]
    interface.  CoreLang only needs atom-key maps, restriction, and bijective
    atom swapping for syntax/typing/substitution lemmas, so those operations
    live here instead of depending on the full store/resource stack. *)

From ContextBase Require Export Prelude.

#[global] Instance stale_atom_env {A} : Stale (gmap atom A) := dom.

Section AtomEnv.

Context {A : Type}.

Definition atom_env_swap (x y : atom) (m : gmap atom A) : gmap atom A :=
  kmap (atom_swap x y) m.

Definition store_swap := atom_env_swap.

Lemma atom_env_swap_lookup (x y : atom) (m : gmap atom A) (z : atom) :
  atom_env_swap x y m !! atom_swap x y z = m !! z.
Proof.
  unfold atom_env_swap.
  rewrite (lookup_kmap (M1:=gmap atom) (M2:=gmap atom)
    (Inj0:=atom_swap_inj x y) (atom_swap x y) m z).
  reflexivity.
Qed.

Lemma store_swap_lookup (x y : atom) (m : gmap atom A) (z : atom) :
  store_swap x y m !! atom_swap x y z = m !! z.
Proof.
  apply atom_env_swap_lookup.
Qed.

Lemma atom_env_swap_lookup_inv (x y : atom) (m : gmap atom A) (z : atom) :
  atom_env_swap x y m !! z = m !! atom_swap x y z.
Proof.
  rewrite <- (atom_swap_involutive x y z) at 1.
  apply atom_env_swap_lookup.
Qed.

Lemma store_swap_lookup_inv (x y : atom) (m : gmap atom A) (z : atom) :
  store_swap x y m !! z = m !! atom_swap x y z.
Proof.
  apply atom_env_swap_lookup_inv.
Qed.

Lemma atom_env_swap_dom (x y : atom) (m : gmap atom A) :
  dom (atom_env_swap x y m) = aset_swap x y (dom m).
Proof.
  unfold atom_env_swap, aset_swap.
  rewrite (dom_kmap_L (M:=gmap atom) (M2:=gmap atom)
    (Inj0:=atom_swap_inj x y) (atom_swap x y) m).
  reflexivity.
Qed.

Lemma store_swap_dom (x y : atom) (m : gmap atom A) :
  dom (store_swap x y m) = aset_swap x y (dom m).
Proof.
  apply atom_env_swap_dom.
Qed.

Lemma atom_env_swap_empty (x y : atom) :
  atom_env_swap x y (∅ : gmap atom A) = ∅.
Proof.
  apply map_eq. intros z.
  rewrite atom_env_swap_lookup_inv.
  rewrite !lookup_empty. reflexivity.
Qed.

Lemma store_swap_empty (x y : atom) :
  store_swap x y (∅ : gmap atom A) = ∅.
Proof.
  apply atom_env_swap_empty.
Qed.

Lemma atom_env_swap_involutive (x y : atom) (m : gmap atom A) :
  atom_env_swap x y (atom_env_swap x y m) = m.
Proof.
  apply map_eq. intros z.
  rewrite !atom_env_swap_lookup_inv, atom_swap_involutive. reflexivity.
Qed.

Lemma store_swap_involutive (x y : atom) (m : gmap atom A) :
  store_swap x y (store_swap x y m) = m.
Proof.
  apply atom_env_swap_involutive.
Qed.

Lemma atom_env_swap_sym (x y : atom) (m : gmap atom A) :
  atom_env_swap x y m = atom_env_swap y x m.
Proof.
  apply map_eq. intros z.
  rewrite !atom_env_swap_lookup_inv, atom_swap_sym. reflexivity.
Qed.

Lemma store_swap_sym (x y : atom) (m : gmap atom A) :
  store_swap x y m = store_swap y x m.
Proof.
  apply atom_env_swap_sym.
Qed.

Lemma atom_env_swap_delete (x y z : atom) (m : gmap atom A) :
  atom_env_swap x y (delete z m) =
  delete (atom_swap x y z) (atom_env_swap x y m).
Proof.
  unfold atom_env_swap.
  rewrite (kmap_delete (M1:=gmap atom) (M2:=gmap atom)
    (Inj0:=atom_swap_inj x y) (atom_swap x y) m z).
  reflexivity.
Qed.

Lemma store_swap_delete (x y z : atom) (m : gmap atom A) :
  store_swap x y (delete z m) =
  delete (atom_swap x y z) (store_swap x y m).
Proof.
  apply atom_env_swap_delete.
Qed.

Lemma atom_env_swap_insert (x y z : atom) (v : A) (m : gmap atom A) :
  atom_env_swap x y (<[z := v]> m) =
  <[atom_swap x y z := v]> (atom_env_swap x y m).
Proof.
  unfold atom_env_swap.
  rewrite (kmap_insert (M1:=gmap atom) (M2:=gmap atom)
    (Inj0:=atom_swap_inj x y) (atom_swap x y) m z v).
  reflexivity.
Qed.

Lemma store_swap_insert (x y z : atom) (v : A) (m : gmap atom A) :
  store_swap x y (<[z := v]> m) =
  <[atom_swap x y z := v]> (store_swap x y m).
Proof.
  apply atom_env_swap_insert.
Qed.

End AtomEnv.

Arguments atom_env_swap {_} _ _ _.
Arguments store_swap {_} _ _ _.
Arguments stale_atom_env /.
