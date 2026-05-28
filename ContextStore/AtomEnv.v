(** * Atom-key finite-map environments

    This module is intentionally below ContextStore's generic [StoreA]
    interface.  CoreLang only needs atom-key maps, restriction, and bijective
    atom swapping for syntax/typing/substitution lemmas, so those operations
    live here instead of depending on the full store/resource stack. *)

From ContextBase Require Export Prelude.

#[global] Instance stale_atom_env {A} : Stale (gmap atom A) := dom.

Section AtomEnv.

Context {A : Type}.

Lemma kmap_swap_lookup (x y : atom) (m : gmap atom A) (z : atom) :
  (kmap (swap x y) m : gmap atom A) !! swap x y z = m !! z.
Proof.
  rewrite (lookup_kmap (M1:=gmap atom) (M2:=gmap atom)
    (Inj0:=swap_inj x y) (swap x y) m z).
  reflexivity.
Qed.

Lemma kmap_swap_lookup_inv (x y : atom) (m : gmap atom A) (z : atom) :
  (kmap (swap x y) m : gmap atom A) !! z = m !! swap x y z.
Proof.
  rewrite <- (swap_involutive x y z) at 1.
  apply kmap_swap_lookup.
Qed.

Lemma kmap_swap_dom (x y : atom) (m : gmap atom A) :
  dom (kmap (swap x y) m : gmap atom A) = set_swap x y (dom m).
Proof.
  unfold set_swap.
  rewrite (dom_kmap_L (M:=gmap atom) (M2:=gmap atom)
    (Inj0:=swap_inj x y) (swap x y) m).
  reflexivity.
Qed.

Lemma kmap_swap_empty (x y : atom) :
  (kmap (swap x y) (∅ : gmap atom A) : gmap atom A) = ∅.
Proof.
  apply map_eq. intros z.
  rewrite kmap_swap_lookup_inv.
  rewrite !lookup_empty. reflexivity.
Qed.

Lemma kmap_swap_involutive (x y : atom) (m : gmap atom A) :
  (kmap (swap x y) (kmap (swap x y) m : gmap atom A) : gmap atom A) = m.
Proof.
  apply map_eq. intros z.
  rewrite !kmap_swap_lookup_inv, swap_involutive. reflexivity.
Qed.

Lemma kmap_swap_sym (x y : atom) (m : gmap atom A) :
  (kmap (swap x y) m : gmap atom A) = kmap (swap y x) m.
Proof.
  apply map_eq. intros z.
  rewrite !kmap_swap_lookup_inv, swap_sym. reflexivity.
Qed.

Lemma kmap_swap_delete (x y z : atom) (m : gmap atom A) :
  (kmap (swap x y) (delete z m) : gmap atom A) =
  delete (swap x y z) (kmap (swap x y) m : gmap atom A).
Proof.
  rewrite (kmap_delete (M1:=gmap atom) (M2:=gmap atom)
    (Inj0:=swap_inj x y) (swap x y) m z).
  reflexivity.
Qed.

Lemma kmap_swap_insert (x y z : atom) (v : A) (m : gmap atom A) :
  (kmap (swap x y) (<[z := v]> m) : gmap atom A) =
  <[swap x y z := v]> (kmap (swap x y) m : gmap atom A).
Proof.
  rewrite (kmap_insert (M1:=gmap atom) (M2:=gmap atom)
    (Inj0:=swap_inj x y) (swap x y) m z v).
  reflexivity.
Qed.

End AtomEnv.

Arguments stale_atom_env /.
