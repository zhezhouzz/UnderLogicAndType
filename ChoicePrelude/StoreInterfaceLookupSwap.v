(** * Concrete store lookup and swap interface lemmas *)

From ChoicePrelude Require Import Prelude StoreCore StoreKeyAction StoreRestrict StoreBind.
From ChoicePrelude Require Export StoreInterfaceCore.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

Lemma store_lookup_none_of_not_elem_dom (s : Store) x :
  x ∉ dom s →
  s !! x = None.
Proof.
  apply storeA_lookup_none_of_not_elem_dom.
Qed.

Lemma store_lookup_union_Some_raw (s1 s2 : Store) i v :
  ((@union (gmap atom V) _ (s1 : gmap atom V) (s2 : gmap atom V)) !! i = Some v) ↔
    s1 !! i = Some v ∨ (s1 !! i = None ∧ s2 !! i = Some v).
Proof.
  apply storeA_lookup_union_Some_raw.
Qed.

Lemma atom_swap_inj x y : Inj (=) (=) (atom_swap x y).
Proof.
  intros z1 z2 Heq.
  rewrite <- (atom_swap_involutive x y z1).
  rewrite <- (atom_swap_involutive x y z2).
  by rewrite Heq.
Qed.

Lemma store_swap_lookup (x y : atom) (s : Store) (z : atom) :
  ((store_swap x y s : gmap atom V) !! atom_swap x y z) =
  ((s : gmap atom V) !! z).
Proof.
  unfold store_swap.
  change (((storeA_swap x y s : gmap atom V) !! key_swap x y z) =
    ((s : gmap atom V) !! z)).
  apply storeA_swap_lookup.
Qed.

Lemma store_swap_lookup_inv (x y : atom) (s : Store) (z : atom) :
  ((store_swap x y s : gmap atom V) !! z) =
  ((s : gmap atom V) !! atom_swap x y z).
Proof.
  rewrite <- (atom_swap_involutive x y z) at 1.
  apply store_swap_lookup.
Qed.

Lemma lstore_swap_fresh (a b : logic_var) (s : LStore) :
  a ∉ dom (s : LStore) ->
  b ∉ dom (s : LStore) ->
  lstore_swap a b s = s.
Proof.
  intros Ha Hb.
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ _ a b s = s).
  apply storeA_swap_fresh; assumption.
Qed.

Lemma lstore_swap_commute_fresh
    (a b c d : logic_var) (s : LStore) :
  c <> a ->
  c <> b ->
  d <> a ->
  d <> b ->
  lstore_swap a b (lstore_swap c d s) =
  lstore_swap c d (lstore_swap a b s).
Proof.
  intros Hca Hcb Hda Hdb.
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ _ a b
      (@storeA_swap V logic_var _ _ _ c d s) =
    @storeA_swap V logic_var _ _ _ c d
      (@storeA_swap V logic_var _ _ _ a b s)).
  rewrite storeA_swap_conjugate.
  replace (key_swap a b c) with c by (symmetry; apply key_swap_fresh; congruence).
  replace (key_swap a b d) with d by (symmetry; apply key_swap_fresh; congruence).
  reflexivity.
Qed.

Lemma store_swap_delete (x y z : atom) (s : Store) :
  (store_swap x y (delete z s) : gmap atom V) =
  delete (atom_swap x y z) (store_swap x y s).
Proof.
  unfold store_swap.
  change (storeA_swap x y (delete z s) =
    delete (key_swap x y z) (storeA_swap x y s)).
  apply storeA_swap_delete.
Qed.

Lemma store_swap_insert (x y z : atom) (v : V) (s : Store) :
  (store_swap x y (<[z := v]> s) : gmap atom V) =
  <[atom_swap x y z := v]> (store_swap x y s).
Proof.
  unfold store_swap.
  change (storeA_swap x y (<[z := v]> s) =
    <[key_swap x y z := v]> (storeA_swap x y s)).
  apply storeA_swap_insert.
Qed.

End StoreInterface.
