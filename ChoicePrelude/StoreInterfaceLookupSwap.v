(** * Concrete store lookup and swap interface lemmas *)

From ChoicePrelude Require Import Prelude StoreCore StoreKeyAction StoreRestrict StoreBind.
From ChoicePrelude Require Export StoreInterfaceCore.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

Lemma store_map_eq (s1 s2 : Store) :
  (∀ x, s1 !! x = s2 !! x) →
  s1 = s2.
Proof.
  apply storeA_map_eq.
Qed.

Lemma store_elem_of_dom_lookup_some (s : Store) x v :
  s !! x = Some v →
  x ∈ dom s.
Proof.
  apply storeA_elem_of_dom_lookup_some.
Qed.

Lemma store_lookup_none_of_not_elem_dom (s : Store) x :
  x ∉ dom s →
  s !! x = None.
Proof.
  apply storeA_lookup_none_of_not_elem_dom.
Qed.

Lemma store_lookup_insert_ne (s : Store) x z v :
  z ≠ x →
  <[x := v]> s !! z = s !! z.
Proof.
  apply storeA_lookup_insert_ne.
Qed.

Lemma store_lookup_union_Some_raw (s1 s2 : Store) i v :
  ((@union (gmap atom V) _ (s1 : gmap atom V) (s2 : gmap atom V)) !! i = Some v) ↔
    s1 !! i = Some v ∨ (s1 !! i = None ∧ s2 !! i = Some v).
Proof.
  apply storeA_lookup_union_Some_raw.
Qed.

Lemma store_lookup_none_of_dom (σ : Store) (X : aset) (x : atom) :
  dom σ = X →
  x ∉ X →
  σ !! x = None.
Proof.
  apply storeA_lookup_none_of_dom.
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

Lemma store_swap_dom (x y : atom) (s : Store) :
  dom (store_swap x y s) = aset_swap x y (dom s).
Proof.
  unfold store_swap, aset_swap.
  change (dom (storeA_swap x y s) = gset_swap x y (dom s)).
  apply storeA_swap_dom.
Qed.

Lemma lstore_restrict_dom (s : LStore) (X : lvset) :
  dom (lstore_restrict s X : LStore) = dom (s : LStore) ∩ X.
Proof.
  apply storeA_restrict_dom.
Qed.

Lemma lstore_swap_dom (a b : logic_var) (s : LStore) :
  dom (lstore_swap a b s : LStore) = gset_swap a b (dom (s : LStore)).
Proof.
  unfold lstore_swap, lstore_rekey.
  apply storeA_rekey_dom, key_swap_inj.
Qed.

Lemma store_swap_empty (x y : atom) :
  (store_swap x y (∅ : Store) : gmap atom V) = ∅.
Proof.
  apply store_map_eq. intros z.
  rewrite store_swap_lookup_inv.
  reflexivity.
Qed.

Lemma store_swap_involutive (x y : atom) (s : Store) :
  (store_swap x y (store_swap x y s) : gmap atom V) = s.
Proof.
  apply store_map_eq. intros z.
  rewrite !store_swap_lookup_inv, atom_swap_involutive. reflexivity.
Qed.

Lemma store_swap_sym (x y : atom) (s : Store) :
  (store_swap x y s : gmap atom V) = store_swap y x s.
Proof.
  apply store_map_eq. intros z.
  rewrite !store_swap_lookup_inv, atom_swap_sym. reflexivity.
Qed.

Lemma store_swap_fresh (x y : atom) (s : Store) :
  x ∉ dom s →
  y ∉ dom s →
  (store_swap x y s : gmap atom V) = s.
Proof.
  intros Hx Hy.
  apply store_map_eq. intros z.
  rewrite store_swap_lookup_inv.
  destruct (decide (z = x)) as [->|Hzx].
  - rewrite atom_swap_l.
    rewrite !store_lookup_none_of_not_elem_dom by assumption. reflexivity.
  - destruct (decide (z = y)) as [->|Hzy].
    + rewrite atom_swap_r.
      rewrite !store_lookup_none_of_not_elem_dom by assumption. reflexivity.
    + rewrite atom_swap_fresh by congruence. reflexivity.
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

Lemma store_swap_conjugate (a b x y : atom) (s : Store) :
  (store_swap a b (store_swap x y s) : gmap atom V) =
  store_swap (atom_swap a b x) (atom_swap a b y) (store_swap a b s).
Proof.
  apply store_map_eq. intros z.
  rewrite !store_swap_lookup_inv.
  rewrite atom_swap_conjugate_inv. reflexivity.
Qed.

Lemma store_swap_conjugate_inv (a b x y : atom) (s : Store) :
  (store_swap x y (store_swap a b s) : gmap atom V) =
  store_swap a b (store_swap (atom_swap a b x) (atom_swap a b y) s).
Proof.
  apply store_map_eq. intros z.
  rewrite !store_swap_lookup_inv.
  rewrite atom_swap_conjugate. reflexivity.
Qed.

Lemma store_swap_union (x y : atom) (s1 s2 : Store) :
  (store_swap x y (s1 ∪ s2) : gmap atom V) =
  store_swap x y s1 ∪ store_swap x y s2.
Proof.
  unfold store_swap.
  change (storeA_swap x y (s1 ∪ s2) =
    storeA_swap x y s1 ∪ storeA_swap x y s2).
  apply storeA_swap_union.
Qed.

Lemma store_shift_lookup k (s : Store) (z : atom) :
  ((store_shift k s : gmap atom V) !! z) = ((s : gmap atom V) !! z).
Proof.
  change (((storeA_shift k s : gmap atom V) !! key_shift k z) =
    ((s : gmap atom V) !! z)).
  apply storeA_shift_lookup.
Qed.

Lemma lstore_shift_lookup k (s : LStore) (z : logic_var) :
  ((lstore_shift k s : gmap logic_var V) !! key_shift k z) =
  ((s : gmap logic_var V) !! z).
Proof.
  apply storeA_shift_lookup.
Qed.

End StoreInterface.
