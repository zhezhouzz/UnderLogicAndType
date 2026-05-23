(** * Concrete store restriction interface lemmas *)

From ChoicePrelude Require Import Prelude StoreCore StoreKeyAction StoreRestrict StoreBind.
From ChoicePrelude Require Export StoreInterfaceLookupSwap.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation LStore := (@StoreA V logic_var _ _) (only parsing).

Lemma map_restrict_store_lookup_some (s : Store) (X : aset) (z : atom) (v : V) :
  ((s : gmap atom V) !! z) = Some v →
  z ∈ X →
  (map_restrict V s X : gmap atom V) !! z = Some v.
Proof.
  apply storeA_restrict_lookup_some_2.
Qed.

Lemma map_restrict_store_lookup_none_l (s : Store) (X : aset) (z : atom) :
  ((s : gmap atom V) !! z) = None →
  (map_restrict V s X : gmap atom V) !! z = None.
Proof.
  apply storeA_restrict_lookup_none_l.
Qed.

Lemma map_restrict_store_lookup_none_r (s : Store) (X : aset) (z : atom) :
  z ∉ X →
  (map_restrict V s X : gmap atom V) !! z = None.
Proof.
  apply storeA_restrict_lookup_none_r.
Qed.

Lemma store_restrict_lookup (s : Store) (X : aset) (z : atom) :
  ((store_restrict s X : gmap atom V) !! z) =
  if decide (z ∈ X) then ((s : gmap atom V) !! z) else None.
Proof.
  apply storeA_restrict_lookup.
Qed.

Lemma store_restrict_dom (s : Store) (X : aset) :
  dom (store_restrict s X : gmap atom V) = dom (s : gmap atom V) ∩ X.
Proof.
  apply storeA_restrict_dom.
Qed.

Lemma store_restrict_dom_subset (s : Store) (X : aset) :
  dom (store_restrict s X : gmap atom V) ⊆ X.
Proof.
  apply storeA_restrict_dom_subset.
Qed.

Lemma store_restrict_empty (X : aset) :
  store_restrict (∅ : Store) X = (∅ : gmap atom V).
Proof.
  apply storeA_restrict_empty.
Qed.

Lemma store_restrict_empty_set (s : Store) :
  store_restrict s ∅ = (∅ : gmap atom V).
Proof.
  apply storeA_restrict_empty_set.
Qed.

Lemma store_restrict_idemp (s : Store) (X : aset) :
  dom (s : gmap atom V) ⊆ X → store_restrict s X = (s : gmap atom V).
Proof.
  apply storeA_restrict_idemp.
Qed.

Lemma store_restrict_restrict (s : Store) (X Y : aset) :
  store_restrict (store_restrict s X) Y = (store_restrict s (X ∩ Y) : gmap atom V).
Proof.
  apply storeA_restrict_restrict.
Qed.

Lemma store_restrict_twice_same (s : Store) (X : aset) :
  store_restrict (store_restrict s X) X = (store_restrict s X : gmap atom V).
Proof.
  apply storeA_restrict_twice_same.
Qed.

Lemma store_restrict_twice_subset (s : Store) (X Y : aset) :
  Y ⊆ X →
  store_restrict (store_restrict s X) Y = (store_restrict s Y : gmap atom V).
Proof.
  apply storeA_restrict_twice_subset.
Qed.

Lemma store_restrict_comm (s : Store) (X Y : aset) :
  store_restrict (store_restrict s X) Y =
  (store_restrict (store_restrict s Y) X : gmap atom V).
Proof.
  apply storeA_restrict_comm.
Qed.

Lemma store_restrict_idemp_eq (s : Store) (X : aset) :
  dom (s : gmap atom V) = X →
  store_restrict s X = (s : gmap atom V).
Proof.
  apply storeA_restrict_idemp_eq.
Qed.

Lemma store_restrict_insert_in (s : Store) (X : aset) (x : atom) (v : V) :
  x ∈ X →
  store_restrict (<[x := v]> s) X =
  <[x := v]> (store_restrict s X : gmap atom V).
Proof.
  apply storeA_restrict_insert_in.
Qed.

Lemma store_restrict_insert_notin (s : Store) (X : aset) (x : atom) (v : V) :
  x ∉ X →
  store_restrict (<[x := v]> s) X =
  (store_restrict s X : gmap atom V).
Proof.
  apply storeA_restrict_insert_notin.
Qed.

Lemma store_restrict_lookup_some (s : Store) (X : aset) (x : atom) (y : V) :
  ((store_restrict s X : gmap atom V) !! x) = Some y →
  x ∈ X ∧ ((s : gmap atom V) !! x) = Some y.
Proof.
  apply storeA_restrict_lookup_some.
Qed.

Lemma store_restrict_lookup_some_2 (s : Store) (X : aset) (x : atom) (y : V) :
  ((s : gmap atom V) !! x) = Some y →
  x ∈ X →
  ((store_restrict s X : gmap atom V) !! x) = Some y.
Proof.
  apply storeA_restrict_lookup_some_2.
Qed.

Lemma store_restrict_eq_mono (s1 s2 : Store) (X Y : aset) :
  X ⊆ Y →
  (store_restrict s1 Y : gmap atom V) = store_restrict s2 Y →
  (store_restrict s1 X : gmap atom V) = store_restrict s2 X.
Proof. apply storeA_restrict_eq_mono. Qed.


Lemma store_restrict_lookup_transport (s1 s2 : Store) (X : aset) (x : atom) (v : V) :
  x ∈ X →
  (store_restrict s1 X : gmap atom V) = store_restrict s2 X →
  s1 !! x = Some v →
  s2 !! x = Some v.
Proof. apply storeA_restrict_lookup_transport. Qed.


Lemma store_restrict_swap (x y : atom) (s : Store) (X : aset) :
  (store_restrict (store_swap x y s) (aset_swap x y X) : gmap atom V) =
  store_swap x y (store_restrict s X).
Proof.
  unfold store_restrict, store_swap, aset_swap.
  apply storeA_restrict_swap.
Qed.

Lemma map_restrict_store_swap_fresh (x y : atom) (s : Store) (X : aset) :
  x ∉ X →
  y ∉ X →
  (map_restrict V (store_swap x y s) X : gmap atom V) = map_restrict V s X.
Proof.
  unfold store_swap, store_restrict, storeA_restrict.
  apply storeA_restrict_swap_fresh.
Qed.

Lemma store_restrict_empty_union_elements (σ : Store) (X : aset) :
  (store_restrict ((∅ : Store) ∪ store_restrict σ (list_to_set (elements X) : aset)) X : gmap atom V) =
  store_restrict σ X.
Proof. apply storeA_restrict_empty_union_elements. Qed.


Lemma store_restrict_empty_union_elements_subset
    (σ τ : Store) (X F : aset) :
  F ⊆ X →
  (store_restrict τ X : gmap atom V) = σ →
  (store_restrict
    (store_restrict ((∅ : Store) ∪ store_restrict τ (list_to_set (elements X) : aset)) X)
    F : gmap atom V) =
  store_restrict σ F.
Proof. apply storeA_restrict_empty_union_elements_subset. Qed.


Lemma store_restrict_induce_disjoint (s1 s2 : Store) :
  s1 ##ₘ (store_restrict s2 (dom s2 ∖ dom s1)) ∧
  s1 ∪ s2 = s1 ∪ (store_restrict s2 (dom s2 ∖ dom s1) : gmap atom V).
Proof. apply storeA_restrict_induce_disjoint. Qed.


Lemma store_restrict_union (s1 s2 : Store) (X : aset) :
  store_compat s1 s2 →
  (store_restrict (s1 ∪ s2) X : gmap atom V) =
  store_restrict s1 X ∪ store_restrict s2 X.
Proof. apply storeA_restrict_union. Qed.


Lemma store_restrict_union_cover (s1 s2 : Store) (X1 X2 : aset) :
  store_compat s1 s2 →
  X1 ⊆ dom s1 →
  X2 ⊆ dom s2 →
  (store_restrict (s1 ∪ s2) (X1 ∪ X2) : gmap atom V) =
  store_restrict s1 X1 ∪ store_restrict s2 X2.
Proof. apply storeA_restrict_union_cover. Qed.


Lemma store_restrict_insert_singleton (σ : Store) (x : atom) (v : V) :
  (store_restrict (<[x := v]> σ) {[x]} : gmap atom V) = {[x := v]}.
Proof. apply storeA_restrict_insert_singleton. Qed.


Lemma store_restrict_singleton_lookup (σ : Store) (x : atom) (v : V) :
  σ !! x = Some v →
  (store_restrict σ {[x]} : gmap atom V) = {[x := v]}.
Proof. apply storeA_restrict_singleton_lookup. Qed.


Lemma store_restrict_insert_singleton_ne
    (σ : Store) (x y : atom) (v : V) :
  x ≠ y →
  (store_restrict (<[x := v]> σ) {[y]} : gmap atom V) = store_restrict σ {[y]}.
Proof. apply storeA_restrict_insert_singleton_ne. Qed.


Lemma store_restrict_insert_fresh_union
    (σ : Store) (X : aset) (x : atom) (v : V) :
  σ !! x = None →
  x ∉ X →
  (store_restrict (<[x := v]> σ) (X ∪ {[x]}) : gmap atom V) =
  <[x := v]> (store_restrict σ X).
Proof. apply storeA_restrict_insert_fresh_union. Qed.


Lemma store_restrict_insert_fresh_union_lookup_none
    (σ : Store) (X : aset) (x : atom) (v : V) :
  σ !! x = None →
  x ∉ X →
  (<[x := v]> (store_restrict σ X) : Store) !! x = Some v.
Proof. apply storeA_restrict_insert_fresh_union_lookup_none. Qed.


Lemma store_restrict_union_singleton_insert
    (σ : Store) (X : aset) (x : atom) (v : V) :
  dom σ ⊆ X →
  x ∉ X →
  (store_restrict (σ ∪ {[x := v]}) (X ∪ {[x]}) : gmap atom V) = <[x := v]> σ.
Proof. apply storeA_restrict_union_singleton_insert. Qed.


Lemma store_restrict_union_from_parts
    (σ ρ σx : Store) (S : aset) (x : atom) :
  x ∉ S →
  (store_restrict σ S : gmap atom V) = ρ →
  (store_restrict σ {[x]} : gmap atom V) = σx →
  (store_restrict σ (S ∪ {[x]}) : gmap atom V) = ρ ∪ σx.
Proof. apply storeA_restrict_union_from_parts. Qed.


Lemma store_eq_insert_of_restrict_singleton
    (X : aset) (σx σ : Store) (ν : atom) (vx : V) :
  dom σx = X ∪ {[ν]} →
  ν ∉ X →
  (store_restrict σx X : gmap atom V) = σ →
  (store_restrict σx {[ν]} : gmap atom V) = {[ν := vx]} →
  σx = <[ν := vx]> σ.
Proof. apply storeA_eq_insert_of_restrict_singleton. Qed.


Lemma store_restrict_union_partition (s : Store) (X Y : aset) :
  dom s ⊆ X ∪ Y →
  X ∩ Y = ∅ →
  (store_restrict s X : gmap atom V) ∪ store_restrict s Y = s.
Proof. apply storeA_restrict_union_partition. Qed.


Lemma store_restrict_union_piece_l (s1 s2 : Store) (X Y : aset) :
  store_compat s1 s2 →
  dom s1 ⊆ X →
  dom s2 ⊆ Y →
  Y ∩ X = ∅ →
  (store_restrict (s1 ∪ s2) X : gmap atom V) = s1.
Proof. apply storeA_restrict_union_piece_l. Qed.


Lemma store_restrict_union_piece_r (s1 s2 : Store) (X Y : aset) :
  store_compat s1 s2 →
  dom s1 ⊆ X →
  dom s2 ⊆ Y →
  X ∩ Y = ∅ →
  (store_restrict (s1 ∪ s2) Y : gmap atom V) = s2.
Proof. apply storeA_restrict_union_piece_r. Qed.


Lemma store_restrict_union_base_singleton (s1 s2 : Store) (D : aset) (y : atom) :
  D ⊆ dom s1 →
  dom s2 = D ∪ {[y]} →
  y ∉ dom s1 →
  (store_restrict s1 D : gmap atom V) = store_restrict s2 D →
  (store_restrict (s1 ∪ store_restrict s2 {[y]}) (D ∪ {[y]}) : gmap atom V) = s2.
Proof. apply storeA_restrict_union_base_singleton. Qed.


Lemma store_restrict_wand_product
    (sn sm : Store) (S X Y : aset) :
  store_compat (store_restrict sn X) sm →
  store_compat sn (store_restrict sm S) →
  Y ⊆ S →
  Y ⊆ dom sm →
  (store_restrict (sn ∪ store_restrict sm S) Y : gmap atom V) =
  store_restrict (store_restrict sn X ∪ sm) Y.
Proof. apply storeA_restrict_wand_product. Qed.

End StoreInterface.
