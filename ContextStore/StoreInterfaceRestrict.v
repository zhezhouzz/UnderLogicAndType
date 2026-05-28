(** * Concrete store restriction interface lemmas *)

From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import StoreCore StoreKeyAction StoreRestrictCore StoreRestrictUnion StoreBind.
From ContextStore Require Export StoreInterfaceCore.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Local Notation Store := (@StoreA V atom _ _) (only parsing).
Local Notation store_restrict := storeA_restrict (only parsing).

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

Lemma store_restrict_union_base_project
    (sbase sfull : Store) (X : aset) (y : atom) :
  X ⊆ dom sbase ->
  dom sfull = dom sbase ∪ {[y]} ->
  y ∉ dom sbase ->
  (store_restrict sfull X : gmap atom V) = store_restrict sbase X ->
  (store_restrict
    (sbase ∪ store_restrict sfull {[y]})
    (X ∪ {[y]}) : gmap atom V) =
  store_restrict sfull (X ∪ {[y]}).
Proof. apply storeA_restrict_union_base_project. Qed.

End StoreInterface.
