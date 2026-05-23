(** * Concrete store interfaces *)

From ChoicePrelude Require Import Prelude StoreCore StoreKeyAction StoreRestrict StoreBind.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Definition Store : Type := @StoreA V atom _ _.
Definition LStore : Type := @StoreA V logic_var _ _.

Global Typeclasses Transparent Store LStore.

#[global] Instance store_empty : Empty Store := gmap_empty.
#[global] Instance store_lookup : Lookup atom V Store := lookup.
#[global] Instance store_partial_alter : PartialAlter atom V Store := gmap_partial_alter.
#[global] Instance store_insert : Insert atom V Store := map_insert.
#[global] Instance store_delete : Delete atom Store := map_delete.
#[global] Instance store_union : Union Store := map_union.
#[global] Instance store_singleton : SingletonM atom V Store := map_singleton.
#[global] Instance lstore_lookup : Lookup logic_var V LStore := lookup.

Definition store_compat (s1 s2 : Store) : Prop := storeA_compat s1 s2.

Definition store_restrict (s : Store) (X : aset) : Store := storeA_restrict s X.

Definition store_rekey (f : atom → atom) (s : Store) : Store :=
  storeA_rekey f s.

Definition store_swap (x y : atom) (s : Store) : Store :=
  store_rekey (key_swap x y) s.

Definition store_shift (k : nat) (s : Store) : Store :=
  store_rekey (key_shift k) s.

Definition store_bind (s1 s2 s : Store) : Prop := storeA_bind s1 s2 s.

Definition lstore_compat (s1 s2 : LStore) : Prop := storeA_compat s1 s2.

Definition lstore_restrict (s : LStore) (X : lvset) : LStore :=
  storeA_restrict s X.

Definition lstore_rekey (f : logic_var → logic_var) (s : LStore) : LStore :=
  storeA_rekey f s.

Definition lstore_swap (x y : logic_var) (s : LStore) : LStore :=
  lstore_rekey (key_swap x y) s.

Definition lstore_shift (k : nat) (s : LStore) : LStore :=
  lstore_rekey (key_shift k) s.

Lemma lstore_rekey_dom
    (f : logic_var → logic_var) (Hf : Inj (=) (=) f) (s : LStore) :
  dom (lstore_rekey f s : LStore) = set_map f (dom (s : LStore)).
Proof.
  unfold lstore_rekey.
  apply storeA_rekey_dom. exact Hf.
Qed.

Definition lstore_bind (s1 s2 s : LStore) : Prop := storeA_bind s1 s2 s.

Definition lc_lstore (s : LStore) : Prop := lc_lvars (dom s).

Definition LStoreOn (D : lvset) : Type :=
  StoreAOn (V:=V) (K:=logic_var) D.

Definition lso_store {D : lvset} (s : LStoreOn D) : LStore :=
  storeAO_store s.

Definition lso_dom {D : lvset} (s : LStoreOn D) :
  dom (lso_store s : LStore) = D :=
  storeAO_dom s.

Definition lstore_on_ext D (s1 s2 : LStoreOn D) :
  lso_store s1 = lso_store s2 ->
  s1 = s2.
Proof.
  apply storeA_on_ext.
Qed.

Definition lstore_on_restrict
    (D' : lvset) {D : lvset} (s : LStoreOn D)
    (Hsub : D' ⊆ D) : LStoreOn D'.
Proof.
  exact (storeA_on_restrict D' s Hsub).
Defined.

Definition lstore_on_rekey
    (f : logic_var → logic_var) (Hf : Inj (=) (=) f)
    {D : lvset} (s : LStoreOn D) : LStoreOn (set_map f D).
Proof.
  exact (storeA_on_rekey f Hf s).
Defined.

Lemma lstore_on_rekey_id_on_dom
    (f : logic_var → logic_var) (Hf : Inj (=) (=) f)
    (D : lvset) (s : LStoreOn D) :
  (forall v, v ∈ D -> f v = v) ->
  lso_store (lstore_on_rekey f Hf s) = lso_store s.
Proof.
  apply storeA_on_rekey_id_on_dom.
Qed.

Definition lstore_on_swap
    (a b : logic_var) {D : lvset} (s : LStoreOn D)
    : LStoreOn (gset_swap a b D).
Proof.
  exact (storeA_on_rekey (key_swap a b) (key_swap_inj a b) s).
Defined.

Definition lstore_on_open_back
    (k : nat) (x : atom) (D : lvset)
    (s : LStoreOn (lvars_open k x D)) : LStoreOn D.
Proof.
  refine {| storeAO_store := lstore_swap (LVBound k) (LVFree x) (lso_store s) |}.
  unfold lstore_swap, lstore_rekey.
  change (dom ((@storeA_rekey V logic_var _ _
      (key_swap (LVBound k) (LVFree x)) (lso_store s)) : gmap logic_var V) = D).
  rewrite storeA_rekey_dom by apply key_swap_inj.
  change (gset_swap (LVBound k) (LVFree x) (dom (lso_store s : LStore)) = D).
  rewrite (lso_dom s).
  rewrite lvars_open_unfold, gset_swap_involutive. reflexivity.
Defined.

Definition lstore_on_open_front
    (k : nat) (x : atom) {D : lvset} (s : LStoreOn D)
    : LStoreOn (lvars_open k x D).
Proof.
  refine {| storeAO_store :=
    lstore_swap (LVBound k) (LVFree x) (lso_store s) |}.
  unfold lstore_swap, lstore_rekey.
  change (dom ((@storeA_rekey V logic_var _ _
      (key_swap (LVBound k) (LVFree x)) (lso_store s)) : gmap logic_var V) =
    lvars_open k x D).
  rewrite storeA_rekey_dom by apply key_swap_inj.
  change (gset_swap (LVBound k) (LVFree x) (dom (lso_store s : LStore)) =
    lvars_open k x D).
  rewrite (lso_dom s), lvars_open_unfold. reflexivity.
Defined.

Lemma lstore_on_open_back_front k x D (s : LStoreOn D) :
  lstore_on_open_back k x D (lstore_on_open_front k x s) = s.
Proof.
  apply lstore_on_ext.
  unfold lstore_on_open_back, lstore_on_open_front. cbn [lso_store].
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ _ (LVBound k) (LVFree x)
      (@storeA_swap V logic_var _ _ _ (LVBound k) (LVFree x)
        (lso_store s)) =
    lso_store s).
  apply storeA_swap_involutive.
Qed.

Lemma lstore_on_open_front_back k x D
    (s : LStoreOn (lvars_open k x D)) :
  lstore_on_open_front k x (lstore_on_open_back k x D s) = s.
Proof.
  apply lstore_on_ext.
  unfold lstore_on_open_back, lstore_on_open_front. cbn [lso_store].
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ _ (LVBound k) (LVFree x)
      (@storeA_swap V logic_var _ _ _ (LVBound k) (LVFree x)
        (lso_store s)) =
    lso_store s).
  apply storeA_swap_involutive.
Qed.

End StoreInterface.
