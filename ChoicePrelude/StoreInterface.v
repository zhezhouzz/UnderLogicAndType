(** * Concrete store interfaces *)

From ChoicePrelude Require Export StoreBind.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Definition Store : Type := @StoreA V atom _ _.
Definition LStore : Type := @StoreA V logic_var _ _.

Typeclasses Transparent Store LStore.

#[global] Instance store_empty : Empty Store := gmap_empty.
#[global] Instance store_partial_alter : PartialAlter atom V Store := gmap_partial_alter.
#[global] Instance store_insert : Insert atom V Store := map_insert.
#[global] Instance store_delete : Delete atom Store := map_delete.
#[global] Instance store_union : Union Store := map_union.
#[global] Instance store_singleton : SingletonM atom V Store := map_singleton.

Definition store_compat (s1 s2 : Store) : Prop := storeA_compat s1 s2.

Definition store_restrict (s : Store) (X : aset) : Store := storeA_restrict s X.

Definition store_swap (x y : atom) (s : Store) : Store :=
  storeA_swap x y s.

Definition store_shift (k : nat) (s : Store) : Store :=
  storeA_shift k s.

Definition store_bind (s1 s2 s : Store) : Prop := storeA_bind s1 s2 s.

Definition lstore_compat (s1 s2 : LStore) : Prop := storeA_compat s1 s2.

Definition lstore_restrict (s : LStore) (X : lvset) : LStore :=
  storeA_restrict s X.

Definition lstore_swap (x y : logic_var) (s : LStore) : LStore :=
  storeA_swap x y s.

Definition lstore_shift (k : nat) (s : LStore) : LStore :=
  storeA_shift k s.

Definition lstore_bind (s1 s2 s : LStore) : Prop := storeA_bind s1 s2 s.

Definition lc_lstore (s : LStore) : Prop := lc_lvars (dom s).

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


Lemma store_compat_refl (s : Store) : store_compat s s.
Proof.
  apply storeA_compat_refl.
Qed.

Lemma store_compat_sym (s1 s2 : Store) :
  store_compat s1 s2 → store_compat s2 s1.
Proof.
  apply storeA_compat_sym.
Qed.

Lemma store_compat_swap (x y : atom) (s1 s2 : Store) :
  store_compat (store_swap x y s1) (store_swap x y s2) ↔
  store_compat s1 s2.
Proof. apply storeA_compat_swap. Qed.

Lemma store_compat_union_inv_l (s1 s2 s3 : Store) :
  store_compat (s1 ∪ s2) s3 →
  store_compat s1 s3.
Proof. apply storeA_compat_union_inv_l. Qed.

Lemma store_compat_union_inv_r (s1 s2 s3 : Store) :
  store_compat s1 s2 →
  store_compat (s1 ∪ s2) s3 →
  store_compat s2 s3.
Proof. apply storeA_compat_union_inv_r. Qed.

Lemma store_compat_union_intro_r (s1 s2 s3 : Store) :
  store_compat s1 s2 →
  store_compat s1 s3 →
  store_compat s1 (s2 ∪ s3).
Proof. apply storeA_compat_union_intro_r. Qed.

Lemma store_union_comm (s1 s2 : Store) :
  store_compat s1 s2 →
  s1 ∪ s2 = s2 ∪ s1.
Proof. apply storeA_union_comm. Qed.

Lemma store_union_absorb_l (s1 s2 : Store) :
  store_compat s1 s2 →
  dom s2 ⊆ dom s1 →
  s1 ∪ s2 = s1.
Proof. apply storeA_union_absorb_l. Qed.

Lemma store_union_absorb_r (s1 s2 : Store) :
  store_compat s1 s2 →
  dom s1 ⊆ dom s2 →
  s1 ∪ s2 = s2.
Proof. apply storeA_union_absorb_r. Qed.

Lemma store_compat_insert_l_fresh (s1 s2 : Store) (x : atom) (v : V) :
  store_compat s1 s2 →
  x ∉ dom s2 →
  store_compat (<[x := v]> (s1 : gmap atom V)) s2.
Proof. apply storeA_compat_insert_l_fresh. Qed.

Lemma store_compat_insert_r_fresh (s1 s2 : Store) (x : atom) (v : V) :
  store_compat s1 s2 →
  x ∉ dom s1 →
  store_compat s1 (<[x := v]> (s2 : gmap atom V)).
Proof. apply storeA_compat_insert_r_fresh. Qed.

Lemma store_insert_union_l (s1 s2 : Store) (x : atom) (v : V) :
  (<[x := v]> s1 : gmap atom V) ∪ s2 = <[x := v]> (s1 ∪ s2).
Proof. apply storeA_insert_union_l. Qed.

Lemma store_insert_union_l_fresh (s1 s2 : Store) (x : atom) (v : V) :
  x ∉ dom s2 →
  (<[x := v]> s1 : gmap atom V) ∪ s2 = <[x := v]> (s1 ∪ s2).
Proof. apply storeA_insert_union_l_fresh. Qed.

Lemma store_insert_union_r_fresh (s1 s2 : Store) (x : atom) (v : V) :
  x ∉ dom s1 →
  s1 ∪ (<[x := v]> s2 : gmap atom V) = <[x := v]> (s1 ∪ s2).
Proof. apply storeA_insert_union_r_fresh. Qed.

Lemma store_union_singleton_insert_fresh (σ : Store) (x : atom) (v : V) :
  x ∉ dom σ →
  σ ∪ ({[x := v]} : Store) = <[x := v]> σ.
Proof. apply storeA_union_singleton_insert_fresh. Qed.

Lemma store_union_dom (s1 s2 : Store) :
  store_compat s1 s2 →
  dom (s1 ∪ s2) = dom s1 ∪ dom s2.
Proof. apply storeA_union_dom. Qed.

Lemma disj_dom_store_compat (s1 s2 : Store) :
  dom s1 ∩ dom s2 = ∅ → store_compat s1 s2.
Proof. apply storeA_disj_dom_compat. Qed.

Lemma store_compat_restrict_singleton_fresh (s1 s2 : Store) (y : atom) :
  y ∉ dom s1 →
  store_compat s1 (store_restrict s2 {[y]}).
Proof. apply storeA_compat_restrict_singleton_fresh. Qed.

Lemma store_compat_restrict (s1 s2 : Store) (X : aset) :
  store_compat s1 s2 →
  store_compat (store_restrict s1 X) (store_restrict s2 X).
Proof. apply storeA_compat_restrict. Qed.

Lemma store_compat_restrict_r (s1 s2 : Store) (X : aset) :
  store_compat s1 s2 → store_compat s1 (store_restrict s2 X).
Proof. apply storeA_compat_restrict_r. Qed.

Lemma store_compat_restrict_l_full_r (s1 s2 : Store) (X : aset) :
  dom s1 ⊆ X →
  store_compat s1 (store_restrict s2 X) →
  store_compat s1 s2.
Proof. apply storeA_compat_restrict_l_full_r. Qed.

Lemma store_compat_restrict_eq (s1 s2 : Store) :
  store_compat s1 s2 →
  dom s1 ⊆ dom s2 →
  store_restrict s2 (dom s1) = s1.
Proof. apply storeA_compat_restrict_eq. Qed.

Lemma store_compat_spec (s1 s2 : Store) :
  store_compat s1 s2 ↔
  store_restrict s1 (dom s1 ∩ dom s2) =
  store_restrict s2 (dom s1 ∩ dom s2).
Proof. apply storeA_compat_spec. Qed.

End StoreInterface.
