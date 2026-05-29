(** * Concrete store interfaces *)

From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import StoreCore StoreRestrict StoreFilterMapKey.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Definition Store : Type := gmap atom V.
Definition LStore : Type := gmap logic_var V.

Global Typeclasses Transparent Store LStore.

#[global] Instance store_empty : Empty Store := gmap_empty.
#[global] Instance store_lookup : Lookup atom V Store := lookup.
#[global] Instance store_partial_alter : PartialAlter atom V Store := gmap_partial_alter.
#[global] Instance store_insert : Insert atom V Store := map_insert.
#[global] Instance store_delete : Delete atom Store := map_delete.
#[global] Instance store_union : Union Store := map_union.
#[global] Instance store_singleton : SingletonM atom V Store := map_singleton.
#[global] Instance lstore_lookup : Lookup logic_var V LStore := lookup.

Notation store_restrict := storeA_restrict (only parsing).

Definition lstore_rekey (f : logic_var → logic_var) (s : LStore) : LStore :=
  storeA_rekey f s.

Definition lstore_swap (x y : logic_var) (s : LStore) : LStore :=
  lstore_rekey (swap x y) s.

Definition lstore_to_store (s : LStore) : Store :=
  storeA_filter_map_key (logic_var_to_atom ∅) s.

Definition lstore_bound_part (s : LStore) : gmap nat V :=
  storeA_filter_map_key
    (fun v => match v with LVBound k => Some k | LVFree _ => None end) s.

Lemma lstore_to_store_lookup (s : LStore) x :
  (lstore_to_store s : gmap atom V) !! x =
  (s : gmap logic_var V) !! LVFree x.
Proof.
  unfold lstore_to_store.
  change (lvar_store_to_atom_store s !! x = (s : gmap logic_var V) !! LVFree x).
  apply lvar_store_to_atom_store_lookup.
Qed.

Lemma lstore_bound_part_lookup (s : LStore) k :
  lstore_bound_part s !! k =
  (s : gmap logic_var V) !! LVBound k.
Proof.
  unfold lstore_bound_part.
  destruct (storeA_filter_map_key
    (fun v0 : logic_var => match v0 with LVBound k0 => Some k0 | LVFree _ => None end)
    s !! k) as [v|] eqn:Htarget.
  - apply storeA_filter_map_key_lookup_some_inv in Htarget
      as [[j|y] [Hsrc Hmap]].
    + cbn in Hmap. inversion Hmap. subst j. symmetry. exact Hsrc.
    + discriminate.
  - destruct ((s : gmap logic_var V) !! LVBound k) as [v|] eqn:Hsrc;
      [|reflexivity].
    pose proof (storeA_filter_map_key_lookup_some_unique
      (fun v0 : logic_var => match v0 with LVBound k0 => Some k0 | LVFree _ => None end)
      s (LVBound k) k v Hsrc eq_refl) as Hsome.
    assert (Huniq : forall k0 v0,
      (s : gmap logic_var V) !! k0 = Some v0 ->
      (fun v1 : logic_var =>
        match v1 with LVBound k1 => Some k1 | LVFree _ => None end) k0 = Some k ->
      k0 = LVBound k).
    {
      intros [j|y] A _ Hmap; cbn in Hmap; [|discriminate].
      inversion Hmap. reflexivity.
    }
    specialize (Hsome Huniq).
    rewrite Htarget in Hsome. discriminate.
Qed.

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

Definition lstore_on_open_back
    (k : nat) (x : atom) (D : lvset)
    (s : LStoreOn (lvars_open k x D)) : LStoreOn D.
Proof.
  refine {| storeAO_store := lstore_swap (LVBound k) (LVFree x) (lso_store s) |}.
  unfold lstore_swap, lstore_rekey.
  change (dom ((storeA_map_key
      (swap (LVBound k) (LVFree x)) (lso_store s)) : gmap logic_var V) = D).
  rewrite storeA_rekey_dom by apply swap_inj.
  change (set_swap (LVBound k) (LVFree x) (dom (lso_store s : LStore)) = D).
  rewrite (lso_dom s).
  better_base_solver.
Defined.

Definition lstore_on_open_front
    (k : nat) (x : atom) {D : lvset} (s : LStoreOn D)
    : LStoreOn (lvars_open k x D).
Proof.
  refine {| storeAO_store :=
    lstore_swap (LVBound k) (LVFree x) (lso_store s) |}.
  unfold lstore_swap, lstore_rekey.
  change (dom ((storeA_map_key
      (swap (LVBound k) (LVFree x)) (lso_store s)) : gmap logic_var V) =
    lvars_open k x D).
  rewrite storeA_rekey_dom by apply swap_inj.
  change (set_swap (LVBound k) (LVFree x) (dom (lso_store s : LStore)) =
    lvars_open k x D).
  rewrite (lso_dom s). reflexivity.
Defined.

Lemma lstore_on_open_back_front k x D (s : LStoreOn D) :
  lstore_on_open_back k x D (lstore_on_open_front k x s) = s.
Proof.
  apply lstore_on_ext.
  unfold lstore_on_open_back, lstore_on_open_front. cbn [lso_store].
  unfold lstore_swap, lstore_rekey.
  change (@storeA_swap V logic_var _ _ (LVBound k) (LVFree x)
      (@storeA_swap V logic_var _ _ (LVBound k) (LVFree x)
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
  change (@storeA_swap V logic_var _ _ (LVBound k) (LVFree x)
      (@storeA_swap V logic_var _ _ (LVBound k) (LVFree x)
        (lso_store s)) =
    lso_store s).
  apply storeA_swap_involutive.
Qed.

End StoreInterface.
