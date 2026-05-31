(** * Concrete store interfaces *)

From ContextBase Require Import Prelude LogicVar LogicVarShift BaseTactics.
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

Lemma lstore_to_store_restrict_lookup (s : LStore) X x :
  LVFree x ∈ X ->
  (lstore_to_store (storeA_restrict s X) : gmap atom V) !! x =
  (lstore_to_store s : gmap atom V) !! x.
Proof.
  intros Hx.
  rewrite !lstore_to_store_lookup.
  destruct ((s : gmap logic_var V) !! LVFree x) as [v|] eqn:Hs.
  - apply storeA_restrict_lookup_some_2; [exact Hs|exact Hx].
  - apply storeA_restrict_lookup_none_l. exact Hs.
Qed.

Lemma lstore_bound_part_restrict_lookup (s : LStore) X k :
  LVBound k ∈ X ->
  lstore_bound_part (storeA_restrict s X) !! k =
  lstore_bound_part s !! k.
Proof.
  intros Hk.
  rewrite !lstore_bound_part_lookup.
  destruct ((s : gmap logic_var V) !! LVBound k) as [v|] eqn:Hs.
  - apply storeA_restrict_lookup_some_2; [exact Hs|exact Hk].
  - apply storeA_restrict_lookup_none_l. exact Hs.
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

Definition lstore_on_mlsubst_back
    (D : lvset) (ρ : LStore)
    (s : LStoreOn (D ∖ dom (ρ : gmap logic_var V))) : LStoreOn D.
Proof.
  refine {| storeAO_store :=
    (lso_store s ∪ storeA_restrict ρ D : gmap logic_var V) |}.
  change (dom ((lso_store s : gmap logic_var V) ∪
      (storeA_restrict ρ D : gmap logic_var V)) = D).
  rewrite dom_union_L.
  change (dom (lso_store s : LStore) ∪
    dom (storeA_restrict ρ D : LStore) = D).
  rewrite (lso_dom s).
  replace (dom (storeA_restrict ρ D : LStore))
    with (dom (ρ : gmap logic_var V) ∩ D).
  2:{ symmetry. apply (@storeA_restrict_dom V logic_var _ _ ρ D). }
  apply set_eq. intros z.
  rewrite elem_of_union, elem_of_difference, elem_of_intersection.
  split.
  - intros [[HzD _]|[_ HzD]]; exact HzD.
  - intros HzD.
    destruct (decide (z ∈ dom (ρ : gmap logic_var V))) as [Hzρ|Hzρ].
    + right. split; assumption.
    + left. split; assumption.
Defined.

Lemma lstore_on_mlsubst_back_restrict_eq
    D (ρ1 ρ2 : LStore)
    (s1 : LStoreOn (D ∖ dom (ρ1 : gmap logic_var V)))
    (s2 : LStoreOn (D ∖ dom (ρ2 : gmap logic_var V))) :
  storeA_restrict ρ1 D = storeA_restrict ρ2 D ->
  lso_store s1 = lso_store s2 ->
  lstore_on_mlsubst_back D ρ1 s1 =
  lstore_on_mlsubst_back D ρ2 s2.
Proof.
  intros Hρ Hs.
  apply lstore_on_ext.
  unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
  rewrite Hs, Hρ. reflexivity.
Qed.

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

Definition lstore_shift_from (k : nat) (s : LStore) : LStore :=
  lstore_rekey (logic_var_shift_from k) s.

Definition lstore_on_shift_from
    (k : nat) {D : lvset} (s : LStoreOn D)
    : LStoreOn (lvars_shift_from k D) :=
  lstore_on_rekey (logic_var_shift_from k) (logic_var_shift_from_inj k) s.

Lemma lstore_shift_from_below_id k D (s : LStoreOn D) :
  (forall n, n ∈ lvars_bv D -> n < k) ->
  lso_store (lstore_on_shift_from k s) = lso_store s.
Proof.
  intros Hbelow.
  apply lstore_on_rekey_id_on_dom.
  intros [n|x] Hin; cbn [logic_var_shift_from].
  - destruct (decide (k <= n)) as [Hbad|_].
    + exfalso. pose proof (Hbelow n ltac:(apply lvars_bv_elem; exact Hin)).
      lia.
    + reflexivity.
  - reflexivity.
Qed.

Lemma lstore_shift_from_open_swap j k x (s : LStore) :
  j <= k ->
  lstore_shift_from j (lstore_swap (LVBound k) (LVFree x) s) =
  lstore_swap (LVBound (S k)) (LVFree x) (lstore_shift_from j s).
Proof.
  intros Hjk.
  unfold lstore_shift_from, lstore_swap, lstore_rekey.
  rewrite !storeA_rekey_compose;
    try apply logic_var_shift_from_inj;
    try apply swap_inj.
  apply storeA_rekey_ext_on_dom. intros v _.
  symmetry. apply logic_var_open_shift_from_under_gen. exact Hjk.
Qed.

Lemma lstore_on_shift_from_open_front j k x D (s : LStoreOn D) :
  j <= k ->
  lso_store (lstore_on_shift_from j (lstore_on_open_front k x s)) =
  lso_store (lstore_on_open_front (S k) x (lstore_on_shift_from j s)).
Proof.
  intros Hjk.
  destruct s as [s Hdom]. simpl.
  unfold lstore_on_shift_from, lstore_on_open_front, lstore_on_rekey,
    storeA_on_rekey.
  cbn [lso_store storeAO_store].
  apply lstore_shift_from_open_swap. exact Hjk.
Qed.

Lemma lstore_on_shift_from_open_back j k x D
    (s : LStoreOn (lvars_open k x D)) :
  j <= k ->
  lso_store (lstore_on_shift_from j (lstore_on_open_back k x D s)) =
  lstore_swap (LVBound (S k)) (LVFree x)
    (lso_store (lstore_on_shift_from j s)).
Proof.
  intros Hjk.
  destruct s as [s Hdom]. simpl.
  unfold lstore_on_shift_from, lstore_on_open_back, lstore_on_rekey,
    storeA_on_rekey.
  cbn [lso_store storeAO_store].
  apply lstore_shift_from_open_swap. exact Hjk.
Qed.

End StoreInterface.
