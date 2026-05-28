(** * Concrete store interfaces *)

From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import StoreCore StoreKeyAction StoreRestrictCore StoreRestrictUnion StoreBind.

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

Notation store_restrict := storeA_restrict (only parsing).

Definition store_rekey (f : atom → atom) (s : Store) : Store :=
  storeA_rekey f s.

Definition lstore_rekey (f : logic_var → logic_var) (s : LStore) : LStore :=
  storeA_rekey f s.

Definition lstore_swap (x y : logic_var) (s : LStore) : LStore :=
  lstore_rekey (swap x y) s.

Definition lstore_to_store (s : LStore) : Store :=
  map_fold (fun v a acc =>
    match v with
    | LVFree x => <[x := a]> acc
    | LVBound _ => acc
    end) (∅ : Store) s.

Definition lstore_bound_part (s : LStore) : gmap nat V :=
  map_fold (fun v a acc =>
    match v with
    | LVFree _ => acc
    | LVBound k => <[k := a]> acc
    end) (∅ : gmap nat V) s.

Local Lemma raw_gmap_lookup_insert_value
    {K : Type} `{Countable K} (m : gmap K V) i (a : V) :
  @gmap_lookup K _ _ V i (<[i := a]> m) = Some a.
Proof.
  change (((<[i := a]> m : gmap K V) !! i) = Some a).
  apply map_lookup_insert.
Qed.

Local Lemma raw_gmap_lookup_insert_ne
    {K : Type} `{Countable K} (m : gmap K V) i j (a : V) :
  i <> j ->
  @gmap_lookup K _ _ V j (<[i := a]> m) =
  @gmap_lookup K _ _ V j m.
Proof.
  intros Hneq.
  change (((<[i := a]> m : gmap K V) !! j) = (m : gmap K V) !! j).
  apply map_lookup_insert_ne. congruence.
Qed.

Lemma lstore_to_store_lookup (s : LStore) x :
  (lstore_to_store s : gmap atom V) !! x =
  (s : gmap logic_var V) !! LVFree x.
Proof.
  unfold lstore_to_store.
  refine (@fin_maps.map_fold_ind logic_var (gmap logic_var) _ _ _ _ _ _ _ _ _
    V
    (fun s => forall x,
      @gmap_lookup atom _ _ V x (map_fold
        (fun v a acc =>
          match v with
          | LVFree x => <[x := a]> acc
          | LVBound _ => acc
          end) (∅ : gmap atom V) s) =
      @gmap_lookup logic_var _ _ V (LVFree x) s) _ _ (s : gmap logic_var V) x).
  - intros x0. cbn. reflexivity.
  - intros v a s' Hfresh Hfold IH x0.
    rewrite Hfold. cbn.
    destruct v as [k|y].
    + change ((map_fold
          (fun v a acc =>
            match v with
            | LVFree x => <[x:=a]> acc
            | LVBound _ => acc
            end) (∅ : gmap atom V) s') !! x0 =
        @gmap_lookup logic_var _ _ V (LVFree x0)
          (<[LVBound k:=a]> s' : gmap logic_var V)).
      assert (Hne : @gmap_lookup logic_var _ _ V (LVFree x0)
          (<[LVBound k:=a]> s' : gmap logic_var V) =
        @gmap_lookup logic_var _ _ V (LVFree x0) s').
      { apply raw_gmap_lookup_insert_ne. discriminate. }
      rewrite Hne. apply IH.
    + destruct (decide (x0 = y)) as [->|Hxy].
      * change (((<[y:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree x => <[x:=a]> acc
              | LVBound _ => acc
              end) (∅ : gmap atom V) s') : gmap atom V) !! y) =
          @gmap_lookup logic_var _ _ V (LVFree y)
            (<[LVFree y:=a]> s' : gmap logic_var V)).
        assert (Hleft : ((<[y:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree x => <[x:=a]> acc
              | LVBound _ => acc
              end) (∅ : gmap atom V) s') : gmap atom V) !! y) = Some a).
        { apply raw_gmap_lookup_insert_value. }
        assert (Hright : @gmap_lookup logic_var _ _ V (LVFree y)
            (<[LVFree y:=a]> s' : gmap logic_var V) = Some a).
        { apply raw_gmap_lookup_insert_value. }
        rewrite Hleft, Hright. reflexivity.
      * change (((<[y:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree x => <[x:=a]> acc
              | LVBound _ => acc
              end) (∅ : gmap atom V) s') : gmap atom V) !! x0) =
          @gmap_lookup logic_var _ _ V (LVFree x0)
            (<[LVFree y:=a]> s' : gmap logic_var V)).
        assert (Hleft : ((<[y:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree x => <[x:=a]> acc
              | LVBound _ => acc
              end) (∅ : gmap atom V) s') : gmap atom V) !! x0) =
          (map_fold
            (fun v a acc =>
              match v with
              | LVFree x => <[x:=a]> acc
              | LVBound _ => acc
              end) (∅ : gmap atom V) s') !! x0).
        { apply raw_gmap_lookup_insert_ne. congruence. }
        assert (Hright : @gmap_lookup logic_var _ _ V (LVFree x0)
            (<[LVFree y:=a]> s' : gmap logic_var V) =
          @gmap_lookup logic_var _ _ V (LVFree x0) s').
        { apply raw_gmap_lookup_insert_ne. congruence. }
        rewrite Hleft, Hright. apply IH.
Qed.

Lemma lstore_bound_part_lookup (s : LStore) k :
  lstore_bound_part s !! k =
  (s : gmap logic_var V) !! LVBound k.
Proof.
  unfold lstore_bound_part.
  refine (@fin_maps.map_fold_ind logic_var (gmap logic_var) _ _ _ _ _ _ _ _ _
    V
    (fun s => forall k,
      @gmap_lookup nat _ _ V k (map_fold
        (fun v a acc =>
          match v with
          | LVFree _ => acc
          | LVBound k => <[k := a]> acc
          end) (∅ : gmap nat V) s) =
      @gmap_lookup logic_var _ _ V (LVBound k) s) _ _ (s : gmap logic_var V) k).
  - intros k0. cbn. reflexivity.
  - intros v a s' Hfresh Hfold IH k0.
    rewrite Hfold. cbn.
    destruct v as [j|y].
    + destruct (decide (k0 = j)) as [->|Hkj].
      * change (((<[j:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree _ => acc
              | LVBound k => <[k:=a]> acc
              end) (∅ : gmap nat V) s') : gmap nat V) !! j) =
          @gmap_lookup logic_var _ _ V (LVBound j)
            (<[LVBound j:=a]> s' : gmap logic_var V)).
        assert (Hleft : ((<[j:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree _ => acc
              | LVBound k => <[k:=a]> acc
              end) (∅ : gmap nat V) s') : gmap nat V) !! j) = Some a).
        { apply raw_gmap_lookup_insert_value. }
        assert (Hright : @gmap_lookup logic_var _ _ V (LVBound j)
            (<[LVBound j:=a]> s' : gmap logic_var V) = Some a).
        { apply raw_gmap_lookup_insert_value. }
        rewrite Hleft, Hright. reflexivity.
      * change (((<[j:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree _ => acc
              | LVBound k => <[k:=a]> acc
              end) (∅ : gmap nat V) s') : gmap nat V) !! k0) =
          @gmap_lookup logic_var _ _ V (LVBound k0)
            (<[LVBound j:=a]> s' : gmap logic_var V)).
        assert (Hleft : ((<[j:=a]> (map_fold
            (fun v a acc =>
              match v with
              | LVFree _ => acc
              | LVBound k => <[k:=a]> acc
              end) (∅ : gmap nat V) s') : gmap nat V) !! k0) =
          (map_fold
            (fun v a acc =>
              match v with
              | LVFree _ => acc
              | LVBound k => <[k:=a]> acc
              end) (∅ : gmap nat V) s') !! k0).
        { apply raw_gmap_lookup_insert_ne. congruence. }
        assert (Hright : @gmap_lookup logic_var _ _ V (LVBound k0)
            (<[LVBound j:=a]> s' : gmap logic_var V) =
          @gmap_lookup logic_var _ _ V (LVBound k0) s').
        { apply raw_gmap_lookup_insert_ne. congruence. }
        rewrite Hleft, Hright. apply IH.
    + change ((map_fold
          (fun v a acc =>
            match v with
            | LVFree _ => acc
            | LVBound k => <[k:=a]> acc
            end) (∅ : gmap nat V) s') !! k0 =
        @gmap_lookup logic_var _ _ V (LVBound k0)
          (<[LVFree y:=a]> s' : gmap logic_var V)).
      assert (Hne : @gmap_lookup logic_var _ _ V (LVBound k0)
          (<[LVFree y:=a]> s' : gmap logic_var V) =
        @gmap_lookup logic_var _ _ V (LVBound k0) s').
      { apply raw_gmap_lookup_insert_ne. discriminate. }
      rewrite Hne. apply IH.
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
  change (dom ((@storeA_rekey V logic_var _ _
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
  change (dom ((@storeA_rekey V logic_var _ _
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
