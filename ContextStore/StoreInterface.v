(** * Concrete store interfaces *)

From ContextBase Require Import Prelude LogicVar LogicVarShift BaseTactics.
From ContextStore Require Import StoreCore StoreRestrict StoreFilterMapKey.

Declare Scope store_scope.
Delimit Scope store_scope with store.

Section StoreInterface.

Context {V : Type} `{ValueSig V}.

Definition Store : Type := gmap atom V.
Definition LStore : Type := gmap logic_var V.

Global Typeclasses Transparent Store LStore.

Bind Scope store_scope with Store.
Bind Scope store_scope with LStore.

#[global] Instance store_empty : Empty Store := gmap_empty.
#[global] Instance store_lookup : Lookup atom V Store := lookup.
#[global] Instance store_partial_alter : PartialAlter atom V Store := gmap_partial_alter.
#[global] Instance store_insert : Insert atom V Store := map_insert.
#[global] Instance store_delete : Delete atom Store := map_delete.
#[global] Instance store_union : Union Store := map_union.
#[global] Instance store_singleton : SingletonM atom V Store := map_singleton.
#[global] Instance lstore_lookup : Lookup logic_var V LStore := lookup.

Lemma atom_store_to_lvar_store_store_insert x v (s : Store) :
  atom_store_to_lvar_store (<[x := v]> s) =
  <[LVFree x := v]> (atom_store_to_lvar_store s).
Proof.
  unfold store_insert.
  apply atom_store_to_lvar_store_insert.
Qed.

Lemma atom_store_to_lvar_store_store_empty :
  atom_store_to_lvar_store (∅ : Store) = (∅ : LStore).
Proof.
  unfold store_empty.
  apply atom_store_to_lvar_store_empty.
Qed.

Notation store_restrict := storeA_restrict (only parsing).
Notation "σ '↾' X" := (storeA_restrict σ X)
  (at level 20, no associativity,
   format "σ  ↾  X") : store_scope.
Notation "σ1 '##ₛ' σ2" := (storeA_compat σ1 σ2)
  (at level 70, no associativity,
   format "σ1  ##ₛ  σ2") : store_scope.
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

Lemma lstore_on_mlsubst_back_merge
    D (ρ_outer ρ_inner : LStore)
    (s_nested : LStoreOn
      ((D ∖ dom (ρ_outer : gmap logic_var V))
        ∖ dom (ρ_inner : gmap logic_var V)))
    (s_merged : LStoreOn
      (D ∖ dom (ρ_outer ∪ ρ_inner : gmap logic_var V))) :
  dom (ρ_outer : gmap logic_var V) ##
    dom (ρ_inner : gmap logic_var V) ->
  lso_store s_nested = lso_store s_merged ->
  lstore_on_mlsubst_back D ρ_outer
    (lstore_on_mlsubst_back
      (D ∖ dom (ρ_outer : gmap logic_var V)) ρ_inner s_nested) =
  lstore_on_mlsubst_back D (ρ_outer ∪ ρ_inner) s_merged.
Proof.
  intros Hdisj Hs.
  apply lstore_on_ext.
  unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
  change (((lso_store s_nested ∪
      storeA_restrict ρ_inner (D ∖ dom (ρ_outer : gmap logic_var V))) ∪
      storeA_restrict ρ_outer D : gmap logic_var V) =
    (lso_store s_merged ∪
      storeA_restrict (ρ_outer ∪ ρ_inner) D : gmap logic_var V)).
  rewrite Hs.
  rewrite <- (assoc_L (∪)
    (lso_store s_merged)
    (storeA_restrict ρ_inner (D ∖ dom (ρ_outer : gmap logic_var V)))
    (storeA_restrict ρ_outer D)).
  f_equal.
  apply storeA_restrict_union_residual_l.
  unfold storeA_compat, map_compat.
  intros z v1 v2 Houter Hinner.
  exfalso.
  apply elem_of_dom_2 in Houter.
  apply elem_of_dom_2 in Hinner.
  set_solver.
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

Lemma lstore_on_open_mlsubst_back_fresh
    k y D (ρ : LStore)
    (s1 : LStoreOn (lvars_open k y
      (D ∖ dom (ρ : gmap logic_var V))))
    (s2 : LStoreOn (lvars_open k y D
      ∖ dom (ρ : gmap logic_var V))) :
  LVBound k ∉ dom (ρ : gmap logic_var V) ->
  LVFree y ∉ dom (ρ : gmap logic_var V) ->
  lso_store s1 = lso_store s2 ->
  lstore_on_mlsubst_back D ρ
    (lstore_on_open_back k y (D ∖ dom (ρ : gmap logic_var V)) s1) =
  lstore_on_open_back k y D
    (lstore_on_mlsubst_back (lvars_open k y D) ρ s2).
Proof.
  intros Hbound Hfree Hs.
  apply lstore_on_ext.
  unfold lstore_on_mlsubst_back, lstore_on_open_back.
  cbn [lso_store storeAO_store].
  unfold lstore_swap, lstore_rekey.
  change (storeA_swap (LVBound k) (LVFree y) (lso_store s1) ∪
      storeA_restrict ρ D =
    storeA_swap (LVBound k) (LVFree y)
      (lso_store s2 ∪ storeA_restrict ρ (lvars_open k y D))).
  transitivity
    (storeA_swap (LVBound k) (LVFree y) (lso_store s2) ∪
      storeA_swap (LVBound k) (LVFree y)
        (storeA_restrict ρ (lvars_open k y D))).
  - rewrite Hs.
    f_equal.
    rewrite <- storeA_restrict_swap.
    replace (set_swap (LVBound k) (LVFree y) (lvars_open k y D))
      with D by better_base_solver.
    replace (storeA_swap (LVBound k) (LVFree y) ρ) with ρ; [reflexivity|].
    symmetry.
    apply storeA_swap_fresh; assumption.
  - symmetry.
    apply storeA_swap_union.
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

Lemma lstore_on_shift_from_mlsubst_back_atom_store
    k D (σ : Store) (s1 : LStoreOn (D ∖ dom (atom_store_to_lvar_store σ : LStore)))
    (s2 : LStoreOn (lvars_shift_from k D ∖
      dom (atom_store_to_lvar_store σ : LStore))) :
  lso_store s2 = lso_store (lstore_on_shift_from k s1) ->
  lso_store (lstore_on_shift_from k
    (lstore_on_mlsubst_back D (atom_store_to_lvar_store σ) s1)) =
  lso_store (lstore_on_mlsubst_back (lvars_shift_from k D)
    (atom_store_to_lvar_store σ) s2).
Proof.
  intros Hs.
  unfold lstore_on_shift_from, lstore_on_rekey, storeA_on_rekey,
    lstore_on_mlsubst_back.
  cbn [lso_store storeAO_store].
  change (storeA_rekey (logic_var_shift_from k)
      (lso_store s1 ∪ storeA_restrict (atom_store_to_lvar_store σ) D) =
    lso_store s2 ∪
      storeA_restrict (atom_store_to_lvar_store σ) (lvars_shift_from k D)).
  rewrite (storeA_map_key_union (V:=V) (logic_var_shift_from k)
    (logic_var_shift_from_inj k) (lso_store s1)
    (storeA_restrict (atom_store_to_lvar_store σ) D)).
  rewrite Hs.
  f_equal.
  - unfold lstore_on_shift_from, lstore_on_rekey, storeA_on_rekey.
    destruct s1. reflexivity.
  - 
  replace (atom_store_to_lvar_store σ)
    with (lvar_store_shift_from k (atom_store_to_lvar_store σ)) at 2
    by apply lvar_store_shift_from_atom_store.
  unfold lvar_store_shift_from.
  rewrite <- storeA_restrict_rekey by apply logic_var_shift_from_inj.
  reflexivity.
Qed.

Lemma lstore_shift_restrict_mlsubst_back_raw
    k D (σ : Store) (sD s2 : LStore) :
  dom (sD : gmap logic_var V) = D ->
  dom (s2 : gmap logic_var V) =
    lvars_shift_from k D ∖ dom (atom_store_to_lvar_store σ : LStore) ->
  lstore_shift_from k sD =
    s2 ∪ storeA_restrict (atom_store_to_lvar_store σ : LStore)
      (lvars_shift_from k D) ->
  lstore_shift_from k
    (storeA_restrict sD
      (D ∖ dom (atom_store_to_lvar_store σ : LStore))) =
  s2.
Proof.
  intros HdomD Hdom2 Hshift.
  set (ρ := atom_store_to_lvar_store σ : LStore).
  apply storeA_map_eq. intros z.
  destruct (decide (z ∈ dom (s2 : gmap logic_var V))) as [Hz|Hz].
  - assert (HzD : z ∈ lvars_shift_from k D ∖ dom (ρ : gmap logic_var V)).
    { rewrite Hdom2 in Hz. subst ρ. exact Hz. }
    assert (Hzmap : z ∈ lvars_shift_from k
        (D ∖ dom (ρ : gmap logic_var V))).
    {
      subst ρ. rewrite atom_store_to_lvar_store_dom in *.
      rewrite lvars_shift_from_difference_of_atoms. exact HzD.
    }
    unfold lvars_shift_from in Hzmap.
    apply elem_of_map in Hzmap as [u [-> Hu]].
    unfold lstore_shift_from, lstore_rekey.
    change ((storeA_rekey (logic_var_shift_from k)
        (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V))) : LStore) !!
        logic_var_shift_from k u =
      (s2 : LStore) !! logic_var_shift_from k u).
    replace ((storeA_rekey (logic_var_shift_from k)
        (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V))) : LStore) !!
        logic_var_shift_from k u)
      with ((storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V))) !! u).
    2:{
      symmetry.
      exact (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
        (Inj0:=logic_var_shift_from_inj k)
        (logic_var_shift_from k)
        (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V))) u).
    }
    rewrite (storeA_restrict_lookup (V:=V) sD
      (D ∖ dom (ρ : gmap logic_var V)) u).
    destruct (decide (u ∈ D ∖ dom (ρ : gmap logic_var V))) as [_|Hbad];
      [|contradiction].
    pose proof (f_equal
      (fun s : LStore => s !! logic_var_shift_from k u) Hshift) as HuLookup.
    unfold lstore_shift_from, lstore_rekey in HuLookup.
    change ((storeA_rekey (logic_var_shift_from k) sD : LStore) !!
        logic_var_shift_from k u =
      (s2 ∪ storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
        logic_var_shift_from k u) in HuLookup.
    replace ((storeA_rekey (logic_var_shift_from k) sD : LStore) !!
        logic_var_shift_from k u) with (sD !! u) in HuLookup.
    2:{
      symmetry.
      exact (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
        (Inj0:=logic_var_shift_from_inj k)
        (logic_var_shift_from k) sD u).
    }
    replace ((s2 ∪ storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
        logic_var_shift_from k u)
      with ((s2 : LStore) !! logic_var_shift_from k u) in HuLookup.
    { exact HuLookup. }
    symmetry.
    assert (Hright :
      (storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
        logic_var_shift_from k u = None).
    {
      apply storeA_restrict_lookup_none_l.
      subst ρ.
      destruct u as [n|x]; cbn [logic_var_shift_from].
      - destruct (decide (k <= n)); apply atom_store_to_lvar_store_lookup_bound_none.
      - apply not_elem_of_dom_1.
        rewrite atom_store_to_lvar_store_dom in Hu.
        set_solver.
    }
    destruct (s2 !! logic_var_shift_from k u) as [v|] eqn:Hs2u.
    + apply map_lookup_union_Some_raw. left. exact Hs2u.
    + apply map_lookup_union_None. split; assumption.
  - transitivity (@None V).
    + apply not_elem_of_dom_1.
      unfold lstore_shift_from, lstore_rekey.
      change (z ∉ dom (storeA_rekey (logic_var_shift_from k)
        (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V))) : LStore)).
      replace (dom (storeA_rekey (logic_var_shift_from k)
          (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V))) : LStore))
        with (set_map (logic_var_shift_from k)
          (dom (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) : LStore))
          : lvset).
      2:{ symmetry. apply storeA_rekey_dom, logic_var_shift_from_inj. }
      replace (dom (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) : LStore))
        with (dom (sD : LStore) ∩ (D ∖ dom (ρ : gmap logic_var V))).
      2:{ symmetry. apply storeA_restrict_dom. }
      replace (dom (sD : LStore)) with D by (symmetry; exact HdomD).
      subst ρ.
      rewrite atom_store_to_lvar_store_dom.
      replace (D ∩ (D ∖ lvars_of_atoms (dom (σ : gmap atom V))))
        with (D ∖ lvars_of_atoms (dom (σ : gmap atom V))) by set_solver.
      change (z ∉ lvars_shift_from k
        (D ∖ lvars_of_atoms (dom (σ : gmap atom V)))).
      rewrite lvars_shift_from_difference_of_atoms.
      rewrite <- (atom_store_to_lvar_store_dom σ).
      replace (lvars_shift_from k D ∖ dom (atom_store_to_lvar_store σ : LStore))
        with (dom (s2 : gmap logic_var V)) by (rewrite Hdom2; reflexivity).
      exact Hz.
    + symmetry. apply not_elem_of_dom_1. exact Hz.
Qed.

Lemma lstore_mlsubst_back_restrict_shift_raw
    k D (σ : Store) (sD s2 : LStore) :
  dom (sD : gmap logic_var V) = D ->
  dom (s2 : gmap logic_var V) =
    lvars_shift_from k D ∖ dom (atom_store_to_lvar_store σ : LStore) ->
  lstore_shift_from k sD =
    s2 ∪ storeA_restrict (atom_store_to_lvar_store σ : LStore)
      (lvars_shift_from k D) ->
  storeA_restrict sD
      (D ∖ dom (atom_store_to_lvar_store σ : LStore)) ∪
    storeA_restrict (atom_store_to_lvar_store σ : LStore) D =
  sD.
Proof.
  intros HdomD Hdom2 Hshift.
  set (ρ := atom_store_to_lvar_store σ : LStore).
  apply storeA_map_eq. intros z.
  destruct (decide (z ∈ dom (ρ : gmap logic_var V))) as [Hzρ|Hzρ].
  - destruct (decide (z ∈ D)) as [HzD|HzD].
    + destruct z as [n|x].
      * subst ρ. rewrite atom_store_to_lvar_store_dom in Hzρ.
        unfold lvars_of_atoms in Hzρ.
        apply elem_of_map in Hzρ as [a [Hbad _]].
        discriminate.
      * assert (Hs2none : (s2 : LStore) !! LVFree x = None).
        {
          destruct ((s2 : gmap logic_var V) !! LVFree x) as [v|] eqn:Hlook;
            [|exact Hlook].
          exfalso.
          assert (Hdomx : LVFree x ∈ dom (s2 : gmap logic_var V)).
          { apply elem_of_dom. exists v. exact Hlook. }
          clear Hlook.
          rewrite Hdom2 in Hdomx.
          subst ρ.
          apply elem_of_difference in Hdomx as [_ Hnot].
          exact (Hnot Hzρ).
        }
        pose proof (f_equal (fun s : LStore => s !! LVFree x) Hshift) as Hx.
        unfold lstore_shift_from, lstore_rekey in Hx.
        change ((storeA_rekey (logic_var_shift_from k) sD : LStore) !!
            LVFree x =
          (s2 ∪ storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
            LVFree x) in Hx.
        change (LVFree x) with (logic_var_shift_from k (LVFree x)) in Hx.
        replace ((storeA_rekey (logic_var_shift_from k) sD : LStore) !!
            logic_var_shift_from k (LVFree x)) with (sD !! LVFree x) in Hx.
        2:{
          symmetry.
          exact (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
            (Inj0:=logic_var_shift_from_inj k)
            (logic_var_shift_from k) sD (LVFree x)).
        }
        replace ((s2 ∪ storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
            logic_var_shift_from k (LVFree x))
          with ((storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
            logic_var_shift_from k (LVFree x)) in Hx.
        2:{
          cbn [logic_var_shift_from].
          destruct ((storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
              LVFree x) as [v|] eqn:Hr.
          - symmetry. apply map_lookup_union_Some_raw. right. split; assumption.
          - symmetry. apply map_lookup_union_None. split; assumption.
        }
        assert (Hρx :
          (storeA_restrict ρ (lvars_shift_from k D) : LStore) !!
            logic_var_shift_from k (LVFree x) =
          (ρ : LStore) !! LVFree x).
        {
          cbn [logic_var_shift_from].
          destruct ((ρ : LStore) !! LVFree x) as [v|] eqn:Hlook.
          - apply storeA_restrict_lookup_some_2; [exact Hlook|].
            apply elem_of_map. exists (LVFree x). split; [reflexivity|exact HzD].
          - apply storeA_restrict_lookup_none_l. exact Hlook.
        }
        rewrite Hρx in Hx.
        replace ((storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) ∪
            storeA_restrict ρ D : LStore) !! LVFree x)
          with ((ρ : LStore) !! LVFree x).
        -- symmetry. exact Hx.
        -- assert (Hleft :
             (storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) : LStore) !!
               LVFree x = None).
           { apply storeA_restrict_lookup_none_r. set_solver. }
           destruct ((ρ : LStore) !! LVFree x) as [v|] eqn:Hlook.
           ++ symmetry. apply map_lookup_union_Some_raw. right. split; [exact Hleft|].
              apply storeA_restrict_lookup_some_2; [exact Hlook|exact HzD].
           ++ symmetry. apply map_lookup_union_None. split; [exact Hleft|].
              apply storeA_restrict_lookup_none_l. exact Hlook.
    + rewrite lookup_union_r.
      * rewrite storeA_restrict_lookup.
        destruct (decide (z ∈ D)) as [Hbad|_]; [contradiction|].
        symmetry. apply not_elem_of_dom_1. rewrite HdomD. exact HzD.
      * apply storeA_restrict_lookup_none_r. set_solver.
	  - replace ((storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) ∪
          storeA_restrict ρ D : LStore) !! z)
        with ((storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) : LStore) !! z).
	    + rewrite (storeA_restrict_lookup (V:=V) sD
          (D ∖ dom (ρ : gmap logic_var V)) z).
	      destruct (decide (z ∈ D)) as [HzD|HzD].
		      * rewrite decide_True by set_solver. reflexivity.
		      * rewrite decide_False by set_solver.
		        symmetry. apply not_elem_of_dom_1. rewrite HdomD. exact HzD.
	    + assert (Hright : (storeA_restrict ρ D : LStore) !! z = None).
        { apply storeA_restrict_lookup_none_l.
          apply not_elem_of_dom_1. exact Hzρ. }
        destruct ((storeA_restrict sD (D ∖ dom (ρ : gmap logic_var V)) : LStore) !! z)
          as [v|] eqn:Hleft.
        * symmetry. apply map_lookup_union_Some_raw. left. exact Hleft.
        * symmetry. apply map_lookup_union_None. split; assumption.
Qed.

Lemma lstore_on_shift_restrict_mlsubst_back
    k D (σ : Store) (sD : LStoreOn D)
    (s2 : LStoreOn (lvars_shift_from k D ∖
      dom (atom_store_to_lvar_store σ : LStore))) :
  lso_store (lstore_on_shift_from k sD) =
    lso_store (lstore_on_mlsubst_back (lvars_shift_from k D)
      (atom_store_to_lvar_store σ) s2) ->
  lso_store (lstore_on_shift_from k
    (lstore_on_restrict (D ∖ dom (atom_store_to_lvar_store σ : LStore))
      sD ltac:(set_solver))) =
  lso_store s2.
Proof.
  destruct sD as [sD HdomD], s2 as [s2 Hdom2].
  cbn [lso_store storeAO_store].
  intros Hshift.
  apply lstore_shift_restrict_mlsubst_back_raw; assumption.
Qed.

Lemma lstore_on_mlsubst_back_restrict_shift
    k D (σ : Store) (sD : LStoreOn D)
    (s2 : LStoreOn (lvars_shift_from k D ∖
      dom (atom_store_to_lvar_store σ : LStore))) :
  lso_store (lstore_on_shift_from k sD) =
    lso_store (lstore_on_mlsubst_back (lvars_shift_from k D)
      (atom_store_to_lvar_store σ) s2) ->
  lso_store (lstore_on_mlsubst_back D (atom_store_to_lvar_store σ)
    (lstore_on_restrict (D ∖ dom (atom_store_to_lvar_store σ : LStore))
      sD ltac:(set_solver))) =
  lso_store sD.
Proof.
  destruct sD as [sD HdomD], s2 as [s2 Hdom2].
  unfold lstore_on_mlsubst_back.
  cbn [lso_store storeAO_store].
  intros Hshift.
  exact (lstore_mlsubst_back_restrict_shift_raw
    k D σ sD s2 HdomD Hdom2 Hshift).
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

Notation "σ '↾ₛ' X" := (storeA_restrict σ X)
  (at level 20, no associativity,
   format "σ  ↾ₛ  X", only printing).
Notation "σ1 '##ₛ' σ2" := (storeA_compat σ1 σ2)
  (at level 70, no associativity,
   format "σ1  ##ₛ  σ2", only printing).
