(** * Generic stores: partial key projection *)

From ContextBase Require Import Prelude LogicVar LogicVarOpenEnv LogicVarShift BaseTactics.
From ContextStore Require Import StoreCore.

Notation lvar_to_atom := logic_var_to_atom (only parsing).

Section StoreFilterMapKey.

Context {V : Type} `{ValueSig V}.

Definition storeA_filter_map_key
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') (s : gmap K V) : gmap K' V :=
  map_fold (fun k v (acc : gmap K' V) =>
    match f k with
    | Some k' => <[k' := v]> acc
    | None => acc
    end) ∅ s.

Lemma storeA_filter_map_key_empty
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') :
  storeA_filter_map_key f (∅ : gmap K V) = (∅ : gmap K' V).
Proof.
  unfold storeA_filter_map_key. reflexivity.
Qed.

Lemma storeA_filter_map_key_lookup_some_inv
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') (s : gmap K V) k' v :
  storeA_filter_map_key f s !! k' = Some v ->
  exists k, s !! k = Some v /\ f k = Some k'.
Proof.
  unfold storeA_filter_map_key.
  refine (fin_maps.map_fold_ind (M:=gmap K)
    (fun s => forall tgt v,
      map_fold
        (fun k v acc =>
          match f k with
          | Some tgt' => <[tgt' := v]> acc
          | None => acc
          end) ∅ s !! tgt = Some v ->
      exists k, s !! k = Some v /\ f k = Some tgt) _ _ s k' v).
  - intros tgt val Hlookup.
    better_map_solver.
  - intros src val s' Hfresh Hfold IH tgt v' Hlookup.
    rewrite Hfold in Hlookup.
    destruct (f src) as [fk|] eqn:Hfk.
    + apply lookup_insert_Some in Hlookup as [[-> ->]|[Hne Hlookup]].
      * exists src. split; [apply map_lookup_insert|exact Hfk].
      * apply IH in Hlookup as [k0 [Hk0 Hfk0]].
        exists k0. split; [|exact Hfk0].
        rewrite map_lookup_insert_ne; [exact Hk0|].
        intros ->. rewrite Hfresh in Hk0. discriminate.
    + apply IH in Hlookup as [k0 [Hk0 Hfk0]].
      exists k0. split; [|exact Hfk0].
      rewrite map_lookup_insert_ne; [exact Hk0|].
      intros ->. rewrite Hfk in Hfk0. discriminate.
Qed.

Lemma storeA_filter_map_key_lookup_some_unique
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') (s : gmap K V) k k' v :
  s !! k = Some v ->
  f k = Some k' ->
  (forall k0 v0, s !! k0 = Some v0 -> f k0 = Some k' -> k0 = k) ->
  storeA_filter_map_key f s !! k' = Some v.
Proof.
  unfold storeA_filter_map_key.
  refine (fin_maps.map_fold_ind (M:=gmap K)
    (fun s => forall k tgt v,
      s !! k = Some v ->
      f k = Some tgt ->
      (forall k0 v0, s !! k0 = Some v0 -> f k0 = Some tgt -> k0 = k) ->
      map_fold
        (fun k v acc =>
          match f k with
          | Some tgt' => <[tgt' := v]> acc
          | None => acc
          end) ∅ s !! tgt = Some v) _ _ s k k' v).
  - intros src tgt val Hlookup _ _.
    better_map_solver.
  - intros i vi s' Hfresh Hfold IH src tgt val Hlookup Hfk Huniq.
    rewrite Hfold.
    destruct (decide (i = src)) as [->|Hik].
    + rewrite map_lookup_insert in Hlookup. inversion Hlookup. subst vi.
      rewrite Hfk. apply map_lookup_insert.
    + rewrite map_lookup_insert_ne in Hlookup by congruence.
      destruct (f i) as [fi|] eqn:Hfi.
      * destruct (decide (fi = tgt)) as [->|Hne].
        -- exfalso.
           pose proof (Huniq i vi (map_lookup_insert s' i vi) Hfi) as Hi.
           congruence.
        -- rewrite map_lookup_insert_ne by congruence.
           eapply IH; [exact Hlookup|exact Hfk|].
           intros k0 v0 Hk0 Hfk0.
           eapply Huniq; [|exact Hfk0].
           rewrite map_lookup_insert_ne; [exact Hk0|].
           intros ->. rewrite Hfresh in Hk0. discriminate.
      * eapply IH; [exact Hlookup|exact Hfk|].
        intros k0 v0 Hk0 Hfk0.
        eapply Huniq; [|exact Hfk0].
        rewrite map_lookup_insert_ne; [exact Hk0|].
        intros ->. rewrite Hfi in Hfk0. discriminate.
Qed.

Lemma filter_map_key_lookup_none_no_preimage
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') (s : gmap K V) k' :
  (forall k v, s !! k = Some v -> f k <> Some k') ->
  storeA_filter_map_key f s !! k' = None.
Proof.
  unfold storeA_filter_map_key.
  refine (fin_maps.map_fold_ind (M:=gmap K)
    (fun s => forall tgt,
      (forall k v, s !! k = Some v -> f k <> Some tgt) ->
      map_fold
        (fun k v acc =>
          match f k with
          | Some tgt' => <[tgt' := v]> acc
          | None => acc
          end) ∅ s !! tgt = None) _ _ s k').
  - intros tgt _.
    change ((∅ : gmap K' V) !! tgt = None).
    better_map_solver.
  - intros i vi s' Hfresh Hfold IH tgt Hnone.
    rewrite Hfold.
    destruct (f i) as [fi|] eqn:Hfi.
    + destruct (decide (fi = tgt)) as [->|Hne].
      * exfalso. exact (Hnone i vi (map_lookup_insert s' i vi) Hfi).
      * rewrite map_lookup_insert_ne by congruence.
        apply IH. intros k v Hk Hfk.
        apply (Hnone k v); [|exact Hfk].
        rewrite map_lookup_insert_ne; [exact Hk|].
        intros ->. rewrite Hfresh in Hk. discriminate.
    + apply IH. intros k v Hk Hfk.
      apply (Hnone k v); [|exact Hfk].
      rewrite map_lookup_insert_ne; [exact Hk|].
      intros ->. rewrite Hfi in Hfk. discriminate.
Qed.

Local Notation AtomStore := (gmap atom V) (only parsing).
Local Notation LVarStore := (gmap logic_var V) (only parsing).

Definition atom_store_to_lvar_store (s : AtomStore) : LVarStore :=
  storeA_map_key LVFree s.

Definition lvar_store_open (η : gmap nat atom) (s : LVarStore) : AtomStore :=
  storeA_filter_map_key (lvar_to_atom η) s.

Definition lvar_store_to_atom_store (s : LVarStore) : AtomStore :=
  lvar_store_open ∅ s.

Definition lvar_store_shift_from (k : nat) (s : LVarStore) : LVarStore :=
  storeA_rekey (logic_var_shift_from k) s.

Definition lvar_store_shift (s : LVarStore) : LVarStore :=
  lvar_store_shift_from 0 s.

Definition lvar_store_open_one (k : nat) (x : atom)
    (s : LVarStore) : LVarStore :=
  storeA_rekey (logic_var_open k x) s.

Definition lvar_store_open_lvars (η : gmap nat atom)
    (s : LVarStore) : LVarStore :=
  storeA_rekey (logic_var_open_env η) s.

Definition lvar_store_atom_dom (s : LVarStore) : aset :=
  lvars_fv (dom (s : gmap logic_var V)).

Definition lvar_store_closed (s : LVarStore) : Prop :=
  lc_lvars (dom (s : gmap logic_var V)).

Definition lvar_store_bvar_scope (s : LVarStore) : lvset :=
  lvars_of_bvars (lvars_bv (dom (s : gmap logic_var V))).

Definition lvar_store_swap (x y : atom) (s : LVarStore) : LVarStore :=
  storeA_rekey (logic_var_swap x y) s.

Lemma atom_store_to_lvar_store_dom (s : AtomStore) :
  dom (atom_store_to_lvar_store s : gmap logic_var V) =
  lvars_of_atoms (dom (s : gmap atom V)).
Proof.
  unfold atom_store_to_lvar_store, lvars_of_atoms.
  apply storeA_map_key_dom.
  intros x y Heq. inversion Heq. reflexivity.
Qed.

Lemma atom_store_to_lvar_store_insert x v (s : AtomStore) :
  atom_store_to_lvar_store (<[x := v]> s) =
  <[LVFree x := v]> (atom_store_to_lvar_store s).
Proof.
  unfold atom_store_to_lvar_store.
  apply storeA_map_key_insert.
  intros a b Heq. inversion Heq. reflexivity.
Qed.

Lemma atom_store_to_lvar_store_closed (s : AtomStore) :
  lvar_store_closed (atom_store_to_lvar_store s).
Proof.
  unfold lvar_store_closed.
  rewrite !atom_store_to_lvar_store_dom.
  apply (proj2 (lc_lvars_no_bv _)).
  apply lvars_bv_of_atoms.
Qed.

Lemma atom_store_to_lvar_store_lookup_bound_none (s : AtomStore) k :
  (atom_store_to_lvar_store s : gmap logic_var V) !! LVBound k = None.
Proof.
  apply not_elem_of_dom.
  rewrite atom_store_to_lvar_store_dom.
  unfold lvars_of_atoms.
  intros Hin. apply elem_of_map in Hin as [x [Hbad _]].
  discriminate.
Qed.

Lemma atom_store_to_lvar_store_lookup_free_none (s : AtomStore) x :
  x ∉ dom (s : gmap atom V) ->
  (atom_store_to_lvar_store s : gmap logic_var V) !! LVFree x = None.
Proof.
  intros Hfresh.
  apply not_elem_of_dom.
  rewrite atom_store_to_lvar_store_dom.
  unfold lvars_of_atoms.
  intros Hin. apply elem_of_map in Hin as [y [Hy HyD]].
  inversion Hy. subst y. exact (Hfresh HyD).
Qed.

Lemma atom_store_to_lvar_store_lookup_free (s : AtomStore) x :
  (atom_store_to_lvar_store s : gmap logic_var V) !! LVFree x =
  (s : gmap atom V) !! x.
Proof.
  unfold atom_store_to_lvar_store.
  change ((storeA_map_key LVFree s : gmap logic_var V) !! LVFree x =
    (s : gmap atom V) !! x).
  apply storeA_map_key_lookup.
  intros a b Heq. inversion Heq. reflexivity.
Qed.

Lemma atom_store_to_lvar_store_union (s1 s2 : AtomStore) :
  atom_store_to_lvar_store (s1 ∪ s2) =
  atom_store_to_lvar_store s1 ∪ atom_store_to_lvar_store s2.
Proof.
  apply storeA_map_eq. intros v.
  destruct v as [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none.
    symmetry. apply map_lookup_union_None. split;
      rewrite atom_store_to_lvar_store_lookup_bound_none; reflexivity.
  - rewrite atom_store_to_lvar_store_lookup_free.
    destruct ((s1 : gmap atom V) !! x) as [v1|] eqn:H1.
    + rewrite (lookup_union_l' (M:=gmap atom) (A:=V)
        (s1 : gmap atom V) (s2 : gmap atom V) x) by eauto.
      symmetry. rewrite (lookup_union_l' (M:=gmap logic_var) (A:=V)
        (atom_store_to_lvar_store s1 : gmap logic_var V)
        (atom_store_to_lvar_store s2 : gmap logic_var V)
        (LVFree x)) by (rewrite atom_store_to_lvar_store_lookup_free; eauto).
      rewrite atom_store_to_lvar_store_lookup_free. reflexivity.
    + rewrite (lookup_union_r (M:=gmap atom) (A:=V)
        (s1 : gmap atom V) (s2 : gmap atom V) x H1).
      symmetry. rewrite (lookup_union_r (M:=gmap logic_var) (A:=V)
        (atom_store_to_lvar_store s1 : gmap logic_var V)
        (atom_store_to_lvar_store s2 : gmap logic_var V)
        (LVFree x)).
      * rewrite atom_store_to_lvar_store_lookup_free. reflexivity.
      * rewrite atom_store_to_lvar_store_lookup_free. exact H1.
Qed.

Lemma lvar_store_atom_dom_insert_bound (s : LVarStore) k v :
  lvar_store_atom_dom (<[LVBound k := v]> s) = lvar_store_atom_dom s.
Proof.
  unfold lvar_store_atom_dom.
  rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
    (s : gmap logic_var V) (LVBound k) v).
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  better_set_solver.
Qed.

Lemma lvar_store_shift_free_notin_from k x (s : LVarStore) :
  LVFree x ∉ dom (s : gmap logic_var V) ->
  LVFree x ∉ dom (lvar_store_shift_from k s : gmap logic_var V).
Proof.
  intros Hfresh.
  unfold lvar_store_shift_from.
  change (LVFree x ∉ dom (storeA_rekey (logic_var_shift_from k) s : gmap logic_var V)).
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  intros Hin. apply elem_of_map in Hin as [v [Hv HvD]].
  destruct v as [n|y]; cbn [logic_var_shift_from] in Hv.
  - destruct (decide (k <= n)); discriminate.
  - inversion Hv. subst y. exact (Hfresh HvD).
Qed.

Lemma lvar_store_shift_free_notin x (s : LVarStore) :
  LVFree x ∉ dom (s : gmap logic_var V) ->
  LVFree x ∉ dom (lvar_store_shift s : gmap logic_var V).
Proof.
  apply lvar_store_shift_free_notin_from.
Qed.

Lemma lvar_store_shift_insert_from k v A (s : LVarStore) :
  lvar_store_shift_from k (<[v := A]> s) =
  <[logic_var_shift_from k v := A]> (lvar_store_shift_from k s).
Proof.
  unfold lvar_store_shift_from.
  apply storeA_rekey_insert, logic_var_shift_from_inj.
Qed.

Lemma lvar_store_shift_insert v A (s : LVarStore) :
  lvar_store_shift (<[v := A]> s) =
  <[logic_var_shift_from 0 v := A]> (lvar_store_shift s).
Proof.
  apply lvar_store_shift_insert_from.
Qed.

Lemma lvar_store_shift_insert_free x A (s : LVarStore) :
  lvar_store_shift (<[LVFree x := A]> s) =
  <[LVFree x := A]> (lvar_store_shift s).
Proof.
  apply lvar_store_shift_insert.
Qed.

Lemma lvar_store_atom_dom_shift_from k (s : LVarStore) :
  lvar_store_atom_dom (lvar_store_shift_from k s) = lvar_store_atom_dom s.
Proof.
  unfold lvar_store_atom_dom, lvar_store_shift_from.
  change (lvars_fv (dom (storeA_rekey (logic_var_shift_from k) s : gmap logic_var V)) =
    lvars_fv (dom (s : gmap logic_var V))).
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  apply lvars_shift_from_fv.
Qed.

Lemma lvar_store_atom_dom_shift (s : LVarStore) :
  lvar_store_atom_dom (lvar_store_shift s) = lvar_store_atom_dom s.
Proof.
  apply lvar_store_atom_dom_shift_from.
Qed.

Lemma lvar_store_open_lvars_shift_from k η (s : LVarStore) :
  open_env_fresh_for_lvars η (dom (s : gmap logic_var V)) ->
  lvar_store_open_lvars (open_env_shift_from k η)
    (lvar_store_shift_from k s) =
  lvar_store_shift_from k (lvar_store_open_lvars η s).
Proof.
  intros Hfresh.
  unfold lvar_store_open_lvars, lvar_store_shift_from.
  assert (Hfresh_shift :
    open_env_fresh_for_lvars (open_env_shift_from k η)
      (dom (storeA_rekey (logic_var_shift_from k) s : gmap logic_var V))).
  {
    rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
    change (open_env_fresh_for_lvars (open_env_shift_from k η)
      (lvars_shift_from k (dom (s : gmap logic_var V)))).
    apply open_env_shift_from_fresh_for_lvars. exact Hfresh.
  }
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_open_env (open_env_shift_from k η))
    (logic_var_shift_from k) s).
  2:{ intros a b _ _ Hab. eapply logic_var_shift_from_inj. exact Hab. }
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh_shift. }
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_shift_from k)
    (logic_var_open_env η) s).
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
  2:{ intros a b _ _ Hab. eapply logic_var_shift_from_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_env_shift_from.
Qed.

Lemma lvar_store_open_one_shift_under_gen j k x (s : LVarStore) :
  j <= k ->
  lvar_store_open_one (S k) x (lvar_store_shift_from j s) =
  lvar_store_shift_from j (lvar_store_open_one k x s).
Proof.
  intros Hjk.
  unfold lvar_store_open_one, lvar_store_shift_from.
  rewrite storeA_rekey_compose; try apply logic_var_shift_from_inj;
    try apply swap_inj.
  rewrite storeA_rekey_compose; try apply logic_var_shift_from_inj;
    try apply swap_inj.
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_shift_from_under_gen. exact Hjk.
Qed.

Lemma lvar_store_open_one_insert k x v A (s : LVarStore) :
  lvar_store_open_one k x (<[v := A]> s) =
  <[logic_var_open k x v := A]> (lvar_store_open_one k x s).
Proof.
  unfold lvar_store_open_one.
  apply storeA_rekey_insert.
  apply swap_inj.
Qed.

Lemma lvar_store_shift_atom_store (s : AtomStore) :
  lvar_store_shift (atom_store_to_lvar_store s) = atom_store_to_lvar_store s.
Proof.
  apply storeA_map_eq. intros v.
  destruct v as [k|x].
  - transitivity (@None V).
    + change (((lvar_store_shift (atom_store_to_lvar_store s) : LVarStore)
          : gmap logic_var V) !! LVBound k = None).
      apply not_elem_of_dom.
      unfold lvar_store_shift, lvar_store_shift_from.
      change (LVBound k ∉
        dom (storeA_rekey (logic_var_shift_from 0) (atom_store_to_lvar_store s)
          : gmap logic_var V)).
      rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
      intros Hin. apply elem_of_map in Hin as [u [Hu HuD]].
      destruct u as [n|y]; cbn [logic_var_shift_from] in Hu.
      * exfalso.
        apply elem_of_dom in HuD as [A HA].
        rewrite atom_store_to_lvar_store_lookup_bound_none in HA. discriminate.
      * inversion Hu.
    + symmetry. apply atom_store_to_lvar_store_lookup_bound_none.
  - unfold lvar_store_shift, lvar_store_shift_from.
    unfold kmap.
    change ((kmap (M2:=gmap logic_var) (logic_var_shift_from 0)
        (atom_store_to_lvar_store s)) !! LVFree x =
      atom_store_to_lvar_store s !! LVFree x).
    change (LVFree x) with (logic_var_shift_from 0 (LVFree x)) at 1.
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj 0)
      (logic_var_shift_from 0) (atom_store_to_lvar_store s) (LVFree x)).
    reflexivity.
Qed.

Lemma lvar_store_shift_from_atom_store k (s : AtomStore) :
  lvar_store_shift_from k (atom_store_to_lvar_store s) =
  atom_store_to_lvar_store s.
Proof.
  apply storeA_map_eq. intros v.
  destruct v as [n|x].
  - transitivity (@None V).
    + apply not_elem_of_dom.
      unfold lvar_store_shift_from.
      change (LVBound n ∉
        dom (storeA_rekey (logic_var_shift_from k) (atom_store_to_lvar_store s)
          : gmap logic_var V)).
      rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
      intros Hin. apply elem_of_map in Hin as [u [Hu HuD]].
      destruct u as [m|y]; cbn [logic_var_shift_from] in Hu.
      * destruct (decide (k <= m)); inversion Hu; subst.
        all: apply elem_of_dom in HuD as [A HA];
          rewrite atom_store_to_lvar_store_lookup_bound_none in HA;
          discriminate.
      * discriminate.
    + symmetry. apply atom_store_to_lvar_store_lookup_bound_none.
  - unfold lvar_store_shift_from.
    change ((storeA_rekey (logic_var_shift_from k)
        (atom_store_to_lvar_store s) : gmap logic_var V) !! LVFree x =
      atom_store_to_lvar_store s !! LVFree x).
    change (LVFree x) with (logic_var_shift_from k (LVFree x)) at 1.
    rewrite storeA_rekey_lookup by apply logic_var_shift_from_inj.
    reflexivity.
Qed.

Lemma logic_var_swap_match x y v :
  match v with
  | LVFree z => LVFree (swap x y z)
  | LVBound k => LVBound k
  end = logic_var_swap x y v.
Proof.
  destruct v as [k|z].
  - unfold swap. repeat destruct decide; congruence.
  - rewrite logic_var_free_swap.
    reflexivity.
Qed.

Lemma lvar_store_swap_lookup x y (s : LVarStore) v :
  lvar_store_swap x y s !!
    (match v with
     | LVFree z => LVFree (swap x y z)
     | LVBound k => LVBound k
     end) = s !! v.
Proof.
  rewrite logic_var_swap_match.
  unfold lvar_store_swap.
  unfold kmap.
  change ((kmap (M2:=gmap logic_var) (swap (LVFree x) (LVFree y)) s) !!
      swap (LVFree x) (LVFree y) v = (s : gmap logic_var V) !! v).
  rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (Inj0:=swap_inj (LVFree x) (LVFree y))
    (swap (LVFree x) (LVFree y)) s v).
  reflexivity.
Qed.

Lemma lvar_store_swap_lookup_inv x y (s : LVarStore) v :
  lvar_store_swap x y s !! v =
  s !! (match v with
        | LVFree z => LVFree (swap x y z)
        | LVBound k => LVBound k
        end).
Proof.
  rewrite logic_var_swap_match.
  rewrite <- (logic_var_swap_involutive x y v) at 1.
  rewrite <- logic_var_swap_match.
  apply lvar_store_swap_lookup.
Qed.

Lemma lvar_store_swap_dom x y (s : LVarStore) :
  dom (lvar_store_swap x y s : gmap logic_var V) =
  lvars_swap x y (dom (s : gmap logic_var V)).
Proof.
  unfold lvar_store_swap.
  change (dom (storeA_rekey (logic_var_swap x y) s : gmap logic_var V) =
    set_swap (LVFree x) (LVFree y) (dom (s : gmap logic_var V))).
  rewrite storeA_rekey_dom by apply swap_inj.
  unfold set_swap.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]]. exists u. split; [|exact Hu].
    reflexivity.
  - intros [u [-> Hu]]. exists u. split; [|exact Hu].
    reflexivity.
Qed.

Lemma lvar_store_swap_insert x y (s : LVarStore) v A :
  lvar_store_swap x y (<[v := A]> s) =
  <[match v with
     | LVFree z => LVFree (swap x y z)
     | LVBound k => LVBound k
     end := A]> (lvar_store_swap x y s).
Proof.
  rewrite logic_var_swap_match.
  unfold lvar_store_swap.
  apply storeA_rekey_insert, swap_inj.
Qed.

Lemma lvar_store_swap_atom_dom x y (s : LVarStore) :
  lvar_store_atom_dom (lvar_store_swap x y s) =
  set_swap x y (lvar_store_atom_dom s).
Proof.
  apply set_eq. intros z.
  unfold lvar_store_atom_dom.
  rewrite elem_of_set_swap, !lvars_fv_elem.
  split.
  - intros Hz.
    change (LVFree z ∈ dom ((lvar_store_swap x y s : LVarStore)
      : gmap logic_var V)) in Hz.
    apply elem_of_dom in Hz as [A Hz].
    rewrite lvar_store_swap_lookup_inv in Hz.
    change (LVFree (swap x y z) ∈ dom (s : gmap logic_var V)).
    apply elem_of_dom. exists A. exact Hz.
  - intros Hz.
    change (LVFree (swap x y z) ∈ dom (s : gmap logic_var V)) in Hz.
    apply elem_of_dom in Hz as [A Hlookup].
    change (LVFree z ∈ dom ((lvar_store_swap x y s : LVarStore)
      : gmap logic_var V)).
    apply elem_of_dom. exists A.
    rewrite lvar_store_swap_lookup_inv.
    exact Hlookup.
Qed.

Lemma lvar_store_atom_dom_lookup_free (s : LVarStore) x A :
  s !! LVFree x = Some A ->
  x ∈ lvar_store_atom_dom s.
Proof.
  intros Hlookup.
  unfold lvar_store_atom_dom.
  apply lvars_fv_elem.
  change (LVFree x ∈ dom (s : gmap logic_var V)).
  apply elem_of_dom. eexists. exact Hlookup.
Qed.

Lemma lvar_store_swap_fresh x y (s : LVarStore) :
  x ∉ lvar_store_atom_dom s ->
  y ∉ lvar_store_atom_dom s ->
  lvar_store_swap x y s = s.
Proof.
  intros Hx Hy.
  apply storeA_map_eq. intros v.
  rewrite lvar_store_swap_lookup_inv.
  destruct v as [k|z]; cbn.
  - reflexivity.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite swap_l.
      destruct (s !! LVFree y) eqn:Hlooky.
      * exfalso. apply Hy. eapply lvar_store_atom_dom_lookup_free. exact Hlooky.
      * destruct (s !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. eapply lvar_store_atom_dom_lookup_free. exact Hlookx.
        -- reflexivity.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite swap_r.
        destruct (s !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. eapply lvar_store_atom_dom_lookup_free. exact Hlookx.
        -- destruct (s !! LVFree y) eqn:Hlooky.
           ++ exfalso. apply Hy. eapply lvar_store_atom_dom_lookup_free. exact Hlooky.
           ++ reflexivity.
      * base_swap_normalize. reflexivity.
Qed.

Lemma lvar_store_swap_atom_store_fresh (s : AtomStore) x y :
  x ∉ dom (s : gmap atom V) ->
  y ∉ dom (s : gmap atom V) ->
  lvar_store_swap x y (atom_store_to_lvar_store s) =
  atom_store_to_lvar_store s.
Proof.
  intros Hx Hy.
  apply storeA_map_eq. intros v.
  rewrite lvar_store_swap_lookup_inv.
  destruct v as [k|z]; cbn.
  - rewrite !atom_store_to_lvar_store_lookup_bound_none. reflexivity.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite swap_l.
      rewrite !atom_store_to_lvar_store_lookup_free_none by assumption.
      reflexivity.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite swap_r.
        rewrite !atom_store_to_lvar_store_lookup_free_none by assumption.
        reflexivity.
      * base_swap_normalize. reflexivity.
Qed.

Lemma lvar_store_swap_atom_store_insert_fresh (s : AtomStore) x y v :
  x ∉ dom (s : gmap atom V) ->
  y ∉ dom (s : gmap atom V) ->
  x <> y ->
  lvar_store_swap y x (atom_store_to_lvar_store (<[y := v]> s)) =
  <[LVFree x := v]> (atom_store_to_lvar_store s).
Proof.
  intros Hx Hy Hxy.
  rewrite atom_store_to_lvar_store_insert.
  rewrite lvar_store_swap_insert.
  cbn.
  rewrite swap_l.
  rewrite lvar_store_swap_atom_store_fresh by assumption.
  reflexivity.
Qed.

Lemma lvar_store_open_one_atom_store k x (s : AtomStore) :
  x ∉ dom (s : gmap atom V) ->
  lvar_store_open_one k x (atom_store_to_lvar_store s) =
  atom_store_to_lvar_store s.
Proof.
  intros Hx.
  unfold lvar_store_open_one.
  change (storeA_swap (LVBound k) (LVFree x)
    (atom_store_to_lvar_store s) = atom_store_to_lvar_store s).
  apply storeA_swap_fresh.
  - apply not_elem_of_dom.
    apply atom_store_to_lvar_store_lookup_bound_none.
  - apply not_elem_of_dom.
    apply atom_store_to_lvar_store_lookup_free_none. exact Hx.
Qed.

Lemma lvar_store_open_one_bind_atom_store x v (s : AtomStore) :
  x ∉ dom (s : gmap atom V) ->
  lvar_store_open_one 0 x
    (<[LVBound 0 := v]> (lvar_store_shift (atom_store_to_lvar_store s))) =
  <[LVFree x := v]> (atom_store_to_lvar_store s).
Proof.
  intros Hx.
  rewrite lvar_store_shift_atom_store.
  rewrite lvar_store_open_one_insert.
  replace (logic_var_open 0 x (LVBound 0)) with (LVFree x).
  rewrite lvar_store_open_one_atom_store by exact Hx.
  reflexivity.
  unfold swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma lvar_store_open_atom_store η (s : AtomStore) :
  lvar_store_open η (atom_store_to_lvar_store s) = s.
Proof.
  refine (fin_maps.map_fold_ind (M:=gmap atom)
    (fun s => lvar_store_open η (atom_store_to_lvar_store s) = s) _ _ s).
  - unfold lvar_store_open, atom_store_to_lvar_store,
      storeA_filter_map_key.
    rewrite kmap_empty. reflexivity.
  - intros x v s' Hfresh Hfold IH.
    rewrite atom_store_to_lvar_store_insert.
    unfold lvar_store_open, storeA_filter_map_key at 1.
    rewrite (map_fold_insert_L
      (M:=gmap logic_var)
      (fun w A acc =>
        match lvar_to_atom η w with
        | Some y => <[y:=A]> acc
        | None => acc
        end)
      (∅ : gmap atom V) (LVFree x) v (atom_store_to_lvar_store s')).
    + change (map_fold
        (fun w A acc =>
          match lvar_to_atom η w with
          | Some y => <[y:=A]> acc
          | None => acc
          end) ∅ (atom_store_to_lvar_store s'))
        with (lvar_store_open η (atom_store_to_lvar_store s')).
      cbn [lvar_to_atom logic_var_to_atom].
      rewrite IH. reflexivity.
    + intros i j Ai Aj acc Hne Hi Hj.
      destruct i as [ki|xi], j as [kj|xj];
        cbn [lvar_to_atom logic_var_to_atom] in *; try reflexivity.
      * rewrite map_lookup_insert_ne in Hi by congruence.
        rewrite atom_store_to_lvar_store_lookup_bound_none in Hi. discriminate.
      * rewrite map_lookup_insert_ne in Hi by congruence.
        rewrite atom_store_to_lvar_store_lookup_bound_none in Hi. discriminate.
      * rewrite map_lookup_insert_ne in Hj by congruence.
        rewrite atom_store_to_lvar_store_lookup_bound_none in Hj. discriminate.
      * apply insert_insert_ne. congruence.
    + apply atom_store_to_lvar_store_lookup_free_none.
      apply not_elem_of_dom. exact Hfresh.
Qed.

Lemma lvar_store_open_env_insert_fresh k x η (s : LVarStore) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  s !! LVBound k = None ->
  s !! LVFree x = None ->
  lvar_store_open (<[k := x]> η) s = lvar_store_open η s.
Proof.
  intros Hη Havoid Hbound Hfree.
  unfold lvar_store_open.
  apply map_fold_ext_on_lookup. intros v U Hv acc.
  erewrite lvar_to_atom_insert_open_env_fresh; try reflexivity; eauto.
  - intros ->.
    rewrite Hbound in Hv. discriminate.
  - intros ->.
    rewrite Hfree in Hv. discriminate.
Qed.

Lemma lvar_store_open_insert_bound_commute
    (k : nat) (x : atom) (A : V) (η : gmap nat atom)
    (s : LVarStore) (j : logic_var) (U : V) (acc : gmap atom V) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  s !! LVFree x = None ->
  j <> LVBound k ->
  (<[LVBound k := A]> s) !! j = Some U ->
  <[x := A]>
    (match lvar_to_atom (<[k := x]> η) j with
     | Some y => <[y := U]> acc
     | None => acc
     end) =
  match lvar_to_atom (<[k := x]> η) j with
  | Some y => <[y := U]> (<[x := A]> acc)
  | None => <[x := A]> acc
  end.
Proof.
  intros Hη Havoid Hfree Hj Hlookup.
  destruct j as [n|y]; cbn [lvar_to_atom logic_var_to_atom].
  - destruct (decide (n = k)) as [->|Hnk]; [congruence|].
    rewrite lookup_insert_ne by congruence.
    destruct (η !! n) as [z|] eqn:Hηn; [|reflexivity].
    apply insert_insert_ne. intros ->. exact (Havoid n Hηn).
  - destruct (decide (y = x)) as [->|Hyx].
    + rewrite lookup_insert_ne in Hlookup by congruence.
      rewrite Hfree in Hlookup. discriminate.
    + apply insert_insert_ne. congruence.
Qed.

Lemma lvar_store_open_step_commute
    (η : gmap nat atom) (i j : logic_var)
    (Ai Aj : V) (acc : gmap atom V) :
  i <> j ->
  (forall x,
    lvar_to_atom η i = Some x ->
    lvar_to_atom η j = Some x ->
    i = j) ->
  match lvar_to_atom η i with
  | Some x => <[x:=Ai]>
      (match lvar_to_atom η j with
       | Some y => <[y:=Aj]> acc
       | None => acc
       end)
  | None =>
      match lvar_to_atom η j with
      | Some y => <[y:=Aj]> acc
      | None => acc
      end
  end =
  match lvar_to_atom η j with
  | Some y => <[y:=Aj]>
      (match lvar_to_atom η i with
       | Some x => <[x:=Ai]> acc
       | None => acc
       end)
  | None =>
      match lvar_to_atom η i with
      | Some x => <[x:=Ai]> acc
      | None => acc
      end
  end.
Proof.
  intros Hne Hinj.
  destruct (lvar_to_atom η i) as [x|] eqn:Hi;
    destruct (lvar_to_atom η j) as [y|] eqn:Hj; try reflexivity.
  destruct (decide (x = y)) as [Hxy|Hxy].
  - subst y. exfalso. apply Hne. exact (Hinj x eq_refl eq_refl).
  - apply insert_insert_ne. congruence.
Qed.

Lemma lvar_store_open_insert_bound_atom_store k x A η (s : LVarStore) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η)
    (dom (<[LVBound k := A]> s : LVarStore)) ->
  s !! LVBound k = None ->
  s !! LVFree x = None ->
  lvar_store_open (<[k := x]> η) (<[LVBound k := A]> s) =
  <[x := A]> (lvar_store_open η s).
Proof.
  intros Hη Havoid Hfresh Hbound Hfree.
  unfold lvar_store_open, storeA_filter_map_key at 1.
  rewrite (map_fold_insert_L
    (fun v U acc =>
      match lvar_to_atom (<[k:=x]> η) v with
      | Some y => <[y:=U]> acc
      | None => acc
      end)
    (∅ : gmap atom V) (LVBound k) A s).
  - cbn [lvar_to_atom logic_var_to_atom].
    rewrite lookup_insert_eq.
    change (map_fold
      (fun v U acc =>
        match lvar_to_atom (<[k:=x]> η) v with
        | Some y => <[y:=U]> acc
        | None => acc
        end) ∅ s)
      with (lvar_store_open (<[k:=x]> η) s).
    rewrite lvar_store_open_env_insert_fresh by assumption.
    reflexivity.
  - intros j1 j2 U1 U2 acc Hne Hj1 Hj2.
    destruct (decide (j1 = LVBound k)) as [->|Hj1k].
    + cbn [lvar_to_atom logic_var_to_atom]. rewrite lookup_insert_eq.
      rewrite lookup_insert_eq in Hj1.
      injection Hj1 as HU1. symmetry in HU1. subst U1.
      eapply (lvar_store_open_insert_bound_commute k x A η s j2 U2 acc);
        try assumption; congruence.
    + destruct (decide (j2 = LVBound k)) as [->|Hj2k].
      * cbn [lvar_to_atom logic_var_to_atom]. rewrite lookup_insert_eq.
        rewrite lookup_insert_eq in Hj2.
        injection Hj2 as HU2. symmetry in HU2. subst U2.
        symmetry.
        eapply (lvar_store_open_insert_bound_commute k x A η s j1 U1 acc);
          try assumption; congruence.
      * eapply lvar_store_open_step_commute; [exact Hne|].
        intros y Hy1 Hy2.
        eapply lvar_to_atom_inj_on_fresh; try eassumption.
        -- change (j1 ∈ dom (<[LVBound k:=A]> (s : gmap logic_var V))).
           apply elem_of_dom. exists U1. exact Hj1.
        -- change (j2 ∈ dom (<[LVBound k:=A]> (s : gmap logic_var V))).
           apply elem_of_dom. exists U2. exact Hj2.
  - exact Hbound.
Qed.

Lemma lvar_store_to_atom_store_atom_store (s : AtomStore) :
  lvar_store_to_atom_store (atom_store_to_lvar_store s) = s.
Proof.
  unfold lvar_store_to_atom_store.
  apply lvar_store_open_atom_store.
Qed.

Lemma lvar_store_to_atom_store_lookup_some (s : LVarStore) x v :
  lvar_store_to_atom_store s !! x = Some v ->
  s !! LVFree x = Some v.
Proof.
  unfold lvar_store_to_atom_store, lvar_store_open.
  intros Hlookup.
  apply storeA_filter_map_key_lookup_some_inv in Hlookup as [[k|y] [Hsrc Hmap]].
  - cbn [lvar_to_atom logic_var_to_atom] in Hmap.
    rewrite lookup_empty in Hmap. discriminate.
  - cbn [lvar_to_atom logic_var_to_atom] in Hmap.
    inversion Hmap. subst y. exact Hsrc.
Qed.

Lemma lvar_store_to_atom_store_lookup_free_some (s : LVarStore) x v :
  (s : gmap logic_var V) !! LVFree x = Some v ->
  lvar_store_to_atom_store s !! x = Some v.
Proof.
  unfold lvar_store_to_atom_store, lvar_store_open.
  intros Hlookup.
  eapply storeA_filter_map_key_lookup_some_unique; [exact Hlookup|reflexivity|].
  intros [k|y] A Hsrc Hmap.
  - cbn [lvar_to_atom logic_var_to_atom] in Hmap.
    rewrite lookup_empty in Hmap. discriminate.
  - cbn [lvar_to_atom logic_var_to_atom] in Hmap.
    inversion Hmap. reflexivity.
Qed.

Lemma lvar_store_to_atom_store_lookup (s : LVarStore) x :
  lvar_store_to_atom_store s !! x = (s : gmap logic_var V) !! LVFree x.
Proof.
  destruct ((s : gmap logic_var V) !! LVFree x) as [v|] eqn:Hlookup.
  - apply lvar_store_to_atom_store_lookup_free_some. exact Hlookup.
  - unfold lvar_store_to_atom_store, lvar_store_open.
    apply filter_map_key_lookup_none_no_preimage.
    intros [k|y] A Hsrc Hmap.
    + cbn [lvar_to_atom logic_var_to_atom] in Hmap.
      rewrite lookup_empty in Hmap. discriminate.
    + cbn [lvar_to_atom logic_var_to_atom] in Hmap.
      inversion Hmap. subst y. rewrite Hlookup in Hsrc. discriminate.
Qed.

Lemma lvar_store_to_atom_store_insert_free (s : LVarStore) x v :
  lvar_store_to_atom_store (<[LVFree x := v]> s) =
  <[x := v]> (lvar_store_to_atom_store s).
Proof.
  apply (map_eq (M:=gmap atom)). intros y.
  rewrite lvar_store_to_atom_store_lookup.
  destruct (decide (y = x)) as [->|Hyx].
  - change ((((<[LVFree x := v]> (s : gmap logic_var V))
        : gmap logic_var V) !! LVFree x) =
      (((<[x := v]> (lvar_store_to_atom_store s)) : gmap atom V) !! x)).
    rewrite map_lookup_insert.
    change (Some v =
      (((<[x := v]> (lvar_store_to_atom_store s)) : gmap atom V) !! x)).
    symmetry.
    exact (map_lookup_insert (lvar_store_to_atom_store s) x v).
  - rewrite (map_lookup_insert_ne (s : gmap logic_var V) (LVFree x) (LVFree y) v)
      by congruence.
    change ((s : gmap logic_var V) !! LVFree y =
      (((<[x := v]> (lvar_store_to_atom_store s)) : gmap atom V) !! y)).
    transitivity (lvar_store_to_atom_store s !! y).
    + symmetry. apply lvar_store_to_atom_store_lookup.
    + symmetry.
      apply map_lookup_insert_ne. congruence.
Qed.

Lemma lvar_to_atom_insert_free_lookup_ne
    (s : LVarStore) x v a :
  a <> x ->
  lvar_store_to_atom_store (<[LVFree x := v]> s) !! a =
  lvar_store_to_atom_store s !! a.
Proof.
  intros Hax.
  rewrite lvar_store_to_atom_store_insert_free.
  apply lookup_insert_ne. congruence.
Qed.

Lemma lvar_store_to_atom_store_swap x y (s : LVarStore) :
  lvar_store_to_atom_store (lvar_store_swap x y s) =
  (@storeA_swap V atom _ _ x y (lvar_store_to_atom_store s) : gmap atom V).
Proof.
  apply (map_eq (M:=gmap atom)). intros z.
  rewrite lvar_store_to_atom_store_lookup.
  transitivity (lvar_store_to_atom_store s !! swap x y z).
  - rewrite lvar_store_swap_lookup_inv.
    symmetry. apply lvar_store_to_atom_store_lookup.
  - symmetry. apply storeA_swap_lookup_inv.
Qed.

Lemma lvar_store_to_atom_store_dom_subset (s : LVarStore) :
  dom (lvar_store_to_atom_store s) ⊆ lvar_store_atom_dom s.
Proof.
  intros x Hx.
  change (x ∈ dom (lvar_store_to_atom_store s : gmap atom V)) in Hx.
  apply elem_of_dom in Hx as [v Hv].
  apply lvar_store_to_atom_store_lookup_some in Hv.
  unfold lvar_store_atom_dom.
  apply lvars_fv_elem.
  change (((s : LVarStore) : gmap logic_var V) !! LVFree x = Some v) in Hv.
  better_map_solver.
Qed.

End StoreFilterMapKey.
