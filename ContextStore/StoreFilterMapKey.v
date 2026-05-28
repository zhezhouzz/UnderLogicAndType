(** * Generic stores: partial key projection *)

From ContextBase Require Import Prelude LogicVar LogicVarOpenEnv LogicVarShift BaseTactics.
From ContextStore Require Import StoreCore.

Notation lvar_to_atom := logic_var_to_atom (only parsing).

Section StoreFilterMapKey.

Context {V : Type} `{ValueSig V}.

Definition storeA_filter_map_key
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') (s : StoreA K) : StoreA K' :=
  map_fold (fun k v (acc : gmap K' V) =>
    match f k with
    | Some k' => <[k' := v]> acc
    | None => acc
    end) ∅ s.

Lemma storeA_filter_map_key_empty
    {K K' : Type} `{Countable K} `{Countable K'}
    (f : K -> option K') :
  storeA_filter_map_key f (∅ : StoreA K) = (∅ : StoreA K').
Proof.
  unfold storeA_filter_map_key. reflexivity.
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

Lemma atom_store_to_lvar_store_atom_dom (s : AtomStore) :
  lvar_store_atom_dom (atom_store_to_lvar_store s) =
  dom (s : gmap atom V).
Proof.
  unfold lvar_store_atom_dom.
  rewrite atom_store_to_lvar_store_dom.
  apply lvars_fv_of_atoms.
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
    unfold storeA_rekey, storeA_map_key.
    change ((kmap (M2:=gmap logic_var) (logic_var_shift_from 0)
        (atom_store_to_lvar_store s)) !! LVFree x =
      atom_store_to_lvar_store s !! LVFree x).
    change (LVFree x) with (logic_var_shift_from 0 (LVFree x)) at 1.
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj 0)
      (logic_var_shift_from 0) (atom_store_to_lvar_store s) (LVFree x)).
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
  unfold storeA_rekey, storeA_map_key.
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
        -- symmetry. exact Hlookx.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite swap_r.
        destruct (s !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. eapply lvar_store_atom_dom_lookup_free. exact Hlookx.
        -- destruct (s !! LVFree y) eqn:Hlooky.
           ++ exfalso. apply Hy. eapply lvar_store_atom_dom_lookup_free. exact Hlooky.
           ++ symmetry. exact Hlooky.
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
      storeA_filter_map_key, storeA_map_key.
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
  refine (fin_maps.map_fold_ind (M:=gmap logic_var)
    (fun s => forall x v,
      map_fold
        (fun w A acc =>
          match lvar_to_atom ∅ w with
          | Some y => <[y:=A]> acc
          | None => acc
          end) ∅ s !! x = Some v ->
      s !! LVFree x = Some v) _ _ s x v).
  - intros a A Hlookup.
    rewrite (map_fold_empty (K:=logic_var) (M:=gmap logic_var)) in Hlookup.
    change ((∅ : gmap atom V) !! a = Some A) in Hlookup.
    better_map_solver.
  - intros w A s' Hfresh Hfold IH a B.
    rewrite Hfold.
    destruct w as [k|y]; cbn [lvar_to_atom logic_var_to_atom].
    + intros Hlookup.
      change ((<[LVBound k := A]> (s' : gmap logic_var V) :
        gmap logic_var V) !! LVFree a = Some B).
      rewrite map_lookup_insert_ne by discriminate.
      apply IH. exact Hlookup.
    + intros Hlookup.
      apply (proj1 (lookup_insert_Some (M:=gmap atom)
        (map_fold
           (fun w A acc =>
             match lvar_to_atom ∅ w with
             | Some y => <[y:=A]> acc
             | None => acc
             end) ∅ s') y a A B)) in Hlookup.
      destruct Hlookup as [[-> ->]|[Hya Hlookup]].
      * change ((<[LVFree a := B]> (s' : gmap logic_var V) :
          gmap logic_var V) !! LVFree a = Some B).
        rewrite map_lookup_insert. reflexivity.
      * change ((<[LVFree y := A]> (s' : gmap logic_var V) :
          gmap logic_var V) !! LVFree a = Some B).
        rewrite map_lookup_insert_ne by congruence.
        apply IH. exact Hlookup.
Qed.

Lemma lvar_store_to_atom_store_lookup_free_some (s : LVarStore) x v :
  (s : gmap logic_var V) !! LVFree x = Some v ->
  lvar_store_to_atom_store s !! x = Some v.
Proof.
  unfold lvar_store_to_atom_store, lvar_store_open.
  refine (fin_maps.map_fold_ind (M:=gmap logic_var)
    (fun s => forall x v,
      (s : gmap logic_var V) !! LVFree x = Some v ->
      map_fold
        (fun w A acc =>
          match lvar_to_atom ∅ w with
          | Some y => <[y:=A]> acc
          | None => acc
          end) ∅ s !! x = Some v) _ _ s x v).
  - intros a A Hlookup.
    change ((∅ : gmap logic_var V) !! LVFree a = Some A) in Hlookup.
    better_map_solver.
  - intros w A s' Hfresh Hfold IH a B Hlookup.
    destruct w as [k|y]; cbn [lvar_to_atom logic_var_to_atom].
    + rewrite Hfold.
      change ((<[LVBound k := A]> (s' : gmap logic_var V) :
        gmap logic_var V) !! LVFree a = Some B) in Hlookup.
      rewrite map_lookup_insert_ne in Hlookup by discriminate.
      apply IH. exact Hlookup.
    + rewrite Hfold.
      change ((<[LVFree y := A]> (s' : gmap logic_var V) :
        gmap logic_var V) !! LVFree a = Some B) in Hlookup.
      destruct (decide (y = a)) as [->|Hya].
      * rewrite map_lookup_insert in Hlookup.
        inversion Hlookup. subst A.
        cbn [lvar_to_atom logic_var_to_atom].
        change (((<[a:=B]>
          (map_fold
             (fun w A acc =>
               match lvar_to_atom ∅ w with
               | Some y => <[y:=A]> acc
               | None => acc
               end) ∅ s' : gmap atom V)) : gmap atom V) !! a = Some B).
        exact (map_lookup_insert
          (map_fold
             (fun w A acc =>
               match lvar_to_atom ∅ w with
               | Some y => <[y:=A]> acc
               | None => acc
               end) ∅ s' : gmap atom V) a B).
      * rewrite map_lookup_insert_ne in Hlookup by congruence.
        cbn [lvar_to_atom logic_var_to_atom].
        change (((<[y:=A]>
          (map_fold
             (fun w A acc =>
               match lvar_to_atom ∅ w with
               | Some y => <[y:=A]> acc
               | None => acc
               end) ∅ s' : gmap atom V)) : gmap atom V) !! a = Some B).
        replace (((<[y:=A]>
          (map_fold
             (fun w A acc =>
               match lvar_to_atom ∅ w with
               | Some y => <[y:=A]> acc
               | None => acc
               end) ∅ s' : gmap atom V)) : gmap atom V) !! a)
          with ((map_fold
             (fun w A acc =>
               match lvar_to_atom ∅ w with
               | Some y => <[y:=A]> acc
               | None => acc
               end) ∅ s' : gmap atom V) !! a).
        -- apply IH. exact Hlookup.
        -- symmetry. apply map_lookup_insert_ne. congruence.
Qed.

Lemma lvar_store_to_atom_store_lookup (s : LVarStore) x :
  lvar_store_to_atom_store s !! x = (s : gmap logic_var V) !! LVFree x.
Proof.
  destruct (lvar_store_to_atom_store s !! x) as [v|] eqn:Hatom.
  - apply lvar_store_to_atom_store_lookup_some in Hatom.
    symmetry. exact Hatom.
  - destruct ((s : gmap logic_var V) !! LVFree x) as [v|] eqn:Hlv;
      [|reflexivity].
    pose proof (lvar_store_to_atom_store_lookup_free_some s x v Hlv) as Hatom'.
    rewrite Hatom in Hatom'. discriminate.
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
