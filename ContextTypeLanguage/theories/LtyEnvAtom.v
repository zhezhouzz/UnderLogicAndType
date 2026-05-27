(** * ContextTypeLanguage.LtyEnvAtom

    Atom-environment lifting, lvar swapping, and atom-env interaction laws. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnvOpen.

Lemma atom_env_to_lty_env_dom Σ :
  dom (atom_env_to_lty_env Σ) = lvars_of_atoms (dom Σ).
Proof.
  unfold atom_env_to_lty_env, lvars_of_atoms.
  apply storeA_map_key_dom.
  intros x y H. inversion H. reflexivity.
Qed.

Lemma atom_env_to_lty_env_insert x T Σ :
  atom_env_to_lty_env (<[x := T]> Σ) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
  unfold atom_env_to_lty_env.
  apply storeA_map_key_insert.
  intros a b H. inversion H. reflexivity.
Qed.

Lemma atom_env_to_lty_env_closed Σ :
  lty_env_closed (atom_env_to_lty_env Σ).
Proof.
  unfold lty_env_closed.
  rewrite !atom_env_to_lty_env_dom.
  apply lvars_bv_of_atoms.
Qed.

Lemma atom_env_to_lty_env_atom_dom Σ :
  lty_env_atom_dom (atom_env_to_lty_env Σ) = dom Σ.
Proof.
  unfold lty_env_atom_dom.
  rewrite atom_env_to_lty_env_dom.
  apply lvars_fv_of_atoms.
Qed.

Lemma atom_env_to_lty_env_lookup_bound_none Σ k :
  atom_env_to_lty_env Σ !! LVBound k = None.
Proof.
  change (((atom_env_to_lty_env Σ : lty_env) : gmap logic_var ty) !!
    LVBound k = None).
  apply not_elem_of_dom.
  rewrite atom_env_to_lty_env_dom.
  unfold lvars_of_atoms.
  intros Hin. apply elem_of_map in Hin as [x [Hbad _]].
  discriminate.
Qed.

Lemma atom_env_to_lty_env_lookup_free_none Δ x :
  x ∉ dom Δ ->
  atom_env_to_lty_env Δ !! LVFree x = None.
Proof.
  intros Hfresh.
  change (((atom_env_to_lty_env Δ : lty_env) : gmap logic_var ty) !!
    LVFree x = None).
  apply not_elem_of_dom.
  rewrite atom_env_to_lty_env_dom.
  unfold lvars_of_atoms.
  intros Hin. apply elem_of_map in Hin as [y [Hy HyD]].
  inversion Hy. subst y. exact (Hfresh HyD).
Qed.

Lemma atom_env_to_lty_env_lookup_free Δ x :
  atom_env_to_lty_env Δ !! LVFree x = Δ !! x.
Proof.
  unfold atom_env_to_lty_env.
  change ((storeA_map_key LVFree Δ : gmap logic_var ty) !! LVFree x =
    (Δ : gmap atom ty) !! x).
  apply storeA_map_key_lookup.
  intros a b H. inversion H. reflexivity.
Qed.

Lemma lty_env_shift_atom_env Σ :
  lty_env_shift (atom_env_to_lty_env Σ) = atom_env_to_lty_env Σ.
Proof.
  apply storeA_map_eq. intros v.
  destruct v as [k|x].
  - transitivity (@None ty).
    + change (((lty_env_shift (atom_env_to_lty_env Σ) : lty_env)
          : gmap logic_var ty) !! LVBound k = None).
      apply not_elem_of_dom.
      unfold lty_env_shift, lty_env_shift_from.
      change (LVBound k ∉
        dom (storeA_rekey (logic_var_shift_from 0) (atom_env_to_lty_env Σ)
          : gmap logic_var ty)).
      rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
      intros Hin. apply elem_of_map in Hin as [u [Hu HuD]].
      destruct u as [n|y]; cbn [logic_var_shift_from] in Hu.
      * exfalso.
        apply elem_of_dom in HuD as [T HT].
        rewrite atom_env_to_lty_env_lookup_bound_none in HT. discriminate.
      * inversion Hu.
    + symmetry. apply atom_env_to_lty_env_lookup_bound_none.
  - unfold lty_env_shift, lty_env_shift_from.
    unfold storeA_rekey.
    change ((kmap (M2:=gmap logic_var) (logic_var_shift_from 0)
        (atom_env_to_lty_env Σ)) !! LVFree x =
      atom_env_to_lty_env Σ !! LVFree x).
    change (LVFree x) with (logic_var_shift_from 0 (LVFree x)) at 1.
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj 0)
      (logic_var_shift_from 0) (atom_env_to_lty_env Σ) (LVFree x)).
    reflexivity.
Qed.

Lemma logic_var_swap_inj x y :
  Inj (=) (=) (logic_var_swap x y).
Proof.
  intros v1 v2 Heq.
  rewrite <- (logic_var_swap_involutive x y v1).
  rewrite <- (logic_var_swap_involutive x y v2).
  by rewrite Heq.
Qed.

Lemma logic_var_swap_match x y v :
  match v with
  | LVFree z => LVFree (atom_swap x y z)
  | LVBound k => LVBound k
  end = logic_var_swap x y v.
Proof.
  destruct v as [k|z].
  - rewrite logic_var_swap_unfold.
    unfold eq_swap. repeat destruct decide; congruence.
  - rewrite logic_var_swap_unfold, logic_var_free_eq_swap.
    reflexivity.
Qed.

Lemma lty_env_swap_lookup x y Σ v :
  lty_env_swap x y Σ !! (match v with
                         | LVFree z => LVFree (atom_swap x y z)
                         | LVBound k => LVBound k
                         end) = Σ !! v.
Proof.
  rewrite logic_var_swap_match.
  unfold lty_env_swap.
  unfold storeA_rekey.
  change ((kmap (M2:=gmap logic_var) (logic_var_swap x y) Σ) !!
      logic_var_swap x y v = (Σ : gmap logic_var ty) !! v).
  rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (Inj0:=logic_var_swap_inj x y)
    (logic_var_swap x y) Σ v).
  reflexivity.
Qed.

Lemma lty_env_swap_lookup_inv x y Σ v :
  lty_env_swap x y Σ !! v =
  Σ !! (match v with
        | LVFree z => LVFree (atom_swap x y z)
        | LVBound k => LVBound k
        end).
Proof.
  rewrite logic_var_swap_match.
  rewrite <- (logic_var_swap_involutive x y v) at 1.
  rewrite <- logic_var_swap_match.
  apply lty_env_swap_lookup.
Qed.

Lemma lty_env_swap_dom x y Σ :
  dom (lty_env_swap x y Σ) = lvars_swap x y (dom Σ).
Proof.
  unfold lty_env_swap, lvars_swap.
  change (dom (storeA_rekey (logic_var_swap x y) Σ : gmap logic_var ty) =
    gset_swap (LVFree x) (LVFree y) (dom (Σ : gmap logic_var ty))).
  rewrite storeA_rekey_dom by apply logic_var_swap_inj.
  unfold gset_swap.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]]. exists u. split; [|exact Hu].
    rewrite logic_var_swap_unfold. reflexivity.
  - intros [u [-> Hu]]. exists u. split; [|exact Hu].
    rewrite <- logic_var_swap_unfold. reflexivity.
Qed.

Lemma lty_env_swap_insert x y Σ v T :
  lty_env_swap x y (<[v := T]> Σ) =
  <[match v with
     | LVFree z => LVFree (atom_swap x y z)
     | LVBound k => LVBound k
     end := T]> (lty_env_swap x y Σ).
Proof.
  rewrite logic_var_swap_match.
  unfold lty_env_swap.
  apply storeA_rekey_insert, logic_var_swap_inj.
Qed.

Lemma lty_env_swap_atom_dom x y Σ :
  lty_env_atom_dom (lty_env_swap x y Σ) =
  aset_swap x y (lty_env_atom_dom Σ).
Proof.
  apply set_eq. intros z.
  unfold lty_env_atom_dom.
  rewrite elem_of_aset_swap, !lvars_fv_elem.
  split.
  - intros Hz.
    change (LVFree z ∈ dom ((lty_env_swap x y Σ : lty_env)
      : gmap logic_var ty)) in Hz.
    apply elem_of_dom in Hz as [T Hz].
    rewrite lty_env_swap_lookup_inv in Hz.
    change (LVFree (atom_swap x y z) ∈ dom (Σ : gmap logic_var ty)).
    apply elem_of_dom. exists T. exact Hz.
  - intros Hz.
    change (LVFree (atom_swap x y z) ∈ dom (Σ : gmap logic_var ty)) in Hz.
    apply elem_of_dom in Hz as [T Hlookup].
    change (LVFree z ∈ dom ((lty_env_swap x y Σ : lty_env)
      : gmap logic_var ty)).
    apply elem_of_dom. exists T.
    rewrite lty_env_swap_lookup_inv.
    exact Hlookup.
Qed.

Lemma lty_env_atom_dom_lookup_free Σ x T :
  Σ !! LVFree x = Some T ->
  x ∈ lty_env_atom_dom Σ.
Proof.
  intros Hlookup.
  unfold lty_env_atom_dom.
  apply lvars_fv_elem.
  change (LVFree x ∈ dom (Σ : gmap logic_var ty)).
  apply elem_of_dom. eexists. exact Hlookup.
Qed.

Lemma lty_env_swap_fresh x y Σ :
  x ∉ lty_env_atom_dom Σ ->
  y ∉ lty_env_atom_dom Σ ->
  lty_env_swap x y Σ = Σ.
Proof.
  intros Hx Hy.
  apply storeA_map_eq. intros v.
  rewrite lty_env_swap_lookup_inv.
  destruct v as [k|z]; cbn.
  - reflexivity.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite atom_swap_l.
      destruct (Σ !! LVFree y) eqn:Hlooky.
      * exfalso. apply Hy. eapply lty_env_atom_dom_lookup_free. exact Hlooky.
      * destruct (Σ !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. eapply lty_env_atom_dom_lookup_free. exact Hlookx.
        -- symmetry. exact Hlookx.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite atom_swap_r.
        destruct (Σ !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. eapply lty_env_atom_dom_lookup_free. exact Hlookx.
        -- destruct (Σ !! LVFree y) eqn:Hlooky.
           ++ exfalso. apply Hy. eapply lty_env_atom_dom_lookup_free. exact Hlooky.
           ++ symmetry. exact Hlooky.
      * rewrite atom_swap_fresh by congruence. reflexivity.
Qed.

Lemma lty_env_swap_atom_env_fresh Δ x y :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  lty_env_swap x y (atom_env_to_lty_env Δ) = atom_env_to_lty_env Δ.
Proof.
  intros Hx Hy.
  apply storeA_map_eq. intros v.
  rewrite lty_env_swap_lookup_inv.
  destruct v as [k|z]; cbn.
  - rewrite !atom_env_to_lty_env_lookup_bound_none. reflexivity.
  - destruct (decide (z = x)) as [->|Hzx].
    + rewrite atom_swap_l.
      rewrite !atom_env_to_lty_env_lookup_free_none by assumption.
      reflexivity.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite atom_swap_r.
        rewrite !atom_env_to_lty_env_lookup_free_none by assumption.
        reflexivity.
      * rewrite atom_swap_fresh by congruence. reflexivity.
Qed.

Lemma lty_env_swap_atom_env_insert_fresh Δ x y T :
  x ∉ dom Δ ->
  y ∉ dom Δ ->
  x <> y ->
  lty_env_swap y x (atom_env_to_lty_env (<[y := T]> Δ)) =
  <[LVFree x := T]> (atom_env_to_lty_env Δ).
Proof.
  intros Hx Hy Hxy.
  rewrite atom_env_to_lty_env_insert.
  rewrite lty_env_swap_insert.
  cbn.
  rewrite atom_swap_l.
  rewrite lty_env_swap_atom_env_fresh by assumption.
  reflexivity.
Qed.

Lemma lty_env_open_atom_env η Σ :
  lty_env_open η (atom_env_to_lty_env Σ) = Σ.
Proof.
  refine (fin_maps.map_fold_ind (M:=gmap atom)
    (fun Σ => lty_env_open η (atom_env_to_lty_env Σ) = Σ) _ _ Σ).
  - unfold lty_env_open, atom_env_to_lty_env, storeA_map_key.
    rewrite kmap_empty. reflexivity.
  - intros x T Σ' Hfresh Hfold IH.
    rewrite atom_env_to_lty_env_insert.
    unfold lty_env_open at 1.
    rewrite (map_fold_insert_L
      (M:=gmap logic_var)
      (fun v U acc =>
        match lvar_to_atom η v with
        | Some y => <[y:=U]> acc
        | None => acc
        end)
      (∅ : gmap atom ty) (LVFree x) T (atom_env_to_lty_env Σ')).
    + change (map_fold
        (fun v U acc =>
          match lvar_to_atom η v with
          | Some y => <[y:=U]> acc
          | None => acc
          end) ∅ (atom_env_to_lty_env Σ'))
        with (lty_env_open η (atom_env_to_lty_env Σ')).
      cbn [lvar_to_atom logic_var_to_atom].
      rewrite IH. reflexivity.
    + intros i j Ti Tj acc Hne Hi Hj.
      destruct i as [ki|xi], j as [kj|xj]; cbn [lvar_to_atom logic_var_to_atom] in *;
        try reflexivity.
      * rewrite lookup_insert_ne in Hi by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hi by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hj by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj. discriminate.
      * apply insert_insert_ne. congruence.
    + apply atom_env_to_lty_env_lookup_free_none.
      apply not_elem_of_dom. exact Hfresh.
Qed.

Lemma lty_env_to_atom_env_atom_env Σ :
  lty_env_to_atom_env (atom_env_to_lty_env Σ) = Σ.
Proof.
  unfold lty_env_to_atom_env.
  apply lty_env_open_atom_env.
Qed.

Lemma lty_env_to_atom_env_lookup_some Σ x T :
  lty_env_to_atom_env Σ !! x = Some T ->
  Σ !! LVFree x = Some T.
Proof.
  unfold lty_env_to_atom_env, lty_env_open.
  refine (fin_maps.map_fold_ind (M:=gmap logic_var)
    (fun Σ => forall x T,
      map_fold
        (fun v U acc =>
          match lvar_to_atom ∅ v with
          | Some y => <[y:=U]> acc
          | None => acc
          end) ∅ Σ !! x = Some T ->
      Σ !! LVFree x = Some T) _ _ Σ x T).
  - intros a U Hlookup.
    rewrite (map_fold_empty (K:=logic_var) (M:=gmap logic_var)) in Hlookup.
    rewrite lookup_empty in Hlookup. discriminate.
  - intros v U Σ' Hfresh Hfold IH a T0.
    rewrite Hfold.
    destruct v as [k|y]; cbn [lvar_to_atom logic_var_to_atom].
    + intros Hlookup.
      change ((<[LVBound k := U]> (Σ' : gmap logic_var ty) :
        gmap logic_var ty) !! LVFree a = Some T0).
      rewrite (lookup_insert_ne (M:=gmap logic_var)) by discriminate.
      apply IH. exact Hlookup.
    + intros Hlookup.
      apply (proj1 (lookup_insert_Some (M:=gmap atom)
        (map_fold
           (fun v U acc =>
             match lvar_to_atom ∅ v with
             | Some y => <[y:=U]> acc
             | None => acc
             end) ∅ Σ') y a U T0)) in Hlookup.
      destruct Hlookup as [[-> ->]|[Hya Hlookup]].
      * change ((<[LVFree a := T0]> (Σ' : gmap logic_var ty) :
          gmap logic_var ty) !! LVFree a = Some T0).
        rewrite lookup_insert_eq. reflexivity.
      * change ((<[LVFree y := U]> (Σ' : gmap logic_var ty) :
          gmap logic_var ty) !! LVFree a = Some T0).
        rewrite (lookup_insert_ne (M:=gmap logic_var)) by congruence.
        apply IH. exact Hlookup.
Qed.

Lemma lty_env_to_atom_env_lookup_free_some Σ x T :
  (Σ : gmap logic_var ty) !! LVFree x = Some T ->
  lty_env_to_atom_env Σ !! x = Some T.
Proof.
  unfold lty_env_to_atom_env, lty_env_open.
  refine (fin_maps.map_fold_ind (M:=gmap logic_var)
    (fun Σ => forall x T,
      (Σ : gmap logic_var ty) !! LVFree x = Some T ->
      map_fold
        (fun v U acc =>
          match lvar_to_atom ∅ v with
          | Some y => <[y:=U]> acc
          | None => acc
          end) ∅ Σ !! x = Some T) _ _ Σ x T).
  - intros a U Hlookup.
    rewrite lookup_empty in Hlookup. discriminate.
  - intros v U Σ' Hfresh Hfold IH a T0 Hlookup.
    destruct v as [k|y]; cbn [lvar_to_atom logic_var_to_atom].
    + rewrite Hfold.
      change ((<[LVBound k := U]> (Σ' : gmap logic_var ty) :
        gmap logic_var ty) !! LVFree a = Some T0) in Hlookup.
      rewrite (lookup_insert_ne (M:=gmap logic_var)) in Hlookup by discriminate.
      apply IH. exact Hlookup.
    + rewrite Hfold.
      change ((<[LVFree y := U]> (Σ' : gmap logic_var ty) :
        gmap logic_var ty) !! LVFree a = Some T0) in Hlookup.
      destruct (decide (y = a)) as [->|Hya].
      * rewrite (lookup_insert_eq (M:=gmap logic_var)) in Hlookup.
        inversion Hlookup. subst U.
        cbn [lvar_to_atom logic_var_to_atom].
        change (((<[a:=T0]>
          (map_fold
             (fun v U acc =>
               match lvar_to_atom ∅ v with
               | Some y => <[y:=U]> acc
               | None => acc
               end) ∅ Σ' : gmap atom ty)) : gmap atom ty) !! a = Some T0).
        exact (lookup_insert_eq
          (M:=gmap atom)
          (map_fold
             (fun v U acc =>
               match lvar_to_atom ∅ v with
               | Some y => <[y:=U]> acc
               | None => acc
               end) ∅ Σ' : gmap atom ty) a T0).
      * rewrite (lookup_insert_ne (M:=gmap logic_var)) in Hlookup by congruence.
        cbn [lvar_to_atom logic_var_to_atom].
        change (((<[y:=U]>
          (map_fold
             (fun v U acc =>
               match lvar_to_atom ∅ v with
               | Some y => <[y:=U]> acc
               | None => acc
               end) ∅ Σ' : gmap atom ty)) : gmap atom ty) !! a = Some T0).
        replace (((<[y:=U]>
          (map_fold
             (fun v U acc =>
               match lvar_to_atom ∅ v with
               | Some y => <[y:=U]> acc
               | None => acc
               end) ∅ Σ' : gmap atom ty)) : gmap atom ty) !! a)
          with ((map_fold
             (fun v U acc =>
               match lvar_to_atom ∅ v with
               | Some y => <[y:=U]> acc
               | None => acc
               end) ∅ Σ' : gmap atom ty) !! a).
        -- apply IH. exact Hlookup.
        -- symmetry. apply lookup_insert_ne. congruence.
Qed.

Lemma lty_env_to_atom_env_lookup Σ x :
  lty_env_to_atom_env Σ !! x = (Σ : gmap logic_var ty) !! LVFree x.
Proof.
  destruct (lty_env_to_atom_env Σ !! x) as [T|] eqn:Hatom.
  - apply lty_env_to_atom_env_lookup_some in Hatom. symmetry. exact Hatom.
  - destruct ((Σ : gmap logic_var ty) !! LVFree x) as [T|] eqn:Hlv;
      [|reflexivity].
    pose proof (lty_env_to_atom_env_lookup_free_some Σ x T Hlv) as Hatom'.
    rewrite Hatom in Hatom'. discriminate.
Qed.

Lemma lty_env_to_atom_env_insert_free Σ x T :
  lty_env_to_atom_env (<[LVFree x := T]> Σ) =
  <[x := T]> (lty_env_to_atom_env Σ).
Proof.
  apply map_eq. intros y.
  rewrite lty_env_to_atom_env_lookup.
  destruct (decide (y = x)) as [->|Hyx].
  - change ((((<[LVFree x := T]> (Σ : gmap logic_var ty))
        : gmap logic_var ty) !! LVFree x) =
      (((<[x := T]> (lty_env_to_atom_env Σ)) : gmap atom ty) !! x)).
    rewrite (lookup_insert_eq (M:=gmap logic_var)).
    change (Some T =
      (((<[x := T]> (lty_env_to_atom_env Σ)) : gmap atom ty) !! x)).
    symmetry.
    exact (lookup_insert_eq (M:=gmap atom) (lty_env_to_atom_env Σ) x T).
  - rewrite (lookup_insert_ne (M:=gmap logic_var) (Σ : gmap logic_var ty) (LVFree x) (LVFree y) T)
      by congruence.
    change ((Σ : gmap logic_var ty) !! LVFree y =
      (((<[x := T]> (lty_env_to_atom_env Σ)) : gmap atom ty) !! y)).
    transitivity (lty_env_to_atom_env Σ !! y).
    + symmetry. apply lty_env_to_atom_env_lookup.
    + symmetry.
      apply lookup_insert_ne. congruence.
Qed.

Lemma lty_env_to_atom_env_swap x y Σ :
  lty_env_to_atom_env (lty_env_swap x y Σ) =
  store_swap x y (lty_env_to_atom_env Σ).
Proof.
  apply map_eq. intros z.
  rewrite lty_env_to_atom_env_lookup.
  rewrite store_swap_lookup_inv.
  rewrite lty_env_to_atom_env_lookup.
  rewrite lty_env_swap_lookup_inv.
  reflexivity.
Qed.

Lemma lty_env_to_atom_env_dom_subset Σ :
  dom (lty_env_to_atom_env Σ) ⊆ lty_env_atom_dom Σ.
Proof.
  intros x Hx.
  apply elem_of_dom in Hx as [T HT].
  apply lty_env_to_atom_env_lookup_some in HT.
  unfold lty_env_atom_dom.
  apply lvars_fv_elem.
  eapply storeA_elem_of_dom_lookup_some. exact HT.
Qed.

Lemma lty_env_open_one_atom_env k x Σ :
  x ∉ dom Σ ->
  lty_env_open_one k x (atom_env_to_lty_env Σ) =
  atom_env_to_lty_env Σ.
Proof.
  intros Hx.
  apply lty_env_open_one_fresh_noop.
  - intros Hin.
    change (LVBound k ∈ dom ((atom_env_to_lty_env Σ : lty_env)
      : gmap logic_var ty)) in Hin.
    apply elem_of_dom in Hin as [T HT].
    rewrite atom_env_to_lty_env_lookup_bound_none in HT. discriminate.
  - intros Hin.
    change (LVFree x ∈ dom ((atom_env_to_lty_env Σ : lty_env)
      : gmap logic_var ty)) in Hin.
    apply elem_of_dom in Hin as [T HT].
    rewrite atom_env_to_lty_env_lookup_free_none in HT by exact Hx.
    discriminate.
Qed.

Lemma lty_env_open_one_bind_atom_env x T Σ :
  x ∉ dom Σ ->
  lty_env_open_one 0 x (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
  intros Hx.
  rewrite lty_env_shift_atom_env.
  rewrite lty_env_open_one_insert.
  replace (logic_var_open 0 x (LVBound 0)) with (LVFree x).
  rewrite lty_env_open_one_atom_env by exact Hx.
  reflexivity.
  rewrite logic_var_open_unfold.
  unfold eq_swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma lvars_shift_from_of_atoms k X :
  lvars_shift_from k (lvars_of_atoms X) = lvars_of_atoms X.
Proof.
  apply lvars_shift_from_below_id.
  intros n Hn. rewrite lvars_bv_of_atoms in Hn. set_solver.
Qed.

Lemma lty_env_bind_atom_env_dom T Σ :
  dom (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  lvars_shift_from 0 (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]}.
Proof.
  rewrite lty_env_shift_atom_env.
  change (dom ((<[LVBound 0 := T]> (atom_env_to_lty_env Σ) : lty_env)
      : gmap logic_var ty) =
    lvars_shift_from 0 (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]}).
  transitivity ({[LVBound 0]} ∪
    dom ((atom_env_to_lty_env Σ : lty_env) : gmap logic_var ty)).
  { rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
      (((atom_env_to_lty_env Σ : lty_env) : gmap logic_var ty))
      (LVBound 0) T).
    reflexivity. }
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_shift_from_of_atoms.
  set_solver.
Qed.
