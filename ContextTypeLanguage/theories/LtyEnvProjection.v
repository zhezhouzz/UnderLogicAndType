(** * ContextTypeLanguage.LtyEnvProjection

    Projection from lvar-keyed type environments to atom-keyed environments. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnvAtom.

Lemma map_fold_ext_on_lookup
    {K A B : Type} `{Countable K}
    (f g : K -> A -> B -> B) (b : B) (m : gmap K A) :
  (forall i x, m !! i = Some x -> forall acc, f i x acc = g i x acc) ->
  map_fold f b m = map_fold g b m.
Proof.
  intros Hext.
  rewrite !map_fold_foldr.
  assert (Haux : forall l,
    (forall i x, (i, x) ∈ l -> m !! i = Some x) ->
    foldr (uncurry f) b l = foldr (uncurry g) b l).
  {
    induction l as [|[i x] l IH]; intros Hl; simpl; [reflexivity|].
    rewrite Hext by (apply Hl; left; reflexivity).
    f_equal. apply IH. intros j y Hjy.
    apply Hl. right. exact Hjy.
  }
  apply Haux. intros i x Hin.
  rewrite <- elem_of_map_to_list. exact Hin.
Qed.

Lemma lvar_to_atom_insert_open_env_fresh η k x v :
  η !! k = None ->
  open_env_avoids_atom x η ->
  v <> LVBound k ->
  v <> LVFree x ->
  lvar_to_atom (<[k := x]> η) v = lvar_to_atom η v.
Proof.
  intros Hη Havoid Hbound Hfree.
  destruct v as [n|y]; cbn [lvar_to_atom logic_var_to_atom].
  - rewrite lookup_insert_ne by congruence. reflexivity.
  - reflexivity.
Qed.

Lemma lty_env_open_env_insert_fresh k x η Σ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  Σ !! LVBound k = None ->
  Σ !! LVFree x = None ->
  lty_env_open (<[k := x]> η) Σ = lty_env_open η Σ.
Proof.
  intros Hη Havoid Hbound Hfree.
  change ((Σ : gmap logic_var ty) !! LVBound k = None) in Hbound.
  change ((Σ : gmap logic_var ty) !! LVFree x = None) in Hfree.
  unfold lty_env_open.
  apply map_fold_ext_on_lookup. intros v U Hv acc.
  erewrite lvar_to_atom_insert_open_env_fresh; try reflexivity; eauto.
  - intros ->.
    change ((Σ : gmap logic_var ty) !! LVBound k = Some U) in Hv.
    rewrite Hbound in Hv. discriminate.
  - intros ->.
    change ((Σ : gmap logic_var ty) !! LVFree x = Some U) in Hv.
    rewrite Hfree in Hv. discriminate.
Qed.

Lemma lty_env_open_insert_bound_commute
    (k : nat) (x : atom) (T : ty) (η : gmap nat atom)
    (Σ : lty_env) (j : logic_var) (U : ty) (acc : gmap atom ty) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  Σ !! LVFree x = None ->
  j <> LVBound k ->
  (<[LVBound k := T]> Σ) !! j = Some U ->
  <[x := T]>
    (match lvar_to_atom (<[k := x]> η) j with
     | Some y => <[y := U]> acc
     | None => acc
     end) =
  match lvar_to_atom (<[k := x]> η) j with
  | Some y => <[y := U]> (<[x := T]> acc)
  | None => <[x := T]> acc
  end.
Proof.
  intros Hη Havoid Hfree Hj Hlookup.
  change ((<[LVBound k:=T]> (Σ : gmap logic_var ty)) !! j = Some U) in Hlookup.
  change ((Σ : gmap logic_var ty) !! LVFree x = None) in Hfree.
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

Lemma lvar_to_atom_open_env_free η v x :
  lvar_to_atom η v = Some x ->
  logic_var_open_env η v = LVFree x.
Proof.
  destruct v as [k|y]; cbn [lvar_to_atom logic_var_to_atom logic_var_open_env].
  - intros ->. reflexivity.
  - intros H. inversion H. reflexivity.
Qed.

Lemma lvar_to_atom_inj_on_fresh η D v1 v2 x :
  open_env_fresh_for_lvars η D ->
  v1 ∈ D ->
  v2 ∈ D ->
  lvar_to_atom η v1 = Some x ->
  lvar_to_atom η v2 = Some x ->
  v1 = v2.
Proof.
  intros Hfresh Hv1 Hv2 Hx1 Hx2.
  pose proof (open_env_fresh_for_lvars_inj_on η D Hfresh) as Hinj.
  eapply Hinj; try eassumption.
  rewrite (lvar_to_atom_open_env_free η v1 x Hx1).
  rewrite (lvar_to_atom_open_env_free η v2 x Hx2).
  reflexivity.
Qed.

Lemma lty_env_open_step_commute
    (η : gmap nat atom) (i j : logic_var)
    (Ti Tj : ty) (acc : gmap atom ty) :
  i <> j ->
  (forall x,
    lvar_to_atom η i = Some x ->
    lvar_to_atom η j = Some x ->
    i = j) ->
  match lvar_to_atom η i with
  | Some x => <[x:=Ti]>
      (match lvar_to_atom η j with
       | Some y => <[y:=Tj]> acc
       | None => acc
       end)
  | None =>
      match lvar_to_atom η j with
      | Some y => <[y:=Tj]> acc
      | None => acc
      end
  end =
  match lvar_to_atom η j with
  | Some y => <[y:=Tj]>
      (match lvar_to_atom η i with
       | Some x => <[x:=Ti]> acc
       | None => acc
       end)
  | None =>
      match lvar_to_atom η i with
      | Some x => <[x:=Ti]> acc
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

Lemma lty_env_open_insert_bound_atom_env k x T η Σ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η)
    (dom (<[LVBound k := T]> Σ : lty_env)) ->
  Σ !! LVBound k = None ->
  Σ !! LVFree x = None ->
  lty_env_open (<[k := x]> η) (<[LVBound k := T]> Σ) =
  <[x := T]> (lty_env_open η Σ).
Proof.
  intros Hη Havoid Hfresh Hbound Hfree.
  unfold lty_env_open, lvar_store_open, storeA_filter_map_key at 1.
  rewrite (map_fold_insert_L
    (fun v U acc =>
      match lvar_to_atom (<[k:=x]> η) v with
      | Some y => <[y:=U]> acc
      | None => acc
      end)
    (∅ : gmap atom ty) (LVBound k) T Σ).
  - cbn [lvar_to_atom logic_var_to_atom].
    rewrite lookup_insert_eq.
    change (map_fold
      (fun v U acc =>
        match lvar_to_atom (<[k:=x]> η) v with
        | Some y => <[y:=U]> acc
        | None => acc
        end) ∅ Σ)
      with (lty_env_open (<[k:=x]> η) Σ).
    rewrite lty_env_open_env_insert_fresh by assumption.
    reflexivity.
  - intros j1 j2 U1 U2 acc Hne Hj1 Hj2.
    change ((<[LVBound k:=T]> (Σ : gmap logic_var ty)) !! j1 = Some U1) in Hj1.
    change ((<[LVBound k:=T]> (Σ : gmap logic_var ty)) !! j2 = Some U2) in Hj2.
    destruct (decide (j1 = LVBound k)) as [->|Hj1k].
    + cbn [lvar_to_atom logic_var_to_atom]. rewrite lookup_insert_eq.
      rewrite lookup_insert_eq in Hj1.
      injection Hj1 as HU1. symmetry in HU1. subst U1.
      eapply (lty_env_open_insert_bound_commute k x T η Σ j2 U2 acc);
        try assumption; congruence.
    + destruct (decide (j2 = LVBound k)) as [->|Hj2k].
      * cbn [lvar_to_atom logic_var_to_atom]. rewrite lookup_insert_eq.
        rewrite lookup_insert_eq in Hj2.
        injection Hj2 as HU2. symmetry in HU2. subst U2.
        symmetry.
        eapply (lty_env_open_insert_bound_commute k x T η Σ j1 U1 acc);
          try assumption; congruence.
      * eapply lty_env_open_step_commute; [exact Hne|].
        intros y Hy1 Hy2.
        eapply lvar_to_atom_inj_on_fresh; try eassumption.
        -- change (j1 ∈ dom (<[LVBound k:=T]> (Σ : gmap logic_var ty))).
           apply elem_of_dom. exists U1. exact Hj1.
        -- change (j2 ∈ dom (<[LVBound k:=T]> (Σ : gmap logic_var ty))).
           apply elem_of_dom. exists U2. exact Hj2.
  - change ((Σ : gmap logic_var ty) !! LVBound k = None) in Hbound.
    exact Hbound.
Qed.
