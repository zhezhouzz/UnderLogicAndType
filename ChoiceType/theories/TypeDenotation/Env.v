(** * ChoiceType.TypeDenotation.Env

    Logic-variable type environments and environment-opening helpers for
    choice-type denotations. *)

From LocallyNameless Require Import Tactics.
From ChoiceType Require Export TypeDenotation.FormulaEquiv.
From ChoiceType Require Import QualifierProps.

Definition lty_env : Type := gmap logic_var ty.

Definition lty_env_shift (Σ : lty_env) : lty_env :=
  kmap logic_var_shift Σ.

Definition lty_env_open_one (k : nat) (x : atom) (Σ : lty_env) : lty_env :=
  map_fold (fun v T acc => <[logic_var_open k x v := T]> acc) ∅ Σ.

Definition lty_env_closed (Σ : lty_env) : Prop :=
  lvars_bv (dom Σ) = ∅.

Definition atom_env_to_lty_env (Σ : gmap atom ty) : lty_env :=
  map_fold (fun x T acc => <[LVFree x := T]> acc) ∅ Σ.

Definition lvar_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  match v with
  | LVFree x => Some x
  | LVBound k => η !! k
  end.

Definition lty_env_open (η : gmap nat atom) (Σ : lty_env) : gmap atom ty :=
  map_fold (fun v T acc =>
    match lvar_to_atom η v with
    | Some x => <[x := T]> acc
    | None => acc
    end) ∅ Σ.

Definition open_cty_env (η : gmap nat atom) (τ : choice_ty) : choice_ty :=
  map_fold (fun k x acc => cty_open k x acc) τ η.

#[global] Instance mopen_choice_ty_inst :
  MOpen (gmap nat atom) choice_ty choice_ty := open_cty_env.

#[global] Instance open_lty_env_atom_inst : Open atom lty_env :=
  lty_env_open_one.

#[global] Instance mopen_lty_env_inst :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lty_env_open.

Lemma open_cty_env_empty τ :
  open_cty_env ∅ τ = τ.
Proof. unfold open_cty_env. rewrite map_fold_empty. reflexivity. Qed.

Definition lty_env_atom_dom (Σ : lty_env) : aset :=
  lvars_fv (dom Σ).

Definition lty_env_bvar_scope (Σ : lty_env) : lvset :=
  lvars_of_bvars (lvars_bv (dom Σ)).

Definition lty_env_agree_on_lvars
    (D : lvset) (Σ1 Σ2 : lty_env) : Prop :=
  ∀ v, v ∈ D → Σ1 !! v = Σ2 !! v.

Lemma lty_env_agree_on_lvars_mono D E Σ1 Σ2 :
  D ⊆ E →
  lty_env_agree_on_lvars E Σ1 Σ2 →
  lty_env_agree_on_lvars D Σ1 Σ2.
Proof. intros HDE Hagree v Hv. apply Hagree. exact (HDE v Hv). Qed.

Lemma lty_env_agree_on_lvars_refl D Σ :
  lty_env_agree_on_lvars D Σ Σ.
Proof. intros v Hv. reflexivity. Qed.

Lemma lty_env_agree_on_lvars_sym D Σ1 Σ2 :
  lty_env_agree_on_lvars D Σ1 Σ2 →
  lty_env_agree_on_lvars D Σ2 Σ1.
Proof. intros Hagree v Hv. symmetry. apply Hagree. exact Hv. Qed.

Lemma lty_env_agree_on_lvars_union D1 D2 Σ1 Σ2 :
  lty_env_agree_on_lvars D1 Σ1 Σ2 →
  lty_env_agree_on_lvars D2 Σ1 Σ2 →
  lty_env_agree_on_lvars (D1 ∪ D2) Σ1 Σ2.
Proof.
  intros H1 H2 v Hv.
  apply elem_of_union in Hv as [Hv|Hv]; [apply H1 | apply H2]; exact Hv.
Qed.

Lemma lty_env_agree_on_lvars_insert_same D Σ1 Σ2 v T :
  lty_env_agree_on_lvars (D ∖ {[v]}) Σ1 Σ2 →
  lty_env_agree_on_lvars D (<[v := T]> Σ1) (<[v := T]> Σ2).
Proof.
  intros Hagree w Hw.
  destruct (decide (w = v)) as [->|Hne].
  - change ((<[v := T]> Σ1 : lty_env) !! v =
            (<[v := T]> Σ2 : lty_env) !! v).
    rewrite !(lookup_insert_eq Σ1 v T).
    rewrite !(lookup_insert_eq Σ2 v T).
    reflexivity.
  - change ((<[v := T]> Σ1 : lty_env) !! w =
            (<[v := T]> Σ2 : lty_env) !! w).
    rewrite !(lookup_insert_ne Σ1 v w T) by congruence.
    rewrite !(lookup_insert_ne Σ2 v w T) by congruence.
    apply Hagree. set_solver.
Qed.

Lemma lty_env_agree_on_lvars_insert_same_keep D Σ1 Σ2 v T :
  lty_env_agree_on_lvars D Σ1 Σ2 →
  lty_env_agree_on_lvars (D ∪ {[v]})
    (<[v := T]> Σ1) (<[v := T]> Σ2).
Proof.
  intros Hagree.
  apply lty_env_agree_on_lvars_insert_same.
  intros w Hw. apply Hagree. set_solver.
Qed.

Lemma lty_env_atom_dom_shift Σ :
  lty_env_atom_dom (lty_env_shift Σ) = lty_env_atom_dom Σ.
Proof.
  unfold lty_env_atom_dom, lty_env_shift.
  change (lvars_fv (dom (kmap logic_var_shift Σ : gmap logic_var ty)) =
    lvars_fv (dom Σ)).
  rewrite (dom_kmap_L (Inj0:=logic_var_shift_inj) logic_var_shift Σ).
  change (lvars_fv (lvars_shift (dom Σ)) = lvars_fv (dom Σ)).
  apply lvars_fv_shift.
Qed.

Lemma lty_env_agree_on_lvars_shift D Σ1 Σ2 :
  lty_env_agree_on_lvars D Σ1 Σ2 →
  lty_env_agree_on_lvars (set_map logic_var_shift D)
    (lty_env_shift Σ1) (lty_env_shift Σ2).
Proof.
  intros Hagree v Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  unfold lty_env_shift.
  transitivity (Σ1 !! u).
  - eapply lookup_kmap. apply logic_var_shift_inj.
  - transitivity (Σ2 !! u).
    + apply Hagree. exact Hu.
    + symmetry. eapply lookup_kmap. apply logic_var_shift_inj.
Qed.

Lemma lty_env_agree_on_lvars_shift_insert_bound D Σ1 Σ2 T :
  lty_env_agree_on_lvars D Σ1 Σ2 →
  lty_env_agree_on_lvars
    (set_map logic_var_shift D ∪ {[LVBound 0]})
    (<[LVBound 0 := T]> (lty_env_shift Σ1))
    (<[LVBound 0 := T]> (lty_env_shift Σ2)).
Proof.
  intros Hagree.
  apply lty_env_agree_on_lvars_insert_same_keep.
  apply lty_env_agree_on_lvars_shift.
  exact Hagree.
Qed.

Lemma lty_env_atom_dom_insert_bound Σ k T :
  lty_env_atom_dom (<[LVBound k := T]> Σ) = lty_env_atom_dom Σ.
Proof.
  unfold lty_env_atom_dom.
  rewrite (dom_insert_L (M:=gmap logic_var) (A:=ty) Σ (LVBound k) T).
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma lty_env_shift_insert v T Σ :
  lty_env_shift (<[v := T]> Σ) =
  <[logic_var_shift v := T]> (lty_env_shift Σ).
Proof.
  unfold lty_env_shift.
  rewrite (kmap_insert (M1:=gmap logic_var) (M2:=gmap logic_var)
    logic_var_shift (Inj0:=logic_var_shift_inj) (A:=ty) Σ v T).
  reflexivity.
Qed.

Lemma logic_var_open_inj_fresh k x v1 v2 :
  v1 ≠ LVFree x →
  v2 ≠ LVFree x →
  logic_var_open k x v1 = logic_var_open k x v2 →
  v1 = v2.
Proof.
  intros Hx1 Hx2 Hop.
  destruct v1 as [i|y], v2 as [j|z]; cbn [logic_var_open] in Hop.
  - repeat destruct decide; subst; try reflexivity; congruence.
  - destruct decide; subst; [congruence |].
    inversion Hop; reflexivity.
  - destruct decide; subst; [congruence |].
    inversion Hop; reflexivity.
  - inversion Hop; reflexivity.
Qed.

Lemma logic_var_open_inj_on k x (D : lvset) :
  LVFree x ∉ D →
  ∀ v1 v2 : logic_var,
    v1 ∈ D →
    v2 ∈ D →
    logic_var_open k x v1 = logic_var_open k x v2 →
    v1 = v2.
Proof.
  intros Hfresh v1 v2 Hv1 Hv2 Hop.
  eapply logic_var_open_inj_fresh; eauto; set_solver.
Qed.

Lemma lty_env_shift_free_notin x Σ :
  LVFree x ∉ dom Σ →
  LVFree x ∉ dom (lty_env_shift Σ).
Proof.
  intros Hfresh.
  unfold lty_env_shift in *.
  change (LVFree x ∉ dom (kmap logic_var_shift Σ : gmap logic_var ty)).
  rewrite (dom_kmap_L (Inj0:=logic_var_shift_inj) logic_var_shift Σ).
  intros Hx.
  apply elem_of_map in Hx as [v [Hv Hvin]].
  destruct v as [k|y]; cbn [logic_var_shift] in Hv; inversion Hv; subst.
  apply Hfresh. exact Hvin.
Qed.

Lemma lty_env_shift_insert_free_notin x v T Σ :
  LVFree x ∉ dom (<[v := T]> Σ) →
  LVFree x ∉ dom (<[logic_var_shift v := T]> (lty_env_shift Σ)).
Proof.
  intros Hfresh Hbad.
  change (LVFree x ∈ dom (<[logic_var_shift v := T]> (lty_env_shift Σ))) in Hbad.
  pose proof (dom_insert_L (M:=gmap logic_var) (A:=ty)
    (lty_env_shift Σ) (logic_var_shift v) T) as Hdom_shift.
  setoid_rewrite Hdom_shift in Hbad.
  apply elem_of_union in Hbad as [Hbad|Hbad].
  - apply elem_of_singleton in Hbad.
    destruct v as [j|y]; cbn [logic_var_shift] in Hbad; inversion Hbad; subst.
    apply Hfresh.
    apply elem_of_dom. exists T.
    apply lookup_insert_eq.
  - assert (Htail : LVFree x ∉ dom Σ).
    {
      intros Htail.
      apply Hfresh.
      apply elem_of_dom in Htail as [Tx Htail].
      destruct (decide (v = LVFree x)) as [->|Hne].
      - apply elem_of_dom. exists T.
        apply lookup_insert_eq.
      - apply elem_of_dom. exists Tx.
        change ((<[v := T]> Σ : lty_env) !! LVFree x = Some Tx).
        rewrite (lookup_insert_ne Σ v (LVFree x) T) by congruence.
        exact Htail.
    }
    apply lty_env_shift_free_notin in Htail.
    contradiction.
Qed.

Lemma lty_env_open_one_dom k x Σ :
  dom (lty_env_open_one k x Σ) = lvars_open k x (dom Σ).
Proof.
  unfold lty_env_open_one.
  refine (fin_maps.map_fold_ind
    (fun Σ => dom (map_fold
      (fun (v : logic_var) (T : ty) (acc : lty_env) =>
        <[logic_var_open k x v := T]> acc) ∅ Σ) =
      lvars_open k x (dom Σ)) _ _ Σ).
  - rewrite map_fold_empty, dom_empty_L.
    unfold lvars_open. rewrite set_map_empty. reflexivity.
  - intros v T Σ' Hfresh Hfold IH.
    rewrite Hfold.
    rewrite (dom_insert_L
      (map_fold
        (fun (v0 : logic_var) (T0 : ty) (acc : lty_env) =>
          <[logic_var_open k x v0 := T0]> acc) ∅ Σ')
      (logic_var_open k x v) T).
    replace (dom (map_fold
        (fun (v0 : logic_var) (T0 : ty) (acc : lty_env) =>
          <[logic_var_open k x v0 := T0]> acc) ∅ Σ'))
      with (lvars_open k x (dom Σ')) by (symmetry; exact IH).
    rewrite (dom_insert_L Σ' v T).
    unfold lvars_open.
    rewrite set_map_union_L, set_map_singleton_L.
    reflexivity.
Qed.

Lemma logic_var_bv_elem_singleton v k :
  k ∈ logic_var_bv v →
  v = LVBound k.
Proof.
  destruct v as [j|y]; cbn [logic_var_bv].
  - intros Hk. apply elem_of_singleton in Hk. subst. reflexivity.
  - set_solver.
Qed.

Lemma logic_var_open_no_bv k x v :
  k ∉ logic_var_bv v →
  logic_var_open k x v = v.
Proof.
  destruct v as [j|y]; cbn [logic_var_bv logic_var_open].
  - intros Hnot.
    destruct (decide (j = k)) as [->|Hjk]; [set_solver | reflexivity].
  - reflexivity.
Qed.

Lemma lty_env_open_one_no_bv k x Σ :
  k ∉ lvars_bv (dom Σ) →
  lty_env_open_one k x Σ = Σ.
Proof.
  induction Σ as [|v T Σ Hlookup IH] using map_ind.
  - intros _. reflexivity.
  - intros Hno.
    unfold lty_env_open_one at 1.
    rewrite (map_fold_insert_L
      (fun v U acc => <[logic_var_open k x v := U]> acc)
      (∅ : lty_env) v T Σ).
    + rewrite logic_var_open_no_bv.
      2:{
        intros Hkv. apply Hno. apply lvars_bv_elem.
        pose proof (logic_var_bv_elem_singleton _ _ Hkv) as ->.
        set_solver.
      }
      change (map_fold
        (fun v U acc => <[logic_var_open k x v := U]> acc) ∅ Σ)
        with (lty_env_open_one k x Σ).
      rewrite IH.
      * reflexivity.
      * intros HkΣ. apply Hno.
        apply lvars_bv_elem.
        apply lvars_bv_elem in HkΣ. set_solver.
    + intros i j Ti Tj acc Hne Hi Hj.
      assert (Hi_open : logic_var_open k x i = i).
      {
        apply logic_var_open_no_bv. intros Hki.
        apply Hno. apply lvars_bv_elem.
        pose proof (logic_var_bv_elem_singleton _ _ Hki) as ->.
        apply elem_of_dom_2 in Hi. exact Hi.
      }
      assert (Hj_open : logic_var_open k x j = j).
      {
        apply logic_var_open_no_bv. intros Hkj.
        apply Hno. apply lvars_bv_elem.
        pose proof (logic_var_bv_elem_singleton _ _ Hkj) as ->.
        apply elem_of_dom_2 in Hj. exact Hj.
      }
      rewrite Hi_open, Hj_open.
      apply insert_insert_ne. exact Hne.
    + exact Hlookup.
Qed.

Lemma lty_env_open_one_same_index_absorb k x y Σ :
  lty_env_open_one k y (lty_env_open_one k x Σ) =
  lty_env_open_one k x Σ.
Proof.
  apply lty_env_open_one_no_bv.
  rewrite lty_env_open_one_dom, lvars_bv_open.
  set_solver.
Qed.

Lemma lty_env_open_one_insert_fresh k x v T Σ :
  Σ !! v = None →
  LVFree x ∉ dom (<[v := T]> Σ) →
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof.
  intros Hlookup Hfresh.
  unfold lty_env_open_one.
  refine (map_fold_insert_L
    (fun (v : logic_var) (T : ty) (acc : lty_env) =>
      <[logic_var_open k x v := T]> acc)
    (∅ : lty_env) v T Σ _ Hlookup).
  intros v1 v2 T1 T2 acc Hne Hlookup1 Hlookup2.
  assert (Hv1fresh : v1 ≠ LVFree x).
  { intros ->. apply Hfresh. apply elem_of_dom_2 in Hlookup1. exact Hlookup1. }
  assert (Hv2fresh : v2 ≠ LVFree x).
  { intros ->. apply Hfresh. apply elem_of_dom_2 in Hlookup2. exact Hlookup2. }
  assert (Hopen_ne : logic_var_open k x v1 ≠ logic_var_open k x v2).
  {
    intros Heq. apply Hne.
    eapply logic_var_open_inj_fresh; eauto.
  }
  apply map_eq. intros w.
  destruct (decide (w = logic_var_open k x v1)) as [->|Hw1].
  - change ((<[logic_var_open k x v1 := T1]>
      (<[logic_var_open k x v2 := T2]> acc) : lty_env) !!
      logic_var_open k x v1 =
      (<[logic_var_open k x v2 := T2]>
        (<[logic_var_open k x v1 := T1]> acc) : lty_env) !!
      logic_var_open k x v1).
    rewrite (lookup_insert_eq
      (<[logic_var_open k x v2 := T2]> acc)
      (logic_var_open k x v1) T1).
    rewrite (lookup_insert_ne
      (<[logic_var_open k x v1 := T1]> acc)
      (logic_var_open k x v2) (logic_var_open k x v1) T2) by congruence.
    rewrite (lookup_insert_eq acc (logic_var_open k x v1) T1).
    reflexivity.
  - destruct (decide (w = logic_var_open k x v2)) as [->|Hw2].
    + change ((<[logic_var_open k x v1 := T1]>
        (<[logic_var_open k x v2 := T2]> acc) : lty_env) !!
        logic_var_open k x v2 =
        (<[logic_var_open k x v2 := T2]>
          (<[logic_var_open k x v1 := T1]> acc) : lty_env) !!
        logic_var_open k x v2).
      rewrite (lookup_insert_ne
        (<[logic_var_open k x v2 := T2]> acc)
        (logic_var_open k x v1) (logic_var_open k x v2) T1) by congruence.
      rewrite (lookup_insert_eq acc (logic_var_open k x v2) T2).
      rewrite (lookup_insert_eq
        (<[logic_var_open k x v1 := T1]> acc)
        (logic_var_open k x v2) T2).
      reflexivity.
    + change ((<[logic_var_open k x v1 := T1]>
        (<[logic_var_open k x v2 := T2]> acc) : lty_env) !! w =
        (<[logic_var_open k x v2 := T2]>
          (<[logic_var_open k x v1 := T1]> acc) : lty_env) !! w).
      rewrite (lookup_insert_ne
        (<[logic_var_open k x v2 := T2]> acc)
        (logic_var_open k x v1) w T1) by congruence.
      rewrite (lookup_insert_ne acc
        (logic_var_open k x v2) w T2) by congruence.
      rewrite (lookup_insert_ne
        (<[logic_var_open k x v1 := T1]> acc)
        (logic_var_open k x v2) w T2) by congruence.
      rewrite (lookup_insert_ne acc
        (logic_var_open k x v1) w T1) by congruence.
      reflexivity.
Qed.

Lemma lty_env_open_one_shift k x Σ :
  LVFree x ∉ dom Σ →
  lty_env_open_one (S k) x (lty_env_shift Σ) =
  lty_env_shift (lty_env_open_one k x Σ).
Proof.
  induction Σ as [|v T Σ Hlookup IH] using map_ind.
  - intros _. unfold lty_env_open_one, lty_env_shift.
    replace (kmap logic_var_shift (∅ : lty_env)) with (∅ : lty_env)
      by (symmetry; apply kmap_empty).
    change (map_fold
      (fun (v : logic_var) (T : ty) (acc : lty_env) =>
        <[logic_var_open (S k) x v := T]> acc) (∅ : lty_env) (∅ : lty_env))
      with (∅ : lty_env).
    change (map_fold
      (fun (v : logic_var) (T : ty) (acc : lty_env) =>
        <[logic_var_open k x v := T]> acc) (∅ : lty_env) (∅ : lty_env))
      with (∅ : lty_env).
    symmetry. apply kmap_empty.
  - intros Hfresh.
    rewrite !lty_env_shift_insert.
    rewrite lty_env_open_one_insert_fresh.
    2:{
      unfold lty_env_shift.
      eapply not_elem_of_dom.
      intros Hbad.
      rewrite (dom_kmap_L (Inj0:=logic_var_shift_inj) logic_var_shift Σ) in Hbad.
      apply elem_of_map in Hbad as [u [Hu HuΣ]].
      apply logic_var_shift_inj in Hu. subst u.
      apply not_elem_of_dom in Hlookup. contradiction.
    }
    2:{
      apply lty_env_shift_insert_free_notin.
      exact Hfresh.
    }
    rewrite lty_env_open_one_insert_fresh by (try exact Hlookup; set_solver).
    rewrite IH by set_solver.
    rewrite lty_env_shift_insert.
    rewrite logic_var_shift_open.
    reflexivity.
Qed.

Lemma lvars_open_shift_dom k x Σ :
  lvars_open (S k) x (lvars_shift (dom Σ)) =
  lvars_shift (dom (lty_env_open_one k x Σ)).
Proof.
  rewrite lty_env_open_one_dom.
  rewrite <- lvars_shift_open.
  reflexivity.
Qed.

Lemma lty_env_open_one_shift_insert_bound k x T Σ :
  LVFree x ∉ dom Σ →
  lty_env_open_one (S k) x (<[LVBound 0 := T]> (lty_env_shift Σ)) =
  <[LVBound 0 := T]> (lty_env_shift (lty_env_open_one k x Σ)).
Proof.
  intros Hfresh.
  rewrite lty_env_open_one_insert_fresh.
  2:{
    unfold lty_env_shift.
    change ((kmap logic_var_shift Σ : lty_env) !! LVBound 0 = None).
    eapply not_elem_of_dom.
    rewrite (dom_kmap_L (Inj0:=logic_var_shift_inj) logic_var_shift Σ).
    intros Hbad.
    apply elem_of_map in Hbad as [v [Hv _]].
    destruct v as [j|y]; cbn [logic_var_shift] in Hv; discriminate.
  }
  2:{
    intros Hbad.
    apply elem_of_dom in Hbad as [Tbad Hbad].
    change ((<[LVBound 0 := T]> (lty_env_shift Σ) : lty_env) !!
      LVFree x = Some Tbad) in Hbad.
    rewrite (lookup_insert_ne (lty_env_shift Σ) (LVBound 0) (LVFree x) T)
      in Hbad by discriminate.
    apply elem_of_dom_2 in Hbad.
    apply lty_env_shift_free_notin in Hfresh.
    contradiction.
  }
  cbn [logic_var_open].
  destruct (decide (0 = S k)) as [Hbad|_]; [lia |].
  rewrite lty_env_open_one_shift by exact Hfresh.
  reflexivity.
Qed.

Lemma lvars_bv_of_bvars (B : gset nat) :
  lvars_bv (lvars_of_bvars B) = B.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem.
  unfold lvars_of_bvars.
  rewrite elem_of_map.
  split.
  - intros [j [Hj HjB]]. inversion Hj. subst. exact HjB.
  - intros Hk. exists k. split; [reflexivity | exact Hk].
Qed.

Lemma lvars_bv_shift D k :
  k ∈ lvars_bv (lvars_shift D) ↔
  ∃ j, k = S j ∧ j ∈ lvars_bv D.
Proof.
  rewrite lvars_bv_elem.
  unfold lvars_shift.
  rewrite elem_of_map.
  split.
  - intros [v [Hv HvD]].
    destruct v as [j|y]; cbn [logic_var_shift] in Hv; inversion Hv; subst.
    exists j. split; [reflexivity |].
    apply lvars_bv_elem. exact HvD.
  - intros [j [-> Hj]].
    exists (LVBound j). split; [reflexivity |].
    apply lvars_bv_elem. exact Hj.
Qed.

Lemma lty_env_bvar_scope_shift_open_noop k x Σ :
  LVBound k ∉ dom Σ →
  lvars_open (S k) x (lty_env_bvar_scope (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
  intros Hfresh.
  apply lvars_open_no_bv.
  unfold lty_env_bvar_scope.
  rewrite lvars_bv_of_bvars.
  change (dom (lty_env_shift Σ)) with
    (dom (kmap logic_var_shift Σ : gmap logic_var ty)).
  rewrite (dom_kmap_L (Inj0:=logic_var_shift_inj) logic_var_shift Σ).
  intros Hin.
  apply lvars_bv_shift in Hin as [j [Hjk Hj]].
  inversion Hjk. subst j.
  apply Hfresh. apply lvars_bv_elem. exact Hj.
Qed.

Lemma lty_env_bvar_scope_shift_open_one_noop k x Σ :
  LVBound k ∉ dom Σ →
  lty_env_bvar_scope (lty_env_shift (lty_env_open_one k x Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof.
  intros Hfresh.
  unfold lty_env_bvar_scope.
  change (dom (lty_env_shift (lty_env_open_one k x Σ))) with
    (dom (kmap logic_var_shift (lty_env_open_one k x Σ) : gmap logic_var ty)).
  change (dom (lty_env_shift Σ)) with
    (dom (kmap logic_var_shift Σ : gmap logic_var ty)).
  rewrite !(dom_kmap_L (Inj0:=logic_var_shift_inj) logic_var_shift).
  rewrite lty_env_open_one_dom.
  rewrite lvars_open_no_bv.
  - reflexivity.
  - intros Hk. apply Hfresh. apply lvars_bv_elem. exact Hk.
Qed.

Lemma lty_env_bvar_scope_open_one_shift_under_result k x Σ D :
  LVBound k ∉ dom Σ →
  lvars_open (S k) x
    (lty_env_bvar_scope (lty_env_shift Σ) ∪ D ∪ {[LVBound 0]}) =
  lty_env_bvar_scope (lty_env_shift (lty_env_open_one k x Σ)) ∪
    lvars_open (S k) x D ∪ {[LVBound 0]}.
Proof.
  intros Hfresh.
  unfold lvars_open at 1.
  rewrite !set_map_union_L, set_map_singleton_L.
  fold (lvars_open (S k) x (lty_env_bvar_scope (lty_env_shift Σ))).
  fold (lvars_open (S k) x D).
  cbn [logic_var_open].
  destruct (decide (0 = S k)) as [Hbad|_]; [lia |].
  rewrite lty_env_bvar_scope_shift_open_noop by exact Hfresh.
  rewrite lty_env_bvar_scope_shift_open_one_noop by exact Hfresh.
  set_solver.
Qed.

Lemma lvars_open_shift_union_bound0 k x D :
  lvars_open (S k) x (lvars_shift D ∪ {[LVBound 0]}) =
  lvars_shift (lvars_open k x D) ∪ {[LVBound 0]}.
Proof.
  unfold lvars_open at 1.
  rewrite set_map_union_L, set_map_singleton_L.
  fold (lvars_open (S k) x (lvars_shift D)).
  rewrite <- lvars_shift_open.
  cbn [logic_var_open].
  destruct (decide (S k = 0)) as [Hbad|_]; [lia |].
  reflexivity.
Qed.

Lemma lvars_open_shift_dom_union_bound0 k x Σ :
  lvars_open (S k) x (lvars_shift (dom Σ) ∪ {[LVBound 0]}) =
  lvars_shift (dom (lty_env_open_one k x Σ)) ∪ {[LVBound 0]}.
Proof.
  rewrite lvars_open_shift_union_bound0.
  rewrite lty_env_open_one_dom.
  reflexivity.
Qed.

Lemma lty_env_atom_dom_open_one k x Σ :
  lty_env_atom_dom (lty_env_open_one k x Σ) =
  lty_env_atom_dom Σ ∪
    (if decide (k ∈ lvars_bv (dom Σ)) then {[x]} else ∅).
Proof.
  unfold lty_env_atom_dom.
  rewrite lty_env_open_one_dom.
  apply lvars_fv_open.
Qed.

Lemma atom_env_to_lty_env_dom Σ :
  dom (atom_env_to_lty_env Σ) = lvars_of_atoms (dom Σ).
Proof.
  unfold atom_env_to_lty_env, lvars_of_atoms.
  refine (fin_maps.map_fold_ind
    (fun Σ => dom (map_fold
        (fun (x : atom) (T : ty) (acc : lty_env) => <[LVFree x := T]> acc)
        (∅ : lty_env) Σ)
      = set_map LVFree (dom Σ)) _ _ Σ).
  - rewrite dom_empty_L. rewrite set_map_empty. reflexivity.
  - intros x T Σ' Hfresh Hfold IH.
    rewrite Hfold.
      replace (dom (map_fold
          (fun (x : atom) (T : ty) (acc : lty_env) => <[LVFree x := T]> acc)
          (∅ : lty_env) Σ'))
        with (set_map (C:=aset) (D:=lvset) LVFree (dom Σ'))
        by exact (eq_sym IH).
      rewrite dom_insert_L.
      rewrite set_map_union_L, set_map_singleton_L.
    set_solver.
Qed.

Lemma lty_env_shift_insert_free x T Σ :
  lty_env_shift (<[LVFree x := T]> Σ) =
  <[LVFree x := T]> (lty_env_shift Σ).
Proof.
  unfold lty_env_shift.
  rewrite (kmap_insert (M1:=gmap logic_var) (M2:=gmap logic_var)
    logic_var_shift (Inj0:=logic_var_shift_inj) (A:=ty) Σ (LVFree x) T).
  reflexivity.
Qed.

Lemma lty_env_shift_atom_env Σ :
  lty_env_shift (atom_env_to_lty_env Σ) = atom_env_to_lty_env Σ.
Proof.
  unfold atom_env_to_lty_env.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      lty_env_shift
        (map_fold
          (fun (x : atom) (T : ty) (acc : lty_env) =>
            <[LVFree x := T]> acc)
          (∅ : lty_env) Σ) =
      map_fold
        (fun (x : atom) (T : ty) (acc : lty_env) =>
          <[LVFree x := T]> acc)
        (∅ : lty_env) Σ) _ _ Σ).
  - unfold lty_env_shift. rewrite map_fold_empty.
    change (kmap logic_var_shift (∅ : gmap logic_var ty) =
      (∅ : gmap logic_var ty)).
    apply kmap_empty.
  - intros x T Σ' Hfresh Hfold IH.
    rewrite Hfold.
    rewrite lty_env_shift_insert_free.
    rewrite IH.
    reflexivity.
Qed.

Lemma lty_env_insert_free_comm i j Ti Tj (Σ : lty_env) :
  i ≠ j →
  <[LVFree i := Ti]> (<[LVFree j := Tj]> Σ) =
  <[LVFree j := Tj]> (<[LVFree i := Ti]> Σ).
Proof.
  intros Hne.
  apply map_eq. intros lv.
  destruct (decide (lv = LVFree i)) as [Hli|Hli];
    destruct (decide (lv = LVFree j)) as [Hlj|Hlj]; subst.
  - congruence.
  - change ((<[LVFree i:=Ti]> (<[LVFree j:=Tj]> Σ) : lty_env) !! LVFree i =
            (<[LVFree j:=Tj]> (<[LVFree i:=Ti]> Σ) : lty_env) !! LVFree i).
    rewrite (lookup_insert_eq (<[LVFree j:=Tj]> Σ : lty_env) (LVFree i) Ti).
    rewrite (lookup_insert_ne (<[LVFree i:=Ti]> Σ : lty_env)
      (LVFree j) (LVFree i) Tj) by congruence.
    rewrite (lookup_insert_eq Σ (LVFree i) Ti).
    reflexivity.
  - change ((<[LVFree i:=Ti]> (<[LVFree j:=Tj]> Σ) : lty_env) !! LVFree j =
            (<[LVFree j:=Tj]> (<[LVFree i:=Ti]> Σ) : lty_env) !! LVFree j).
    rewrite (lookup_insert_ne (<[LVFree j:=Tj]> Σ : lty_env)
      (LVFree i) (LVFree j) Ti) by congruence.
    rewrite (lookup_insert_eq Σ (LVFree j) Tj).
    rewrite (lookup_insert_eq (<[LVFree i:=Ti]> Σ : lty_env) (LVFree j) Tj).
    reflexivity.
  - change ((<[LVFree i:=Ti]> (<[LVFree j:=Tj]> Σ) : lty_env) !! lv =
            (<[LVFree j:=Tj]> (<[LVFree i:=Ti]> Σ) : lty_env) !! lv).
    rewrite (lookup_insert_ne (<[LVFree j:=Tj]> Σ : lty_env)
      (LVFree i) lv Ti) by congruence.
    rewrite (lookup_insert_ne Σ (LVFree j) lv Tj) by congruence.
    rewrite (lookup_insert_ne (<[LVFree i:=Ti]> Σ : lty_env)
      (LVFree j) lv Tj) by congruence.
    rewrite (lookup_insert_ne Σ (LVFree i) lv Ti) by congruence.
    reflexivity.
Qed.

Lemma atom_env_to_lty_env_insert x T Σ :
  x ∉ dom Σ →
  atom_env_to_lty_env (<[x := T]> Σ) =
  <[LVFree x := T]> (atom_env_to_lty_env Σ).
Proof.
  intros Hfresh.
  unfold atom_env_to_lty_env.
  rewrite (map_fold_insert_L
    (fun (x : atom) (T : ty) (acc : lty_env) => <[LVFree x := T]> acc)
    (∅ : lty_env) x T Σ).
  - reflexivity.
  - intros i j Ti Tj acc Hne _ _.
    apply lty_env_insert_free_comm. exact Hne.
  - apply not_elem_of_dom. exact Hfresh.
Qed.

Lemma atom_env_to_lty_env_closed Σ :
  lty_env_closed (atom_env_to_lty_env Σ).
Proof.
  unfold lty_env_closed.
  rewrite atom_env_to_lty_env_dom.
  apply lvars_bv_of_atoms.
Qed.

Lemma atom_env_to_lty_env_atom_dom Σ :
  lty_env_atom_dom (atom_env_to_lty_env Σ) = dom Σ.
Proof.
  unfold lty_env_atom_dom. rewrite atom_env_to_lty_env_dom.
  apply lvars_fv_of_atoms.
Qed.

Lemma atom_env_to_lty_env_lookup_bound_none Σ k :
  atom_env_to_lty_env Σ !! LVBound k = None.
Proof.
  apply not_elem_of_dom.
  rewrite atom_env_to_lty_env_dom.
  intros Hin.
  unfold lvars_of_atoms in Hin.
  rewrite elem_of_map in Hin.
  destruct Hin as [y [Hy _]].
  congruence.
Qed.

Definition lty_env_swap (x y : atom) (Σ : lty_env) : lty_env :=
  kmap (logic_var_swap x y) Σ.

Lemma logic_var_swap_inj x y :
  Inj (=) (=) (logic_var_swap x y).
Proof.
  intros v1 v2 Heq.
  rewrite <- (logic_var_swap_involutive x y v1).
  rewrite <- (logic_var_swap_involutive x y v2).
  by rewrite Heq.
Qed.

Lemma lty_env_swap_lookup x y Σ v :
  lty_env_swap x y Σ !! logic_var_swap x y v = Σ !! v.
Proof.
  unfold lty_env_swap.
  eapply lookup_kmap. apply logic_var_swap_inj.
Qed.

Lemma lty_env_swap_lookup_inv x y Σ v :
  lty_env_swap x y Σ !! v = Σ !! logic_var_swap x y v.
Proof.
  rewrite <- (logic_var_swap_involutive x y v) at 1.
  apply lty_env_swap_lookup.
Qed.

Lemma lty_env_swap_insert x y Σ v T :
  lty_env_swap x y (<[v := T]> Σ) =
  <[logic_var_swap x y v := T]> (lty_env_swap x y Σ).
Proof.
  unfold lty_env_swap.
  rewrite (kmap_insert (M1:=gmap logic_var) (M2:=gmap logic_var)
    (logic_var_swap x y) (Inj0:=logic_var_swap_inj x y)
    (A:=ty) Σ v T).
  reflexivity.
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
    apply elem_of_dom in Hz as [T Hz].
    rewrite lty_env_swap_lookup_inv in Hz.
    apply elem_of_dom. exists T.
    exact Hz.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hlookup].
    apply elem_of_dom. exists T.
    rewrite lty_env_swap_lookup_inv.
    exact Hlookup.
Qed.

Lemma lty_env_swap_fresh x y Σ :
  x ∉ lty_env_atom_dom Σ →
  y ∉ lty_env_atom_dom Σ →
  lty_env_swap x y Σ = Σ.
Proof.
  intros Hx Hy.
  destruct (decide (x = y)) as [->|Hxy].
  {
    apply map_eq. intros v.
    rewrite lty_env_swap_lookup_inv.
    destruct v as [k|z]; cbn [logic_var_swap].
    - reflexivity.
    - unfold atom_swap.
      repeat match goal with
      | H : _ = _ |- _ => subst
      | |- context[decide (?a = ?b)] => destruct (decide (a = b)); subst; try congruence
      end; reflexivity.
  }
  apply map_eq. intros v.
  rewrite lty_env_swap_lookup_inv.
  destruct v as [k|z]; cbn [logic_var_swap].
  - reflexivity.
  - unfold atom_swap.
    destruct (decide (z = x)) as [->|Hzx].
    + destruct (Σ !! LVFree y) eqn:Hlooky.
      * exfalso. apply Hy. unfold lty_env_atom_dom.
        apply lvars_fv_elem. apply elem_of_dom. eexists. exact Hlooky.
      * destruct (Σ !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. unfold lty_env_atom_dom.
           apply lvars_fv_elem. apply elem_of_dom. eexists. exact Hlookx.
        -- symmetry. exact Hlookx.
    + destruct (decide (z = y)) as [->|Hzy].
      * destruct (Σ !! LVFree x) eqn:Hlookx.
        -- exfalso. apply Hx. unfold lty_env_atom_dom.
           apply lvars_fv_elem. apply elem_of_dom. eexists. exact Hlookx.
        -- destruct (Σ !! LVFree y) eqn:Hlooky.
           ++ exfalso. apply Hy. unfold lty_env_atom_dom.
              apply lvars_fv_elem. apply elem_of_dom. eexists. exact Hlooky.
           ++ symmetry. exact Hlooky.
      * reflexivity.
Qed.

Lemma lty_env_swap_insert_fresh_to x y Σ T :
  x ∉ lty_env_atom_dom Σ →
  y ∉ lty_env_atom_dom Σ →
  x <> y →
  lty_env_swap y x (<[LVFree y := T]> Σ) =
  <[LVFree x := T]> Σ.
Proof.
  intros Hx Hy Hxy.
  rewrite lty_env_swap_insert.
  cbn [logic_var_swap].
  unfold atom_swap.
  destruct (decide (y = y)) as [_|Hbad]; [|congruence].
  destruct (decide (y = x)) as [Hyx|_]; [congruence |].
  rewrite lty_env_swap_fresh by assumption.
  reflexivity.
Qed.

Lemma atom_env_to_lty_env_lookup_free_none Δ x :
  x ∉ dom Δ →
  atom_env_to_lty_env Δ !! LVFree x = None.
Proof.
  intros Hx.
  apply not_elem_of_dom.
  rewrite atom_env_to_lty_env_dom.
  intros Hbad. apply Hx.
  rewrite <- lvars_fv_of_atoms.
  apply lvars_fv_elem. exact Hbad.
Qed.

Lemma atom_env_to_lty_env_lookup_free Δ x :
  atom_env_to_lty_env Δ !! LVFree x = Δ !! x.
Proof.
  induction Δ as [|y T Δ Hy IH] using map_ind.
  - unfold atom_env_to_lty_env. rewrite map_fold_empty, lookup_empty.
    reflexivity.
  - rewrite atom_env_to_lty_env_insert by (apply not_elem_of_dom; exact Hy).
    destruct (decide (x = y)) as [->|Hne].
    + change ((<[LVFree y := T]> (atom_env_to_lty_env Δ) : lty_env) !! LVFree y =
        (<[y := T]> Δ : gmap atom ty) !! y).
      rewrite (lookup_insert_eq (atom_env_to_lty_env Δ) (LVFree y) T).
      rewrite (lookup_insert_eq Δ y T).
      reflexivity.
    + change ((<[LVFree y := T]> (atom_env_to_lty_env Δ) : lty_env) !! LVFree x =
        (<[y := T]> Δ : gmap atom ty) !! x).
      rewrite (lookup_insert_ne (atom_env_to_lty_env Δ) (LVFree y) (LVFree x) T)
        by congruence.
      rewrite (lookup_insert_ne Δ y x T) by congruence.
      exact IH.
Qed.

Lemma lty_env_swap_atom_env_fresh Δ x y :
  x ∉ dom Δ →
  y ∉ dom Δ →
  lty_env_swap x y (atom_env_to_lty_env Δ) = atom_env_to_lty_env Δ.
Proof.
  intros Hx Hy.
  apply map_eq. intros v.
  rewrite lty_env_swap_lookup_inv.
  destruct v as [k|z]; cbn [logic_var_swap].
  - rewrite !atom_env_to_lty_env_lookup_bound_none. reflexivity.
  - unfold atom_swap.
    destruct (decide (z = x)) as [->|Hzx].
    + rewrite !atom_env_to_lty_env_lookup_free_none by assumption.
      reflexivity.
    + destruct (decide (z = y)) as [->|Hzy].
      * rewrite !atom_env_to_lty_env_lookup_free_none by assumption.
        reflexivity.
      * reflexivity.
Qed.

Lemma lty_env_swap_atom_env_insert_fresh Δ x y T :
  x ∉ dom Δ →
  y ∉ dom Δ →
  x <> y →
  lty_env_swap y x (atom_env_to_lty_env (<[y := T]> Δ)) =
  <[LVFree x := T]> (atom_env_to_lty_env Δ).
Proof.
  intros Hx Hy Hxy.
  rewrite atom_env_to_lty_env_insert by exact Hy.
  rewrite lty_env_swap_insert.
  cbn [logic_var_swap].
  unfold atom_swap.
  destruct (decide (y = y)) as [_|Hbad]; [|congruence].
  rewrite lty_env_swap_atom_env_fresh by assumption.
  reflexivity.
Qed.

Lemma lty_env_open_atom_env η Σ :
  lty_env_open η (atom_env_to_lty_env Σ) = Σ.
Proof.
  unfold atom_env_to_lty_env.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      lty_env_open η
        (map_fold
          (fun (x : atom) (T : ty) (acc : lty_env) =>
            <[LVFree x := T]> acc) ∅ Σ) = Σ) _ _ Σ).
  - unfold lty_env_open. rewrite map_fold_empty. reflexivity.
  - intros x T Σ' Hfresh Hfold IH.
    rewrite Hfold.
    unfold lty_env_open in *.
    rewrite (map_fold_insert_L
      (M:=gmap logic_var)
      (fun v U acc =>
        match lvar_to_atom η v with
        | Some y => <[y:=U]> acc
        | None => acc
        end)
      (∅ : gmap atom ty) (LVFree x) T
      (map_fold
        (fun (x : atom) (T : ty) (acc : lty_env) =>
          <[LVFree x:=T]> acc) ∅ Σ')).
    + cbn [lvar_to_atom].
      change (map_fold
        (fun v U acc =>
          match lvar_to_atom η v with
          | Some y => <[y:=U]> acc
          | None => acc
          end)
        ∅
        (map_fold
          (fun (x : atom) (T : ty) (acc : lty_env) =>
            <[LVFree x:=T]> acc) ∅ Σ')) with
        (lty_env_open η
          (map_fold
            (fun (x : atom) (T : ty) (acc : lty_env) =>
              <[LVFree x:=T]> acc) ∅ Σ')).
      change (lty_env_open η
          (map_fold
            (fun (x : atom) (T : ty) (acc : lty_env) =>
              <[LVFree x:=T]> acc) ∅ Σ') = Σ') in IH.
      rewrite IH. reflexivity.
    + intros i j Ti Tj acc Hne Hi Hj.
      cbn [lvar_to_atom] in *.
      destruct i as [ki|xi], j as [kj|xj]; cbn [lvar_to_atom] in *;
        try reflexivity.
      * rewrite lookup_insert_ne in Hi by congruence.
        change (map_fold
          (fun (x0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree x0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hi.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hi by congruence.
        change (map_fold
          (fun (x0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree x0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hi.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hj by congruence.
        change (map_fold
          (fun (x0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree x0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hj.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj. discriminate.
      * rewrite <- insert_insert_ne by congruence. reflexivity.
    + change (map_fold
        (fun (x0 : atom) (T0 : ty) (acc : lty_env) =>
          <[LVFree x0:=T0]> acc) ∅ Σ')
        with (atom_env_to_lty_env Σ').
      apply not_elem_of_dom.
      rewrite atom_env_to_lty_env_dom.
      unfold lvars_of_atoms.
      intros Hin.
      rewrite elem_of_map in Hin.
      destruct Hin as [y [Hy HyΣ]].
      inversion Hy. subst.
      apply elem_of_dom in HyΣ as [Ty HTy].
      rewrite Hfresh in HTy. discriminate.
Qed.

Lemma lty_env_open_one_atom_env k x Σ :
  lty_env_open_one k x (atom_env_to_lty_env Σ) = atom_env_to_lty_env Σ.
Proof.
  unfold atom_env_to_lty_env.
  refine (fin_maps.map_fold_ind
    (fun Σ =>
      lty_env_open_one k x
        (map_fold
          (fun (y : atom) (T : ty) (acc : lty_env) =>
            <[LVFree y := T]> acc)
          (∅ : lty_env) Σ) =
      map_fold
        (fun (y : atom) (T : ty) (acc : lty_env) =>
          <[LVFree y := T]> acc)
        (∅ : lty_env) Σ) _ _ Σ).
  - unfold lty_env_open_one. rewrite map_fold_empty. reflexivity.
  - intros y T Σ' Hfresh Hfold IH.
    rewrite Hfold.
    unfold lty_env_open_one at 1.
    rewrite (map_fold_insert_L
      (fun v U acc => <[logic_var_open k x v := U]> acc)
      (∅ : lty_env) (LVFree y) T
      (map_fold
        (fun (y : atom) (T : ty) (acc : lty_env) =>
          <[LVFree y := T]> acc)
        (∅ : lty_env) Σ')).
    + cbn [logic_var_open].
      change (map_fold
        (fun v U acc => <[logic_var_open k x v := U]> acc) ∅
        (map_fold
          (fun (y0 : atom) (T0 : ty) (acc : lty_env) =>
            <[LVFree y0:=T0]> acc) ∅ Σ')) with
        (lty_env_open_one k x
          (map_fold
            (fun (y0 : atom) (T0 : ty) (acc : lty_env) =>
              <[LVFree y0:=T0]> acc) ∅ Σ')).
      rewrite IH. reflexivity.
    + intros i j Ti Tj acc Hne Hi Hj.
      destruct i as [ki|yi], j as [kj|yj]; cbn [logic_var_open] in *;
        try reflexivity.
      * rewrite lookup_insert_ne in Hi by congruence.
        change (map_fold
          (fun (y0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree y0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hi.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hi by congruence.
        change (map_fold
          (fun (y0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree y0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hi.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hj by congruence.
        change (map_fold
          (fun (y0 : atom) (T0 : ty) (acc0 : lty_env) =>
            <[LVFree y0:=T0]> acc0) ∅ Σ')
          with (atom_env_to_lty_env Σ') in Hj.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj. discriminate.
      * apply lty_env_insert_free_comm. congruence.
    + change (map_fold
        (fun (y0 : atom) (T0 : ty) (acc : lty_env) =>
          <[LVFree y0:=T0]> acc) ∅ Σ')
        with (atom_env_to_lty_env Σ').
      apply not_elem_of_dom.
      rewrite atom_env_to_lty_env_dom.
      unfold lvars_of_atoms.
      intros Hin.
      apply elem_of_map in Hin as [z [Hz Hzdom]].
      inversion Hz. subst z.
      apply elem_of_dom in Hzdom as [Uz Hlookup].
      rewrite Hfresh in Hlookup. discriminate.
Qed.

Lemma lty_env_open_one_bind_atom_env x T Σ :
  x ∉ dom Σ →
  lty_env_open_one 0 x
    (<[LVBound 0 := T]> (lty_env_shift (atom_env_to_lty_env Σ))) =
  atom_env_to_lty_env (<[x := T]> Σ).
Proof.
  intros Hx.
  rewrite lty_env_shift_atom_env.
  unfold lty_env_open_one.
  rewrite (map_fold_insert_L
    (fun v U acc => <[logic_var_open 0 x v := U]> acc)
    (∅ : lty_env) (LVBound 0) T (atom_env_to_lty_env Σ)).
  - cbn [logic_var_open].
    destruct (decide (0 = 0)) as [_|Hbad]; [|congruence].
    change (map_fold
      (fun v U acc => <[logic_var_open 0 x v:=U]> acc) ∅
      (atom_env_to_lty_env Σ)) with
      (lty_env_open_one 0 x (atom_env_to_lty_env Σ)).
    rewrite lty_env_open_one_atom_env.
    rewrite atom_env_to_lty_env_insert by exact Hx.
    reflexivity.
  - intros i j Ti Tj acc Hne Hi Hj.
    destruct i as [ki|yi], j as [kj|yj]; cbn [logic_var_open] in *.
    + destruct (decide (ki = 0)) as [->|Hki0];
        destruct (decide (kj = 0)) as [->|Hkj0].
      * congruence.
      * rewrite lookup_insert in Hi.
        rewrite lookup_insert_ne in Hj by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj. discriminate.
      * rewrite lookup_insert_ne in Hi by congruence.
        rewrite lookup_insert in Hj.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
      * rewrite lookup_insert_ne in Hi by congruence.
        rewrite lookup_insert_ne in Hj by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
    + destruct (decide (ki = 0)) as [->|Hki0].
      * rewrite lookup_insert in Hi.
        rewrite lookup_insert_ne in Hj by congruence.
        assert (Hyj : yj ∈ dom Σ).
        {
          apply elem_of_dom_2 in Hj.
          rewrite atom_env_to_lty_env_dom in Hj.
          unfold lvars_of_atoms in Hj.
          apply elem_of_map in Hj as [z [Hz Hzdom]].
          inversion Hz. subst z. exact Hzdom.
        }
        apply lty_env_insert_free_comm. set_solver.
      * rewrite lookup_insert_ne in Hi by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hi. discriminate.
    + destruct (decide (kj = 0)) as [->|Hkj0].
      * rewrite lookup_insert in Hj.
        rewrite lookup_insert_ne in Hi by congruence.
        assert (Hyi : yi ∈ dom Σ).
        {
          apply elem_of_dom_2 in Hi.
          rewrite atom_env_to_lty_env_dom in Hi.
          unfold lvars_of_atoms in Hi.
          apply elem_of_map in Hi as [z [Hz Hzdom]].
          inversion Hz. subst z. exact Hzdom.
        }
        symmetry. apply lty_env_insert_free_comm. set_solver.
      * rewrite lookup_insert_ne in Hj by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj. discriminate.
    + apply lty_env_insert_free_comm. congruence.
  - apply atom_env_to_lty_env_lookup_bound_none.
Qed.

Lemma lty_env_bind_atom_env_dom T Σ :
  dom (<[LVBound 0 := T]> (atom_env_to_lty_env Σ)) =
  lvars_shift (lvars_of_atoms (dom Σ)) ∪ {[LVBound 0]}.
Proof.
  rewrite (dom_insert_L (atom_env_to_lty_env Σ) (LVBound 0) T).
  rewrite atom_env_to_lty_env_dom.
  rewrite lvars_shift_of_atoms.
  set_solver.
Qed.

Lemma lty_env_open_insert_bound_atom_env k x T η Σ :
  x ∉ dom Σ →
  lty_env_open (<[k := x]> η) (<[LVBound k := T]> (atom_env_to_lty_env Σ)) =
  <[x := T]> Σ.
Proof.
  intros Hx.
  unfold lty_env_open.
  set (ηx := <[k:=x]> η).
  set (f := fun (v : logic_var) (U : ty) (acc : gmap atom ty) =>
    match lvar_to_atom ηx v with
    | Some y => <[y:=U]> acc
    | None => acc
    end).
  change (map_fold f ∅ (<[LVBound k:=T]> (atom_env_to_lty_env Σ)) =
    <[x:=T]> Σ).
  rewrite (map_fold_insert_L f ∅ (LVBound k) T (atom_env_to_lty_env Σ)).
  - subst f ηx. cbn [lvar_to_atom].
    rewrite lookup_insert.
    change (map_fold
      (fun v U acc =>
        match lvar_to_atom (<[k:=x]> η) v with
        | Some y => <[y:=U]> acc
        | None => acc
        end)
      ∅ (atom_env_to_lty_env Σ))
      with (lty_env_open (<[k:=x]> η) (atom_env_to_lty_env Σ)).
    rewrite lty_env_open_atom_env.
    destruct (decide (k = k)); [reflexivity | congruence].
  - subst f ηx.
    intros j1 j2 z1 z2 acc Hne Hj1 Hj2.
    cbn [lvar_to_atom].
    destruct j1 as [j1|y1], j2 as [j2|y2]; cbn [lvar_to_atom] in *.
    + destruct (decide (j1 = k)) as [->|Hj1k];
        destruct (decide (j2 = k)) as [->|Hj2k].
      * congruence.
      * rewrite lookup_insert in Hj1.
        rewrite lookup_insert_ne in Hj2 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj2.
        discriminate.
      * rewrite lookup_insert_ne in Hj1 by congruence.
        rewrite lookup_insert in Hj2.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj1.
        discriminate.
      * rewrite lookup_insert_ne in Hj1 by congruence.
        rewrite lookup_insert_ne in Hj2 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj1.
        discriminate.
    + destruct (decide (j1 = k)) as [->|Hj1k].
      * rewrite lookup_insert in Hj1.
        assert (Hy2 : y2 ∈ dom Σ).
        {
          rewrite lookup_insert_ne in Hj2 by congruence.
          apply elem_of_dom_2 in Hj2.
          rewrite atom_env_to_lty_env_dom in Hj2.
          unfold lvars_of_atoms in Hj2.
          rewrite elem_of_map in Hj2.
          destruct Hj2 as [y [Hy Hydom]].
          inversion Hy. subst. exact Hydom.
        }
        rewrite lookup_insert.
        destruct (decide (k = k)) as [_|Hkk]; [| congruence].
        rewrite insert_insert_ne by set_solver. reflexivity.
      * rewrite lookup_insert_ne in Hj1 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj1.
        discriminate.
    + destruct (decide (j2 = k)) as [->|Hj2k].
      * rewrite lookup_insert in Hj2.
        assert (Hy1 : y1 ∈ dom Σ).
        {
          rewrite lookup_insert_ne in Hj1 by congruence.
          apply elem_of_dom_2 in Hj1.
          rewrite atom_env_to_lty_env_dom in Hj1.
          unfold lvars_of_atoms in Hj1.
          rewrite elem_of_map in Hj1.
          destruct Hj1 as [y [Hy Hydom]].
          inversion Hy. subst. exact Hydom.
        }
        rewrite lookup_insert.
        destruct (decide (k = k)) as [_|Hkk]; [| congruence].
        rewrite <- insert_insert_ne by set_solver. reflexivity.
      * rewrite lookup_insert_ne in Hj2 by congruence.
        rewrite atom_env_to_lty_env_lookup_bound_none in Hj2.
        discriminate.
    + rewrite <- insert_insert_ne by congruence. reflexivity.
  - apply atom_env_to_lty_env_lookup_bound_none.
Qed.

Lemma open_cty_env_singleton k x τ :
  open_cty_env (<[k := x]> ∅) τ = cty_open k x τ.
Proof.
  unfold open_cty_env.
  change (<[k := x]> ∅ : gmap nat atom) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.
