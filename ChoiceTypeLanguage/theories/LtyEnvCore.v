(** * ChoiceTypeLanguage.LtyEnvCore

    Core operations and basic rekey laws for lvar-keyed type environments. *)

From LocallyNameless Require Import Classes.
From ChoiceTypeLanguage Require Export TypeOpen.

Definition lty_env : Type := @StoreA ty logic_var _ _.

Definition lty_env_shift_from (k : nat) (Σ : lty_env) : lty_env :=
  storeA_rekey (logic_var_shift_from k) Σ.

Definition lty_env_shift (Σ : lty_env) : lty_env :=
  lty_env_shift_from 0 Σ.

Definition lty_env_open_one (k : nat) (x : atom) (Σ : lty_env) : lty_env :=
  storeA_rekey (logic_var_open k x) Σ.

Definition lty_env_closed (Σ : lty_env) : Prop :=
  lvars_bv (dom Σ) = ∅.

Definition atom_env_to_lty_env (Σ : gmap atom ty) : lty_env :=
  storeA_map_key LVFree Σ.

Definition lvar_to_atom (η : gmap nat atom) (v : logic_var) : option atom :=
  logic_var_to_atom η v.

(** [lty_env_open] interprets an lvar-keyed type environment back as an
    atom-keyed one.  Free lvars project to their atoms, bound lvars project
    through [η], and unassigned bound lvars are discarded.  This is a partial
    projection, not a same-key rekeying operation. *)
Definition lty_env_open (η : gmap nat atom) (Σ : lty_env) : gmap atom ty :=
  map_fold (fun v T acc =>
    match lvar_to_atom η v with
    | Some x => <[x := T]> acc
    | None => acc
    end) ∅ Σ.

Definition lty_env_open_lvars (η : gmap nat atom) (Σ : lty_env) : lty_env :=
  storeA_rekey (logic_var_open_env η) Σ.

Definition lty_env_atom_dom (Σ : lty_env) : aset :=
  lvars_fv (dom Σ).

Definition lty_env_bvar_scope (Σ : lty_env) : lvset :=
  lvars_of_bvars (lvars_bv (dom Σ)).

Definition typed_lty_env_bind (Σ : lty_env) (T : ty) : lty_env :=
  <[LVBound 0 := T]> (lty_env_shift Σ).

Definition lty_env_agree_on_lvars
    (D : lvset) (Σ1 Σ2 : lty_env) : Prop :=
  storeA_agree_on D Σ1 Σ2.

Definition lty_env_swap (x y : atom) (Σ : lty_env) : lty_env :=
  storeA_rekey (logic_var_swap x y) Σ.

#[global] Instance open_lty_env_atom_inst : Open atom lty_env :=
  lty_env_open_one.

#[global] Instance mopen_lty_env_inst :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lty_env_open.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.

Lemma lty_env_agree_on_lvars_mono D E Σ1 Σ2 :
  D ⊆ E ->
  lty_env_agree_on_lvars E Σ1 Σ2 ->
  lty_env_agree_on_lvars D Σ1 Σ2.
Proof.
  apply storeA_agree_on_mono.
Qed.

Lemma lty_env_agree_on_lvars_refl D Σ :
  lty_env_agree_on_lvars D Σ Σ.
Proof.
  apply storeA_agree_on_refl.
Qed.

Lemma lty_env_agree_on_lvars_sym D Σ1 Σ2 :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars D Σ2 Σ1.
Proof.
  apply storeA_agree_on_sym.
Qed.

Lemma lty_env_agree_on_lvars_union D1 D2 Σ1 Σ2 :
  lty_env_agree_on_lvars D1 Σ1 Σ2 ->
  lty_env_agree_on_lvars D2 Σ1 Σ2 ->
  lty_env_agree_on_lvars (D1 ∪ D2) Σ1 Σ2.
Proof.
  apply storeA_agree_on_union.
Qed.

Lemma lty_env_agree_on_lvars_insert_same D Σ1 Σ2 v T :
  lty_env_agree_on_lvars (D ∖ {[v]}) Σ1 Σ2 ->
  lty_env_agree_on_lvars D (<[v := T]> Σ1) (<[v := T]> Σ2).
Proof.
  apply storeA_agree_on_insert_same.
Qed.

Lemma lty_env_agree_on_lvars_insert_same_keep D Σ1 Σ2 v T :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars (D ∪ {[v]})
    (<[v := T]> Σ1) (<[v := T]> Σ2).
Proof.
  apply storeA_agree_on_insert_same_keep.
Qed.

Lemma lty_env_atom_dom_shift_from k Σ :
  lty_env_atom_dom (lty_env_shift_from k Σ) = lty_env_atom_dom Σ.
Proof.
  unfold lty_env_atom_dom, lty_env_shift_from.
  change (lvars_fv (dom (storeA_rekey (logic_var_shift_from k) Σ : gmap logic_var ty)) =
    lvars_fv (dom (Σ : gmap logic_var ty))).
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  apply lvars_shift_from_fv.
Qed.

Lemma lty_env_atom_dom_shift Σ :
  lty_env_atom_dom (lty_env_shift Σ) = lty_env_atom_dom Σ.
Proof.
  apply lty_env_atom_dom_shift_from.
Qed.

Lemma lty_env_agree_on_lvars_shift_from k D Σ1 Σ2 :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars (lvars_shift_from k D)
    (lty_env_shift_from k Σ1) (lty_env_shift_from k Σ2).
Proof.
  intros Hag v Hv.
  unfold lvars_shift_from in Hv.
  apply elem_of_map in Hv as [u [-> Hu]].
  unfold lty_env_shift_from.
  unfold storeA_rekey.
  change ((kmap (M2:=gmap logic_var) (logic_var_shift_from k) Σ1) !!
      logic_var_shift_from k u =
    (kmap (M2:=gmap logic_var) (logic_var_shift_from k) Σ2) !!
      logic_var_shift_from k u).
  rewrite !(lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
    (Inj0:=logic_var_shift_from_inj k) (logic_var_shift_from k) _ u).
  apply Hag, Hu.
Qed.

Lemma lty_env_agree_on_lvars_shift_insert_bound D Σ1 Σ2 T :
  lty_env_agree_on_lvars D Σ1 Σ2 ->
  lty_env_agree_on_lvars (lvars_shift_from 0 D ∪ {[LVBound 0]})
    (<[LVBound 0 := T]> (lty_env_shift Σ1))
    (<[LVBound 0 := T]> (lty_env_shift Σ2)).
Proof.
  intros Hag.
  apply lty_env_agree_on_lvars_insert_same_keep.
  apply lty_env_agree_on_lvars_shift_from. exact Hag.
Qed.

Lemma lty_env_atom_dom_insert_bound Σ k T :
  lty_env_atom_dom (<[LVBound k := T]> Σ) = lty_env_atom_dom Σ.
Proof.
  unfold lty_env_atom_dom.
  rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var) Σ (LVBound k) T).
  rewrite lvars_fv_union, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma lty_env_shift_insert_from k v T Σ :
  lty_env_shift_from k (<[v := T]> Σ) =
  <[logic_var_shift_from k v := T]> (lty_env_shift_from k Σ).
Proof.
  unfold lty_env_shift_from.
  apply storeA_rekey_insert, logic_var_shift_from_inj.
Qed.

Lemma lty_env_shift_insert v T Σ :
  lty_env_shift (<[v := T]> Σ) =
  <[logic_var_shift_from 0 v := T]> (lty_env_shift Σ).
Proof.
  apply lty_env_shift_insert_from.
Qed.

Lemma lty_env_shift_insert_free x T Σ :
  lty_env_shift (<[LVFree x := T]> Σ) =
  <[LVFree x := T]> (lty_env_shift Σ).
Proof.
  apply lty_env_shift_insert.
Qed.

Lemma lty_env_open_lvars_shift_from k η Σ :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_shift_from k η)
    (lty_env_shift_from k Σ) =
  lty_env_shift_from k (lty_env_open_lvars η Σ).
Proof.
  intros Hfresh.
  unfold lty_env_open_lvars, lty_env_shift_from.
  assert (Hfresh_shift :
    open_env_fresh_for_lvars (open_env_shift_from k η)
      (dom (storeA_rekey (logic_var_shift_from k) Σ : gmap logic_var ty))).
  {
    rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
    change (open_env_fresh_for_lvars (open_env_shift_from k η)
      (lvars_shift_from k (dom (Σ : gmap logic_var ty)))).
    apply open_env_shift_from_fresh_for_lvars. exact Hfresh.
  }
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_open_env (open_env_shift_from k η))
    (logic_var_shift_from k) Σ).
  2:{ intros a b _ _ Hab. eapply logic_var_shift_from_inj. exact Hab. }
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh_shift. }
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_shift_from k)
    (logic_var_open_env η) Σ).
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
  2:{ intros a b _ _ Hab. eapply logic_var_shift_from_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_env_shift_from.
Qed.

Lemma logic_var_open_inj_fresh k x v1 v2 :
  logic_var_open k x v1 = logic_var_open k x v2 ->
  v1 = v2.
Proof.
  intros H.
  rewrite <- (logic_var_open_involutive k x v1).
  rewrite <- (logic_var_open_involutive k x v2).
  by rewrite H.
Qed.

Lemma logic_var_open_inj_on k x (D : lvset) :
  Inj (=) (=) (logic_var_open k x).
Proof.
  intros v1 v2 H. apply logic_var_open_inj_fresh with (k:=k) (x:=x).
  exact H.
Qed.

Lemma lty_env_shift_free_notin_from k x Σ :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (lty_env_shift_from k Σ).
Proof.
  intros Hfresh.
  unfold lty_env_shift_from.
  change (LVFree x ∉ dom (storeA_rekey (logic_var_shift_from k) Σ : gmap logic_var ty)).
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  intros Hin. apply elem_of_map in Hin as [v [Hv HvD]].
  destruct v as [n|y]; cbn [logic_var_shift_from] in Hv.
  - destruct (decide (k <= n)); discriminate.
  - inversion Hv. subst y. exact (Hfresh HvD).
Qed.

Lemma lty_env_shift_free_notin x Σ :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (lty_env_shift Σ).
Proof.
  apply lty_env_shift_free_notin_from.
Qed.

Lemma lty_env_shift_insert_free_notin x v T Σ :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (lty_env_shift (<[v := T]> Σ)) ->
  x ∉ lty_env_atom_dom Σ.
Proof.
  intros Hfresh _ Hx.
  unfold lty_env_atom_dom in Hx.
  apply Hfresh. apply lvars_fv_elem. exact Hx.
Qed.
