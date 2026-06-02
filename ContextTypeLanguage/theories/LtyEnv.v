(** * ContextTypeLanguage.LtyEnv

    Type-language names and laws for ty-valued lvar stores. *)

From LocallyNameless Require Import Classes.
From ContextStore Require Export Store.
From ContextTypeLanguage Require Export TypeOpen.

(** * ContextTypeLanguage.LtyEnv

    Thin TypeLanguage names for [ty]-valued lvar stores.  The operations and
    laws live in [ContextStore]; this file only fixes the value type and
    provides the TypeLanguage instances used by opening notation. *)


Notation lty_env := (gmap logic_var ty) (only parsing).
Local Notation StoreT := (Store (V := value)) (only parsing).

Notation lty_env_shift_from :=
  (@lvar_store_shift_from ty) (only parsing).
Notation lty_env_shift :=
  (@lvar_store_shift ty) (only parsing).
Notation lty_env_open_one :=
  (@lvar_store_open_one ty) (only parsing).
Notation lty_env_closed :=
  (@lvar_store_closed ty) (only parsing).
Notation atom_env_to_lty_env :=
  (@atom_store_to_lvar_store ty) (only parsing).
Notation lty_env_open :=
  (@lvar_store_open ty) (only parsing).
Notation lty_env_to_atom_env :=
  (@lvar_store_to_atom_store ty) (only parsing).
Notation lty_env_open_lvars :=
  (@lvar_store_open_lvars ty) (only parsing).
Notation lty_env_atom_dom :=
  (@lvar_store_atom_dom ty) (only parsing).
Notation lty_env_bvar_scope :=
  (@lvar_store_bvar_scope ty) (only parsing).
Notation lty_env_swap :=
  (@lvar_store_swap ty) (only parsing).

Notation typed_lty_env_bind :=
  (@lvar_store_bind ty) (only parsing).

Definition lty_env_msubst_store (σ : StoreT) (Σ : lty_env) : lty_env :=
  storeA_restrict Σ (dom Σ ∖ lvars_of_atoms (dom (σ : gmap atom value))).

#[global] Instance stale_lty_env : Stale lty_env := lvar_store_atom_dom.
Arguments stale_lty_env /.

#[global] Instance open_lty_env_atom_inst : Open atom lty_env :=
  lvar_store_open_one.

#[global] Instance mopen_lty_env_inst :
  MOpen (gmap nat atom) lty_env (gmap atom ty) := lvar_store_open.

#[global] Instance into_lvars_atom_ty_env : IntoLVars (gmap atom ty) :=
  fun Σ => lvars_of_atoms (dom Σ).

#[global] Instance into_lvars_logic_ty_env : IntoLVars (gmap logic_var ty) :=
  fun Σ => dom Σ.

(** * ContextTypeLanguage.LtyEnv

    Type-language compatibility names for generic lvar-store opening laws. *)


Lemma lty_env_msubst_store_dom σ (Σ : lty_env) :
  dom (lty_env_msubst_store σ Σ) =
  dom Σ ∖ lvars_of_atoms (dom (σ : gmap atom value)).
Proof.
  unfold lty_env_msubst_store.
  rewrite storeA_restrict_dom.
  set_solver.
Qed.

Lemma lty_env_msubst_store_lookup_some σ (Σ : lty_env) v T :
  lty_env_msubst_store σ Σ !! v = Some T ->
  Σ !! v = Some T /\ v ∉ lvars_of_atoms (dom (σ : gmap atom value)).
Proof.
  intros Hlook.
  apply storeA_restrict_lookup_some in Hlook as [Hin HΣ].
  apply elem_of_difference in Hin as [_ Hfresh].
  split; assumption.
Qed.

Lemma lty_env_msubst_store_lookup_some_2 σ (Σ : lty_env) v T :
  Σ !! v = Some T ->
  v ∉ lvars_of_atoms (dom (σ : gmap atom value)) ->
  lty_env_msubst_store σ Σ !! v = Some T.
Proof.
  intros Hlook Hfresh.
  apply storeA_restrict_lookup_some_2.
  - exact Hlook.
  - apply elem_of_difference. split; [by apply elem_of_dom_2 in Hlook|exact Hfresh].
Qed.

Lemma lty_env_msubst_store_shift σ (Σ : lty_env) :
  lty_env_msubst_store σ (lty_env_shift Σ) =
  lty_env_shift (lty_env_msubst_store σ Σ).
Proof.
  unfold lty_env_msubst_store, lty_env_shift, lvar_store_shift,
    lvar_store_shift_from.
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  change (set_map (logic_var_shift_from 0) (dom Σ))
    with (lvars_shift_from 0 (dom Σ)).
  rewrite <- lvars_shift_from_difference_of_atoms.
  unfold lvars_shift_from.
  apply storeA_restrict_rekey.
  apply logic_var_shift_from_inj.
Qed.

Lemma lty_env_msubst_store_insert_bound0_shift σ (Σ : lty_env) T :
  lty_env_msubst_store σ (<[LVBound 0 := T]> (lty_env_shift Σ)) =
  <[LVBound 0 := T]> (lty_env_msubst_store σ (lty_env_shift Σ)).
Proof.
  unfold lty_env_msubst_store.
  rewrite dom_insert_L.
  rewrite storeA_restrict_insert_in.
  - f_equal. apply storeA_map_eq. intros z.
    rewrite !storeA_restrict_lookup.
    destruct (decide (z ∈ ({[LVBound 0]} ∪ dom (lty_env_shift Σ))
      ∖ lvars_of_atoms (dom (σ : gmap atom value)))) as [Hzbig|Hzbig];
      destruct (decide (z ∈ dom (lty_env_shift Σ)
      ∖ lvars_of_atoms (dom (σ : gmap atom value)))) as [Hz|Hz];
      try reflexivity.
    + apply elem_of_difference in Hzbig as [Hzdom Hzfresh].
      apply elem_of_union in Hzdom as [Hz0|Hzdom].
      * rewrite elem_of_singleton in Hz0. subst.
        rewrite lvar_store_shift_lookup_bound0_none. reflexivity.
      * exfalso. apply Hz. apply elem_of_difference. split; assumption.
    + exfalso. apply Hzbig.
      apply elem_of_difference in Hz as [Hzdom Hzfresh].
      apply elem_of_difference. split; [set_solver|exact Hzfresh].
  - apply elem_of_difference. split; [set_solver|].
    unfold lvars_of_atoms. rewrite elem_of_map.
    intros (a & Ha & _). discriminate.
Qed.

Lemma lty_env_msubst_store_typed_bind σ (Σ : lty_env) T :
  lty_env_msubst_store σ (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_msubst_store σ Σ) T.
Proof.
  unfold typed_lty_env_bind, lvar_store_bind.
  rewrite lty_env_msubst_store_insert_bound0_shift.
  rewrite lty_env_msubst_store_shift.
  reflexivity.
Qed.

Lemma lty_env_msubst_store_open_one_fresh k y σ (Σ : lty_env) :
  y ∉ dom (σ : gmap atom value) ->
  lty_env_msubst_store σ (lty_env_open_one k y Σ) =
  lty_env_open_one k y (lty_env_msubst_store σ Σ).
Proof.
  intros Hy.
  unfold lty_env_msubst_store.
  rewrite lvar_store_open_one_dom.
  unfold lty_env_open_one, lvar_store_open_one.
  change (lvars_open k y (dom Σ) ∖ lvars_of_atoms (dom (σ : gmap atom value)))
    with (set_swap (LVBound k) (LVFree y) (dom Σ)
      ∖ lvars_of_atoms (dom (σ : gmap atom value))).
  rewrite <- set_swap_difference_fresh.
  - unfold set_swap.
    rewrite storeA_restrict_rekey by apply swap_inj.
    reflexivity.
  - unfold lvars_of_atoms. rewrite elem_of_map.
    intros (a & Ha & _). discriminate.
  - unfold lvars_of_atoms. rewrite elem_of_map.
    intros (a & Ha & Haσ). inversion Ha. subst. exact (Hy Haσ).
Qed.

Lemma lty_env_open_one_dom k x (Σ : lty_env) :
  dom (lty_env_open_one k x Σ) = lvars_open k x (dom Σ).
Proof. apply lvar_store_open_one_dom. Qed.

Lemma lty_env_open_lvars_empty (Σ : lty_env) :
  lty_env_open_lvars ∅ Σ = Σ.
Proof. apply lvar_store_open_lvars_empty. Qed.

Lemma lty_env_open_lvars_singleton k x (Σ : lty_env) :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars (<[k := x]> ∅) Σ =
  lty_env_open_one k x Σ.
Proof. apply lvar_store_open_lvars_singleton. Qed.

Lemma lty_env_open_lvars_open_one_empty k x (Σ : lty_env) :
  LVFree x ∉ dom Σ ->
  lty_env_open_lvars ∅ (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> ∅) Σ.
Proof. apply lvar_store_open_lvars_open_one_empty. Qed.

Lemma lty_env_open_lvars_dom η (Σ : lty_env) :
  open_env_fresh_for_lvars η (dom Σ) ->
  dom (lty_env_open_lvars η Σ) =
  lvars_open_env η (dom Σ).
Proof. apply lvar_store_open_lvars_dom. Qed.

Lemma lty_env_open_lvars_lookup_fresh η v T (Σ : lty_env) :
  Σ !! v = None ->
  open_env_fresh_for_lvars η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η Σ !! logic_var_open_env η v = None.
Proof. apply lvar_store_open_lvars_lookup_fresh. Qed.

Lemma lty_env_open_lvars_insert_entry η v T (Σ : lty_env) :
  Σ !! v = None ->
  logic_var_open_env_inj_on η (dom (<[v := T]> Σ)) ->
  lty_env_open_lvars η (<[v := T]> Σ) =
  <[logic_var_open_env η v := T]> (lty_env_open_lvars η Σ).
Proof. apply lvar_store_open_lvars_insert_entry. Qed.

Lemma lty_env_open_lvars_insert_fresh η k x (Σ : lty_env) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_fresh_for_lvars (<[k := x]> η) (dom Σ) ->
  lty_env_open_lvars (<[k := x]> η) Σ =
  lty_env_open_one k x (lty_env_open_lvars η Σ).
Proof. apply lvar_store_open_lvars_insert_fresh. Qed.

Lemma lty_env_open_lvars_lift_bound0_singleton η T :
  open_env_values_inj η ->
  lty_env_open_lvars ((kmap S η))
    ((<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lty_env) =
  ((<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lty_env).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite kmap_empty, lty_env_open_lvars_empty. reflexivity.
  - intros Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert.
    rewrite lty_env_open_lvars_insert_fresh.
    + rewrite IH by exact Hinjη.
      rewrite lvar_store_open_one_insert.
      replace (logic_var_open (S k) x (LVBound 0)) with (LVBound 0).
      * replace (lty_env_open_one (S k) x (∅ : lty_env)) with
          ((∅ : gmap logic_var ty) : lty_env); [reflexivity|].
        unfold lty_env_open_one.
        apply (storeA_rekey_empty (V := ty) (K := logic_var)
          (logic_var_open (S k) x)).
      * unfold swap. repeat destruct decide; try lia; try congruence.
    + better_base_solver.
    + better_base_solver.
    + intros i z Hiz Hbad.
      replace (dom (<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lvset)
        with ({[LVBound 0]} : lvset) in Hbad
        by (rewrite dom_insert_L, dom_empty_L; set_solver).
      apply lvars_fv_elem in Hbad.
      unfold lvars_open_env in Hbad.
      apply elem_of_map in Hbad as [v [Hv HvIn]].
      assert (Hv0 : v = LVBound 0) by set_solver.
      subst v.
      cbn [logic_var_open_env] in Hv.
      assert (Hnone :
        delete i (<[S k:=x]> (kmap S η : gmap nat atom)) !! 0 = None).
      {
        destruct (decide (i = 0)) as [->|Hi0].
        - rewrite lookup_delete_eq. reflexivity.
        - rewrite lookup_delete_ne by congruence.
          change ((<[S k:=x]> ((kmap S η)) : gmap nat atom) !! 0 = None).
          destruct (decide (0 = S k)) as [Hbad0|Hneq0]; [lia|].
          rewrite lookup_insert_ne by (intros H; apply Hneq0; symmetry; exact H).
          apply open_env_lift_lookup_zero_none.
      }
      rewrite Hnone in Hv. discriminate.
Qed.

Lemma lty_env_open_lvars_insert_delete_swap_back
    η k y z (Σ : lty_env) :
  η !! k = Some z ->
  y ∉ lvars_fv (dom Σ) ->
  z ∉ lvars_fv (dom Σ) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom Σ) ->
  lty_env_swap y z
    (lty_env_open_lvars (<[k := y]> (delete k η)) Σ) =
  lty_env_open_lvars η Σ.
Proof. apply lvar_store_open_lvars_insert_delete_swap_back. Qed.

Lemma lty_env_open_lvars_open_one η k x (Σ : lty_env) :
  x ∉ lvars_fv (dom Σ) ->
  open_env_fresh_for_lvars η (dom (lty_env_open_one k x Σ)) ->
  lty_env_open_lvars η (lty_env_open_one k x Σ) =
  lty_env_open_lvars (<[k := x]> η) Σ.
Proof. apply lvar_store_open_lvars_open_one. Qed.

Lemma lty_env_open_one_fresh_noop k x (Σ : lty_env) :
  LVBound k ∉ dom Σ ->
  LVFree x ∉ dom Σ ->
  lty_env_open_one k x Σ = Σ.
Proof. apply lvar_store_open_one_fresh_noop. Qed.

Lemma lty_env_open_one_involutive k x (Σ : lty_env) :
  lty_env_open_one k x (lty_env_open_one k x Σ) = Σ.
Proof. apply lvar_store_open_one_involutive. Qed.

Lemma lty_env_open_one_insert k x v T (Σ : lty_env) :
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof. apply lvar_store_open_one_insert. Qed.

Lemma lty_env_open_one_insert_fresh k x v T (Σ : lty_env) :
  logic_var_open k x v ∉ dom (lty_env_open_one k x Σ) ->
  lty_env_open_one k x (<[v := T]> Σ) =
  <[logic_var_open k x v := T]> (lty_env_open_one k x Σ).
Proof. apply lvar_store_open_one_insert_fresh. Qed.

Lemma lty_env_open_one_shift_under_gen j k x (Σ : lty_env) :
  j <= k ->
  lty_env_open_one (S k) x (lty_env_shift_from j Σ) =
  lty_env_shift_from j (lty_env_open_one k x Σ).
Proof. apply lvar_store_open_one_shift_under_gen. Qed.

Lemma lty_env_open_one_shift_under j k x (Σ : lty_env) :
  j <= k ->
  lty_env_open_one (S (S k)) x (lty_env_shift_from (S j) Σ) =
  lty_env_shift_from (S j) (lty_env_open_one (S k) x Σ).
Proof. apply lvar_store_open_one_shift_under. Qed.

Lemma lvars_open_shift_dom_gen j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S k) x (lvars_shift_from j (dom Σ)) =
  lvars_shift_from j (lvars_open k x (dom Σ)).
Proof. apply lvar_store_lvars_open_shift_dom_gen. Qed.

Lemma lvars_open_shift_dom j k x (Σ : lty_env) :
  j <= k ->
  lvars_open (S (S k)) x (lvars_shift_from (S j) (dom Σ)) =
  lvars_shift_from (S j) (lvars_open (S k) x (dom Σ)).
Proof. apply lvar_store_lvars_open_shift_dom. Qed.

Lemma lty_env_open_one_shift_insert_bound k x T (Σ : lty_env) :
  lty_env_open_one (S k) x (lty_env_shift (<[LVBound k := T]> Σ)) =
  lty_env_shift (lty_env_open_one k x (<[LVBound k := T]> Σ)).
Proof. apply lvar_store_open_one_shift_insert_bound. Qed.

Lemma lty_env_bvar_scope_shift_open_noop k x (Σ : lty_env) :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  lvars_open k x (lty_env_bvar_scope (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof. apply lvar_store_bvar_scope_shift_open_noop. Qed.

Lemma lty_env_bvar_scope_shift_open_one_noop k x (Σ : lty_env) :
  LVBound k ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  LVFree x ∉ dom (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one k x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof. apply lvar_store_bvar_scope_shift_open_one_noop. Qed.

Lemma lty_env_bvar_scope_open_one_shift_under_result k x (Σ : lty_env) :
  LVBound (S k) ∉ lty_env_bvar_scope (lty_env_shift Σ) ->
  LVFree x ∉ dom (lty_env_shift Σ) ->
  lty_env_bvar_scope (lty_env_open_one (S k) x (lty_env_shift Σ)) =
  lty_env_bvar_scope (lty_env_shift Σ).
Proof. apply lvar_store_bvar_scope_open_one_shift_under_result. Qed.

Lemma lvars_open_shift_dom_union_bound0 k x (Σ : lty_env) :
  lvars_open (S k) x (lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}) =
  lvars_shift_from 0 (lvars_open k x (dom Σ)) ∪ {[LVBound 0]}.
Proof. apply lvar_store_lvars_open_shift_dom_union_bound0. Qed.

Lemma lty_env_atom_dom_open_one k x (Σ : lty_env) :
  lty_env_atom_dom (lty_env_open_one k x Σ) ⊆ lty_env_atom_dom Σ ∪ {[x]}.
Proof. apply lvar_store_atom_dom_open_one. Qed.

(** * ContextTypeLanguage.LtyEnv

    Type-language compatibility names for generic lvar-store binder laws. *)


Lemma typed_lty_env_bind_dom (Σ : lty_env) T :
  dom (typed_lty_env_bind Σ T) =
  lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}.
Proof. apply lvar_store_bind_dom. Qed.

Lemma typed_lty_env_bind_lookup_free (Σ : lty_env) T x :
  typed_lty_env_bind Σ T !! LVFree x = Σ !! LVFree x.
Proof.
  unfold typed_lty_env_bind, lvar_store_bind.
  rewrite lookup_insert_ne by discriminate.
  unfold lvar_store_shift, lvar_store_shift_from.
  change ((storeA_rekey (logic_var_shift_from 0) Σ
    : gmap logic_var ty) !! logic_var_shift_from 0 (LVFree x) =
    Σ !! LVFree x).
  apply storeA_rekey_lookup.
  apply logic_var_shift_from_inj.
Qed.


Lemma typed_lty_env_bind_atom_env_insert_dom
    (Δ : gmap atom ty) x Tx Ty :
  x ∉ dom Δ ->
  dom (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) =
  dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ∪
  {[LVFree x]}.
Proof. apply lvar_store_bind_atom_store_insert_dom. Qed.

Lemma typed_lty_env_bind_lvars_fv_dom (Σ : lty_env) T :
  lvars_fv (dom (typed_lty_env_bind Σ T)) = lvars_fv (dom Σ).
Proof. apply lvar_store_bind_lvars_fv_dom. Qed.

Lemma lvars_at_depth_typed_lty_env_bind d (Σ : lty_env) T :
  lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T)) =
  lvars_at_depth d (dom Σ).
Proof.
  rewrite typed_lty_env_bind_dom, lvars_at_depth_union.
  rewrite lvars_at_depth_shift_under by lia.
  rewrite lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma typed_lty_env_bind_atom_dom (Σ : lty_env) T :
  lty_env_atom_dom (typed_lty_env_bind Σ T) = lty_env_atom_dom Σ.
Proof. apply lvar_store_bind_atom_dom. Qed.

Lemma lty_env_insert_free_commute
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  <[LVFree x := Tx]> (<[LVFree y := Ty]> Σ) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof. apply lvar_store_insert_free_commute. Qed.

Lemma typed_lty_env_bind_insert_free
    (Σ : lty_env) x Tx T :
  typed_lty_env_bind (<[LVFree x := Tx]> Σ) T =
  <[LVFree x := Tx]> (typed_lty_env_bind Σ T).
Proof. apply lvar_store_bind_insert_free. Qed.

Lemma lty_env_union_insert_free_singleton
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  LVFree x ∉ dom Σ ->
  ((@union (gmap logic_var ty) _
      (<[LVFree y := Ty]> (Σ : gmap logic_var ty))
      (<[LVFree x := Tx]> (∅ : gmap logic_var ty))) : lty_env) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof. apply lvar_store_union_insert_free_singleton. Qed.

Lemma lty_env_closed_insert_free (Σ : lty_env) x T :
  lty_env_closed Σ ->
  lty_env_closed (<[LVFree x := T]> Σ).
Proof. apply lvar_store_closed_insert_free. Qed.

Lemma lty_env_closed_lookup_bound_none (Σ : lty_env) k :
  lty_env_closed Σ ->
  Σ !! LVBound k = None.
Proof. apply lvar_store_closed_lookup_bound_none. Qed.

Lemma lty_env_shift_closed (Σ : lty_env) :
  lty_env_closed Σ ->
  lty_env_shift Σ = Σ.
Proof. apply lvar_store_shift_closed. Qed.

Lemma typed_lty_env_bind_free_notin x (Σ : lty_env) T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (typed_lty_env_bind Σ T).
Proof. apply lvar_store_bind_free_notin. Qed.

Lemma lty_env_shift_lookup_bound0_none (Σ : lty_env) :
  (lty_env_shift Σ : gmap logic_var ty) !! LVBound 0 = None.
Proof. apply lvar_store_shift_lookup_bound0_none. Qed.

Lemma logic_var_open_env_shift0_typed_bind_inj_on η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  logic_var_open_env_inj_on (open_env_shift_from 0 η)
    (dom (<[LVBound 0 := T]> (lty_env_shift Σ))).
Proof. apply logic_var_open_env_shift0_lvar_store_bind_inj_on. Qed.

Lemma typed_lty_env_bind_open_under k x (Σ : lty_env) T :
  LVFree x ∉ dom Σ ->
  lty_env_open_one (S k) x (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_one k x Σ) T.
Proof. apply lvar_store_bind_open_under. Qed.

Lemma typed_lty_env_bind_open_current y (Σ : lty_env) T :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) =
  <[LVFree y := T]> Σ.
Proof. apply lvar_store_bind_open_current. Qed.

Lemma typed_lty_env_bind_open_current_base y (Σ : lty_env) b :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ (TBase b)) =
  <[LVFree y := TBase b]> Σ.
Proof. apply typed_lty_env_bind_open_current. Qed.

Lemma lty_env_open_typed_bind_atom_env (Δ : gmap atom ty) T x :
  x ∉ dom Δ ->
  lty_env_open_one 0 x
    (typed_lty_env_bind (atom_env_to_lty_env Δ) T) =
  atom_env_to_lty_env (<[x := T]> Δ).
Proof. apply lvar_store_open_bind_atom_store. Qed.

Lemma typed_lty_env_bind_open_env_shift0 η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_shift_from 0 η) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof. apply lvar_store_bind_open_env_shift0. Qed.

Lemma typed_lty_env_bind_open_env_lift η (Σ : lty_env) T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars ((kmap S η)) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof. apply lvar_store_bind_open_env_lift. Qed.
