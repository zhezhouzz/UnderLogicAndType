(** * ContextTypeLanguage.LtyEnvBind

    Typed lvar-environment binder laws. *)

From LocallyNameless Require Import Classes.
From ContextTypeLanguage Require Export LtyEnvProjection.

Lemma typed_lty_env_bind_dom Σ T :
  dom (typed_lty_env_bind Σ T) =
  lvars_shift_from 0 (dom Σ) ∪ {[LVBound 0]}.
Proof.
  unfold typed_lty_env_bind, lty_env_shift, lty_env_shift_from.
  change (dom ((<[LVBound 0 := T]>
      (storeA_rekey (logic_var_shift_from 0) Σ) : lty_env)
      : gmap logic_var ty) =
    lvars_shift_from 0 (dom (Σ : gmap logic_var ty)) ∪ {[LVBound 0]}).
  transitivity ({[LVBound 0]} ∪
    dom ((storeA_rekey (logic_var_shift_from 0) Σ : lty_env)
      : gmap logic_var ty)).
  { rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
      (((storeA_rekey (logic_var_shift_from 0) Σ : lty_env)
        : gmap logic_var ty)) (LVBound 0) T).
    reflexivity. }
  rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
  unfold lvars_shift_from.
  set_solver.
Qed.

Lemma typed_lty_env_bind_atom_env_insert_dom
    (Δ : gmap atom ty) x Tx Ty :
  x ∉ dom Δ ->
  dom (typed_lty_env_bind (atom_env_to_lty_env (<[x := Tx]> Δ)) Ty) =
  dom (typed_lty_env_bind (atom_env_to_lty_env Δ) Ty) ∪
  {[LVFree x]}.
Proof.
  intros _.
  rewrite atom_env_to_lty_env_insert.
  rewrite !typed_lty_env_bind_dom.
  change (lvars_shift_from 0
      (dom ((<[LVFree x := Tx]> (atom_env_to_lty_env Δ) : lty_env)
        : gmap logic_var ty)) ∪ {[LVBound 0]} =
    (lvars_shift_from 0
      (dom (atom_env_to_lty_env Δ : gmap logic_var ty)) ∪
      {[LVBound 0]}) ∪ {[LVFree x]}).
  rewrite (dom_insert_L (M:=gmap logic_var) (D:=gset logic_var)
    (((atom_env_to_lty_env Δ : lty_env) : gmap logic_var ty))
    (LVFree x) Tx).
  rewrite lvars_shift_from_union.
  replace (lvars_shift_from 0 ({[LVFree x]} : lvset)) with
    ({[LVFree x]} : lvset).
  2:{
    symmetry. apply lvars_shift_from_below_id.
    intros n Hn. apply lvars_bv_elem in Hn.
    rewrite elem_of_singleton in Hn. discriminate.
  }
  apply set_eq. intros v.
  rewrite !elem_of_union, !elem_of_singleton.
  tauto.
Qed.

Lemma typed_lty_env_bind_lvars_fv_dom Σ T :
  lvars_fv (dom (typed_lty_env_bind Σ T)) = lvars_fv (dom Σ).
Proof.
  rewrite typed_lty_env_bind_dom.
  rewrite lvars_fv_union, lvars_shift_from_fv, lvars_fv_singleton_bound.
  set_solver.
Qed.

Lemma lvars_at_depth_typed_lty_env_bind d Σ T :
  lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T)) =
  lvars_at_depth d (dom Σ).
Proof.
  rewrite typed_lty_env_bind_dom, lvars_at_depth_union.
  rewrite lvars_at_depth_shift_under by lia.
  rewrite lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma typed_lty_env_bind_atom_dom Σ T :
  lty_env_atom_dom (typed_lty_env_bind Σ T) = lty_env_atom_dom Σ.
Proof.
  unfold lvar_store_atom_dom, lvar_store_atom_dom.
  apply typed_lty_env_bind_lvars_fv_dom.
Qed.

Lemma lty_env_insert_free_commute
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  <[LVFree x := Tx]> (<[LVFree y := Ty]> Σ) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof.
  intros Hxy.
  apply (map_eq (M:=gmap logic_var)). intros z.
  change (((<[LVFree x := Tx]> (<[LVFree y := Ty]> (Σ : gmap logic_var ty)))
            : gmap logic_var ty) !! z =
          ((<[LVFree y := Ty]> (<[LVFree x := Tx]> (Σ : gmap logic_var ty)))
            : gmap logic_var ty) !! z).
  rewrite !lookup_insert.
  repeat case_decide; subst; try congruence; reflexivity.
Qed.

Lemma typed_lty_env_bind_insert_free
    (Σ : lty_env) x Tx T :
  typed_lty_env_bind (<[LVFree x := Tx]> Σ) T =
  <[LVFree x := Tx]> (typed_lty_env_bind Σ T).
Proof.
  unfold typed_lty_env_bind.
  rewrite (lvar_store_shift_insert_free (V:=ty)).
  apply (map_eq (M := gmap logic_var)). intros z.
  change (((<[LVBound 0 := T]> (<[LVFree x := Tx]>
              (lty_env_shift Σ : gmap logic_var ty)))
            : gmap logic_var ty) !! z =
          ((<[LVFree x := Tx]> (<[LVBound 0 := T]>
              (lty_env_shift Σ : gmap logic_var ty)))
            : gmap logic_var ty) !! z).
  rewrite !lookup_insert.
  repeat case_decide; subst; try discriminate; reflexivity.
Qed.

Lemma lty_env_union_insert_free_singleton
    (Σ : lty_env) x y Tx Ty :
  x <> y ->
  LVFree x ∉ dom Σ ->
  ((@union (gmap logic_var ty) _
      (<[LVFree y := Ty]> (Σ : gmap logic_var ty))
      (<[LVFree x := Tx]> (∅ : gmap logic_var ty))) : lty_env) =
  <[LVFree y := Ty]> (<[LVFree x := Tx]> Σ).
Proof.
  intros Hxy HxΣ.
  change (<[LVFree x := Tx]> (∅ : gmap logic_var ty))
    with ({[LVFree x := Tx]} : gmap logic_var ty).
  rewrite storeA_union_singleton_insert_fresh.
  - apply lty_env_insert_free_commute. exact Hxy.
  - rewrite dom_insert_L. set_solver.
Qed.

Lemma lty_env_closed_insert_free Σ x T :
  lty_env_closed Σ ->
  lty_env_closed (<[LVFree x := T]> Σ).
Proof.
  intros Hclosed.
  unfold lvar_store_closed in *.
  change (lvars_bv (dom (Σ : gmap logic_var ty)) = ∅) in Hclosed.
  change (lvars_bv (dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
    : gmap logic_var ty)) = ∅).
  rewrite dom_insert_L, lvars_bv_union, Hclosed.
  replace (lvars_bv ({[LVFree x]} : lvset)) with (∅ : gset nat).
  - set_solver.
  - apply set_eq. intros k.
    rewrite lvars_bv_elem, elem_of_singleton, elem_of_empty.
    split; [intros Hbad; inversion Hbad | set_solver].
Qed.

Lemma lty_env_closed_lookup_bound_none Σ k :
  lty_env_closed Σ ->
  Σ !! LVBound k = None.
Proof.
  intros Hclosed.
  change (((Σ : lty_env) : gmap logic_var ty) !! LVBound k = None).
  apply not_elem_of_dom. intros Hdom.
  unfold lvar_store_closed in Hclosed.
  assert (k ∈ lvars_bv (dom Σ)).
  { rewrite lvars_bv_elem. exact Hdom. }
  change (k ∈ lvars_bv (dom (Σ : gmap logic_var ty))) in H.
  rewrite Hclosed in H. set_solver.
Qed.

Lemma lty_env_shift_closed Σ :
  lty_env_closed Σ ->
  lty_env_shift Σ = Σ.
Proof.
  intros Hclosed.
  apply storeA_map_eq. intros v.
  destruct v as [k|x].
  - transitivity (@None ty).
    + change (((lty_env_shift Σ : lty_env) : gmap logic_var ty) !!
        LVBound k = None).
      apply not_elem_of_dom. intros Hdom.
      unfold lvar_store_shift, lvar_store_shift, lty_env_shift_from, lvar_store_shift_from in Hdom.
      change (LVBound k ∈
        dom (storeA_rekey (logic_var_shift_from 0) Σ : gmap logic_var ty))
        in Hdom.
      rewrite storeA_rekey_dom in Hdom by apply logic_var_shift_from_inj.
      apply elem_of_map in Hdom as [u [Hu Hudom]].
      destruct u as [n|y]; cbn [logic_var_shift_from] in Hu.
      * destruct (decide (0 <= n)) as [_|Hbad]; [|lia].
        inversion Hu. subst k.
        unfold lvar_store_closed in Hclosed.
        assert (n ∈ lvars_bv (dom Σ)).
        { rewrite lvars_bv_elem. exact Hudom. }
        change (n ∈ lvars_bv (dom (Σ : gmap logic_var ty))) in H.
        rewrite Hclosed in H. set_solver.
      * discriminate.
    + symmetry. apply lty_env_closed_lookup_bound_none. exact Hclosed.
  - unfold lvar_store_shift, lvar_store_shift, lty_env_shift_from, lvar_store_shift_from.
    unfold storeA_rekey, storeA_map_key.
    change ((kmap (M2:=gmap logic_var) (logic_var_shift_from 0) Σ) !!
      LVFree x = (Σ : gmap logic_var ty) !! LVFree x).
    change (LVFree x) with (logic_var_shift_from 0 (LVFree x)) at 1.
    rewrite (lookup_kmap (M1:=gmap logic_var) (M2:=gmap logic_var)
      (Inj0:=logic_var_shift_from_inj 0)
      (logic_var_shift_from 0) Σ (LVFree x)).
    reflexivity.
Qed.

Lemma typed_lty_env_bind_free_notin x Σ T :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ dom (typed_lty_env_bind Σ T).
Proof.
  intros Hfresh Hin.
  rewrite typed_lty_env_bind_dom in Hin.
  apply elem_of_union in Hin as [Hin|Hin].
  - unfold lvars_shift_from in Hin.
    apply elem_of_map in Hin as [v [Hv HvD]].
    destruct v as [n|y]; cbn [logic_var_shift_from] in Hv.
    + destruct (decide (0 <= n)); discriminate.
    + inversion Hv. subst y. exact (Hfresh HvD).
  - rewrite elem_of_singleton in Hin. discriminate.
Qed.

Lemma logic_var_shift0_ne_bound0 v :
  logic_var_shift_from 0 v <> LVBound 0.
Proof.
  destruct v as [n|x]; cbn [logic_var_shift_from].
  - destruct (decide (0 <= n)) as [_|Hbad]; [discriminate|lia].
  - discriminate.
Qed.

Lemma open_env_shift0_lookup_zero_none η :
  open_env_shift_from 0 η !! 0 = None.
Proof.
  rewrite open_env_shift_from_zero.
  apply eq_None_not_Some. intros [x Hx].
  apply lookup_kmap_Some in Hx as [i [Hi _]].
  - lia.
  - intros i j Hij. lia.
Qed.

Lemma logic_var_open_env_shift0_bound0 η :
  logic_var_open_env (open_env_shift_from 0 η) (LVBound 0) = LVBound 0.
Proof.
  cbn [logic_var_open_env].
  rewrite open_env_shift0_lookup_zero_none. reflexivity.
Qed.

Lemma lty_env_shift_lookup_bound0_none Σ :
  (lty_env_shift Σ : gmap logic_var ty) !! LVBound 0 = None.
Proof.
  apply not_elem_of_dom. intros Hin.
  unfold lvar_store_shift, lvar_store_shift, lty_env_shift_from, lvar_store_shift_from in Hin.
  rewrite storeA_rekey_dom in Hin by apply logic_var_shift_from_inj.
  unfold lvars_shift_from in Hin.
  apply elem_of_map in Hin as [v [Hv _]].
  symmetry in Hv. exact (logic_var_shift0_ne_bound0 v Hv).
Qed.

Lemma logic_var_open_env_shift0_typed_bind_inj_on η Σ T :
  open_env_fresh_for_lvars η (dom Σ) ->
  logic_var_open_env_inj_on (open_env_shift_from 0 η)
    (dom (<[LVBound 0 := T]> (lty_env_shift Σ))).
Proof.
  intros Hfresh v1 v2 Hv1 Hv2 Heq.
  assert (Hfresh_shift :
    open_env_fresh_for_lvars (open_env_shift_from 0 η)
      (dom (lty_env_shift Σ))).
  {
    unfold lvar_store_shift, lvar_store_shift, lty_env_shift_from, lvar_store_shift_from.
    change (open_env_fresh_for_lvars (open_env_shift_from 0 η)
      (dom (storeA_rekey (logic_var_shift_from 0) Σ : gmap logic_var ty))).
    rewrite storeA_rekey_dom by apply logic_var_shift_from_inj.
    change (open_env_fresh_for_lvars (open_env_shift_from 0 η)
      (lvars_shift_from 0 (dom (Σ : gmap logic_var ty)))).
    apply open_env_shift_from_fresh_for_lvars. exact Hfresh.
  }
  change (v1 ∈ dom (<[LVBound 0 := T]> (lty_env_shift Σ : gmap logic_var ty))) in Hv1.
  change (v2 ∈ dom (<[LVBound 0 := T]> (lty_env_shift Σ : gmap logic_var ty))) in Hv2.
  rewrite dom_insert_L in Hv1, Hv2.
  apply elem_of_union in Hv1 as [Hv1|Hv1];
    apply elem_of_union in Hv2 as [Hv2|Hv2].
  - rewrite elem_of_singleton in Hv1.
    rewrite elem_of_singleton in Hv2. congruence.
  - rewrite elem_of_singleton in Hv1. subst v1.
    rewrite logic_var_open_env_shift0_bound0 in Heq.
    unfold lvar_store_shift, lvar_store_shift, lty_env_shift_from, lvar_store_shift_from in Hv2.
    rewrite storeA_rekey_dom in Hv2 by apply logic_var_shift_from_inj.
    unfold lvars_shift_from in Hv2.
    apply elem_of_map in Hv2 as [v [Hv _]].
    subst v2.
    rewrite logic_var_open_env_shift_from in Heq.
    exfalso. symmetry in Heq. exact (logic_var_shift0_ne_bound0 _ Heq).
  - rewrite elem_of_singleton in Hv2. subst v2.
    rewrite logic_var_open_env_shift0_bound0 in Heq.
    unfold lvar_store_shift, lvar_store_shift, lty_env_shift_from, lvar_store_shift_from in Hv1.
    rewrite storeA_rekey_dom in Hv1 by apply logic_var_shift_from_inj.
    unfold lvars_shift_from in Hv1.
    apply elem_of_map in Hv1 as [v [Hv _]].
    subst v1.
    rewrite logic_var_open_env_shift_from in Heq.
    exfalso. exact (logic_var_shift0_ne_bound0 _ Heq).
  - eapply open_env_fresh_for_lvars_inj_on; eassumption.
Qed.

Lemma typed_lty_env_bind_open_under k x Σ T :
  LVFree x ∉ dom Σ ->
  lty_env_open_one (S k) x (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_one k x Σ) T.
Proof.
  intros _.
  unfold typed_lty_env_bind.
  rewrite lty_env_open_one_insert.
  replace (logic_var_open (S k) x (LVBound 0)) with (LVBound 0).
  - unfold lvar_store_shift, lvar_store_shift.
    rewrite lty_env_open_one_shift_under_gen by lia.
    reflexivity.
  - rewrite logic_var_open_unfold.
    unfold swap. repeat destruct decide; try lia; try congruence.
Qed.

Lemma typed_lty_env_bind_open_current y Σ T :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ T) =
  <[LVFree y := T]> Σ.
Proof.
  intros Hfresh Hclosed.
  unfold typed_lty_env_bind.
  rewrite lty_env_open_one_insert.
  replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
  2:{
    rewrite logic_var_open_unfold.
    unfold swap. repeat destruct decide; try lia; try congruence.
  }
  rewrite lty_env_shift_closed by exact Hclosed.
  rewrite lty_env_open_one_fresh_noop.
  - reflexivity.
  - intros Hbound.
    unfold lvar_store_closed in Hclosed.
    assert (0 ∈ lvars_bv (dom Σ)).
    { rewrite lvars_bv_elem. exact Hbound. }
    change (0 ∈ lvars_bv (dom (Σ : gmap logic_var ty))) in H.
    rewrite Hclosed in H. set_solver.
  - exact Hfresh.
Qed.

Lemma typed_lty_env_bind_open_current_base y Σ b :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  lty_env_open_one 0 y (typed_lty_env_bind Σ (TBase b)) =
  <[LVFree y := TBase b]> Σ.
Proof.
  apply typed_lty_env_bind_open_current.
Qed.

Lemma lty_env_open_typed_bind_atom_env (Δ : gmap atom ty) T x :
  x ∉ dom Δ ->
  lty_env_open_one 0 x
    (typed_lty_env_bind (atom_env_to_lty_env Δ) T) =
  atom_env_to_lty_env (<[x := T]> Δ).
Proof.
  intros Hx.
  unfold typed_lty_env_bind.
  rewrite lty_env_open_one_bind_atom_env by exact Hx.
  rewrite atom_env_to_lty_env_insert.
  reflexivity.
Qed.

Lemma typed_lty_env_bind_open_env_shift0 η Σ T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars (open_env_shift_from 0 η) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof.
  intros Hfresh.
  unfold typed_lty_env_bind.
  rewrite (lty_env_open_lvars_insert_entry
    (open_env_shift_from 0 η) (LVBound 0) T (lty_env_shift Σ)).
  - rewrite logic_var_open_env_shift0_bound0.
    unfold lvar_store_shift.
    rewrite (lvar_store_open_lvars_shift_from (V:=ty) 0 η Σ) by exact Hfresh.
    reflexivity.
  - apply lty_env_shift_lookup_bound0_none.
  - apply logic_var_open_env_shift0_typed_bind_inj_on. exact Hfresh.
Qed.

Lemma typed_lty_env_bind_open_env_lift η Σ T :
  open_env_fresh_for_lvars η (dom Σ) ->
  lty_env_open_lvars ((kmap S η)) (typed_lty_env_bind Σ T) =
  typed_lty_env_bind (lty_env_open_lvars η Σ) T.
Proof.
  intros Hfresh.
  rewrite <- open_env_shift_from_zero.
  apply typed_lty_env_bind_open_env_shift0. exact Hfresh.
Qed.
