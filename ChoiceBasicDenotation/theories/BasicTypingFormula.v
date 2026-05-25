(** * BasicDenotation.BasicTypingFormula

    Encoding CoreLang basic type well-formedness side conditions as
    ChoiceLogic formulas.  We keep only the component formulas; obligation
    wrapper sugar is intentionally avoided on the new route. *)

From CoreLang Require Import BasicTyping BasicTypingProps LocallyNamelessProps
  LocallyNamelessExtra.
From ChoiceLogic Require Import Formula.
From ChoiceTypeLanguage Require Import Interface.
From ChoiceBasicDenotation Require Import StoreTyping Term.

Section BasicTypingFormula.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).
Local Notation LogicQualifierT := (logic_qualifier (V := value)) (only parsing).

Definition open_tm_env (η : gmap nat atom) (e : tm) : tm :=
  map_fold (fun k x acc => open_tm k (vfvar x) acc) e η.

Lemma open_tm_env_singleton k y e :
  open_tm_env (<[k := y]> ∅) e =
  open_tm k (vfvar y) e.
Proof.
  unfold open_tm_env.
  change (<[k:=y]> (∅ : gmap nat atom)) with ({[k:=y]} : gmap nat atom).
  rewrite map_fold_singleton.
  reflexivity.
Qed.

Lemma open_tm_env_lc η e :
  lc_tm e ->
  open_tm_env η e = e.
Proof.
  intros Hlc.
  unfold open_tm_env.
  revert e Hlc.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros e Hlc. rewrite map_fold_empty. reflexivity.
  - intros e Hlc.
    rewrite Hfold.
    rewrite IH by exact Hlc.
    apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma open_same_index_fvar_mutual x y :
  (forall v k,
    open_value k (vfvar y) (open_value k (vfvar x) v) =
    open_value k (vfvar x) v) *
  (forall e k,
    open_tm k (vfvar y) (open_tm k (vfvar x) e) =
    open_tm k (vfvar x) e).
Proof.
  apply value_tm_mutind; simpl; intros; try reflexivity; try (f_equal; eauto).
  - destruct (decide (k = n)) as [->|Hkn]; simpl.
    + destruct (decide (n = n)) as [_|Hbad]; [reflexivity | congruence].
    + destruct (decide (k = n)) as [Hbad|_]; [congruence | reflexivity].
Qed.

Lemma open_tm_same_index_fvar x y k e :
  open_tm k (vfvar y) (open_tm k (vfvar x) e) =
  open_tm k (vfvar x) e.
Proof. exact (snd (open_same_index_fvar_mutual x y) e k). Qed.

Lemma open_tm_env_insert_fresh_plain η k x e :
  η !! k = None ->
  open_tm_env (<[k := x]> η) e =
  open_tm k (vfvar x) (open_tm_env η e).
Proof.
  intros Hfresh.
  unfold open_tm_env.
  rewrite (map_fold_insert_L
    (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e k x η).
  - reflexivity.
  - intros i j xi xj acc Hij _ _.
    apply open_swap_tm; [apply LC_fvar | apply LC_fvar | exact Hij].
  - exact Hfresh.
Qed.

Lemma open_tm_env_open_fresh_plain η k x e :
  η !! k = None ->
  open_tm_env η (open_tm k (vfvar x) e) =
  open_tm k (vfvar x) (open_tm_env η e).
Proof.
  unfold open_tm_env.
  refine (fin_maps.map_fold_ind
    (fun η => η !! k = None ->
      map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
        (open_tm k (vfvar x) e) η =
      open_tm k (vfvar x)
        (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e η))
    _ _ η).
  - intros _. rewrite !map_fold_empty. reflexivity.
  - intros i y η0 Hfresh Hfold IH Hnone.
    rewrite (Hfold tm (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
      (open_tm k (vfvar x) e) y).
    rewrite (Hfold tm (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e y).
    assert (Hik : i <> k).
    {
      intros ->.
      rewrite lookup_insert_eq in Hnone. discriminate.
    }
    assert (Hnone0 : η0 !! k = None).
    {
      rewrite lookup_insert_ne in Hnone by congruence.
      exact Hnone.
    }
    rewrite IH by exact Hnone0.
    apply open_swap_tm; [apply LC_fvar | apply LC_fvar | congruence].
Qed.

Lemma open_tm_env_open_tm k x η e :
  open_tm_env η (open_tm k (vfvar x) e) =
  open_tm_env (<[k := x]> η) e.
Proof.
  destruct (η !! k) as [y|] eqn:Hηk.
  - rewrite <-(insert_delete_id η k y Hηk) at 1.
    rewrite open_tm_env_insert_fresh_plain by apply lookup_delete_eq.
    rewrite open_tm_env_open_fresh_plain by apply lookup_delete_eq.
    rewrite open_tm_same_index_fvar.
    replace (<[k := x]> η) with (<[k := x]> (delete k η)).
    2:{
      apply map_eq. intro z.
      destruct (decide (z = k)) as [->|Hzk].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        rewrite lookup_delete_ne by congruence.
        reflexivity.
    }
    rewrite open_tm_env_insert_fresh_plain by apply lookup_delete_eq.
    reflexivity.
  - rewrite open_tm_env_open_fresh_plain by exact Hηk.
    symmetry. apply open_tm_env_insert_fresh_plain. exact Hηk.
Qed.

Lemma tm_lvars_open_tm_env η e :
  open_env_fresh_for_lvars η (tm_lvars e) ->
  tm_lvars (open_tm_env η e) = lvars_open_env η (tm_lvars e).
Proof.
  unfold open_tm_env.
  refine (fin_maps.map_fold_ind
    (fun η => open_env_fresh_for_lvars η (tm_lvars e) ->
      tm_lvars
        (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e η) =
      lvars_open_env η (tm_lvars e))
    _ _ η).
  - intros _. rewrite map_fold_empty, lvars_open_env_empty. reflexivity.
  - intros k x η0 Hfresh Hfold IH Henv.
    rewrite (Hfold tm (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e x).
    rewrite tm_lvars_open.
    + rewrite IH.
      * symmetry. apply lvars_open_env_insert_fresh.
        -- exact Hfresh.
        -- eapply open_env_fresh_for_lvars_insert_head; eassumption.
      * eapply open_env_fresh_for_lvars_insert_tail; eassumption.
    + rewrite <- tm_lvars_fv.
      rewrite IH.
      * eapply open_env_fresh_for_lvars_insert_head; eassumption.
      * eapply open_env_fresh_for_lvars_insert_tail; eassumption.
Qed.

Lemma tm_swap_atom_open_tm_fresh x y k e :
  x ∉ fv_tm e ->
  y ∉ fv_tm e ->
  tm_swap_atom x y (open_tm k (vfvar x) e) =
  open_tm k (vfvar y) e.
Proof.
  intros Hx Hy.
  rewrite tm_swap_atom_open.
  cbn [value_swap_atom].
  rewrite atom_swap_l.
  rewrite tm_swap_atom_fresh by assumption.
  reflexivity.
Qed.

Lemma open_tm_env_insert_open_swap_back η k y z e :
  η !! k = Some z ->
  y ∉ fv_tm e ->
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_fresh_for_lvars (<[k := y]> (delete k η)) (tm_lvars e) ->
  tm_swap_atom y z
    (open_tm_env (<[k := y]> (delete k η)) e) =
  open_tm_env η e.
Proof.
  intros Hηk Hye Hfreshη Hfreshy.
  assert (Hη : η = <[k := z]> (delete k η)).
  { symmetry. apply insert_delete_id. exact Hηk. }
  rewrite Hη at 2.
  rewrite !open_tm_env_insert_fresh_plain by apply lookup_delete_eq.
  apply tm_swap_atom_open_tm_fresh.
  - rewrite <- tm_lvars_fv.
    rewrite tm_lvars_open_tm_env.
    + eapply open_env_fresh_for_lvars_insert_head;
        [apply lookup_delete_eq | exact Hfreshy].
    + eapply open_env_fresh_for_lvars_insert_tail;
        [apply lookup_delete_eq | exact Hfreshy].
  - rewrite <- tm_lvars_fv.
    rewrite tm_lvars_open_tm_env.
    + change (z ∉ lvars_fv (lvars_open_env (delete k η) (tm_lvars e))).
      eapply Hfreshη. exact Hηk.
    + rewrite Hη in Hfreshη.
      eapply open_env_fresh_for_lvars_insert_tail; [apply lookup_delete_eq|].
      exact Hfreshη.
Qed.

Lemma lvars_bv_delete_open_dom (η : gmap nat atom) k y D :
  y ∉ lvars_fv D ->
  lvars_bv D ⊆ dom η ->
  lvars_bv (lvars_open k y D) ⊆ dom (delete k η).
Proof.
  intros HyD Hsub n Hn.
  apply elem_of_dom.
  rewrite lvars_bv_elem in Hn.
  rewrite lvars_open_unfold, gset_swap_elem in Hn.
  destruct (decide (n = k)) as [->|Hnk].
  - exfalso. apply HyD. apply lvars_fv_elem.
    rewrite eq_swap_l in Hn. exact Hn.
  - rewrite eq_swap_fresh in Hn by congruence.
    assert (Hndom : n ∈ dom η).
    { apply Hsub. rewrite lvars_bv_elem. exact Hn. }
    apply elem_of_dom in Hndom as [x Hηn].
    exists x. rewrite lookup_delete_ne by congruence. exact Hηn.
Qed.

Lemma open_env_fresh_for_lvars_delete_open_fresh_atom
    (η : gmap nat atom) k y D :
  y ∉ lvars_fv D ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η D ->
  open_env_fresh_for_lvars (delete k η) (lvars_open k y D).
Proof.
  intros HyD Havoid Hfresh j x Hjx Hbad.
  rewrite lookup_delete_Some in Hjx.
  destruct Hjx as [Hjk Hjx].
  eapply Hfresh; [exact Hjx|].
  apply lvars_fv_elem.
  apply lvars_fv_elem in Hbad.
  unfold lvars_open_env in Hbad |- *.
  apply elem_of_map in Hbad as [v [Hv HvDopen]].
  assert (HuD : logic_var_open k y v ∈ D).
  {
    apply lvars_open_elem_open with (k := k) (x := y).
    rewrite logic_var_open_involutive. exact HvDopen.
  }
  apply elem_of_map.
  exists (logic_var_open k y v). split; [|exact HuD].
  destruct v as [n|a]; cbn [logic_var_open_env] in Hv |- *.
  - destruct (decide (n = k)) as [->|Hnk].
    + rewrite lookup_delete_ne in Hv by congruence.
      rewrite lookup_delete_eq in Hv. discriminate.
    + destruct (decide (n = j)) as [->|Hnj].
      * rewrite lookup_delete_eq in Hv. discriminate.
      * rewrite lookup_delete_ne in Hv by congruence.
        rewrite lookup_delete_ne in Hv by congruence.
        rewrite logic_var_open_unfold, eq_swap_fresh by congruence.
        cbn [logic_var_open_env].
        rewrite lookup_delete_ne by congruence.
        exact Hv.
  - inversion Hv. subst x.
    rewrite logic_var_open_unfold.
    destruct (decide (a = y)) as [->|Hay].
    + exfalso. apply (Havoid j).
      rewrite lookup_delete_ne by congruence. exact Hjx.
    + rewrite eq_swap_fresh by congruence.
      cbn [logic_var_open_env]. reflexivity.
Qed.

Lemma logic_var_open_env_insert_delete_swap_back_on
    (η : gmap nat atom) k y z D v :
  η !! k = Some z ->
  y ∉ lvars_fv D ->
  z ∉ lvars_fv D ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ D) ->
  v ∈ D ->
  logic_var_swap y z
    (logic_var_open_env (<[k := y]> (delete k η)) v) =
  logic_var_open_env η v.
Proof.
  intros Hηk HyD HzD Havoid Hfresh HvD.
  destruct v as [n|a]; cbn [logic_var_open_env].
  - destruct (decide (n = k)) as [->|Hnk].
    + rewrite lookup_insert_eq.
      rewrite Hηk.
      rewrite logic_var_swap_unfold, logic_var_free_eq_swap.
      rewrite atom_swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_delete_ne by congruence.
      destruct (η !! n) as [b|] eqn:Hηn;
        [|rewrite logic_var_swap_unfold;
          rewrite eq_swap_fresh by congruence; reflexivity].
      rewrite logic_var_swap_unfold, logic_var_free_eq_swap.
      rewrite atom_swap_fresh; [reflexivity| |].
      * intros ->. apply (Havoid n).
        rewrite lookup_delete_ne by congruence. exact Hηn.
      * intros ->.
        eapply Hfresh; [exact Hηk|].
        apply lvars_fv_open_env_lookup with (k := n).
        -- rewrite lookup_delete_ne by congruence. exact Hηn.
        -- apply elem_of_union_r. exact HvD.
  - rewrite logic_var_swap_unfold, logic_var_free_eq_swap.
    rewrite atom_swap_fresh; [reflexivity| |].
    + intros ->. apply HyD. apply lvars_fv_elem. exact HvD.
    + intros ->. apply HzD. apply lvars_fv_elem. exact HvD.
Qed.

Lemma lty_env_to_atom_env_open_lvars_insert_open_swap_back_fresh
    (η : gmap nat atom) k y z (Σ : lty_env) :
  η !! k = Some z ->
  y ∉ lvars_fv (dom Σ) ->
  z ∉ lvars_fv (dom Σ) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom Σ) ->
  store_swap y z
    (lty_env_to_atom_env
      (lty_env_open_lvars (<[k := y]> (delete k η)) Σ)) =
  lty_env_to_atom_env (lty_env_open_lvars η Σ).
Proof.
  intros Hηk HyΣ HzΣ Havoid Hfresh.
  rewrite <- lty_env_to_atom_env_swap.
  f_equal.
  unfold lty_env_swap, lty_env_open_lvars.
  assert (Hybig : y ∉ lvars_fv ({[LVBound k]} ∪ dom Σ)).
  {
    intros Hbad.
    rewrite lvars_fv_union in Hbad.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply lvars_fv_elem in Hbad. set_solver.
    - exact (HyΣ Hbad).
  }
  assert (Hfresh_delete :
    open_env_fresh_for_lvars (delete k η)
      (lvars_open k y ({[LVBound k]} ∪ dom Σ))).
  {
    apply open_env_fresh_for_lvars_delete_open_fresh_atom; assumption.
  }
  assert (Hfresh_insert :
    open_env_fresh_for_lvars (<[k:=y]> (delete k η))
      ({[LVBound k]} ∪ dom Σ)).
  {
    eapply open_env_fresh_for_lvars_insert_open_back.
    - rewrite lvars_bv_elem.
      apply elem_of_union_l.
      apply elem_of_singleton.
      reflexivity.
    - exact Hybig.
    - exact Hfresh_delete.
  }
  assert (Hfresh_insert_dom :
    open_env_fresh_for_lvars (<[k:=y]> (delete k η)) (dom Σ)).
  {
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh_insert].
    set_solver.
  }
  rewrite storeA_rekey_compose_inj_on.
  - apply storeA_rekey_ext_on_dom. intros v Hv.
    apply logic_var_open_env_insert_delete_swap_back_on with
      (D := (dom Σ : lvset)); assumption.
  - apply open_env_fresh_for_lvars_inj_on. exact Hfresh_insert_dom.
  - intros a b _ _ Hab. eapply logic_var_swap_inj. exact Hab.
Qed.

Lemma basic_typing_open_env_insert_open_swap_back_fresh
    (η : gmap nat atom) k y z Σ e T :
  η !! k = Some z ->
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  z ∉ lvars_fv (dom Σ) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom Σ) ->
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_fresh_for_lvars (<[k := y]> (delete k η)) (tm_lvars e) ->
  lty_env_to_atom_env
    (lty_env_open_lvars (<[k := y]> (delete k η)) Σ) ⊢ₑ
    open_tm_env (<[k := y]> (delete k η)) e ⋮ T ->
  lty_env_to_atom_env (lty_env_open_lvars η Σ) ⊢ₑ
    open_tm_env η e ⋮ T.
Proof.
  intros Hηk Hy Hz Havoid HfreshΣ Hfreshη Hfreshy Hty.
  pose proof (basic_typing_swap_tm _ _ _ y z Hty) as Hswap.
  rewrite open_tm_env_insert_open_swap_back in Hswap by
    (try exact Hηk; try exact Hfreshη; try exact Hfreshy; set_solver).
  rewrite lty_env_to_atom_env_open_lvars_insert_open_swap_back_fresh in Hswap
    by (try exact Hηk; try exact Havoid; try exact HfreshΣ; set_solver).
  exact Hswap.
Qed.

Lemma lty_env_to_atom_env_open_lvars_closed η (Σ : lty_env) :
  lty_env_closed Σ ->
  lty_env_to_atom_env (lty_env_open_lvars η Σ) =
  lty_env_to_atom_env Σ.
Proof.
  intros Hclosed.
  assert (lty_env_open_lvars η Σ = Σ) as ->; [|reflexivity].
  unfold lty_env_open_lvars.
  assert (Hid : storeA_rekey (fun v : logic_var => v) Σ = Σ).
  {
    apply storeA_map_eq. intros z.
    change (((storeA_rekey (fun v : logic_var => v) Σ : lty_env)
        : gmap logic_var ty) !! z = (Σ : gmap logic_var ty) !! z).
    change z with ((fun v : logic_var => v) z) at 1.
    exact (storeA_rekey_lookup (V:=ty) (fun v : logic_var => v)
      ltac:(intros a b H; exact H) Σ z).
  }
  transitivity (storeA_rekey (fun v : logic_var => v) Σ).
  - apply storeA_rekey_ext_on_dom. intros v Hv.
    destruct v as [k|x]; cbn [logic_var_open_env]; [|reflexivity].
    exfalso.
    change (lvars_bv (dom (Σ : gmap logic_var ty)) = ∅) in Hclosed.
    assert (k ∈ lvars_bv (dom (Σ : gmap logic_var ty))).
    { rewrite lvars_bv_elem. exact Hv. }
    rewrite Hclosed in H. set_solver.
  - exact Hid.
Qed.

Definition basic_tm_has_ltype
    (Σ : lty_env) (e : tm) (T : ty) : Prop :=
  tm_lvars e ⊆ dom Σ /\
  forall η,
    open_env_fresh_for_lvars η (dom Σ ∪ tm_lvars e) ->
    lvars_bv (dom Σ ∪ tm_lvars e) ⊆ dom η ->
    lty_env_to_atom_env (lty_env_open_lvars η Σ) ⊢ₑ
      open_tm_env η e ⋮ T.

Lemma lty_env_to_atom_env_open_lvars_insert_free_subset
    η (Σ : lty_env) x T :
  LVFree x ∉ dom Σ ->
  open_env_fresh_for_lvars η (dom (<[LVFree x := T]> Σ)) ->
  lty_env_to_atom_env (lty_env_open_lvars η Σ) ⊆
  lty_env_to_atom_env
    (lty_env_open_lvars η (<[LVFree x := T]> Σ)).
Proof.
  intros HxΣ Hfresh.
  apply map_subseteq_spec. intros a U Ha.
  apply lty_env_to_atom_env_lookup_some in Ha as Ha_lv.
  rewrite lty_env_open_lvars_insert_entry.
  - apply lty_env_to_atom_env_lookup_free_some.
    destruct (decide (a = x)) as [->|Hax].
    + assert (HnoneΣ : Σ !! LVFree x = None).
      {
        change (((Σ : gmap logic_var ty) !! LVFree x) = None).
        apply not_elem_of_dom_1.
        change (LVFree x ∉ dom (Σ : gmap logic_var ty)).
        exact HxΣ.
      }
      pose proof (lty_env_open_lvars_lookup_fresh
        η (LVFree x) T Σ HnoneΣ Hfresh) as Hnone.
      cbn [logic_var_open_env] in Hnone.
      rewrite Hnone in Ha_lv. discriminate.
    + change (((<[LVFree x := T]>
          ((lty_env_open_lvars η Σ : lty_env) : gmap logic_var ty))
          : gmap logic_var ty) !! LVFree a = Some U).
      rewrite lookup_insert.
      destruct (decide (LVFree x = LVFree a)) as [Heq|_].
      * inversion Heq. congruence.
      * exact Ha_lv.
  - change (((Σ : gmap logic_var ty) !! LVFree x) = None).
    apply not_elem_of_dom_1.
    change (LVFree x ∉ dom (Σ : gmap logic_var ty)).
    exact HxΣ.
  - apply open_env_fresh_for_lvars_inj_on. exact Hfresh.
Qed.

Lemma basic_tm_has_ltype_insert_fresh_lvar
    (Σ : lty_env) e U x T :
  LVFree x ∉ dom Σ ->
  basic_tm_has_ltype Σ e U ->
  basic_tm_has_ltype (<[LVFree x := T]> Σ) e U.
Proof.
  intros HxΣ [Hvars Hty]. split.
  - change (tm_lvars e ⊆
      dom ((<[LVFree x := T]> (Σ : gmap logic_var ty)) : gmap logic_var ty)).
    rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)).
    set_solver.
  - intros η Hfresh Hbv.
    eapply basic_typing_weaken_tm.
    + apply Hty.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        change (dom (Σ : gmap logic_var ty) ∪ tm_lvars e ⊆
          dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
            : gmap logic_var ty) ∪ tm_lvars e).
        rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)).
        set_solver.
      * intros k Hk. apply Hbv.
        rewrite !lvars_bv_elem in Hk |- *.
        change (LVBound k ∈
          dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
            : gmap logic_var ty) ∪ tm_lvars e).
        rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)).
        set_solver.
    + apply lty_env_to_atom_env_open_lvars_insert_free_subset.
      * exact HxΣ.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        set_solver.
Qed.

(** The syntactic well-formedness of [τ] is not a runtime property of the
    world, but we still package it as a world-independent logic qualifier.
    Unlike [basic_choice_ty], this version is scoped by the lvar-domain of [Σ]
    directly, so bound lvars in a type body are preserved until the surrounding
    formula open swaps them to atoms. *)
Definition choice_ty_wf_lqual
    (Σ : lty_env) (τ : choice_ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_choice_ty_lvars (dom Σ) τ).

Definition choice_ty_wf_formula
    (Σ : lty_env) (τ : choice_ty) : Formula :=
  FAtom (choice_ty_wf_lqual Σ τ).

Lemma formula_fv_choice_ty_wf_formula Σ τ :
  formula_fv (choice_ty_wf_formula Σ τ) = lvars_fv (dom Σ).
Proof. reflexivity. Qed.

Definition expr_basic_typing_lqual
    (Σ : lty_env) (e : tm) (T : ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_tm_has_ltype Σ e T).

Definition expr_basic_typing_formula
    (Σ : lty_env) (e : tm) (T : ty) : Formula :=
  FAtom (expr_basic_typing_lqual Σ e T).

Lemma formula_fv_expr_basic_typing_formula Σ e T :
  formula_fv (expr_basic_typing_formula Σ e T) = lvars_fv (dom Σ).
Proof. reflexivity. Qed.

Lemma formula_open_choice_ty_wf_formula k y Σ τ :
  formula_open k y (choice_ty_wf_formula Σ τ) =
  choice_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ).
Proof.
  unfold choice_ty_wf_formula, choice_ty_wf_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 _. cbn [lqual_prop].
    rewrite lty_env_open_one_dom.
    rewrite basic_choice_ty_lvars_open.
    reflexivity.
Qed.

Lemma basic_tm_has_ltype_open_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Proof.
  intros Hy [Hsub Hty].
  set (D := dom Σ ∪ tm_lvars e).
  assert (HyD : y ∉ lvars_fv D).
  {
    subst D. rewrite lvars_fv_union, tm_lvars_fv. exact Hy.
  }
  assert (HyΣ : y ∉ lvars_fv (dom Σ)).
  {
    intros HyΣ. apply Hy. apply elem_of_union_l. exact HyΣ.
  }
  assert (Hye : y ∉ fv_tm e).
  {
    intros Hye. apply Hy. apply elem_of_union_r. exact Hye.
  }
  split.
  - rewrite tm_lvars_open by exact Hye.
    rewrite lty_env_open_one_dom.
    apply lvars_open_mono. exact Hsub.
  - intros η Hfresh Hdom.
    assert (HDopen :
      dom (lty_env_open_one k y Σ) ∪ tm_lvars (open_tm k (vfvar y) e) =
      lvars_open k y D).
    {
      subst D.
      rewrite lty_env_open_one_dom.
      rewrite tm_lvars_open by exact Hye.
      rewrite lvars_open_union. reflexivity.
    }
    destruct (decide (k ∈ lvars_bv D)) as [HkD|HkD].
    + assert (Hfresh_open : open_env_fresh_for_lvars η (lvars_open k y D)).
      { rewrite <- HDopen. exact Hfresh. }
      assert (Hfresh_insert :
        open_env_fresh_for_lvars (<[k := y]> η) D).
      {
        eapply open_env_fresh_for_lvars_insert_open_back; eassumption.
      }
      assert (Hdom_insert : lvars_bv D ⊆ dom (<[k := y]> η)).
      {
        apply lvars_bv_open_insert_dom.
        rewrite <- HDopen. exact Hdom.
      }
      specialize (Hty (<[k := y]> η) Hfresh_insert Hdom_insert).
      rewrite open_tm_env_open_tm.
      rewrite lty_env_open_lvars_open_one.
      * exact Hty.
      * exact HyΣ.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv. apply elem_of_union_l. exact Hv.
    + assert (HDnoop : lvars_open k y D = D).
      {
        apply lvars_open_fresh_index.
        - exact HkD.
        - exact HyD.
      }
      assert (HopenΣ : lty_env_open_one k y Σ = Σ).
      {
        apply lty_env_open_one_fresh_noop.
        - intros Hbad. apply HkD. subst D.
          rewrite lvars_bv_union. apply elem_of_union_l.
          rewrite lvars_bv_elem. exact Hbad.
        - intros Hbad. apply HyΣ. apply lvars_fv_elem. exact Hbad.
      }
      assert (Hopene : open_tm k (vfvar y) e = e).
      {
        apply tm_open_no_bv.
        intros Hbad. apply HkD. subst D.
        rewrite lvars_bv_union. apply elem_of_union_r. exact Hbad.
      }
      rewrite HopenΣ, Hopene in Hfresh, Hdom |- *.
      exact (Hty η Hfresh Hdom).
Qed.

Lemma basic_tm_has_ltype_open_one_cofinite k Σ e T :
  basic_tm_has_ltype Σ e T ->
  exists L : aset,
    forall y,
      y ∉ L ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T.
Proof.
  intros Hty.
  exists (lvars_fv (dom Σ) ∪ fv_tm e).
  intros y Hy.
  apply basic_tm_has_ltype_open_one_fresh; [exact Hy|exact Hty].
Qed.

Lemma basic_tm_has_ltype_close_one_cofinite k Σ e T :
  (exists L : aset,
    forall y,
      y ∉ L ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T) ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros [L Hcof].
  set (D := dom Σ ∪ tm_lvars e).
  split.
  - pose (y := fresh_for (L ∪ lvars_fv D)).
    assert (Hy : y ∉ L ∪ lvars_fv D) by
      (subst y; apply fresh_for_not_in).
    specialize (Hcof y ltac:(set_solver)) as [Hsub _].
    assert (Hyfv : y ∉ fv_tm e).
    {
      subst D. rewrite lvars_fv_union, tm_lvars_fv in Hy. set_solver.
    }
    rewrite tm_lvars_open in Hsub by exact Hyfv.
    rewrite lty_env_open_one_dom in Hsub.
    apply lvars_open_subseteq_iff in Hsub. exact Hsub.
  - intros η Hfreshη Hdomη.
    pose (y := fresh_for
      (L ∪ lvars_fv D ∪ open_env_atoms (delete k η))).
    assert (Hy : y ∉ L ∪ lvars_fv D ∪ open_env_atoms (delete k η)) by
      (subst y; apply fresh_for_not_in).
    specialize (Hcof y ltac:(set_solver)) as [_ Hty_open].
    assert (HyD : y ∉ lvars_fv D) by set_solver.
    assert (HyΣ : y ∉ lvars_fv (dom Σ)).
    { subst D. rewrite lvars_fv_union in HyD. set_solver. }
    assert (Hye : y ∉ fv_tm e).
    { subst D. rewrite lvars_fv_union, tm_lvars_fv in HyD. set_solver. }
    assert (Havoid : open_env_avoids_atom y (delete k η)).
    {
      apply open_env_avoids_atom_of_notin_atoms. set_solver.
    }
    assert (HDopen :
      dom (lty_env_open_one k y Σ) ∪ tm_lvars (open_tm k (vfvar y) e) =
      lvars_open k y D).
    {
      subst D.
      rewrite lty_env_open_one_dom.
      rewrite tm_lvars_open by exact Hye.
      rewrite lvars_open_union. reflexivity.
    }
    destruct (decide (k ∈ lvars_bv D)) as [HkD|HkD].
    + assert (Hkdom : k ∈ dom η).
      { apply Hdomη. exact HkD. }
      apply elem_of_dom in Hkdom as [z Hηk].
      assert (HzΣ : z ∉ lvars_fv (dom Σ)).
      {
        intros HzΣ. eapply Hfreshη; [exact Hηk|].
        apply lvars_fv_open_env_free. subst D.
        apply elem_of_union_l. apply lvars_fv_elem. exact HzΣ.
      }
      assert (Hfreshξ :
        open_env_fresh_for_lvars (delete k η)
          (dom (lty_env_open_one k y Σ) ∪
            tm_lvars (open_tm k (vfvar y) e))).
      {
        rewrite HDopen.
        apply open_env_fresh_for_lvars_delete_open_fresh_atom.
        - exact HyD.
        - exact Havoid.
        - exact Hfreshη.
      }
      assert (Hdomξ :
        lvars_bv (dom (lty_env_open_one k y Σ) ∪
          tm_lvars (open_tm k (vfvar y) e)) ⊆ dom (delete k η)).
      {
        rewrite HDopen.
        apply lvars_bv_delete_open_dom; assumption.
      }
      specialize (Hty_open (delete k η) Hfreshξ Hdomξ).
      rewrite open_tm_env_open_tm in Hty_open.
      rewrite lty_env_open_lvars_open_one in Hty_open.
      2:{ exact HyΣ. }
      2:{
        eapply open_env_fresh_for_lvars_mono; [|exact Hfreshξ].
        intros v Hv. apply elem_of_union_l. exact Hv.
      }
      eapply basic_typing_open_env_insert_open_swap_back_fresh.
      * exact Hηk.
      * subst D. rewrite lvars_fv_union, tm_lvars_fv in HyD. exact HyD.
      * exact HzΣ.
      * exact Havoid.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfreshη].
        subst D. intros v Hv.
        apply elem_of_union in Hv as [Hv|Hv].
        -- rewrite lvars_bv_elem in HkD.
           rewrite elem_of_singleton in Hv. subst v. exact HkD.
        -- apply elem_of_union_l. exact Hv.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfreshη].
        subst D. intros v Hv. apply elem_of_union_r. exact Hv.
      * eapply open_env_fresh_for_lvars_mono.
        -- subst D. intros v Hv. apply elem_of_union_r. exact Hv.
        -- eapply open_env_fresh_for_lvars_insert_open_back.
           ++ exact HkD.
           ++ exact HyD.
           ++ apply open_env_fresh_for_lvars_delete_open_fresh_atom;
                assumption.
      * exact Hty_open.
    + assert (HopenΣ : lty_env_open_one k y Σ = Σ).
      {
        apply lty_env_open_one_fresh_noop.
        - intros Hbad. apply HkD. subst D.
          rewrite lvars_bv_union. apply elem_of_union_l.
          rewrite lvars_bv_elem. exact Hbad.
        - intros Hbad. apply HyΣ. apply lvars_fv_elem. exact Hbad.
      }
      assert (Hopene : open_tm k (vfvar y) e = e).
      {
        apply tm_open_no_bv.
        intros Hbad. apply HkD. subst D.
        rewrite lvars_bv_union. apply elem_of_union_r. exact Hbad.
      }
      rewrite HopenΣ, Hopene in Hty_open.
      exact (Hty_open η Hfreshη Hdomη).
Qed.

Lemma basic_tm_has_ltype_of_atom_typing Σ e T :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hclosed Hty.
  split.
  - pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
    pose proof (typing_tm_lc _ _ _ Hty) as Hlc.
    rewrite (tm_lvars_lc_eq_atoms e Hlc).
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply Hfv in Hx.
    apply elem_of_dom in Hx as [Tx HTx].
    apply lty_env_to_atom_env_lookup_some in HTx.
    change ((Σ : gmap logic_var ty) !! LVFree x = Some Tx) in HTx.
    apply elem_of_dom_2 in HTx. exact HTx.
  - intros η _ _.
    rewrite lty_env_to_atom_env_open_lvars_closed by exact Hclosed.
    rewrite open_tm_env_lc.
    + exact Hty.
    + eapply typing_tm_lc. exact Hty.
Qed.

Lemma basic_tm_has_ltype_open_one_cofinite_iff k Σ e T :
  basic_tm_has_ltype Σ e T <->
  exists L : aset,
    forall y,
      y ∉ L ->
      basic_tm_has_ltype (lty_env_open_one k y Σ)
        (open_tm k (vfvar y) e) T.
Proof.
  split.
  - apply basic_tm_has_ltype_open_one_cofinite.
  - apply basic_tm_has_ltype_close_one_cofinite.
Qed.

Lemma basic_typing_lty_env_to_atom_env_fv_subset Σ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  fv_tm e ⊆ lvars_fv (dom Σ).
Proof.
  intros Hty.
  pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
  pose proof (lty_env_to_atom_env_dom_subset Σ) as Hdom.
  unfold lty_env_atom_dom in Hdom.
  set_solver.
Qed.

Lemma choice_ty_wf_lqual_denote_iff Σ τ (m : WfWorldT) :
  logic_qualifier_denote (choice_ty_wf_lqual Σ τ) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_choice_ty_lvars (dom Σ) τ.
Proof.
  unfold choice_ty_wf_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma choice_ty_wf_formula_models_iff Σ τ (m : WfWorldT) :
  res_models m (choice_ty_wf_formula Σ τ) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_choice_ty_lvars (dom Σ) τ.
Proof.
  unfold res_models, choice_ty_wf_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply choice_ty_wf_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply choice_ty_wf_lqual_denote_iff. exact Hden.
Qed.

Lemma choice_ty_wf_formula_scope_dom Σ τ (m : WfWorldT) :
  res_models m (choice_ty_wf_formula Σ τ) ->
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hmodels.
  apply choice_ty_wf_formula_models_iff in Hmodels as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma choice_ty_wf_formula_basic_lvars Σ τ (m : WfWorldT) :
  res_models m (choice_ty_wf_formula Σ τ) ->
  basic_choice_ty_lvars (dom Σ) τ.
Proof.
  intros Hmodels.
  apply choice_ty_wf_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma choice_ty_wf_formula_fv_cty_subset Σ τ (m : WfWorldT) :
  res_models m (choice_ty_wf_formula Σ τ) ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hmodels.
  pose proof (choice_ty_wf_formula_basic_lvars Σ τ m Hmodels)
    as [Hvars _].
  rewrite <- choice_ty_lvars_fv.
  apply lvars_fv_mono. exact Hvars.
Qed.

Lemma choice_ty_wf_formula_insert_fresh_lvar
    (Σ : lty_env) τ (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models m (choice_ty_wf_formula Σ τ) ->
  res_models mx (choice_ty_wf_formula (<[LVFree x := T]> Σ) τ).
Proof.
  intros HxΣ Hout Hext Hm.
  apply choice_ty_wf_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  apply choice_ty_wf_formula_models_iff.
  split.
  - intros v Hv.
    change (v ∈ dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
      : gmap logic_var ty)) in Hv.
    rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + rewrite elem_of_singleton in Hv. subst v. exact I.
    + exact (Hlc v Hv).
  - split.
    + pose proof (res_extend_by_dom m Fx mx Hext) as Hdom.
      intros a Ha.
      change (a ∈ lvars_fv (dom ((<[LVFree x := T]>
        (Σ : gmap logic_var ty)) : gmap logic_var ty))) in Ha.
      rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Ha.
      rewrite lvars_fv_union, lvars_fv_singleton_free in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      * rewrite elem_of_singleton in Ha. subst a.
        unfold ext_out in Hout.
        rewrite Hdom, Hout. set_solver.
      * rewrite Hdom. set_solver.
    + change (basic_choice_ty_lvars
        (dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
          : gmap logic_var ty)) τ).
      apply basic_choice_ty_lvars_insert_fresh. exact Hbasic.
Qed.

Lemma expr_basic_typing_lqual_denote_iff Σ e T (m : WfWorldT) :
  logic_qualifier_denote (expr_basic_typing_lqual Σ e T) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  unfold expr_basic_typing_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_models_iff Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  unfold res_models, expr_basic_typing_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply expr_basic_typing_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply expr_basic_typing_lqual_denote_iff. exact Hden.
Qed.

Lemma expr_basic_typing_formula_scope_dom Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) ->
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma expr_basic_typing_formula_basic_ltype Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_insert_fresh_lvar
    (Σ : lty_env) e U (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models m (expr_basic_typing_formula Σ e U) ->
  res_models mx (expr_basic_typing_formula (<[LVFree x := T]> Σ) e U).
Proof.
  intros HxΣ Hout Hext Hm.
  apply expr_basic_typing_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split.
  - intros v Hv.
    change (v ∈ dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
      : gmap logic_var ty)) in Hv.
    rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + rewrite elem_of_singleton in Hv. subst v. exact I.
    + exact (Hlc v Hv).
  - split.
    + pose proof (res_extend_by_dom m Fx mx Hext) as Hdom.
      intros a Ha.
      change (a ∈ lvars_fv (dom ((<[LVFree x := T]>
        (Σ : gmap logic_var ty)) : gmap logic_var ty))) in Ha.
      rewrite (dom_insert_L (M := gmap logic_var) (D := gset logic_var)) in Ha.
      rewrite lvars_fv_union, lvars_fv_singleton_free in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      * rewrite elem_of_singleton in Ha. subst a.
        unfold ext_out in Hout.
        rewrite Hdom, Hout. set_solver.
      * rewrite Hdom. set_solver.
    + apply basic_tm_has_ltype_insert_fresh_lvar; assumption.
Qed.

Lemma choice_ty_wf_formula_drop_fresh_lvar
    (Σ : lty_env) (τ : choice_ty) (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ choice_ty_lvars τ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models mx (choice_ty_wf_formula (<[LVFree x := T]> Σ) τ) ->
  res_models m (choice_ty_wf_formula Σ τ).
Proof.
  intros HxΣ Hxτ Hout Hext Hmx.
  apply choice_ty_wf_formula_models_iff in Hmx as [Hlcx [Hsubx Hbasicx]].
  apply choice_ty_wf_formula_models_iff.
  split.
  - intros v Hv.
    apply Hlcx.
    destruct (decide (v = LVFree x)) as [->|Hvne].
    + change (LVFree x ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty))).
      apply elem_of_dom. exists T. rewrite lookup_insert_eq. reflexivity.
    + change (v ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty))).
      change (v ∈ dom (Σ : gmap logic_var ty)) in Hv.
      apply elem_of_dom in Hv as [Tv HTv].
      apply elem_of_dom. exists Tv.
      rewrite lookup_insert_ne by congruence. exact HTv.
  - split.
    + pose proof (res_extend_by_dom m Fx mx Hext) as Hdom.
      intros z Hz.
      specialize (Hsubx z).
      unfold ext_out in Hout.
      rewrite Hdom, Hout in Hsubx.
      apply elem_of_union in Hsubx as [Hzm|Hzx].
      * exact Hzm.
      * rewrite elem_of_singleton in Hzx. subst z.
        exfalso. apply HxΣ. rewrite <- lvars_fv_elem. exact Hz.
      * rewrite lvars_fv_elem.
        rewrite lvars_fv_elem in Hz.
        change (LVFree z ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty))).
        destruct (decide (z = x)) as [->|Hzx].
        -- exfalso. exact (HxΣ Hz).
        -- change (LVFree z ∈ dom (Σ : gmap logic_var ty)) in Hz.
           apply elem_of_dom in Hz as [Tz HTz].
           apply elem_of_dom. exists Tz.
           rewrite lookup_insert_ne by congruence. exact HTz.
    + destruct Hbasicx as [Hvars Hshape].
      split; [| exact Hshape].
      intros v Hv.
      specialize (Hvars v Hv).
      change (v ∈ dom (<[LVFree x := T]> (Σ : gmap logic_var ty))) in Hvars.
      assert (Hvne : v <> LVFree x).
      { intros ->. exact (Hxτ Hv). }
      apply elem_of_dom in Hvars as [Tv HTv].
      rewrite lookup_insert_ne in HTv by congruence.
      eapply storeA_elem_of_dom_lookup_some. exact HTv.
Qed.

Lemma expr_basic_typing_formula_tlete_intro
    (Σ : lty_env) e1 e2 T (m : WfWorldT) :
  res_models m (basic_world_formula Σ) ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ T ->
  res_models m (expr_basic_typing_formula Σ (tlete e1 e2) T).
Proof.
  intros Hworld Hty.
  apply basic_world_formula_models_iff in Hworld as [Hlc [Hsub _]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact Hlc|].
  split; [exact Hsub|].
  apply basic_tm_has_ltype_of_atom_typing; [|exact Hty].
  apply lc_lvars_no_bv. exact Hlc.
Qed.

End BasicTypingFormula.
