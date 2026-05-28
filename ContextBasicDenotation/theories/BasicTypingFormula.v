(** * BasicDenotation.BasicTypingFormula

    Encoding CoreLang basic type well-formedness side conditions as
    ContextLogic formulas.  We keep only the component formulas; obligation
    wrapper sugar is intentionally avoided on the new route. *)

From CoreLang Require Import LocallyNamelessExtra.
From ContextBasicDenotation Require Import Notation StoreTyping TermTLet.

Section BasicTypingFormula.

Definition open_tm_env (η : gmap nat atom) (e : tm) : tm :=
  map_fold (fun k x acc => open_tm k (vfvar x) acc) e η.
Definition open_env_atom_swap (x y : atom) (η : gmap nat atom)
    : gmap nat atom :=
  swap x y <$> η.

Lemma open_env_atom_swap_lookup x y η k :
  open_env_atom_swap x y η !! k =
  swap x y <$> (η !! k).
Proof.
  unfold open_env_atom_swap. apply lookup_fmap.
Qed.

Lemma open_env_atom_swap_dom x y η :
  dom (open_env_atom_swap x y η) = dom η.
Proof.
  unfold open_env_atom_swap.
  apply dom_fmap_L.
Qed.

Lemma open_env_atom_swap_involutive x y η :
  open_env_atom_swap x y (open_env_atom_swap x y η) = η.
Proof.
  apply map_eq. intros k.
  rewrite !open_env_atom_swap_lookup.
  destruct (η !! k) as [a|]; cbn; [rewrite swap_involutive|];
    reflexivity.
Qed.

Lemma open_env_atom_swap_delete x y η k :
  delete k (open_env_atom_swap x y η) =
  open_env_atom_swap x y (delete k η).
Proof.
  apply map_eq. intros j.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite lookup_delete_eq.
    unfold open_env_atom_swap. rewrite lookup_fmap, lookup_delete_eq.
    reflexivity.
  - rewrite lookup_delete_ne by congruence.
    unfold open_env_atom_swap.
    rewrite !lookup_fmap, lookup_delete_ne by congruence.
    reflexivity.
Qed.

Lemma logic_var_open_env_atom_swap x y η v :
  logic_var_open_env η (logic_var_swap x y v) =
  logic_var_swap x y (logic_var_open_env (open_env_atom_swap x y η) v).
Proof.
  destruct v as [k|a].
  - rewrite logic_var_swap_unfold.
    rewrite swap_fresh by congruence.
    cbn [logic_var_open_env].
    rewrite open_env_atom_swap_lookup.
    destruct (η !! k) as [b|] eqn:Hη; cbn.
    + rewrite logic_var_swap_unfold.
      rewrite logic_var_free_swap.
      rewrite swap_involutive. reflexivity.
    + rewrite logic_var_swap_unfold.
      rewrite swap_fresh by congruence. reflexivity.
  - cbn [logic_var_open_env].
    rewrite logic_var_swap_unfold, logic_var_free_swap.
    reflexivity.
Qed.

Lemma lvars_swap_elem_iff x y D v :
  v ∈ lvars_swap x y D <-> logic_var_swap x y v ∈ D.
Proof.
  rewrite lvars_swap_unfold, set_swap_elem.
  change (swap (LVFree x) (LVFree y) v) with (logic_var_swap x y v).
  reflexivity.
Qed.

Lemma lvars_open_env_atom_swap x y η D :
  lvars_open_env η (lvars_swap x y D) =
  lvars_swap x y (lvars_open_env (open_env_atom_swap x y η) D).
Proof.
  apply set_eq. intros v.
  unfold lvars_open_env.
  split.
  - intros Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    apply lvars_swap_elem_iff in Hu.
    apply lvars_swap_elem_iff.
    apply elem_of_map.
    exists (logic_var_swap x y u). split.
    + pose proof (logic_var_open_env_atom_swap x y η
        (logic_var_swap x y u)) as Hop.
      rewrite logic_var_swap_involutive in Hop.
      apply (f_equal (logic_var_swap x y)) in Hop.
      rewrite logic_var_swap_involutive in Hop.
      exact Hop.
    + exact Hu.
  - intros Hv.
    apply lvars_swap_elem_iff in Hv.
    apply elem_of_map in Hv as [u [Hu_eq Hu]].
    apply elem_of_map.
    exists (logic_var_swap x y u). split.
    + pose proof (logic_var_open_env_atom_swap x y η u) as Hop.
      rewrite Hop.
      rewrite <- Hu_eq.
      rewrite logic_var_swap_involutive. reflexivity.
    + apply lvars_swap_elem_iff.
      rewrite logic_var_swap_involutive. exact Hu.
Qed.

Lemma open_env_fresh_for_lvars_atom_swap x y η D :
  open_env_fresh_for_lvars η (lvars_swap x y D) ->
  open_env_fresh_for_lvars (open_env_atom_swap x y η) D.
Proof.
  intros Hfresh k a Hka Hbad.
  rewrite open_env_atom_swap_lookup in Hka.
  destruct (η !! k) as [b|] eqn:Hη; cbn in Hka; [|discriminate].
  inversion Hka. subst a.
  eapply Hfresh; [exact Hη|].
  rewrite lvars_open_env_atom_swap.
  rewrite lvars_fv_swap.
  rewrite elem_of_set_swap.
  rewrite <- open_env_atom_swap_delete.
  exact Hbad.
Qed.

Lemma lty_env_open_lvars_atom_swap x y η Σ :
  open_env_fresh_for_lvars η (dom (lty_env_swap x y Σ)) ->
  lty_env_open_lvars η (lty_env_swap x y Σ) =
  lty_env_swap x y
    (lty_env_open_lvars (open_env_atom_swap x y η) Σ).
Proof.
  intros Hfresh.
  assert (HfreshΣ :
    open_env_fresh_for_lvars (open_env_atom_swap x y η) (dom Σ)).
  {
    apply open_env_fresh_for_lvars_atom_swap.
    rewrite <- lvar_store_swap_dom. exact Hfresh.
  }
  unfold lty_env_open_lvars, lvar_store_open_lvars, lty_env_swap, lvar_store_swap.
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_open_env η) (logic_var_swap x y) Σ).
  2:{ intros a b _ _ Hab. eapply logic_var_swap_inj. exact Hab. }
  2:{ apply open_env_fresh_for_lvars_inj_on. exact Hfresh. }
  rewrite (storeA_rekey_compose_inj_on
    (logic_var_swap x y) (logic_var_open_env (open_env_atom_swap x y η)) Σ).
  2:{ apply open_env_fresh_for_lvars_inj_on. exact HfreshΣ. }
  2:{ intros a b _ _ Hab. eapply logic_var_swap_inj. exact Hab. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_open_env_atom_swap.
Qed.

Lemma lty_env_to_atom_env_open_lvars_atom_swap x y η Σ :
  open_env_fresh_for_lvars η (dom (lty_env_swap x y Σ)) ->
  lty_env_to_atom_env (lty_env_open_lvars η (lty_env_swap x y Σ)) =
  (kmap (swap x y)
    (lty_env_to_atom_env
      (lty_env_open_lvars (open_env_atom_swap x y η) Σ)) : gmap atom ty).
Proof.
  intros Hfresh.
  rewrite lty_env_open_lvars_atom_swap by exact Hfresh.
  apply lvar_store_to_atom_store_swap.
Qed.

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

Lemma open_env_atom_swap_insert x y η k a :
  open_env_atom_swap x y (<[k := a]> η) =
  <[k := swap x y a]> (open_env_atom_swap x y η).
Proof.
  unfold open_env_atom_swap.
  apply map_eq. intros j.
  rewrite lookup_fmap.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    rewrite lookup_fmap. reflexivity.
Qed.

Lemma open_env_atom_swap_avoids x y z η :
  open_env_avoids_atom z η ->
  open_env_avoids_atom (swap x y z) (open_env_atom_swap x y η).
Proof.
  intros Havoid k Hlookup.
  rewrite open_env_atom_swap_lookup in Hlookup.
  destruct (η !! k) as [a|] eqn:Hη; cbn in Hlookup; [|discriminate].
  inversion Hlookup as [Heq].
  apply swap_inj in Heq. subst a.
  apply (Havoid k). exact Hη.
Qed.

Lemma open_tm_env_atom_swap x y η e :
  open_tm_env η (tm_swap_atom x y e) =
  tm_swap_atom x y (open_tm_env (open_env_atom_swap x y η) e).
Proof.
  unfold open_tm_env.
  revert e.
  induction η as [|k a η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros e. rewrite !map_fold_empty. reflexivity.
  - intros e.
    rewrite (Hfold tm (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)).
    rewrite open_env_atom_swap_insert.
    rewrite (map_fold_insert_L
      (fun k0 x0 acc => open_tm k0 (vfvar x0) acc)
      e k (swap x y a) (open_env_atom_swap x y η)).
    2:{
      intros i j xi xj acc Hij _ _.
      apply open_swap_tm; [apply LC_fvar | apply LC_fvar | exact Hij].
    }
    2:{ rewrite open_env_atom_swap_lookup, Hfresh. reflexivity. }
    rewrite IH.
    rewrite open_tm_swap_atom.
    reflexivity.
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
  rewrite swap_l.
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
  rewrite set_swap_elem in Hn.
  destruct (decide (n = k)) as [->|Hnk].
  - exfalso. apply HyD. apply lvars_fv_elem.
    rewrite swap_l in Hn. exact Hn.
  - rewrite swap_fresh in Hn by congruence.
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
        rewrite swap_fresh by congruence.
        cbn [logic_var_open_env].
        rewrite lookup_delete_ne by congruence.
        exact Hv.
  - inversion Hv. subst x.
    destruct (decide (a = y)) as [->|Hay].
    + exfalso. apply (Havoid j).
      rewrite lookup_delete_ne by congruence. exact Hjx.
    + rewrite swap_fresh by congruence.
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
      rewrite logic_var_swap_unfold, logic_var_free_swap.
      rewrite swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_delete_ne by congruence.
      destruct (η !! n) as [b|] eqn:Hηn;
        [|rewrite logic_var_swap_unfold;
          rewrite swap_fresh by congruence; reflexivity].
      rewrite logic_var_swap_unfold, logic_var_free_swap.
      rewrite swap_fresh; [reflexivity| |].
      * intros ->. apply (Havoid n).
        rewrite lookup_delete_ne by congruence. exact Hηn.
      * intros ->.
        eapply Hfresh; [exact Hηk|].
        apply lvars_fv_open_env_lookup with (k := n).
        -- rewrite lookup_delete_ne by congruence. exact Hηn.
        -- apply elem_of_union_r. exact HvD.
  - rewrite logic_var_swap_unfold, logic_var_free_swap.
    rewrite swap_fresh; [reflexivity| |].
    + intros ->. apply HyD. apply lvars_fv_elem. exact HvD.
    + intros ->. apply HzD. apply lvars_fv_elem. exact HvD.
Qed.

Lemma lty_env_to_atom_env_open_swap_back
    (η : gmap nat atom) k y z (Σ : lty_env) :
  η !! k = Some z ->
  y ∉ lvars_fv (dom Σ) ->
  z ∉ lvars_fv (dom Σ) ->
  open_env_avoids_atom y (delete k η) ->
  open_env_fresh_for_lvars η ({[LVBound k]} ∪ dom Σ) ->
  (kmap (swap y z)
    (lty_env_to_atom_env
      (lty_env_open_lvars (<[k := y]> (delete k η)) Σ)) : gmap atom ty) =
  lty_env_to_atom_env (lty_env_open_lvars η Σ).
Proof.
  intros Hηk HyΣ HzΣ Havoid Hfresh.
  rewrite <- lvar_store_to_atom_store_swap.
  f_equal.
  unfold lty_env_swap, lvar_store_swap, lty_env_open_lvars, lvar_store_open_lvars.
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

Lemma basic_typing_open_env_swap_back
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
  rewrite lty_env_to_atom_env_open_swap_back in Hswap
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
  unfold lty_env_open_lvars, lvar_store_open_lvars.
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

Lemma lc_tlete_tapp_tm_assoc_source e1 e2 y :
  lc_tm (tlete e1 e2) ->
  lc_tm (tlete e1 (tapp_tm e2 (vfvar y))).
Proof.
  intros Hlc.
  apply lc_lete_iff_body in Hlc as [Hlc1 Hbody2].
  apply lc_lete_iff_body. split; [exact Hlc1|].
  destruct Hbody2 as [L HL].
  exists L. intros x Hx.
  change (lc_tm (open_tm 0 (vfvar x) (tapp_tm e2 (vfvar y)))).
  rewrite open_tapp_tm_lc_arg by constructor.
  apply lc_tapp_tm; [apply HL; exact Hx | constructor].
Qed.

Lemma basic_tm_has_ltype_tapp_tm_tlete_assoc
    (Σ : lty_env) e1 e2 y T :
  lc_tm (tlete e1 e2) ->
  basic_tm_has_ltype Σ (tlete e1 (tapp_tm e2 (vfvar y))) T ->
  basic_tm_has_ltype Σ (tapp_tm (tlete e1 e2) (vfvar y)) T.
Proof.
  intros Hlc [Hsub Hty].
  split.
  - rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. exact Hsub.
  - intros η Hfresh Hbv.
    rewrite open_tm_env_lc.
    + assert (Hfresh_src : open_env_fresh_for_lvars η
        (dom Σ ∪ tm_lvars (tlete e1 (tapp_tm e2 (vfvar y))))).
      { rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar. exact Hfresh. }
      assert (Hbv_src :
        lvars_bv (dom Σ ∪ tm_lvars (tlete e1 (tapp_tm e2 (vfvar y)))) ⊆
        dom η).
      { rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar. exact Hbv. }
      pose proof (Hty η Hfresh_src Hbv_src) as Htyη.
      rewrite open_tm_env_lc in Htyη by
        (apply lc_tlete_tapp_tm_assoc_source; exact Hlc).
      apply basic_typing_tapp_tm_tlete_assoc.
      exact Htyη.
    + apply lc_tapp_tm; [exact Hlc | constructor].
Qed.

Lemma basic_tm_has_ltype_tapp_tm_tlete_assoc_rev
    (Σ : lty_env) e1 e2 y T :
  lc_tm (tlete e1 e2) ->
  basic_tm_has_ltype Σ (tapp_tm (tlete e1 e2) (vfvar y)) T ->
  basic_tm_has_ltype Σ (tlete e1 (tapp_tm e2 (vfvar y))) T.
Proof.
  intros Hlc [Hsub Hty].
  split.
  - rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar. exact Hsub.
  - intros η Hfresh Hbv.
    rewrite open_tm_env_lc.
    + assert (Hfresh_tgt : open_env_fresh_for_lvars η
        (dom Σ ∪ tm_lvars (tapp_tm (tlete e1 e2) (vfvar y)))).
      { rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. exact Hfresh. }
      assert (Hbv_tgt :
        lvars_bv (dom Σ ∪ tm_lvars (tapp_tm (tlete e1 e2) (vfvar y))) ⊆
        dom η).
      { rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. exact Hbv. }
      pose proof (Hty η Hfresh_tgt Hbv_tgt) as Htyη.
      rewrite open_tm_env_lc in Htyη by
        (apply lc_tapp_tm; [exact Hlc | constructor]).
      apply basic_typing_tapp_tm_tlete_assoc_rev.
      exact Htyη.
    + apply lc_tlete_tapp_tm_assoc_source. exact Hlc.
Qed.
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
  apply lvar_store_to_atom_store_lookup_some in Ha as Ha_lv.
  rewrite lty_env_open_lvars_insert_entry.
  - apply lvar_store_to_atom_store_lookup_free_some.
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
      change (((@lvar_store_open_lvars ty) η Σ
        : gmap logic_var ty) !! LVFree x = None) in Hnone.
      change (((@lvar_store_open_lvars ty) η Σ
        : gmap logic_var ty) !! LVFree x = Some U) in Ha_lv.
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

Lemma lvars_swap_mono x y (D E : lvset) :
  D ⊆ E ->
  lvars_swap x y D ⊆ lvars_swap x y E.
Proof.
  intros Hsub v Hv.
  apply lvars_swap_elem_iff in Hv.
  apply lvars_swap_elem_iff.
  apply Hsub. exact Hv.
Qed.

Lemma lvars_swap_union x y (D E : lvset) :
  lvars_swap x y (D ∪ E) = lvars_swap x y D ∪ lvars_swap x y E.
Proof.
  apply set_eq. intros v.
  rewrite elem_of_union.
  rewrite !lvars_swap_elem_iff.
  rewrite elem_of_union. reflexivity.
Qed.

Lemma open_env_fresh_for_lvars_atom_swap_inv x y η D :
  open_env_fresh_for_lvars η D ->
  open_env_fresh_for_lvars (open_env_atom_swap x y η) (lvars_swap x y D).
Proof.
  intros Hfresh k a Hka Hbad.
  rewrite open_env_atom_swap_lookup in Hka.
  destruct (η !! k) as [b|] eqn:Hη; cbn in Hka; [|discriminate].
  inversion Hka. subst a.
  eapply Hfresh; [exact Hη|].
  rewrite open_env_atom_swap_delete in Hbad.
  rewrite lvars_open_env_atom_swap in Hbad.
  rewrite open_env_atom_swap_involutive in Hbad.
  rewrite lvars_fv_swap in Hbad.
  rewrite elem_of_set_swap in Hbad.
  rewrite swap_involutive in Hbad.
  exact Hbad.
Qed.

Lemma basic_tm_has_ltype_swap_atom x y Σ e T :
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_swap x y Σ) (tm_swap_atom x y e) T.
Proof.
  intros [Hsub Hty]. split.
  - rewrite tm_lvars_swap_atom.
    change (lvars_swap x y (tm_lvars e) ⊆
      dom ((@lvar_store_swap ty) x y Σ : gmap logic_var ty)).
    rewrite (lvar_store_swap_dom (V:=ty) x y Σ).
    apply lvars_swap_mono. exact Hsub.
  - intros η Hfresh Hbv.
    set (η' := open_env_atom_swap x y η).
    assert (Hfresh' :
      open_env_fresh_for_lvars η' (dom Σ ∪ tm_lvars e)).
    {
      subst η'.
      apply open_env_fresh_for_lvars_atom_swap.
      change (open_env_fresh_for_lvars η
        (dom ((@lvar_store_swap ty) x y Σ : gmap logic_var ty) ∪
          tm_lvars (tm_swap_atom x y e))) in Hfresh.
      rewrite (lvar_store_swap_dom (V:=ty) x y Σ) in Hfresh.
      rewrite tm_lvars_swap_atom in Hfresh.
      rewrite lvars_swap_union.
      exact Hfresh.
    }
    assert (Hbv' : lvars_bv (dom Σ ∪ tm_lvars e) ⊆ dom η').
    {
      subst η'. rewrite open_env_atom_swap_dom.
      intros k Hk. apply Hbv.
      rewrite !lvars_bv_union in Hk |- *.
      change (k ∈ lvars_bv (dom ((@lvar_store_swap ty) x y Σ
          : gmap logic_var ty)) ∪
        lvars_bv (tm_lvars (tm_swap_atom x y e))).
      rewrite (lvar_store_swap_dom (V:=ty) x y Σ).
      rewrite tm_lvars_swap_atom.
      rewrite !lvars_bv_swap.
      exact Hk.
    }
    subst η'.
    specialize (Hty (open_env_atom_swap x y η) Hfresh' Hbv').
    pose proof (basic_typing_swap_tm _ _ _ x y Hty) as Hswap.
    rewrite <- open_tm_env_atom_swap in Hswap.
    rewrite <- lty_env_to_atom_env_open_lvars_atom_swap in Hswap.
    + exact Hswap.
    + eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      set_solver.
Qed.

Lemma logic_var_swap_open_one x y k v :
  logic_var_swap x y (logic_var_open k x v) =
  logic_var_open k y (logic_var_swap x y v).
Proof.
  rewrite !logic_var_swap_unfold.
  unfold swap.
  repeat destruct decide; subst; try congruence; reflexivity.
Qed.

Lemma lty_env_swap_open_one x y k Σ :
  lty_env_swap x y (lty_env_open_one k x Σ) =
  lty_env_open_one k y (lty_env_swap x y Σ).
Proof.
  unfold lty_env_swap, lvar_store_swap, lty_env_open_one, lvar_store_open_one.
  rewrite (storeA_rekey_compose (logic_var_swap x y) (logic_var_open k x)).
  2:{ apply logic_var_swap_inj. }
  2:{ intros a b H. eapply logic_var_open_inj_fresh. exact H. }
  rewrite (storeA_rekey_compose (logic_var_open k y) (logic_var_swap x y)).
  2:{ intros a b H. eapply logic_var_open_inj_fresh. exact H. }
  2:{ apply logic_var_swap_inj. }
  apply storeA_rekey_ext_on_dom. intros v _.
  apply logic_var_swap_open_one.
Qed.

(** The syntactic well-formedness of [τ] is not a runtime property of the
    world, but we still package it as a world-independent logic qualifier.
    Unlike [basic_context_ty], this version is scoped by the lvar-domain of [Σ]
    directly, so bound lvars in a type body are preserved until the surrounding
    formula open swaps them to atoms. *)
Definition context_ty_wf_lqual
    (Σ : lty_env) (τ : context_ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_context_ty_lvars (dom Σ) τ).
Definition context_ty_wf_formula
    (Σ : lty_env) (τ : context_ty) : Formula :=
  FAtom (context_ty_wf_lqual Σ τ).
Lemma formula_fv_context_ty_wf_formula Σ τ :
  formula_fv (context_ty_wf_formula Σ τ) = lvars_fv (dom Σ).
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
Lemma formula_open_context_ty_wf_formula k y Σ τ :
  formula_open k y (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ).
Proof.
  unfold context_ty_wf_formula, context_ty_wf_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 _. cbn [lqual_prop].
    rewrite lty_env_open_one_dom.
    rewrite basic_context_ty_lvars_open.
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
      eapply basic_typing_open_env_swap_back.
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
    apply lvar_store_to_atom_store_lookup_some in HTx.
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

Lemma basic_tm_has_ltype_open_one_rename_fresh k y z Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  z ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T ->
  basic_tm_has_ltype (lty_env_open_one k z Σ)
    (open_tm k (vfvar z) e) T.
Proof.
  intros Hy Hz Hty.
  pose proof (basic_tm_has_ltype_swap_atom y z
    (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T Hty) as Hswap.
  rewrite lty_env_swap_open_one in Hswap.
  rewrite lvar_store_swap_fresh in Hswap.
  2:{ unfold lty_env_atom_dom, lvar_store_atom_dom. set_solver. }
  2:{ unfold lty_env_atom_dom, lvar_store_atom_dom. set_solver. }
  rewrite tm_swap_atom_open_tm_fresh in Hswap by set_solver.
  exact Hswap.
Qed.

Lemma basic_tm_has_ltype_close_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hy Hopen.
  apply (basic_tm_has_ltype_close_one_cofinite k).
  exists ({[y]} ∪ lvars_fv (dom Σ) ∪ fv_tm e).
  intros z Hz.
  eapply basic_tm_has_ltype_open_one_rename_fresh; [exact Hy| |exact Hopen].
  set_solver.
Qed.

Lemma basic_tm_has_ltype_open_one_fresh_iff k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T <->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Proof.
  intros Hy. split.
  - apply basic_tm_has_ltype_open_one_fresh. exact Hy.
  - apply basic_tm_has_ltype_close_one_fresh. exact Hy.
Qed.

Lemma formula_open_expr_basic_typing_formula k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  formula_open k y (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T.
Proof.
  intros Hy.
  unfold expr_basic_typing_formula, expr_basic_typing_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    apply basic_tm_has_ltype_open_one_fresh_iff. exact Hy.
Qed.

Lemma basic_typing_lty_env_to_atom_env_fv_subset Σ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  fv_tm e ⊆ lvars_fv (dom Σ).
Proof.
  intros Hty.
  pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
  pose proof (lvar_store_to_atom_store_dom_subset Σ) as Hdom.
  unfold lty_env_atom_dom, lvar_store_atom_dom in Hdom.
  set_solver.
Qed.

Lemma context_ty_wf_lqual_denote_iff Σ τ (m : WfWorldT) :
  logic_qualifier_denote (context_ty_wf_lqual Σ τ) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  unfold context_ty_wf_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma context_ty_wf_formula_models_iff Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  unfold res_models, context_ty_wf_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply context_ty_wf_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply context_ty_wf_lqual_denote_iff. exact Hden.
Qed.

Lemma context_ty_wf_formula_scope_dom Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT).
Proof.
  intros Hmodels.
  apply context_ty_wf_formula_models_iff in Hmodels as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma context_ty_wf_formula_basic_lvars Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  intros Hmodels.
  apply context_ty_wf_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma context_ty_wf_formula_fv_cty_subset Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hmodels.
  pose proof (context_ty_wf_formula_basic_lvars Σ τ m Hmodels)
    as [Hvars _].
  rewrite <- context_ty_lvars_fv.
  apply lvars_fv_mono. exact Hvars.
Qed.

Lemma context_ty_wf_formula_insert_fresh_lvar
    (Σ : lty_env) τ (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models m (context_ty_wf_formula Σ τ) ->
  res_models mx (context_ty_wf_formula (<[LVFree x := T]> Σ) τ).
Proof.
  intros HxΣ Hout Hext Hm.
  apply context_ty_wf_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  apply context_ty_wf_formula_models_iff.
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
    + change (basic_context_ty_lvars
        (dom ((<[LVFree x := T]> (Σ : gmap logic_var ty))
          : gmap logic_var ty)) τ).
      apply basic_context_ty_lvars_insert_fresh. exact Hbasic.
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

Lemma expr_basic_typing_formula_tapp_tm_tlete_assoc
    (Σ : lty_env) e1 e2 y T (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  res_models m (expr_basic_typing_formula Σ
    (tlete e1 (tapp_tm e2 (vfvar y))) T) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm (tlete e1 e2) (vfvar y)) T).
Proof.
  intros Hlc Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [HlcΣ [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split; [exact Hsub|].
  eapply basic_tm_has_ltype_tapp_tm_tlete_assoc; eauto.
Qed.

Lemma expr_basic_typing_formula_tapp_tm_tlete_assoc_rev
    (Σ : lty_env) e1 e2 y T (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm (tlete e1 e2) (vfvar y)) T) ->
  res_models m (expr_basic_typing_formula Σ
    (tlete e1 (tapp_tm e2 (vfvar y))) T).
Proof.
  intros Hlc Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [HlcΣ [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split; [exact Hsub|].
  eapply basic_tm_has_ltype_tapp_tm_tlete_assoc_rev; eauto.
Qed.

Lemma res_models_open_expr_basic_typing_to_open
    k y Σ e T (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  res_models m (formula_open k y (expr_basic_typing_formula Σ e T)) ->
  res_models m
    (expr_basic_typing_formula
      (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T).
Proof.
  intros Hy Hmodels.
  unfold res_models, expr_basic_typing_formula, expr_basic_typing_lqual in Hmodels.
  cbn [formula_open lqual_open formula_measure res_models_fuel] in Hmodels.
  destruct Hmodels as [_ Hden].
  unfold logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split.
  - rewrite lty_env_open_one_dom. exact Hlc.
  - split.
    + rewrite lty_env_open_one_dom. exact Hsub.
    + apply basic_tm_has_ltype_open_one_fresh; assumption.
Qed.

Lemma res_models_open_expr_basic_typing_bind0_to_open
    y Σ T e U (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  res_models m
    (formula_open 0 y (expr_basic_typing_formula (typed_lty_env_bind Σ T) e U)) ->
  res_models m
    (expr_basic_typing_formula
      (<[LVFree y := T]> Σ) (open_tm 0 (vfvar y) e) U).
Proof.
  intros Hfresh Hclosed Hye Hmodels.
  apply res_models_open_expr_basic_typing_to_open in Hmodels.
  - rewrite typed_lty_env_bind_open_current in Hmodels by assumption.
    exact Hmodels.
  - rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hy.
    apply elem_of_union in Hy as [HyΣ|Hy]; [|exact (Hye Hy)].
    apply Hfresh. apply lvars_fv_elem. exact HyΣ.
Qed.

Lemma res_models_open_expr_basic_typing_iff
    k y Σ e T (m : WfWorldT) :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  res_models m (formula_open k y (expr_basic_typing_formula Σ e T)) <->
  res_models m
    (expr_basic_typing_formula
      (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T).
Proof.
  intros Hy. split.
  - apply res_models_open_expr_basic_typing_to_open.
    exact Hy.
  - intros Hmodels.
    apply expr_basic_typing_formula_models_iff in Hmodels
      as [Hlc [Hsub Hbasic]].
    unfold res_models, expr_basic_typing_formula, expr_basic_typing_lqual.
    cbn [formula_open lqual_open formula_measure res_models_fuel].
    split.
    + rewrite lty_env_open_one_dom in Hsub. exact Hsub.
    + unfold logic_qualifier_denote.
      cbn [lqual_dom lqual_prop].
      split.
      * rewrite lty_env_open_one_dom in Hlc. exact Hlc.
      * split.
        -- rewrite lty_env_open_one_dom in Hsub. exact Hsub.
        -- eapply basic_tm_has_ltype_close_one_fresh; eauto.
Qed.

Lemma res_models_open_expr_basic_typing_bind0_iff
    y Σ T e U (m : WfWorldT) :
  LVFree y ∉ dom Σ ->
  lty_env_closed Σ ->
  y ∉ fv_tm e ->
  res_models m
    (formula_open 0 y (expr_basic_typing_formula (typed_lty_env_bind Σ T) e U)) <->
  res_models m
    (expr_basic_typing_formula
      (<[LVFree y := T]> Σ) (open_tm 0 (vfvar y) e) U).
Proof.
  intros Hfresh Hclosed Hye.
  rewrite (res_models_open_expr_basic_typing_iff
    0 y (typed_lty_env_bind Σ T) e U m).
  - rewrite typed_lty_env_bind_open_current by assumption.
    reflexivity.
  - rewrite typed_lty_env_bind_lvars_fv_dom.
    intros Hy.
    apply elem_of_union in Hy as [HyΣ|Hy]; [|exact (Hye Hy)].
    apply Hfresh. apply lvars_fv_elem. exact HyΣ.
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

Lemma context_ty_wf_formula_drop_fresh_lvar
    (Σ : lty_env) (τ : context_ty) (m mx : WfWorldT) x T Fx :
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  ext_out Fx = {[x]} ->
  res_extend_by m Fx mx ->
  res_models mx (context_ty_wf_formula (<[LVFree x := T]> Σ) τ) ->
  res_models m (context_ty_wf_formula Σ τ).
Proof.
  intros HxΣ Hxτ Hout Hext Hmx.
  apply context_ty_wf_formula_models_iff in Hmx as [Hlcx [Hsubx Hbasicx]].
  apply context_ty_wf_formula_models_iff.
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
