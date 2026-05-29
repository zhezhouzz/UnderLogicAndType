(** * ContextTypeLanguage.TypeOpen

    Multi-opening for context types and type qualifiers.

    This file is syntax-only: it contains the finite-map opening operations
    for [context_ty] and [type_qualifier], plus their structural laws.  The
    lvar-keyed type environment projection machinery stays in [Env.v]. *)

From ContextTypeLanguage Require Export MultiOpen.
From ContextBase Require Import BaseTactics.

Definition open_cty_env (η : gmap nat atom) (τ : context_ty) : context_ty :=
  map_fold (fun k x acc => cty_open k x acc) τ η.

Definition qual_open_env (η : gmap nat atom) (q : type_qualifier)
    : type_qualifier :=
  map_fold (fun k x acc => qual_open_atom k x acc) q η.

Definition qual_with_vars (D : lvset) : type_qualifier :=
  tqual D (fun _ => True).

#[global] Instance mopen_context_ty_inst :
  MOpen (gmap nat atom) context_ty context_ty := open_cty_env.

Lemma open_cty_env_empty τ :
  open_cty_env ∅ τ = τ.
Proof.
  unfold open_cty_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma open_cty_env_singleton k x τ :
  open_cty_env (<[k := x]> ∅) τ = cty_open k x τ.
Proof.
  unfold open_cty_env.
  change (<[k:=x]> (∅ : gmap nat atom)) with ({[k:=x]} : gmap nat atom).
  rewrite map_fold_singleton.
  reflexivity.
Qed.

Lemma open_cty_env_insert_fresh η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env (<[k := x]> η) τ =
  cty_open k x (open_cty_env η τ).
Proof.
  intros Hfresh Havoid Hinj.
  unfold open_cty_env.
  apply (open_map_fold_insert_fresh_eq cty_open); assumption.
Qed.

Lemma qual_open_env_empty q :
  qual_open_env ∅ q = q.
Proof.
  unfold qual_open_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma qual_open_env_insert_fresh η k x q :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  qual_open_env (<[k := x]> η) q =
  qual_open_atom k x (qual_open_env η q).
Proof.
  intros Hfresh Havoid Hinj.
  unfold qual_open_env.
  apply (open_map_fold_insert_fresh_eq qual_open_atom); assumption.
Qed.

Lemma open_cty_env_cty_vars_equiv η τ1 τ2 :
  τ1 ≡τv τ2 ->
  open_cty_env η τ1 ≡τv open_cty_env η τ2.
Proof.
  unfold open_cty_env.
  revert τ1 τ2.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τ1 τ2 Hτ. rewrite !map_fold_empty. exact Hτ.
  - intros τ1 τ2 Hτ.
    rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    apply cty_vars_equiv_open. apply IH. exact Hτ.
Qed.

Lemma open_cty_env_open_fresh_vars_equiv η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env η (cty_open k x τ) ≡τv
  cty_open k x (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  revert k x τ.
  induction η as [|i xi η Hfreshi Hfold IH] using fin_maps.map_fold_ind.
  - intros k x τ _ _ _. rewrite !map_fold_empty. reflexivity.
  - intros k x τ Hk Havoid Hinj.
    assert (Hik : i <> k).
    {
      intros ->. rewrite lookup_insert in Hk.
      destruct (decide (k = k)) as [_|Hbad]; [discriminate|congruence].
    }
    assert (Hxix : xi <> x).
    {
      intros ->. apply (Havoid i). rewrite lookup_insert.
      destruct (decide (i = i)) as [_|Hbad]; [reflexivity|congruence].
    }
    assert (Hkη : η !! k = None).
    {
      rewrite lookup_insert_ne in Hk by congruence. exact Hk.
    }
    assert (Havoidη : open_env_avoids_atom x η).
    {
      intros j Hj.
      apply (Havoid j).
      destruct (decide (j = i)) as [->|Hji].
      - rewrite Hfreshi in Hj. discriminate.
      - rewrite lookup_insert_ne by congruence. exact Hj.
    }
    assert (Hinjη : open_env_values_inj η).
    {
      intros j1 j2 y Hj1 Hj2.
      apply (Hinj j1 j2 y).
      - destruct (decide (j1 = i)) as [->|Hj1i].
        + rewrite Hfreshi in Hj1. discriminate.
        + rewrite lookup_insert_ne by congruence. exact Hj1.
      - destruct (decide (j2 = i)) as [->|Hj2i].
        + rewrite Hfreshi in Hj2. discriminate.
        + rewrite lookup_insert_ne by congruence. exact Hj2.
    }
    rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    transitivity (cty_open i xi (cty_open k x
        (map_fold (fun k x acc => cty_open k x acc) τ η))).
    + apply cty_vars_equiv_open.
      apply IH; assumption.
    + rewrite cty_open_commute_fvar by assumption.
      reflexivity.
Qed.

Lemma open_cty_env_insert_fresh_vars_equiv η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env (<[k := x]> η) τ ≡τv
  cty_open k x (open_cty_env η τ).
Proof.
  intros Hfresh Havoid Hinj.
  unfold open_cty_env.
  apply (open_map_fold_insert_fresh_rel cty_vars_equiv cty_open);
    assumption.
Qed.

Lemma open_cty_env_open_one_vars_equiv η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env η (cty_open k x τ) ≡τv
  open_cty_env (<[k := x]> η) τ.
Proof.
  intros Hfresh Havoid Hinj.
  transitivity (cty_open k x (open_cty_env η τ)).
  - apply open_cty_env_open_fresh_vars_equiv; assumption.
  - symmetry. apply open_cty_env_insert_fresh_vars_equiv; assumption.
Qed.

Lemma open_cty_env_open_fresh η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env η (cty_open k x τ) =
  cty_open k x (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  revert k x τ.
  induction η as [|i xi η Hfreshi Hfold IH] using fin_maps.map_fold_ind.
  - intros k x τ _ _ _. rewrite !map_fold_empty. reflexivity.
  - intros k x τ Hk Havoid Hinj.
    assert (Hik : i <> k).
    {
      intros ->. rewrite lookup_insert in Hk.
      destruct (decide (k = k)) as [_|Hbad]; [discriminate|congruence].
    }
    assert (Hxix : xi <> x).
    {
      intros ->. apply (Havoid i). rewrite lookup_insert.
      destruct (decide (i = i)) as [_|Hbad]; [reflexivity|congruence].
    }
    assert (Hkη : η !! k = None).
    {
      rewrite lookup_insert_ne in Hk by congruence. exact Hk.
    }
    assert (Havoidη : open_env_avoids_atom x η).
    {
      intros j Hj.
      apply (Havoid j).
      destruct (decide (j = i)) as [->|Hji].
      - rewrite Hfreshi in Hj. discriminate.
      - rewrite lookup_insert_ne by congruence. exact Hj.
    }
    assert (Hinjη : open_env_values_inj η).
    {
      intros j1 j2 y Hj1 Hj2.
      apply (Hinj j1 j2 y).
      - destruct (decide (j1 = i)) as [->|Hj1i].
        + rewrite Hfreshi in Hj1. discriminate.
        + rewrite lookup_insert_ne by congruence. exact Hj1.
      - destruct (decide (j2 = i)) as [->|Hj2i].
        + rewrite Hfreshi in Hj2. discriminate.
        + rewrite lookup_insert_ne by congruence. exact Hj2.
    }
    rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    rewrite IH by assumption.
    rewrite cty_open_commute_fvar by assumption.
    reflexivity.
Qed.

Lemma open_cty_env_open_one η k x τ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_cty_env η (cty_open k x τ) =
  open_cty_env (<[k := x]> η) τ.
Proof.
  intros Hfresh Havoid Hinj.
  rewrite open_cty_env_open_fresh by assumption.
  symmetry. apply open_cty_env_insert_fresh; assumption.
Qed.

Lemma open_cty_env_inter η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) =
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_union η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) =
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_sum η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) =
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold context_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_arrow η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTArrow τx τ) =
  CTArrow (open_cty_env η τx) (open_cty_env ((kmap S η)) τ).
Proof.
  revert τx τ.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τx τ _. rewrite kmap_empty, !open_cty_env_empty.
    reflexivity.
  - intros τx τ Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH τx τ Hinjη).
    cbn [cty_open].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite open_env_lift_insert.
    rewrite open_cty_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_wand η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTWand τx τ) =
  CTWand (open_cty_env η τx) (open_cty_env ((kmap S η)) τ).
Proof.
  revert τx τ.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τx τ _. rewrite kmap_empty, !open_cty_env_empty.
    reflexivity.
  - intros τx τ Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH τx τ Hinjη).
    cbn [cty_open].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite open_env_lift_insert.
    rewrite open_cty_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_over η b q :
  open_env_values_inj η ->
  open_cty_env η (CTOver b q) =
  CTOver b (qual_open_env ((kmap S η)) q).
Proof.
  revert q.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite kmap_empty, open_cty_env_empty, qual_open_env_empty.
    reflexivity.
  - intros q Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH q Hinjη).
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_under η b q :
  open_env_values_inj η ->
  open_cty_env η (CTUnder b q) =
  CTUnder b (qual_open_env ((kmap S η)) q).
Proof.
  revert q.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite kmap_empty, open_cty_env_empty, qual_open_env_empty.
    reflexivity.
  - intros q Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH q Hinjη).
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_preserves_erasure η τ :
  erase_ty (open_cty_env η τ) = erase_ty τ.
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite map_fold_empty. reflexivity.
  - rewrite (Hfold context_ty (fun k x acc => cty_open k x acc)).
    rewrite cty_open_preserves_erasure. exact IH.
Qed.

Lemma qual_open_env_vars η q :
  open_env_fresh_for_lvars η (qual_vars q) ->
  qual_vars (qual_open_env η q) = lvars_open_env η (qual_vars q).
Proof.
  revert q.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite qual_open_env_empty. better_base_solver.
  - intros q Hfresh.
    pose proof (IH q ltac:(eapply open_env_fresh_for_lvars_insert_tail; eassumption))
      as HIH.
    change (qual_vars
      (map_fold (fun k x acc => qual_open_atom k x acc) q (<[k:=x]> η)) =
      lvars_open_env (<[k:=x]> η) (qual_vars q)).
    rewrite (Hfold type_qualifier (fun k x acc => qual_open_atom k x acc)).
    fold (qual_open_env η q).
    rewrite qual_open_atom_vars.
    rewrite HIH.
    rewrite lvars_open_env_insert_fresh.
    + reflexivity.
    + exact Hnone.
    + eapply open_env_fresh_for_lvars_insert_head; eassumption.
Qed.

Lemma context_ty_lvars_open_cty_env η τ :
  open_env_fresh_for_lvars η (context_ty_lvars τ) ->
  context_ty_lvars (open_cty_env η τ) =
  lvars_open_env η (context_ty_lvars τ).
Proof.
  revert τ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros τ _. rewrite open_cty_env_empty. better_base_solver.
  - intros τ Hfresh.
    pose proof (IH τ ltac:(eapply open_env_fresh_for_lvars_insert_tail; eassumption))
      as HIH.
    change (context_ty_lvars
      (map_fold (fun k x acc => cty_open k x acc) τ (<[k:=x]> η)) =
      lvars_open_env (<[k:=x]> η) (context_ty_lvars τ)).
    rewrite (Hfold context_ty (fun k x acc => cty_open k x acc)).
    fold (open_cty_env η τ).
    rewrite cty_open_vars.
    unfold context_ty_open_lvars.
    replace (context_ty_lvars (open_cty_env η τ))
      with (lvars_open_env η (context_ty_lvars τ)) by (symmetry; exact HIH).
    rewrite lvars_open_env_insert_fresh.
    + reflexivity.
    + exact Hnone.
    + eapply open_env_fresh_for_lvars_insert_head; eassumption.
Qed.

Lemma lvars_open_env_lift_qual_vars_difference_bound0 η q :
  open_env_fresh_for_lvars ((kmap S η)) (qual_vars q) ->
  lvars_open_env ((kmap S η)) (qual_vars q ∖ {[LVBound 0]}) =
  qual_vars (qual_open_env ((kmap S η)) q) ∖ {[LVBound 0]}.
Proof.
  intros Hfresh.
  rewrite qual_open_env_vars by exact Hfresh.
  apply set_eq. intros v.
  rewrite elem_of_difference.
  unfold lvars_open_env.
  split.
  - intros Hv.
    apply elem_of_map in Hv as [u [-> Hu]].
    apply elem_of_difference in Hu as [HuD Hu0].
    split.
    + apply elem_of_map. exists u. split; [reflexivity|exact HuD].
    + intros Hbad. apply Hu0.
      rewrite elem_of_singleton in Hbad |- *.
      destruct u as [n|a]; cbn [logic_var_open_env] in Hbad.
      * destruct n as [|n].
        -- rewrite open_env_lift_lookup_zero_none in Hbad.
           reflexivity.
        -- destruct ((kmap S η) !! S n); discriminate.
      * discriminate.
  - intros [Hv Hnot].
    apply elem_of_map in Hv as [u [-> HuD]].
    apply elem_of_map.
    exists u. split; [reflexivity|].
    apply elem_of_difference. split; [exact HuD|].
    intros Hbad. apply Hnot.
    rewrite elem_of_singleton in Hbad |- *.
    subst u.
    cbn [logic_var_open_env].
    better_base_solver.
Qed.

Lemma lvars_fv_open_env_lift_subset_at_depth1 η D :
  lvars_fv (lvars_open_env ((kmap S η)) D) ⊆
  lvars_fv (lvars_open_env η (lvars_at_depth 1 D)).
Proof.
  intros x Hx.
  apply lvars_fv_elem in Hx.
  unfold lvars_open_env in Hx.
  apply elem_of_map in Hx as [v [Hv Hvd]].
  apply lvars_fv_elem.
  unfold lvars_open_env.
  apply elem_of_map.
  destruct v as [n|a].
  - cbn [logic_var_open_env] in Hv.
    destruct n as [|n].
    + rewrite open_env_lift_lookup_zero_none in Hv. discriminate.
    + rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
        S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η n) in Hv.
      destruct (η !! n) as [y|] eqn:Hηn; [|discriminate].
      inversion Hv. subst y.
      exists (LVBound n). split.
      * cbn [logic_var_open_env]. rewrite Hηn. reflexivity.
      * rewrite lvars_at_depth_elem.
        exists (LVBound (S n)). split; [exact Hvd|].
        cbn [logic_var_at_depth].
        rewrite decide_True by lia.
        replace (S n - 1) with n by lia. reflexivity.
  - cbn [logic_var_open_env] in Hv. inversion Hv. subst a.
    exists (LVFree x). split; [reflexivity|].
    rewrite lvars_at_depth_elem.
    exists (LVFree x). split; [exact Hvd|reflexivity].
Qed.

Lemma open_env_lift_fresh_for_lvars_at_depth1 η D :
  open_env_fresh_for_lvars η (lvars_at_depth 1 D) ->
  open_env_fresh_for_lvars ((kmap S η)) D.
Proof.
  intros Hfresh j x Hjx Hbad.
  destruct j as [|j].
  - rewrite open_env_lift_lookup_zero_none in Hjx. discriminate.
  - apply lookup_kmap_Some in Hjx as [i [HSi Hηi]].
    2:{ intros ? ? ?. lia. }
    injection HSi as ->.
    eapply Hfresh; [exact Hηi|].
    replace (delete (S i) ((kmap S η))) with
      (kmap S (delete i η) : gmap nat atom) in Hbad.
    2:{
      exact (@kmap_delete nat (gmap nat) _ _ _ _ _ _ _ _ _
        nat (gmap nat) _ _ _ _ _ _ _ _ _
        S (ltac:(intros ? ? ?; lia)) atom η i).
    }
    eapply lvars_fv_open_env_lift_subset_at_depth1. exact Hbad.
Qed.

Lemma open_env_lift_fresh_for_bound0_singleton η :
  open_env_fresh_for_lvars ((kmap S η)) ({[LVBound 0]}).
Proof.
  intros i x Hi Hbad.
  apply lvars_fv_elem in Hbad.
  unfold lvars_open_env in Hbad.
  apply elem_of_map in Hbad as [v [Hv HvIn]].
  apply elem_of_singleton in HvIn. subst v.
  cbn [logic_var_open_env] in Hv.
  assert (Hnone : delete i (kmap S η : gmap nat atom) !! 0 = None).
  {
    destruct (decide (i = 0)) as [->|Hi0].
    - rewrite lookup_delete_eq. reflexivity.
    - rewrite lookup_delete_ne by congruence.
      apply open_env_lift_lookup_zero_none.
  }
  rewrite Hnone in Hv. discriminate.
Qed.

Lemma logic_var_open_env_lift_bound0 η :
  logic_var_open_env ((kmap S η)) (LVBound 0) = LVBound 0.
Proof.
  cbn [logic_var_open_env].
  rewrite open_env_lift_lookup_zero_none. reflexivity.
Qed.

Lemma open_env_fresh_for_bound0_singleton_nozero η :
  η !! 0 = None ->
  open_env_fresh_for_lvars η ({[LVBound 0]}).
Proof.
  intros Hzero i x Hi Hbad.
  apply lvars_fv_elem in Hbad.
  unfold lvars_open_env in Hbad.
  apply elem_of_map in Hbad as [v [Hv HvIn]].
  apply elem_of_singleton in HvIn. subst v.
  cbn [logic_var_open_env] in Hv.
  assert (Hnone : delete i η !! 0 = None).
  {
    destruct (decide (i = 0)) as [->|Hi0].
    - rewrite lookup_delete_eq. reflexivity.
    - rewrite lookup_delete_ne by congruence. exact Hzero.
  }
  rewrite Hnone in Hv. discriminate.
Qed.

Lemma open_cty_env_inter_vars_equiv η τ1 τ2 :
  open_cty_env η (CTInter τ1 τ2) ≡τv
  CTInter (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  rewrite open_cty_env_inter. reflexivity.
Qed.

Lemma open_cty_env_union_vars_equiv η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) ≡τv
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  rewrite open_cty_env_union. reflexivity.
Qed.

Lemma open_cty_env_sum_vars_equiv η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) ≡τv
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  rewrite open_cty_env_sum. reflexivity.
Qed.

Lemma open_cty_env_arrow_vars_equiv η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTArrow τx τ) ≡τv
  CTArrow (open_cty_env η τx) (open_cty_env ((kmap S η)) τ).
Proof.
  intros Hinj. rewrite open_cty_env_arrow by exact Hinj. reflexivity.
Qed.

Lemma open_cty_env_wand_vars_equiv η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTWand τx τ) ≡τv
  CTWand (open_cty_env η τx) (open_cty_env ((kmap S η)) τ).
Proof.
  intros Hinj. rewrite open_cty_env_wand by exact Hinj. reflexivity.
Qed.

Lemma open_cty_env_over_vars_equiv η b q :
  open_env_values_inj η ->
  open_env_fresh_for_lvars ((kmap S η)) (qual_vars q) ->
  open_cty_env η (CTOver b q) ≡τv
  CTOver b (qual_with_vars (lvars_open_env ((kmap S η)) (qual_vars q))).
Proof.
  intros Hinj Hfresh.
  rewrite open_cty_env_over by exact Hinj.
  cbn [cty_vars_equiv qual_with_vars qual_vars qual_lvars].
  split; [reflexivity|].
  apply qual_open_env_vars. exact Hfresh.
Qed.

Lemma open_cty_env_under_vars_equiv η b q :
  open_env_values_inj η ->
  open_env_fresh_for_lvars ((kmap S η)) (qual_vars q) ->
  open_cty_env η (CTUnder b q) ≡τv
  CTUnder b (qual_with_vars (lvars_open_env ((kmap S η)) (qual_vars q))).
Proof.
  intros Hinj Hfresh.
  rewrite open_cty_env_under by exact Hinj.
  cbn [cty_vars_equiv qual_with_vars qual_vars qual_lvars].
  split; [reflexivity|].
  apply qual_open_env_vars. exact Hfresh.
Qed.

Lemma open_cty_env_lift_shift0_vars_equiv η τ :
  open_env_values_inj η ->
  open_cty_env ((kmap S η)) (cty_shift 0 τ) ≡τv
  cty_shift 0 (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      open_env_values_inj η ->
      map_fold (fun k x acc => cty_open k x acc)
        (cty_shift 0 τ) ((kmap S η)) ≡τv
      cty_shift 0
        (map_fold (fun k x acc => cty_open k x acc) τ η)) _ _ η).
  - intros _. rewrite kmap_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH Hinj.
    pose proof (open_env_values_inj_insert_inv η' k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert.
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
      (cty_shift 0 τ) (<[S k:=x]> (kmap S η')))
      with (open_cty_env (<[S k := x]> (kmap S η'))
        (cty_shift 0 τ)).
    transitivity
      (cty_open (S k) x
        (open_cty_env (kmap S η') (cty_shift 0 τ))).
	    { apply open_cty_env_insert_fresh_vars_equiv.
	      - better_base_solver.
	      - better_base_solver.
	      - apply open_env_values_inj_lift. exact Hinjη. }
    change (open_cty_env (kmap S η') (cty_shift 0 τ))
      with (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
        (cty_shift 0 τ) (kmap S η')).
    transitivity
      (cty_open (S k) x
        (cty_shift 0
          (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ η'))).
    { apply cty_vars_equiv_open. apply IH. exact Hinjη. }
    transitivity
      (cty_shift 0
        (cty_open k x
          (map_fold (fun k0 x0 acc => cty_open k0 x0 acc) τ η'))).
    { rewrite cty_open_shift_under_gen by lia. reflexivity. }
    apply cty_vars_equiv_shift_from.
    symmetry. apply open_cty_env_insert_fresh_vars_equiv; assumption.
Qed.

Lemma open_cty_env_lift_shift0_exact η τ :
  open_env_values_inj η ->
  open_cty_env ((kmap S η)) (cty_shift 0 τ) =
  cty_shift 0 (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      open_env_values_inj η ->
      map_fold (fun k x acc => cty_open k x acc)
        (cty_shift 0 τ) ((kmap S η)) =
      cty_shift 0
        (map_fold (fun k x acc => cty_open k x acc) τ η)) _ _ η).
  - intros _. rewrite kmap_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH Hinj.
    pose proof (open_env_values_inj_insert_inv η' k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert.
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
      (cty_shift 0 τ) (<[S k:=x]> (kmap S η')))
      with (open_cty_env (<[S k := x]> (kmap S η'))
        (cty_shift 0 τ)).
	    rewrite open_cty_env_insert_fresh.
	    2:{ better_base_solver. }
	    2:{ better_base_solver. }
    2:{ apply open_env_values_inj_lift. exact Hinjη. }
    change (open_cty_env (kmap S η') (cty_shift 0 τ))
      with (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
        (cty_shift 0 τ) (kmap S η')).
    rewrite IH by exact Hinjη.
    rewrite cty_open_shift_under_gen by lia.
    change (cty_shift 0 (cty_open k x (open_cty_env η' τ)) =
      cty_shift 0 (open_cty_env (<[k:=x]> η') τ)).
    rewrite open_cty_env_insert_fresh by assumption.
    reflexivity.
Qed.
