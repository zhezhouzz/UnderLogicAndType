(** * ChoiceTypeLanguage.TypeOpen

    Multi-opening for choice types and type qualifiers.

    This file is syntax-only: it contains the finite-map opening operations
    for [choice_ty] and [type_qualifier], plus their structural laws.  The
    lvar-keyed type environment projection machinery stays in [Env.v]. *)

From ChoiceTypeLanguage Require Export MultiOpen.

Definition open_cty_env (η : gmap nat atom) (τ : choice_ty) : choice_ty :=
  map_fold (fun k x acc => cty_open k x acc) τ η.

Definition qual_open_env (η : gmap nat atom) (q : type_qualifier)
    : type_qualifier :=
  map_fold (fun k x acc => qual_open_atom k x acc) q η.

Definition qual_with_vars (D : lvset) : type_qualifier :=
  tqual D (fun _ => True).

#[global] Instance mopen_choice_ty_inst :
  MOpen (gmap nat atom) choice_ty choice_ty := open_cty_env.

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
    rewrite !(Hfold choice_ty (fun k x acc => cty_open k x acc)).
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
    rewrite !(Hfold choice_ty (fun k x acc => cty_open k x acc)).
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
    rewrite !(Hfold choice_ty (fun k x acc => cty_open k x acc)).
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
  - rewrite !(Hfold choice_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_union η τ1 τ2 :
  open_cty_env η (CTUnion τ1 τ2) =
  CTUnion (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold choice_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_sum η τ1 τ2 :
  open_cty_env η (CTSum τ1 τ2) =
  CTSum (open_cty_env η τ1) (open_cty_env η τ2).
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !map_fold_empty. reflexivity.
  - rewrite !(Hfold choice_ty (fun k x acc => cty_open k x acc)).
    cbn [cty_open]. rewrite IH. reflexivity.
Qed.

Lemma open_cty_env_arrow η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTArrow τx τ) =
  CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  revert τx τ.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τx τ _. rewrite open_env_lift_empty, !open_cty_env_empty.
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
      by (try apply open_env_lift_lookup_none;
          try apply open_env_avoids_atom_lift;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_wand η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTWand τx τ) =
  CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  revert τx τ.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros τx τ _. rewrite open_env_lift_empty, !open_cty_env_empty.
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
      by (try apply open_env_lift_lookup_none;
          try apply open_env_avoids_atom_lift;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_over η b q :
  open_env_values_inj η ->
  open_cty_env η (CTOver b q) =
  CTOver b (qual_open_env (open_env_lift η) q).
Proof.
  revert q.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite open_env_lift_empty, open_cty_env_empty, qual_open_env_empty.
    reflexivity.
  - intros q Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH q Hinjη).
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh
      by (try apply open_env_lift_lookup_none;
          try apply open_env_avoids_atom_lift;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_under η b q :
  open_env_values_inj η ->
  open_cty_env η (CTUnder b q) =
  CTUnder b (qual_open_env (open_env_lift η) q).
Proof.
  revert q.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite open_env_lift_empty, open_cty_env_empty, qual_open_env_empty.
    reflexivity.
  - intros q Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_cty_env_insert_fresh by assumption.
    rewrite (IH q Hinjη).
    cbn [cty_open].
    rewrite open_env_lift_insert.
    rewrite qual_open_env_insert_fresh
      by (try apply open_env_lift_lookup_none;
          try apply open_env_avoids_atom_lift;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma open_cty_env_preserves_erasure η τ :
  erase_ty (open_cty_env η τ) = erase_ty τ.
Proof.
  unfold open_cty_env.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite map_fold_empty. reflexivity.
  - rewrite (Hfold choice_ty (fun k x acc => cty_open k x acc)).
    rewrite cty_open_preserves_erasure. exact IH.
Qed.

Lemma qual_open_env_vars η q :
  open_env_fresh_for_lvars η (qual_vars q) ->
  qual_vars (qual_open_env η q) = lvars_open_env η (qual_vars q).
Proof.
  revert q.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros q _. rewrite qual_open_env_empty, lvars_open_env_empty. reflexivity.
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
  CTArrow (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  intros Hinj. rewrite open_cty_env_arrow by exact Hinj. reflexivity.
Qed.

Lemma open_cty_env_wand_vars_equiv η τx τ :
  open_env_values_inj η ->
  open_cty_env η (CTWand τx τ) ≡τv
  CTWand (open_cty_env η τx) (open_cty_env (open_env_lift η) τ).
Proof.
  intros Hinj. rewrite open_cty_env_wand by exact Hinj. reflexivity.
Qed.

Lemma open_cty_env_over_vars_equiv η b q :
  open_env_values_inj η ->
  open_env_fresh_for_lvars (open_env_lift η) (qual_vars q) ->
  open_cty_env η (CTOver b q) ≡τv
  CTOver b (qual_with_vars (lvars_open_env (open_env_lift η) (qual_vars q))).
Proof.
  intros Hinj Hfresh.
  rewrite open_cty_env_over by exact Hinj.
  cbn [cty_vars_equiv qual_with_vars qual_vars qual_lvars].
  split; [reflexivity|].
  apply qual_open_env_vars. exact Hfresh.
Qed.

Lemma open_cty_env_under_vars_equiv η b q :
  open_env_values_inj η ->
  open_env_fresh_for_lvars (open_env_lift η) (qual_vars q) ->
  open_cty_env η (CTUnder b q) ≡τv
  CTUnder b (qual_with_vars (lvars_open_env (open_env_lift η) (qual_vars q))).
Proof.
  intros Hinj Hfresh.
  rewrite open_cty_env_under by exact Hinj.
  cbn [cty_vars_equiv qual_with_vars qual_vars qual_lvars].
  split; [reflexivity|].
  apply qual_open_env_vars. exact Hfresh.
Qed.

Lemma open_cty_env_lift_shift0_vars_equiv η τ :
  open_env_values_inj η ->
  open_cty_env (open_env_lift η) (cty_shift 0 τ) ≡τv
  cty_shift 0 (open_cty_env η τ).
Proof.
  unfold open_cty_env.
  refine (fin_maps.map_fold_ind
    (fun η =>
      open_env_values_inj η ->
      map_fold (fun k x acc => cty_open k x acc)
        (cty_shift 0 τ) (open_env_lift η) ≡τv
      cty_shift 0
        (map_fold (fun k x acc => cty_open k x acc) τ η)) _ _ η).
  - intros _. rewrite open_env_lift_empty, !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH Hinj.
    pose proof (open_env_values_inj_insert_inv η' k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert.
    change (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
      (cty_shift 0 τ) (<[S k:=x]> (open_env_lift η')))
      with (open_cty_env (<[S k := x]> (open_env_lift η'))
        (cty_shift 0 τ)).
    transitivity
      (cty_open (S k) x
        (open_cty_env (open_env_lift η') (cty_shift 0 τ))).
    { apply open_cty_env_insert_fresh_vars_equiv.
      - apply open_env_lift_lookup_none. exact Hfresh.
      - apply open_env_avoids_atom_lift. exact Havoid.
      - apply open_env_values_inj_lift. exact Hinjη. }
    change (open_cty_env (open_env_lift η') (cty_shift 0 τ))
      with (map_fold (fun k0 x0 acc => cty_open k0 x0 acc)
        (cty_shift 0 τ) (open_env_lift η')).
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
