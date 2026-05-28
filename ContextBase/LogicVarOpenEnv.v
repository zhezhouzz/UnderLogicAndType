(** * ContextBase.LogicVarOpenEnv

    Finite simultaneous opening environments for logic-variable sets. *)

From ContextBase Require Export LogicVarAtoms.

Definition logic_var_open_env
    (η : gmap nat atom) (v : logic_var) : logic_var :=
  match v with
  | LVFree x => LVFree x
  | LVBound k =>
      match η !! k with
      | Some x => LVFree x
      | None => LVBound k
      end
  end.

Definition open_env_avoids_atom (x : atom) (η : gmap nat atom) : Prop :=
  forall k, η !! k <> Some x.

Definition lvars_open_env (η : gmap nat atom) (D : lvset) : lvset :=
  set_map (logic_var_open_env η) D.

Definition lvars_open_env_simul
    (η : gmap nat atom) (D : lvset) : lvset :=
  lvars_open_env η D.

Definition open_env_fresh_for_lvars
    (η : gmap nat atom) (D : lvset) : Prop :=
  forall k x,
    η !! k = Some x ->
    x ∉ lvars_fv (lvars_open_env (delete k η) D).

Definition logic_var_open_env_inj_on η (D : lvset) : Prop :=
  forall v1 v2,
    v1 ∈ D ->
    v2 ∈ D ->
    logic_var_open_env η v1 = logic_var_open_env η v2 ->
    v1 = v2.

Lemma logic_var_open_env_empty v :
  logic_var_open_env ∅ v = v.
Proof.
  destruct v as [k|x]; cbn [logic_var_open_env].
  - rewrite lookup_empty. reflexivity.
  - reflexivity.
Qed.

Lemma logic_var_open_env_singleton_fresh k x v :
  v <> LVFree x ->
  logic_var_open_env (<[k := x]> ∅) v = logic_var_open k x v.
Proof.
  intros Hfresh.
  destruct v as [j|y]; cbn [logic_var_open_env logic_var_open].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert_eq.
      rewrite logic_var_open_unfold, swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_empty.
      rewrite logic_var_open_unfold.
      rewrite swap_fresh by congruence. reflexivity.
  - rewrite logic_var_open_unfold.
    assert (Hyx : y <> x).
    { intros ->. apply Hfresh. reflexivity. }
    rewrite swap_fresh by congruence. reflexivity.
Qed.

Lemma logic_var_open_env_open_one_fresh η k x v :
  v <> LVFree x ->
  logic_var_open_env η (logic_var_open k x v) =
  logic_var_open_env (<[k := x]> η) v.
Proof.
  intros Hfresh.
  destruct v as [j|y]; cbn [logic_var_open_env logic_var_open].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite logic_var_open_unfold, swap_l.
      cbn [logic_var_open_env]. rewrite lookup_insert_eq. reflexivity.
    + rewrite logic_var_open_unfold.
      rewrite swap_fresh by congruence.
      cbn [logic_var_open_env]. rewrite lookup_insert_ne by congruence.
      reflexivity.
  - rewrite logic_var_open_unfold.
    assert (Hyx : y <> x).
    { intros ->. apply Hfresh. reflexivity. }
    rewrite swap_fresh by congruence. reflexivity.
Qed.

Lemma logic_var_open_env_open_fresh η k x v :
  η !! k = None ->
  open_env_avoids_atom x η ->
  logic_var_open_env η (logic_var_open k x v) =
  logic_var_open k x (logic_var_open_env η v).
Proof.
  intros Hη Havoid.
  destruct v as [j|y]; cbn [logic_var_open_env logic_var_open].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite logic_var_open_unfold, swap_l.
      cbn [logic_var_open_env]. rewrite Hη.
      rewrite logic_var_open_unfold, swap_l. reflexivity.
    + rewrite logic_var_open_unfold, swap_fresh by congruence.
      cbn [logic_var_open_env].
      destruct (η !! j) as [z|] eqn:Hηj.
      * assert (z <> x).
        { intros ->. specialize (Havoid j). contradiction. }
        rewrite logic_var_open_unfold, swap_fresh by congruence.
        reflexivity.
      * rewrite logic_var_open_unfold, swap_fresh by congruence.
        reflexivity.
  - destruct (decide (y = x)) as [->|Hyx].
    + rewrite logic_var_open_unfold, swap_r.
      cbn [logic_var_open_env]. rewrite Hη.
      reflexivity.
    + rewrite logic_var_open_unfold, swap_fresh by congruence.
      reflexivity.
Qed.

Lemma logic_var_open_env_insert_fresh η k x v :
  η !! k = None ->
  logic_var_open_env η v <> LVFree x ->
  logic_var_open_env (<[k := x]> η) v =
  logic_var_open k x (logic_var_open_env η v).
Proof.
  intros Hη Hfresh.
  destruct v as [j|y]; cbn [logic_var_open_env].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert_eq, Hη.
      rewrite logic_var_open_unfold, swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      destruct (η !! j) as [z|] eqn:Hηj.
      * rewrite logic_var_open_unfold.
        assert (Hzx : z <> x).
        { intros ->. apply Hfresh.
          cbn [logic_var_open_env]. rewrite Hηj. reflexivity. }
        rewrite swap_fresh by congruence. reflexivity.
      * rewrite logic_var_open_unfold.
        rewrite swap_fresh by congruence. reflexivity.
  - rewrite logic_var_open_unfold.
    assert (Hyx : y <> x).
    { intros ->. apply Hfresh. reflexivity. }
    rewrite swap_fresh by congruence. reflexivity.
Qed.

Lemma open_env_lift_empty :
  (kmap S (∅ : gmap nat atom) : gmap nat atom) = ∅.
Proof.
  apply kmap_empty.
Qed.

Lemma open_env_lift_insert k x η :
  (kmap S (<[k := x]> η) : gmap nat atom) =
  <[S k := x]> (kmap S η : gmap nat atom).
Proof.
  rewrite (kmap_insert (M1:=gmap nat) (M2:=gmap nat)
    S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η k x).
  reflexivity.
Qed.

Lemma open_env_lift_lookup_none η k :
  η !! k = None ->
  (kmap S η : gmap nat atom) !! S k = None.
Proof.
  intros Hnone.
  rewrite lookup_kmap_None.
  - intros j Hj. apply Nat.succ_inj in Hj. subst j. exact Hnone.
  - intros ? ? ?. lia.
Qed.

Lemma open_env_lift_lookup_zero_none η :
  (kmap S η : gmap nat atom) !! 0 = None.
Proof.
  rewrite lookup_kmap_None.
  - intros j Hj. lia.
  - intros ? ? ?. lia.
Qed.

Lemma open_env_avoids_atom_empty x :
  open_env_avoids_atom x ∅.
Proof.
  intros k Hbad. rewrite lookup_empty in Hbad. discriminate.
Qed.

Lemma open_env_avoids_atom_insert k x y η :
  x <> y ->
  open_env_avoids_atom x η ->
  open_env_avoids_atom x (<[k := y]> η).
Proof.
  intros Hxy Havoid j.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite lookup_insert_eq. congruence.
  - rewrite lookup_insert_ne by congruence. apply Havoid.
Qed.

Lemma open_env_avoids_atom_lift x η :
  open_env_avoids_atom x η ->
  open_env_avoids_atom x (kmap S η : gmap nat atom).
Proof.
  intros Havoid k.
  destruct k as [|k].
  - rewrite open_env_lift_lookup_zero_none. congruence.
  - destruct (η !! k) as [y|] eqn:Hη.
    + rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
        S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η k).
      intros Hxy. apply (Havoid k). exact Hxy.
    + rewrite open_env_lift_lookup_none by exact Hη. congruence.
Qed.

Lemma open_env_precompose_empty (ξ : gmap nat atom) :
  (∅ ∪ ξ) = ξ.
Proof.
  apply map_eq. intros k.
  rewrite lookup_union, lookup_empty.
  destruct (ξ !! k); reflexivity.
Qed.

Lemma open_env_precompose_empty_r (η : gmap nat atom) :
  (η ∪ ∅) = η.
Proof.
  apply map_eq. intros k.
  rewrite lookup_union, lookup_empty.
  destruct (η !! k); reflexivity.
Qed.

Lemma open_env_precompose_insert_fresh (η : gmap nat atom) k x (ξ : gmap nat atom) :
  η !! k = None ->
  ((<[k := x]> η) ∪ ξ) =
  (η ∪ (<[k := x]> ξ)).
Proof.
  intros Hfresh.
  apply map_eq. intros j.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite !lookup_union, !lookup_insert_eq.
    rewrite Hfresh. destruct (ξ !! k); reflexivity.
  - rewrite !lookup_union, !lookup_insert_ne by congruence.
    destruct (η !! j), (ξ !! j); reflexivity.
Qed.

Definition open_env_atoms (η : gmap nat atom) : aset :=
  map_fold (fun _ x acc => {[x]} ∪ acc) ∅ η.

Lemma open_env_atoms_empty :
  open_env_atoms ∅ = ∅.
Proof.
  unfold open_env_atoms.
  rewrite map_fold_empty. reflexivity.
Qed.

Lemma open_env_atoms_insert k x η :
  η !! k = None ->
  open_env_atoms (<[k := x]> η) = {[x]} ∪ open_env_atoms η.
Proof.
  intros Hfresh.
  unfold open_env_atoms.
  rewrite map_fold_insert_L.
  - reflexivity.
  - intros i j xi xj acc Hij _ _.
    better_set_solver.
  - exact Hfresh.
Qed.

Lemma open_env_atoms_lookup η k x :
  η !! k = Some x ->
  x ∈ open_env_atoms η.
Proof.
  revert k x.
  refine (fin_maps.map_fold_ind
    (fun η => forall k x, η !! k = Some x -> x ∈ open_env_atoms η)
    _ _ η).
  - intros k x Hlookup.
    rewrite lookup_empty in Hlookup. discriminate.
  - intros i y η0 Hfresh Hfold IH k x Hlookup.
    rewrite open_env_atoms_insert by exact Hfresh.
    destruct (decide (k = i)) as [->|Hki].
    + rewrite lookup_insert_eq in Hlookup. inversion Hlookup. better_set_solver.
    + rewrite lookup_insert_ne in Hlookup by congruence.
      apply elem_of_union_r. apply IH with (k := k). exact Hlookup.
Qed.

Lemma open_env_avoids_atom_of_notin_atoms x η :
  x ∉ open_env_atoms η ->
  open_env_avoids_atom x η.
Proof.
  intros Hx k Hlookup.
  apply Hx. eapply open_env_atoms_lookup. exact Hlookup.
Qed.

Lemma lvars_fv_mono (D E : lvset) :
  D ⊆ E ->
  lvars_fv D ⊆ lvars_fv E.
Proof.
  intros HDE x Hx.
  apply lvars_fv_elem.
  apply lvars_fv_elem in Hx.
  exact (HDE _ Hx).
Qed.

Lemma lvars_open_mono k x (D E : lvset) :
  D ⊆ E ->
  lvars_open k x D ⊆ lvars_open k x E.
Proof.
  intros HDE v Hv.
  unfold lvars_open in *.
  apply elem_of_map in Hv as [u [-> Hu]].
  apply elem_of_map. exists u. split; [reflexivity|].
  exact (HDE _ Hu).
Qed.

Lemma lvars_open_env_empty D :
  lvars_open_env ∅ D = D.
Proof.
  unfold lvars_open_env.
  apply set_eq. intros v.
  rewrite elem_of_map.
  split.
  - intros [u [-> Hu]]. rewrite logic_var_open_env_empty. exact Hu.
  - intros Hv. exists v. split; [symmetry; apply logic_var_open_env_empty|exact Hv].
Qed.

Lemma lvars_open_env_union η (D E : lvset) :
  lvars_open_env η (D ∪ E) =
  lvars_open_env η D ∪ lvars_open_env η E.
Proof.
  unfold lvars_open_env.
  apply set_eq. intros v.
  rewrite elem_of_union.
  repeat rewrite elem_of_map.
  split.
  - intros [u [-> Hu]].
    apply elem_of_union in Hu as [Hu|Hu].
    + left. exists u. split; [reflexivity|exact Hu].
    + right. exists u. split; [reflexivity|exact Hu].
  - intros [[u [-> Hu]]|[u [-> Hu]]].
    + exists u. split; [reflexivity|better_set_solver].
    + exists u. split; [reflexivity|better_set_solver].
Qed.

Lemma lvars_open_env_mono η (D E : lvset) :
  D ⊆ E ->
  lvars_open_env η D ⊆ lvars_open_env η E.
Proof.
  intros HDE v Hv.
  unfold lvars_open_env in *.
  apply elem_of_map in Hv as [u [-> Hu]].
  apply elem_of_map. exists u. split; [reflexivity|].
  exact (HDE _ Hu).
Qed.

Lemma lvars_fv_open_env_env_mono η ξ D :
  (forall k x, η !! k = Some x -> ξ !! k = Some x) ->
  lvars_fv (lvars_open_env η D) ⊆ lvars_fv (lvars_open_env ξ D).
Proof.
  intros Hsub x Hx.
  rewrite lvars_fv_elem in Hx |- *.
  unfold lvars_open_env in *.
  apply elem_of_map in Hx as [v [Hv HvD]].
  destruct v as [k|y]; cbn [logic_var_open_env] in Hv.
  - destruct (η !! k) as [z|] eqn:Hη.
    + inversion Hv. subst z.
      apply elem_of_map. exists (LVBound k). split; [|exact HvD].
      cbn [logic_var_open_env]. rewrite (Hsub k x Hη). reflexivity.
    + discriminate.
  - inversion Hv. subst y.
    apply elem_of_map. exists (LVFree x). split; [reflexivity|exact HvD].
Qed.

Lemma lvars_open_env_insert_fresh η k x D :
  η !! k = None ->
  x ∉ lvars_fv (lvars_open_env η D) ->
  lvars_open_env (<[k := x]> η) D =
  lvars_open k x (lvars_open_env η D).
Proof.
  intros Hη Hfresh.
  unfold lvars_open_env.
  rewrite lvars_open_unfold.
  unfold set_swap.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    exists (logic_var_open_env η u). split.
    + assert (Hnot : logic_var_open_env η u <> LVFree x).
      { intros Hbad. apply Hfresh. rewrite lvars_fv_elem.
        apply elem_of_map. exists u. split; [symmetry; exact Hbad|exact Hu]. }
      rewrite (logic_var_open_env_insert_fresh η k x u Hη Hnot).
      reflexivity.
    + apply elem_of_map. exists u. split; [reflexivity|exact Hu].
  - intros [u [-> Hu]].
    apply elem_of_map in Hu as [w [-> Hw]].
    exists w. split; [|exact Hw].
    assert (Hnot : logic_var_open_env η w <> LVFree x).
    { intros Hbad. apply Hfresh. rewrite lvars_fv_elem.
      apply elem_of_map. exists w. split; [symmetry; exact Hbad|exact Hw]. }
    rewrite (logic_var_open_env_insert_fresh η k x w Hη Hnot).
    reflexivity.
Qed.

Lemma lvars_open_env_open_one_fresh η k x D :
  x ∉ lvars_fv D ->
  lvars_open_env η (lvars_open k x D) =
  lvars_open_env (<[k := x]> η) D.
Proof.
  intros Hx.
  unfold lvars_open_env.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    exists (logic_var_open k x u). split.
    + rewrite <- logic_var_open_env_open_one_fresh.
      * rewrite logic_var_open_involutive. reflexivity.
      * intros Hbad.
        apply Hx. apply lvars_fv_elem.
        assert (HuD : logic_var_open k x u ∈ D).
        {
          apply lvars_open_elem_open with (k := k) (x := x).
          rewrite logic_var_open_involutive. exact Hu.
        }
        rewrite Hbad in HuD. exact HuD.
    + apply lvars_open_elem_open with (k := k) (x := x).
      rewrite logic_var_open_involutive. exact Hu.
  - intros [u [-> Hu]].
    exists (logic_var_open k x u). split.
    + rewrite logic_var_open_env_open_one_fresh.
      * reflexivity.
      * intros ->. apply Hx. apply lvars_fv_elem. exact Hu.
    + apply lvars_open_elem_open. exact Hu.
Qed.

Lemma lvars_open_env_simul_empty D :
  lvars_open_env_simul ∅ D = D.
Proof.
  apply lvars_open_env_empty.
Qed.

Lemma lvars_open_env_simul_fresh η D :
  open_env_fresh_for_lvars η D ->
  lvars_open_env η D = lvars_open_env_simul η D.
Proof.
  reflexivity.
Qed.

Lemma open_env_fresh_for_lvars_empty D :
  open_env_fresh_for_lvars ∅ D.
Proof.
  intros k x Hbad. rewrite lookup_empty in Hbad. discriminate.
Qed.

Lemma open_env_fresh_for_lvars_mono η (D E : lvset) :
  D ⊆ E ->
  open_env_fresh_for_lvars η E ->
  open_env_fresh_for_lvars η D.
Proof.
  intros HDE Hfresh k x Hkx Hbad.
  eapply Hfresh; [exact Hkx|].
  apply lvars_fv_mono with (D := lvars_open_env (delete k η) D).
  - apply lvars_open_env_mono. exact HDE.
  - exact Hbad.
Qed.

Lemma open_env_fresh_for_lvars_insert_head η k x D :
  η !! k = None ->
  open_env_fresh_for_lvars (<[k := x]> η) D ->
  x ∉ lvars_fv (lvars_open_env η D).
Proof.
  intros Hη Hfresh.
  specialize (Hfresh k x ltac:(rewrite lookup_insert_eq; reflexivity)).
  replace (delete k (<[k := x]> η)) with η in Hfresh; [exact Hfresh|].
  apply map_eq. intros j.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite lookup_delete_eq, Hη. reflexivity.
  - rewrite lookup_delete_ne by congruence.
    rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma open_env_fresh_for_lvars_insert_tail η k x D :
  η !! k = None ->
  open_env_fresh_for_lvars (<[k := x]> η) D ->
  open_env_fresh_for_lvars η D.
Proof.
  intros Hη Hfresh j y Hjy Hbad.
  assert (Hjk : j <> k).
  { intros ->. rewrite Hη in Hjy. discriminate. }
  eapply Hfresh.
  - rewrite lookup_insert_ne by (intros Heq; apply Hjk; symmetry; exact Heq).
    exact Hjy.
  - eapply lvars_fv_open_env_env_mono; [|exact Hbad].
    intros n z Hnz.
    destruct (decide (n = j)) as [->|Hnj].
    + rewrite lookup_delete_eq in Hnz. discriminate.
    + rewrite lookup_delete_ne in Hnz by congruence.
      destruct (decide (n = k)) as [->|Hnk].
      * rewrite Hη in Hnz. discriminate.
      * rewrite lookup_delete_ne by congruence.
        rewrite lookup_insert_ne by congruence.
        exact Hnz.
Qed.

Lemma open_env_fresh_for_lvars_insert_open_back η k x D :
  k ∈ lvars_bv D ->
  x ∉ lvars_fv D ->
  open_env_fresh_for_lvars η (lvars_open k x D) ->
  open_env_fresh_for_lvars (<[k := x]> η) D.
Proof.
  intros HkD HxD Hfresh j z Hjz Hbad.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite lookup_insert_eq in Hjz. inversion Hjz. subst z.
    assert (Hdel : delete k (<[k:=x]> η) = delete k η).
    {
      apply map_eq. intros n.
      destruct (decide (n = k)) as [->|Hnk].
      - rewrite !lookup_delete_eq. reflexivity.
      - rewrite !lookup_delete_ne by congruence.
        rewrite lookup_insert_ne by congruence. reflexivity.
    }
    rewrite Hdel in Hbad.
    apply lvars_fv_elem in Hbad.
    unfold lvars_open_env in Hbad.
    apply elem_of_map in Hbad as [v [Hv HvD]].
    destruct v as [n|y]; cbn [logic_var_open_env] in Hv.
    + destruct (delete k η !! n) as [w|] eqn:Hηn; [|discriminate].
      inversion Hv. subst w.
      rewrite lookup_delete_Some in Hηn.
	      destruct Hηn as [Hnk Hηn].
	      eapply Hfresh; [exact Hηn|].
	      apply lvars_fv_elem.
	      unfold lvars_open_env.
	      apply elem_of_map.
	      exists (LVFree x). split; [reflexivity|].
	      replace (LVFree x) with (logic_var_open k x (LVBound k)).
	      apply lvars_open_elem_open.
	      rewrite lvars_bv_elem in HkD. exact HkD.
	      rewrite logic_var_open_unfold, swap_l. reflexivity.
    + inversion Hv. subst y.
      apply HxD. apply lvars_fv_elem. exact HvD.
  - rewrite lookup_insert_ne in Hjz by congruence.
    eapply Hfresh; [exact Hjz|].
    assert (Hmap :
      delete j (<[k:=x]> η) = <[k:=x]> (delete j η)).
    {
      apply map_eq. intros n.
      destruct (decide (n = j)) as [->|Hnj].
      - rewrite lookup_delete_eq.
        rewrite lookup_insert_ne by congruence.
        rewrite lookup_delete_eq. reflexivity.
      - rewrite !lookup_delete_ne by congruence.
        destruct (decide (n = k)) as [->|Hnk].
        + rewrite !lookup_insert_eq. reflexivity.
        + rewrite !lookup_insert_ne by congruence.
          rewrite lookup_delete_ne by congruence. reflexivity.
    }
    rewrite (lvars_open_env_open_one_fresh (delete j η) k x D HxD).
    rewrite <- Hmap.
    exact Hbad.
Qed.

Lemma lvars_fv_open_env_lookup η D k x :
  η !! k = Some x ->
  LVBound k ∈ D ->
  x ∈ lvars_fv (lvars_open_env η D).
Proof.
  intros Hη Hk.
  apply lvars_fv_elem.
  unfold lvars_open_env.
  apply elem_of_map.
  exists (LVBound k). split; [|exact Hk].
  cbn [logic_var_open_env]. rewrite Hη. reflexivity.
Qed.

Lemma lvars_fv_open_env_free η D x :
  LVFree x ∈ D ->
  x ∈ lvars_fv (lvars_open_env η D).
Proof.
  intros Hx.
  apply lvars_fv_elem.
  unfold lvars_open_env.
  apply elem_of_map.
  exists (LVFree x). split; [reflexivity|exact Hx].
Qed.

Lemma open_env_fresh_for_lvars_inj_on η D :
  open_env_fresh_for_lvars η D ->
  logic_var_open_env_inj_on η D.
Proof.
  intros Hfresh v1 v2 Hv1 Hv2 Heq.
  destruct v1 as [k1|x1], v2 as [k2|x2];
    cbn [logic_var_open_env] in Heq.
  - destruct (η !! k1) as [x1|] eqn:Hη1;
      destruct (η !! k2) as [x2|] eqn:Hη2.
    + inversion Heq. subst x2.
      destruct (decide (k1 = k2)) as [->|Hne]; [reflexivity|].
      exfalso.
      eapply Hfresh; [exact Hη1|].
      apply lvars_fv_open_env_lookup with (k := k2); [|exact Hv2].
      rewrite lookup_delete_ne by congruence. exact Hη2.
    + discriminate.
    + discriminate.
    + inversion Heq. subst k2. reflexivity.
  - destruct (η !! k1) as [x|] eqn:Hη1; inversion Heq; subst.
    exfalso.
    eapply Hfresh; [exact Hη1|].
    apply lvars_fv_open_env_free. exact Hv2.
  - destruct (η !! k2) as [x|] eqn:Hη2; inversion Heq; subst.
    exfalso.
    eapply Hfresh; [exact Hη2|].
    apply lvars_fv_open_env_free. exact Hv1.
  - inversion Heq. subst x2. reflexivity.
Qed.

Lemma logic_var_to_atom_empty_open_env η v :
  logic_var_to_atom ∅ (logic_var_open_env η v) =
  logic_var_to_atom η v.
Proof.
  destruct v as [k|x]; cbn [logic_var_open_env logic_var_to_atom].
  - destruct (η !! k); reflexivity.
  - reflexivity.
Qed.

Lemma lvars_to_atoms_open_env_simul η D :
  lvars_to_atoms ∅ (lvars_open_env_simul η D) =
  lvars_to_atoms η D.
Proof.
  apply set_eq. intros x.
  rewrite !lvars_to_atoms_elem.
  unfold lvars_open_env_simul, lvars_open_env.
  split.
  - intros [v [Hv Hatom]].
    apply elem_of_map in Hv as [u [-> Hu]].
    exists u. split; [exact Hu|].
    rewrite <- logic_var_to_atom_empty_open_env. exact Hatom.
  - intros [v [Hv Hatom]].
    exists (logic_var_open_env η v). split.
    + apply elem_of_map. exists v. split; [reflexivity|exact Hv].
    + rewrite logic_var_to_atom_empty_open_env. exact Hatom.
Qed.

Lemma lvars_to_atoms_open_env_simul_union η D E :
  lvars_to_atoms ∅ (lvars_open_env_simul η (D ∪ E)) =
  lvars_to_atoms η D ∪ lvars_to_atoms η E.
Proof.
  rewrite lvars_to_atoms_open_env_simul.
  apply lvars_to_atoms_union.
Qed.
