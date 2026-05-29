(** * ContextBase.LogicVarOpenEnv

    Finite simultaneous opening environments for logic-variable sets. *)

From ContextBase Require Export LogicVar.

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

Notation open_env_atom_swap :=
  (fun x y η => swap x y <$> η) (only parsing).

Lemma logic_var_open_env_empty v :
  logic_var_open_env ∅ v = v.
Proof.
  destruct v as [k|x]; cbn [logic_var_open_env].
  - rewrite lookup_empty. reflexivity.
  - reflexivity.
Qed.

Lemma logic_var_open_env_not_free_of_lvars_fv η D x v :
  v ∈ D ->
  x ∉ lvars_fv (lvars_open_env η D) ->
  logic_var_open_env η v <> LVFree x.
Proof.
  intros Hv Hfresh Hbad.
  apply Hfresh. rewrite lvars_fv_elem.
  apply elem_of_map. exists v. split; [symmetry; exact Hbad|exact Hv].
Qed.

Lemma logic_var_open_env_singleton_fresh k x v :
  v <> LVFree x ->
  logic_var_open_env (<[k := x]> ∅) v = logic_var_open k x v.
Proof.
  intros Hfresh.
  destruct v as [j|y]; cbn [logic_var_open_env].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert_eq.
      rewrite swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_empty.
      rewrite swap_fresh by congruence. reflexivity.
  - assert (Hyx : y <> x).
    { intros ->. apply Hfresh. reflexivity. }
    rewrite swap_fresh by congruence. reflexivity.
Qed.

Lemma logic_var_open_env_open_one_fresh η k x v :
  v <> LVFree x ->
  logic_var_open_env η (logic_var_open k x v) =
  logic_var_open_env (<[k := x]> η) v.
Proof.
  intros Hfresh.
  destruct v as [j|y]; cbn [logic_var_open_env].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite swap_l.
      cbn [logic_var_open_env]. rewrite lookup_insert_eq. reflexivity.
    + rewrite swap_fresh by congruence.
      cbn [logic_var_open_env]. rewrite lookup_insert_ne by congruence.
      reflexivity.
  - assert (Hyx : y <> x).
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
  destruct v as [j|y]; cbn [logic_var_open_env].
  - destruct (decide (j = k)) as [->|Hjk].
    + rewrite swap_l.
      cbn [logic_var_open_env]. rewrite Hη.
      rewrite swap_l. reflexivity.
    + rewrite swap_fresh by congruence.
      cbn [logic_var_open_env].
      destruct (η !! j) as [z|] eqn:Hηj.
      * assert (z <> x).
        { intros ->. specialize (Havoid j). contradiction. }
        rewrite swap_fresh by congruence.
        reflexivity.
      * rewrite swap_fresh by congruence.
        reflexivity.
  - destruct (decide (y = x)) as [->|Hyx].
    + rewrite swap_r.
      cbn [logic_var_open_env]. rewrite Hη.
      reflexivity.
    + rewrite swap_fresh by congruence.
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
      rewrite swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      destruct (η !! j) as [z|] eqn:Hηj.
      * assert (Hzx : z <> x).
        { intros ->. apply Hfresh.
          cbn [logic_var_open_env]. rewrite Hηj. reflexivity. }
        rewrite swap_fresh by congruence. reflexivity.
      * rewrite swap_fresh by congruence. reflexivity.
  - assert (Hyx : y <> x).
    { intros ->. apply Hfresh. reflexivity. }
    rewrite swap_fresh by congruence. reflexivity.
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

Lemma open_env_atom_swap_lookup (x y : atom) (η : gmap nat atom) (k : nat) :
  open_env_atom_swap x y η !! k =
  swap x y <$> (η !! k).
Proof.
  apply lookup_fmap.
Qed.

Lemma open_env_atom_swap_dom (x y : atom) (η : gmap nat atom) :
  dom (open_env_atom_swap x y η) = dom η.
Proof.
  apply dom_fmap_L.
Qed.

Lemma open_env_atom_swap_involutive (x y : atom) (η : gmap nat atom) :
  open_env_atom_swap x y (open_env_atom_swap x y η) = η.
Proof.
  apply map_eq. intros k.
  rewrite !open_env_atom_swap_lookup.
  destruct (η !! k) as [a|]; cbn.
  - rewrite swap_involutive. reflexivity.
  - reflexivity.
Qed.

Lemma open_env_atom_swap_delete (x y : atom) (η : gmap nat atom) (k : nat) :
  delete k (open_env_atom_swap x y η) =
  open_env_atom_swap x y (delete k η).
Proof.
  apply map_eq. intros j.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite lookup_delete_eq.
    rewrite lookup_fmap, lookup_delete_eq.
    reflexivity.
  - rewrite lookup_delete_ne by congruence.
    rewrite !lookup_fmap, lookup_delete_ne by congruence.
    reflexivity.
Qed.

Lemma open_env_atom_swap_insert
    (x y : atom) (η : gmap nat atom) (k : nat) (a : atom) :
  open_env_atom_swap x y (<[k := a]> η) =
  <[k := swap x y a]> (open_env_atom_swap x y η).
Proof.
  apply map_eq. intros j.
  rewrite lookup_fmap.
  destruct (decide (j = k)) as [->|Hjk].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    rewrite lookup_fmap. reflexivity.
Qed.

Lemma open_env_atom_swap_avoids (x y z : atom) (η : gmap nat atom) :
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

Definition open_env_values_inj (η : gmap nat atom) : Prop :=
  forall i j x,
    η !! i = Some x ->
    η !! j = Some x ->
    i = j.

Lemma open_env_values_inj_empty :
  open_env_values_inj ∅.
Proof.
  intros i j x Hi _.
  rewrite lookup_empty in Hi. discriminate.
Qed.

Lemma open_env_values_inj_insert (k : nat) (x : atom) (η : gmap nat atom) :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  open_env_values_inj (<[k := x]> η).
Proof.
  intros Hfresh Havoid Hinj i j z Hi Hj.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_insert in Hi.
    destruct (decide (k = k)) as [_|Hbad]; [|congruence].
    assert (z = x) by congruence. subst z.
    destruct (decide (j = k)) as [->|Hjk]; [reflexivity|].
    rewrite lookup_insert_ne in Hj by congruence.
    exfalso. exact (Havoid j Hj).
  - rewrite lookup_insert_ne in Hi by congruence.
    destruct (decide (j = k)) as [->|Hjk].
    + rewrite lookup_insert in Hj.
      destruct (decide (k = k)) as [_|Hbad]; [|congruence].
      assert (z = x) by congruence. subst z.
      exfalso. exact (Havoid i Hi).
    + rewrite lookup_insert_ne in Hj by congruence.
      apply (Hinj i j z); assumption.
Qed.

Lemma open_env_values_inj_lift (η : gmap nat atom) :
  open_env_values_inj η ->
  open_env_values_inj ((kmap S η)).
Proof.
  intros Hinj i j x Hi Hj.
  destruct i as [|i].
  - rewrite open_env_lift_lookup_zero_none in Hi. discriminate.
  - destruct j as [|j].
    + rewrite open_env_lift_lookup_zero_none in Hj. discriminate.
    + assert (η !! i = Some x) as Hiη.
      {
        rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
          S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η i) in Hi.
        exact Hi.
      }
      assert (η !! j = Some x) as Hjη.
      {
        rewrite (lookup_kmap (M1:=gmap nat) (M2:=gmap nat)
          S (Inj0:=ltac:(intros ? ? ?; lia)) (A:=atom) η j) in Hj.
        exact Hj.
      }
      f_equal. eapply Hinj; eassumption.
Qed.

Lemma open_env_values_inj_insert_inv (η : gmap nat atom) (k : nat) (x : atom) :
  η !! k = None ->
  open_env_values_inj (<[k := x]> η) ->
  open_env_values_inj η /\ open_env_avoids_atom x η.
Proof.
  intros Hfresh Hinj.
  split.
  - intros i j y Hi Hj.
    eapply Hinj.
    + rewrite lookup_insert_ne by congruence. exact Hi.
    + rewrite lookup_insert_ne by congruence. exact Hj.
  - intros j Hj.
    pose proof (Hinj k j x) as Hsame.
    rewrite lookup_insert_eq in Hsame.
    rewrite lookup_insert_ne in Hsame by congruence.
    specialize (Hsame eq_refl Hj). congruence.
Qed.

Lemma open_env_values_inj_singleton (k : nat) (x : atom) :
  open_env_values_inj (<[k := x]> ∅).
Proof.
  intros i j y Hi Hj.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_insert_eq in Hi. inversion Hi; subst y.
    destruct (decide (j = k)) as [->|Hjk]; [reflexivity|].
    rewrite lookup_insert_ne in Hj by congruence.
    rewrite lookup_empty in Hj. discriminate.
  - rewrite lookup_insert_ne in Hi by congruence.
    rewrite lookup_empty in Hi. discriminate.
Qed.

Lemma logic_var_open_env_atom_swap
    (x y : atom) (η : gmap nat atom) (v : logic_var) :
  logic_var_open_env η (logic_var_swap x y v) =
  logic_var_swap x y (logic_var_open_env (open_env_atom_swap x y η) v).
Proof.
  destruct v as [k|a].
  - change (logic_var_swap x y (LVBound k)) with
      (swap (LVFree x) (LVFree y) (LVBound k)).
    rewrite swap_fresh by congruence.
    cbn [logic_var_open_env].
    rewrite open_env_atom_swap_lookup.
    destruct (η !! k) as [b|] eqn:Hη; cbn.
    + rewrite logic_var_free_swap, swap_involutive. reflexivity.
    + change (logic_var_swap x y (LVBound k)) with
        (swap (LVFree x) (LVFree y) (LVBound k)).
      rewrite swap_fresh by congruence. reflexivity.
  - cbn [logic_var_open_env].
    rewrite logic_var_free_swap.
    reflexivity.
Qed.

Lemma lvars_swap_elem_iff (x y : atom) (D : lvset) (v : logic_var) :
  v ∈ lvars_swap x y D <-> logic_var_swap x y v ∈ D.
Proof.
  rewrite set_swap_elem.
  change (swap (LVFree x) (LVFree y) v) with (logic_var_swap x y v).
  reflexivity.
Qed.

Lemma lvars_open_env_atom_swap
    (x y : atom) (η : gmap nat atom) (D : lvset) :
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
      apply (f_equal (logic_var_swap x y)) in Hop.
      replace (logic_var_swap x y (logic_var_swap x y u)) with u in Hop
        by (symmetry; apply logic_var_swap_involutive).
      replace (logic_var_swap x y (logic_var_swap x y
        (logic_var_open_env (open_env_atom_swap x y η)
           (logic_var_swap x y u)))) with
        (logic_var_open_env (open_env_atom_swap x y η)
           (logic_var_swap x y u)) in Hop
        by (symmetry; apply logic_var_swap_involutive).
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
      symmetry. apply logic_var_swap_involutive.
    + apply lvars_swap_elem_iff.
      rewrite logic_var_swap_involutive. exact Hu.
Qed.

Lemma open_env_fresh_for_lvars_atom_swap
    (x y : atom) (η : gmap nat atom) (D : lvset) :
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

Lemma open_env_fresh_for_lvars_atom_swap_inv
    (x y : atom) (η : gmap nat atom) (D : lvset) :
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
  unfold swap in Hbad.
  repeat destruct decide; subst; try congruence.
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

Lemma open_env_fresh_for_lvars_singleton (k : nat) (x : atom) (D : lvset) :
  x ∉ lvars_fv D ->
  open_env_fresh_for_lvars (<[k := x]> ∅) D.
Proof.
  intros Hx i z Hi.
  destruct (decide (i = k)) as [->|Hik].
  - rewrite lookup_insert_eq in Hi. inversion Hi; subst z.
    replace (delete k (<[k := x]> (∅ : gmap nat atom))) with
      (∅ : gmap nat atom).
    + rewrite lvars_open_env_empty. exact Hx.
    + apply map_eq. intros j.
      destruct (decide (j = k)) as [->|Hjk].
      * rewrite lookup_delete_eq, lookup_empty. reflexivity.
      * rewrite lookup_delete_ne by congruence.
        rewrite lookup_insert_ne by congruence.
        rewrite lookup_empty. reflexivity.
  - rewrite lookup_insert_ne in Hi by congruence.
    rewrite lookup_empty in Hi. discriminate.
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
  unfold set_swap.
  apply set_eq. intros v.
  rewrite !elem_of_map.
  split.
  - intros [u [-> Hu]].
    exists (logic_var_open_env η u). split.
    + rewrite (logic_var_open_env_insert_fresh η k x u Hη
        (logic_var_open_env_not_free_of_lvars_fv η D x u Hu Hfresh)).
      reflexivity.
    + apply elem_of_map. exists u. split; [reflexivity|exact Hu].
  - intros [u [-> Hu]].
    apply elem_of_map in Hu as [w [-> Hw]].
    exists w. split; [|exact Hw].
    rewrite (logic_var_open_env_insert_fresh η k x w Hη
      (logic_var_open_env_not_free_of_lvars_fv η D x w Hw Hfresh)).
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
        apply elem_of_set_swap in Hu.
        rewrite Hbad in Hu. exact Hu.
    + apply lvars_open_elem_open with (k := k) (x := x).
      rewrite logic_var_open_involutive. exact Hu.
  - intros [u [-> Hu]].
    exists (logic_var_open k x u). split.
    + rewrite logic_var_open_env_open_one_fresh.
      * reflexivity.
      * intros ->. apply Hx. apply lvars_fv_elem. exact Hu.
    + apply lvars_open_elem_open. exact Hu.
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
    rewrite map_delete_insert_same in Hbad.
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
		      apply elem_of_set_swap.
		      rewrite swap_r. rewrite lvars_bv_elem in HkD. exact HkD.
		      rewrite swap_l. reflexivity.
    + inversion Hv. subst y.
      apply HxD. apply lvars_fv_elem. exact HvD.
  - rewrite lookup_insert_ne in Hjz by congruence.
    eapply Hfresh; [exact Hjz|].
    rewrite (lvars_open_env_open_one_fresh (delete j η) k x D HxD).
    rewrite <- map_delete_insert_ne by congruence.
    exact Hbad.
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
      rewrite logic_var_free_swap.
      rewrite swap_l. reflexivity.
    + rewrite lookup_insert_ne by congruence.
      rewrite lookup_delete_ne by congruence.
      destruct (η !! n) as [b|] eqn:Hηn.
      2:{ rewrite swap_fresh by discriminate. reflexivity. }
      rewrite logic_var_free_swap.
      rewrite swap_fresh; [reflexivity| |].
      * intros ->. apply (Havoid n).
        rewrite lookup_delete_ne by congruence. exact Hηn.
      * intros ->.
        eapply Hfresh; [exact Hηk|].
        apply lvars_fv_open_env_lookup with (k := n).
        -- rewrite lookup_delete_ne by congruence. exact Hηn.
        -- apply elem_of_union_r. exact HvD.
  - rewrite logic_var_free_swap.
    rewrite swap_fresh; [reflexivity| |].
    + intros ->. apply HyD. apply lvars_fv_elem. exact HvD.
    + intros ->. apply HzD. apply lvars_fv_elem. exact HvD.
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

Lemma lvars_fv_open_env_union η D E :
  lvars_fv (lvars_open_env η (D ∪ E)) =
  lvars_fv (lvars_open_env η D) ∪
  lvars_fv (lvars_open_env η E).
Proof.
  apply set_eq. intros x.
  unfold lvars_open_env.
  rewrite lvars_fv_elem, elem_of_union, !lvars_fv_elem.
  rewrite !elem_of_map.
  split.
  - intros [v [Hv HDE]].
    apply elem_of_union in HDE as [HD|HE].
    + left. exists v. split; [exact Hv|exact HD].
    + right. exists v. split; [exact Hv|exact HE].
  - intros [[v [Hv HD]]|[v [Hv HE]]].
    + exists v. split; [exact Hv|better_set_solver].
    + exists v. split; [exact Hv|better_set_solver].
Qed.
