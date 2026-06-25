(** * BasicDenotation.Term

    Totality and result extensions for core terms. *)

From CoreLang Require Import LocallyNamelessExtra.
From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBase Require Import BaseTactics.
From Stdlib Require Import List.
Import ListNotations.

Global Notation open_tm_env :=
  (fun η e => map_fold (fun k x acc => open_tm k (vfvar x) acc) e η)
  (only parsing).

Section TermDenotation.

Lemma bvar_lvars_at_fv d n :
  lvars_fv (bvar_lvars_at d n) = ∅.
Proof.
  unfold bvar_lvars_at. destruct (decide (d <= n));
    rewrite ?lvars_fv_singleton_bound; reflexivity.
Qed.

Lemma lvars_bv_singleton_free_atom x :
  lvars_bv ({[LVFree x]} : lvset) = ∅.
Proof.
  apply set_eq. intros k.
  rewrite lvars_bv_elem, elem_of_empty, elem_of_singleton.
  split; [intros H; discriminate H | tauto].
Qed.

Lemma value_tm_lvars_at_fv_mutual :
  (forall v d, lvars_fv (value_lvars_at d v) = fv_value v) *
  (forall e d, lvars_fv (tm_lvars_at d e) = fv_tm e).
Proof.
  apply value_tm_mutind; cbn [value_lvars_at tm_lvars_at fv_value fv_tm];
    intros; try reflexivity.
  - apply lvars_fv_singleton_free.
  - apply bvar_lvars_at_fv.
  - apply H.
  - apply H.
  - apply H.
  - rewrite lvars_fv_union, H, H0. reflexivity.
  - apply H.
  - rewrite lvars_fv_union, H, H0. reflexivity.
  - rewrite !lvars_fv_union, H, H0, H1. set_solver.
Qed.

Lemma value_lvars_at_fv v d :
  lvars_fv (value_lvars_at d v) = fv_value v.
Proof. exact (fst value_tm_lvars_at_fv_mutual v d). Qed.

Lemma tm_lvars_at_fv e d :
  lvars_fv (tm_lvars_at d e) = fv_tm e.
Proof. exact (snd value_tm_lvars_at_fv_mutual e d). Qed.

Lemma tm_lvars_fv e :
  lvars_fv (tm_lvars e) = fv_tm e.
Proof. apply tm_lvars_at_fv. Qed.

Lemma bvar_lvars_at_depth d c n :
  lvars_at_depth d (bvar_lvars_at c n) = bvar_lvars_at (c + d) n.
Proof.
  unfold bvar_lvars_at.
  destruct (decide (c <= n)) as [Hcn|Hcn].
  - apply set_eq. intros u.
    rewrite lvars_at_depth_elem.
    destruct (decide (c + d <= n)) as [Hcdn|Hcdn].
    + split.
      * intros [v [Hv Hvu]].
        rewrite elem_of_singleton in Hv. subst v.
        cbn [logic_var_at_depth] in Hvu.
        destruct (decide (d <= n - c)) as [_|Hbad]; [|lia].
        inversion Hvu. subst u.
        rewrite elem_of_singleton. f_equal. lia.
      * intros Hu.
        rewrite elem_of_singleton in Hu. subst u.
        exists (LVBound (n - c)). split; [set_solver|].
        cbn [logic_var_at_depth].
        destruct (decide (d <= n - c)) as [_|Hbad]; [|lia].
        replace (n - c - d) with (n - (c + d)) by lia.
        reflexivity.
    + split.
      * intros [v [Hv Hvu]].
        rewrite elem_of_singleton in Hv. subst v.
        cbn [logic_var_at_depth] in Hvu.
        destruct (decide (d <= n - c)) as [Hbad|_]; [lia|discriminate].
      * set_solver.
  - destruct (decide (c + d <= n)); [lia|].
    apply set_eq. intros u. rewrite lvars_at_depth_elem.
    split; [intros [v [Hv _]]; set_solver | set_solver].
Qed.

Lemma value_tm_lvars_at_depth_mutual :
  (forall v c d,
      lvars_at_depth d (value_lvars_at c v) = value_lvars_at (c + d) v) *
  (forall e c d,
      lvars_at_depth d (tm_lvars_at c e) = tm_lvars_at (c + d) e).
Proof.
  apply value_tm_mutind; cbn [value_lvars_at tm_lvars_at]; intros;
    try solve [rewrite lvars_at_depth_empty; reflexivity].
  - apply lvars_at_depth_singleton_free.
  - apply bvar_lvars_at_depth.
  - rewrite H. replace (S c + d) with (S (c + d)) by lia. reflexivity.
  - rewrite H. replace (S c + d) with (S (c + d)) by lia. reflexivity.
  - rewrite H. reflexivity.
  - rewrite lvars_at_depth_union, H, H0.
    replace (S c + d) with (S (c + d)) by lia. reflexivity.
  - rewrite H. reflexivity.
  - rewrite lvars_at_depth_union, H, H0. reflexivity.
  - rewrite !lvars_at_depth_union, H, H0, H1. reflexivity.
Qed.

Lemma value_lvars_at_depth v c d :
  lvars_at_depth d (value_lvars_at c v) = value_lvars_at (c + d) v.
Proof. exact (fst value_tm_lvars_at_depth_mutual v c d). Qed.

Lemma tm_lvars_at_depth e c d :
  lvars_at_depth d (tm_lvars_at c e) = tm_lvars_at (c + d) e.
Proof. exact (snd value_tm_lvars_at_depth_mutual e c d). Qed.

Lemma tm_lvars_depth e d :
  lvars_at_depth d (tm_lvars e) = tm_lvars_at d e.
Proof.
  unfold tm_lvars. rewrite tm_lvars_at_depth.
  replace (0 + d) with d by lia. reflexivity.
Qed.

Lemma bvar_lvars_at_open d k y n :
  value_lvars_at d (open_value (d + k) (vfvar y) (vbvar n)) =
  lvars_open k y (value_lvars_at d (vbvar n)).
Proof.
  cbn [open_value value_lvars_at].
  unfold bvar_lvars_at.
  destruct (decide (d + k = n)) as [Heq|Hneq].
  - subst n.
    rewrite decide_True by lia.
    replace (d + k - d) with k by lia.
    rewrite set_swap_singleton.
    unfold swap. repeat destruct decide; try congruence.
    reflexivity.
  - destruct (decide (d <= n)) as [Hdn|Hdn].
    + cbn [value_lvars_at]. unfold bvar_lvars_at. rewrite decide_True by exact Hdn.
      rewrite set_swap_singleton.
      rewrite swap_fresh.
      * reflexivity.
      * intros Heq. inversion Heq. lia.
      * discriminate.
    + cbn [value_lvars_at]. unfold bvar_lvars_at. rewrite decide_False by exact Hdn.
	      rewrite set_swap_empty. reflexivity.
Qed.

Lemma value_tm_lvars_at_open_mutual :
  (forall v d k y,
      y ∉ lvars_fv (value_lvars_at d v) ->
      value_lvars_at d (open_value (d + k) (vfvar y) v) =
      lvars_open k y (value_lvars_at d v)) *
  (forall e d k y,
      y ∉ lvars_fv (tm_lvars_at d e) ->
      tm_lvars_at d (open_tm (d + k) (vfvar y) e) =
      lvars_open k y (tm_lvars_at d e)).
Proof.
  apply value_tm_mutind; cbn [open_value open_tm value_lvars_at tm_lvars_at];
    intros; try solve [rewrite set_swap_empty; reflexivity].
  - symmetry. apply set_swap_fresh.
    + set_solver.
    + rewrite lvars_fv_singleton_free in H. set_solver.
  - apply bvar_lvars_at_open.
  - replace (S (d + k)) with (S d + k) by lia.
    apply H. exact H0.
  - replace (S (d + k)) with (S d + k) by lia.
    apply H. exact H0.
  - apply H. exact H0.
  - rewrite H by (rewrite ?lvars_fv_union in *; set_solver).
    replace (S (d + k)) with (S d + k) by lia.
    rewrite H0 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite <- set_swap_union. reflexivity.
  - apply H. exact H0.
  - rewrite H by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite H0 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite <- set_swap_union. reflexivity.
  - rewrite H by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite H0 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite H1 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite <- !set_swap_union. set_solver.
Qed.

Lemma value_lvars_at_open v d k y :
  y ∉ lvars_fv (value_lvars_at d v) ->
  value_lvars_at d (open_value (d + k) (vfvar y) v) =
  lvars_open k y (value_lvars_at d v).
Proof. exact (fst value_tm_lvars_at_open_mutual v d k y). Qed.

Lemma tm_lvars_at_open e d k y :
  y ∉ lvars_fv (tm_lvars_at d e) ->
  tm_lvars_at d (open_tm (d + k) (vfvar y) e) =
  lvars_open k y (tm_lvars_at d e).
Proof. exact (snd value_tm_lvars_at_open_mutual e d k y). Qed.

Lemma tm_lvars_open k y e :
  y ∉ fv_tm e ->
  tm_lvars (open_tm k (vfvar y) e) =
  lvars_open k y (tm_lvars e).
Proof.
  intros Hy.
  change k with (0 + k) at 1.
  apply tm_lvars_at_open.
  rewrite tm_lvars_at_fv. exact Hy.
Qed.

Lemma value_tm_lvars_no_bv_of_lc_mutual :
  (forall v,
      lc_value v ->
      lvars_bv (value_lvars v) = ∅) /\
  (forall e,
      lc_tm e ->
      lvars_bv (tm_lvars e) = ∅).
Proof.
  refine (lc_mutind
    (fun v _ => lvars_bv (value_lvars v) = ∅)
    (fun e _ => lvars_bv (tm_lvars e) = ∅)
    _
    _
    (fun T e L Hbody IH => _)
    (fun T vf L Hbody IH => _)
    (fun v Hlc IH => IH)
    (fun e1 e2 L Hlc1 IH1 Hbody IH2 => _)
    (fun op v Hlc IH => IH)
    (fun v1 v2 Hlc1 IH1 Hlc2 IH2 => _)
    (fun v et ef Hlcv IHv Hlcet IHet Hlcef IHef => _)).
  - cbn [value_lvars value_lvars_at]. reflexivity.
  - cbn [value_lvars value_lvars_at].
    apply lvars_bv_singleton_free_atom.
  - cbn [value_lvars tm_lvars value_lvars_at tm_lvars_at].
    pose (x := fresh_for (L ∪ fv_tm e)).
    assert (HxL : x ∉ L) by
      (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e)); set_solver).
    assert (Hxfv : x ∉ fv_tm e) by
      (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e)); set_solver).
    specialize (IH x HxL).
    change (lvars_bv (tm_lvars (open_tm 0 (vfvar x) e)) = ∅) in IH.
    rewrite tm_lvars_open in IH by exact Hxfv.
    rewrite <- (tm_lvars_depth e 1).
    apply lvars_bv_at_depth_succ_empty_of_open0 with (x := x).
    exact IH.
  - cbn [value_lvars tm_lvars value_lvars_at tm_lvars_at].
    pose (x := fresh_for (L ∪ fv_value vf)).
    assert (HxL : x ∉ L) by
      (subst x; pose proof (fresh_for_not_in (L ∪ fv_value vf)); set_solver).
    assert (Hxfv : x ∉ fv_value vf) by
      (subst x; pose proof (fresh_for_not_in (L ∪ fv_value vf)); set_solver).
    specialize (IH x HxL).
    change (lvars_bv (value_lvars_at 0 (open_value (0 + 0) (vfvar x) vf)) = ∅) in IH.
    rewrite (value_lvars_at_open vf 0 0 x) in IH by
      (rewrite value_lvars_at_fv; exact Hxfv).
    replace (value_lvars_at 1 vf) with (value_lvars_at (0 + 1) vf)
      by (replace (0 + 1) with 1 by lia; reflexivity).
    rewrite <- (value_lvars_at_depth vf 0 1).
    apply lvars_bv_at_depth_succ_empty_of_open0 with (x := x).
    exact IH.
  - cbn [value_lvars tm_lvars value_lvars_at tm_lvars_at].
    change (tm_lvars_at 0 e1) with (tm_lvars e1).
    rewrite lvars_bv_union, IH1.
    pose (x := fresh_for (L ∪ fv_tm e2)).
    assert (HxL : x ∉ L) by
      (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e2)); set_solver).
    assert (Hxfv : x ∉ fv_tm e2) by
      (subst x; pose proof (fresh_for_not_in (L ∪ fv_tm e2)); set_solver).
    specialize (IH2 x HxL).
    change (lvars_bv (tm_lvars (open_tm 0 (vfvar x) e2)) = ∅) in IH2.
    rewrite tm_lvars_open in IH2 by exact Hxfv.
    rewrite <- (tm_lvars_depth e2 1).
    assert (Hdepth : lvars_bv (lvars_at_depth 1 (tm_lvars e2)) = ∅).
    { apply lvars_bv_at_depth_succ_empty_of_open0 with (x := x). exact IH2. }
    rewrite Hdepth. set_solver.
  - cbn [value_lvars tm_lvars value_lvars_at tm_lvars_at].
    change (value_lvars_at 0 v1) with (value_lvars v1).
    change (value_lvars_at 0 v2) with (value_lvars v2).
    rewrite lvars_bv_union, IH1, IH2. set_solver.
  - cbn [value_lvars tm_lvars value_lvars_at tm_lvars_at].
    change (value_lvars_at 0 v) with (value_lvars v).
    change (tm_lvars_at 0 et) with (tm_lvars et).
    change (tm_lvars_at 0 ef) with (tm_lvars ef).
    rewrite !lvars_bv_union, IHv, IHet, IHef. set_solver.
Qed.

Lemma value_lvars_no_bv_of_lc v :
  lc_value v ->
  lvars_bv (value_lvars v) = ∅.
Proof. exact (proj1 value_tm_lvars_no_bv_of_lc_mutual v). Qed.

Lemma tm_lvars_no_bv_of_lc e :
  lc_tm e ->
  lvars_bv (tm_lvars e) = ∅.
Proof. exact (proj2 value_tm_lvars_no_bv_of_lc_mutual e). Qed.

Lemma value_lvars_lc v :
  lc_value v ->
  lc_lvars (value_lvars v).
Proof.
  intros Hlc. apply lc_lvars_no_bv. apply value_lvars_no_bv_of_lc. exact Hlc.
Qed.

Lemma tm_lvars_lc e :
  lc_tm e ->
  lc_lvars (tm_lvars e).
Proof.
  intros Hlc. apply lc_lvars_no_bv. apply tm_lvars_no_bv_of_lc. exact Hlc.
Qed.

Lemma tm_lvars_lc_subset_atoms_fv e :
  lc_lvars (tm_lvars e) ->
  tm_lvars e ⊆ lvars_of_atoms (fv_tm e).
Proof.
  intros Hlc v Hv.
  pose proof (proj1 (lc_lvars_no_bv (tm_lvars e)) Hlc) as Hbv.
  pose proof (lvars_bv_empty_subset_of_atoms_fv
    (tm_lvars e) Hbv v Hv) as Hin.
  rewrite tm_lvars_fv in Hin. exact Hin.
Qed.

Lemma tm_lvars_lc_eq_atoms e :
  lc_tm e ->
  tm_lvars e = lvars_of_atoms (fv_tm e).
Proof.
  intros Hlc.
  apply set_eq. intros v. split.
  - apply tm_lvars_lc_subset_atoms_fv. apply tm_lvars_lc. exact Hlc.
  - intros Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply lvars_fv_elem.
    rewrite tm_lvars_fv. exact Hx.
Qed.

Lemma value_lvars_lc_eq_atoms v :
  lc_value v ->
  value_lvars v = lvars_of_atoms (fv_value v).
Proof.
  intros Hlc.
  apply set_eq. intros u. split.
  - intros Hu.
    pose proof (proj1 (lc_lvars_no_bv (value_lvars v))
      (value_lvars_lc v Hlc)) as Hbv.
    pose proof (lvars_bv_empty_subset_of_atoms_fv (value_lvars v) Hbv u Hu)
      as Hin.
    unfold value_lvars in Hin.
    rewrite value_lvars_at_fv in Hin. exact Hin.
  - intros Hu.
    unfold lvars_of_atoms in Hu.
    apply elem_of_map in Hu as [x [-> Hx]].
    apply lvars_fv_elem.
    unfold value_lvars.
    rewrite value_lvars_at_fv. exact Hx.
Qed.

Lemma tm_lvars_open_body_subset_lc e x D :
  body_tm e ->
  tm_lvars_at 1 e ⊆ D ->
  tm_lvars (e ^^ x) ⊆ D ∪ {[LVFree x]}.
Proof.
  intros Hbody Hsub u Hu.
  rewrite (tm_lvars_lc_eq_atoms (e ^^ x)) in Hu.
  2:{ apply body_open_tm; [exact Hbody|constructor]. }
  unfold lvars_of_atoms in Hu.
  apply elem_of_map in Hu as [a [-> Ha]].
  apply open_fv_tm in Ha.
  cbn [fv_value] in Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - rewrite elem_of_singleton in Ha. subst a.
    apply elem_of_union_r. rewrite elem_of_singleton. reflexivity.
  - apply elem_of_union_l. apply Hsub.
    apply lvars_fv_elem. rewrite tm_lvars_at_fv. exact Ha.
Qed.

Lemma value_lvars_open_body_subset_lc v x D :
  body_val v ->
  value_lvars_at 1 v ⊆ D ->
  value_lvars (v ^^ x) ⊆ D ∪ {[LVFree x]}.
Proof.
  intros Hbody Hsub u Hu.
  rewrite (value_lvars_lc_eq_atoms (v ^^ x)) in Hu.
  2:{ apply body_open_value; [exact Hbody|constructor]. }
  unfold lvars_of_atoms in Hu.
  apply elem_of_map in Hu as [a [-> Ha]].
  apply open_fv_value in Ha.
  cbn [fv_value] in Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - rewrite elem_of_singleton in Ha. subst a.
    apply elem_of_union_r. rewrite elem_of_singleton. reflexivity.
  - apply elem_of_union_l. apply Hsub.
    apply lvars_fv_elem. rewrite value_lvars_at_fv. exact Ha.
Qed.

Lemma tm_lvars_tlete_open_body_subset e1 e2 x :
  lc_tm (tlete e1 e2) ->
  x ∉ fv_tm e2 ->
  tm_lvars (e2 ^^ x) ⊆ tm_lvars (tlete e1 e2) ∪ {[LVFree x]}.
Proof.
  intros Hlc Hx.
  rewrite (tm_lvars_lc_eq_atoms (e2 ^^ x)).
  2:{
    unfold open_one. cbn [open_tm_atom_inst].
    apply body_open_tm; [|constructor].
    apply lc_lete_iff_body in Hlc as [_ Hbody]. exact Hbody.
  }
  rewrite (tm_lvars_lc_eq_atoms (tlete e1 e2)) by exact Hlc.
  unfold lvars_of_atoms.
  intros z Hz.
  apply elem_of_map in Hz as [a [-> Ha]].
  apply open_fv_tm in Ha.
  cbn [fv_value] in Ha.
  apply elem_of_union in Ha as [Ha|Ha].
  - rewrite elem_of_singleton in Ha. subst a.
    apply elem_of_union. right. set_solver.
  - apply elem_of_union. left.
    apply elem_of_map. exists a. split; [reflexivity|].
    cbn [fv_tm]. apply elem_of_union_r. exact Ha.
Qed.

Lemma elem_of_fv_tm_open_fvar e z k a :
  a ∈ fv_tm (open_tm k (vfvar z) e) ->
  a ∈ {[z]} ∪ fv_tm e.
Proof.
  intros Ha.
  pose proof (open_fv_tm e (vfvar z) k a Ha) as Hopen.
  cbn [fv_value] in Hopen.
  exact Hopen.
Qed.

Lemma fv_tm_open_fvar_subset e z k :
  fv_tm (open_tm k (vfvar z) e) ⊆ {[z]} ∪ fv_tm e.
Proof.
  intros a Ha.
  eapply elem_of_fv_tm_open_fvar. exact Ha.
Qed.

Lemma fv_tm_open_fvar_tlete_body_subset e1 e2 z k :
  fv_tm (open_tm k (vfvar z) e2) ⊆ fv_tm (tlete e1 e2) ∪ {[z]}.
Proof.
  intros a Ha.
  pose proof (elem_of_fv_tm_open_fvar e2 z k a Ha) as Hopen.
  apply elem_of_union in Hopen as [Hz|He2].
  - apply elem_of_union_r. exact Hz.
  - apply elem_of_union_l.
    cbn [fv_tm]. apply elem_of_union_r. exact He2.
Qed.

Lemma fv_tm_tlete_left_subset e1 e2 :
  fv_tm e1 ⊆ fv_tm (tlete e1 e2).
Proof.
  intros a Ha. cbn [fv_tm]. apply elem_of_union_l. exact Ha.
Qed.

Lemma notin_fv_tm_tlete e1 e2 z :
  z ∉ fv_tm e1 ->
  z ∉ fv_tm e2 ->
  z ∉ fv_tm (tlete e1 e2).
Proof.
  intros Hze1 Hze2 Hz.
  cbn [fv_tm] in Hz.
  apply elem_of_union in Hz as [Hz|Hz]; [exact (Hze1 Hz)|exact (Hze2 Hz)].
Qed.

Lemma open_tm_shift0_lc y e :
  lc_tm e ->
  open_tm 0 (vfvar y) (tm_shift 0 e) = e.
Proof.
  intros Hlc.
  rewrite tm_shift_lc_id by exact Hlc.
  apply open_rec_lc_tm. exact Hlc.
Qed.

Lemma open_tapp_tm_shift_bvar0_lc e y :
  lc_tm e ->
  open_tm 0 (vfvar y) (tapp_tm (tm_shift 0 e) (vbvar 0)) =
  tapp_tm e (vfvar y).
Proof.
  intros Hlc.
  unfold tapp_tm.
  cbn [open_tm open_value value_shift].
  rewrite bool_decide_eq_true_2 by lia.
  rewrite open_tm_shift0_lc by exact Hlc.
  destruct (decide (1 = 0)); [lia|].
  destruct (decide (1 = 1)); [|lia].
  reflexivity.
Qed.

Lemma value_tm_open_shift_no_bv_mutual :
  (forall v d x,
      lvars_bv (value_lvars_at d v) = ∅ ->
      open_value d (vfvar x) (value_shift d v) = v) *
  (forall e d x,
      lvars_bv (tm_lvars_at d e) = ∅ ->
      open_tm d (vfvar x) (tm_shift d e) = e).
Proof.
  apply value_tm_mutind; cbn [value_lvars_at tm_lvars_at
    open_value open_tm value_shift tm_shift]; intros.
  - reflexivity.
  - reflexivity.
  - unfold bvar_lvars_at in H.
    destruct (decide (d <= n)) as [Hdn|Hdn].
    + exfalso.
      assert (n - d ∈ lvars_bv ({[LVBound (n - d)]} : lvset)).
      { rewrite lvars_bv_elem. set_solver. }
      rewrite H in H0. set_solver.
    + rewrite bool_decide_eq_false_2 by exact Hdn.
      cbn [open_value].
      destruct (decide (d = n)); [lia|reflexivity].
  - f_equal. apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal.
    + apply H. rewrite lvars_bv_union in H1. set_solver.
    + apply H0. rewrite lvars_bv_union in H1. set_solver.
  - f_equal. apply H. exact H0.
  - f_equal.
    + apply H. rewrite lvars_bv_union in H1. set_solver.
    + apply H0. rewrite lvars_bv_union in H1. set_solver.
  - f_equal.
    + apply H. rewrite !lvars_bv_union in H2. set_solver.
    + apply H0. rewrite !lvars_bv_union in H2. set_solver.
    + apply H1. rewrite !lvars_bv_union in H2. set_solver.
Qed.

Lemma open_tm_shift_no_bv d x e :
  lvars_bv (tm_lvars_at d e) = ∅ ->
  open_tm d (vfvar x) (tm_shift d e) = e.
Proof. exact (snd value_tm_open_shift_no_bv_mutual e d x). Qed.

Lemma open_tm_shift0_lvars_lc y e :
  lc_lvars (tm_lvars e) ->
  open_tm 0 (vfvar y) (tm_shift 0 e) = e.
Proof.
  intros Hlc.
  apply open_tm_shift_no_bv.
  apply lc_lvars_no_bv. exact Hlc.
Qed.

Lemma tm_lvars_tapp_tm_fvar e y :
  tm_lvars (tapp_tm e (vfvar y)) = tm_lvars e ∪ {[LVFree y]}.
Proof.
  unfold tapp_tm, tm_lvars.
  cbn [tm_lvars_at value_lvars_at value_shift].
  unfold bvar_lvars_at.
  destruct (decide (1 <= 0)); [lia|].
  better_set_solver.
Qed.

Fixpoint tapp_tm_fvar_spine (e : tm) (ys : list atom) : tm :=
  match ys with
  | [] => e
  | y :: ys' => tapp_tm (tapp_tm_fvar_spine e ys') (vfvar y)
  end.

Lemma tm_lvars_tapp_tm_fvar_without_arg e y :
  tm_lvars (tapp_tm e (vfvar y)) ∖ {[LVFree y]} ⊆ tm_lvars e.
Proof.
  unfold tapp_tm, tm_lvars.
  cbn [tm_lvars_at value_lvars_at value_shift].
  unfold bvar_lvars_at.
  destruct (decide (1 <= 0)); [lia|].
  better_set_solver.
Qed.

Lemma open_tm_env_singleton k y e :
  open_tm_env (<[k := y]> ∅) e =
  open_tm k (vfvar y) e.
Proof.
  cbn beta.
  change (<[k:=y]> (∅ : gmap nat atom)) with ({[k:=y]} : gmap nat atom).
  rewrite map_fold_singleton.
  reflexivity.
Qed.

Lemma open_tm_env_insert_fresh_plain η k x e :
  η !! k = None ->
  open_tm_env (<[k := x]> η) e =
  open_tm k (vfvar x) (open_tm_env η e).
Proof.
  intros Hfresh.
  cbn beta.
  rewrite (map_fold_insert_L
    (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e k x η).
  - reflexivity.
  - intros i j xi xj acc Hij _ _.
    apply open_swap_tm; [apply LC_fvar | apply LC_fvar | exact Hij].
  - exact Hfresh.
Qed.

Lemma tm_lvars_open_tm_env η e :
  open_env_fresh_for_lvars η (tm_lvars e) ->
  tm_lvars (open_tm_env η e) = lvars_open_env η (tm_lvars e).
Proof.
  cbn beta.
  refine (fin_maps.map_fold_ind
    (fun η => open_env_fresh_for_lvars η (tm_lvars e) ->
      tm_lvars
        (map_fold (fun k0 x0 acc => open_tm k0 (vfvar x0) acc) e η) =
      lvars_open_env η (tm_lvars e))
    _ _ η).
  - intros _. rewrite map_fold_empty. better_base_solver.
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

Lemma tm_lvars_free_notin_of_fv x e :
  x ∉ fv_tm e ->
  LVFree x ∉ tm_lvars e.
Proof.
  intros Hx Hbad.
  apply Hx.
  rewrite <- tm_lvars_fv.
  apply lvars_fv_elem. exact Hbad.
Qed.

Lemma open_tm_env_lift_tapp_shift_bvar0 η e :
  open_tm_env ((kmap S η)) (tapp_tm (tm_shift 0 e) (vbvar 0)) =
  tapp_tm (tm_shift 0 (open_tm_env η e)) (vbvar 0).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite kmap_empty.
    rewrite !map_fold_empty. reflexivity.
  - rewrite open_env_lift_insert.
    rewrite open_tm_env_insert_fresh_plain by better_base_solver.
    rewrite IH.
    rewrite open_tm_env_insert_fresh_plain by exact Hfresh.
    unfold tapp_tm.
    cbn [open_tm open_value value_shift].
    rewrite tm_shift_open_tm_fvar by lia.
    repeat (destruct decide; try lia); try congruence; reflexivity.
Qed.

Lemma open_tm_env_lift_tret_bound0 η :
  open_tm_env ((kmap S η)) (tret (vbvar 0)) = tret (vbvar 0).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite kmap_empty.
    rewrite map_fold_empty. reflexivity.
  - rewrite open_env_lift_insert.
    rewrite open_tm_env_insert_fresh_plain by better_base_solver.
    rewrite IH.
    cbn [open_tm open_value].
    destruct decide as [Hbad|_]; [lia|reflexivity].
Qed.

Lemma open_tm_env_lift2_tapp_ret_bound1_bound0 η :
  open_tm_env (kmap S (kmap S η))
    (tapp_tm (tret (vbvar 1)) (vbvar 0)) =
  tapp_tm (tret (vbvar 1)) (vbvar 0).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite !kmap_empty, map_fold_empty. reflexivity.
  - rewrite !open_env_lift_insert.
    rewrite open_tm_env_insert_fresh_plain.
    2:{
      apply open_env_lift_lookup_none.
      apply open_env_lift_lookup_none.
      exact Hfresh.
    }
    rewrite IH.
    unfold tapp_tm.
    cbn [open_tm open_value].
    repeat destruct decide; try lia; try congruence; reflexivity.
Qed.

Lemma tm_lvars_at_tapp_ret_bound1_bound0_under d :
  tm_lvars_at (S (S d))
    (tapp_tm (tret (vbvar 1)) (vbvar 0)) = ∅.
Proof.
  cbn [tapp_tm tm_lvars_at value_lvars_at].
  unfold bvar_lvars_at.
  repeat (destruct decide; try lia).
  set_solver.
Qed.

Lemma bvar_lvars_at_shift_under d k n :
  k <= d ->
  value_lvars_at (S d) (value_shift k (vbvar n)) =
  value_lvars_at d (vbvar n).
Proof.
  intros Hkd.
  cbn [value_shift value_lvars_at]. unfold bvar_lvars_at.
  destruct (bool_decide (k <= n)) eqn:Hknb.
  - apply bool_decide_eq_true_1 in Hknb.
    cbn [value_lvars_at]. unfold bvar_lvars_at.
    destruct (decide (S d <= S n)) as [Hsdn|Hsdn].
    + destruct (decide (d <= n)) as [_|Hbad]; [|lia].
      replace (S n - S d) with (n - d) by lia.
      reflexivity.
    + destruct (decide (d <= n)) as [Hbad|_]; [lia|reflexivity].
  - apply bool_decide_eq_false_1 in Hknb.
    cbn [value_lvars_at]. unfold bvar_lvars_at.
    destruct (decide (S d <= n)) as [Hsdn|Hsdn].
    + lia.
    + destruct (decide (d <= n)) as [Hdn|Hdn].
      * assert (n = d) by lia. subst n. lia.
      * reflexivity.
Qed.

Lemma value_tm_lvars_at_shift_under_mutual :
  (forall v d k,
      k <= d ->
      value_lvars_at (S d) (value_shift k v) = value_lvars_at d v) *
  (forall e d k,
      k <= d ->
      tm_lvars_at (S d) (tm_shift k e) = tm_lvars_at d e).
Proof.
  apply value_tm_mutind; cbn [value_shift tm_shift value_lvars_at tm_lvars_at];
    intros; try reflexivity.
  - apply bvar_lvars_at_shift_under. exact H.
  - rewrite H by lia. reflexivity.
  - rewrite H by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by lia. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H1.
    rewrite H0 by exact H1. reflexivity.
  - rewrite H by exact H2.
    rewrite H0 by exact H2.
    rewrite H1 by exact H2. reflexivity.
Qed.

Lemma value_lvars_at_shift_under v d k :
  k <= d ->
  value_lvars_at (S d) (value_shift k v) = value_lvars_at d v.
Proof. exact (fst value_tm_lvars_at_shift_under_mutual v d k). Qed.

Lemma tm_lvars_at_shift_under e d k :
  k <= d ->
  tm_lvars_at (S d) (tm_shift k e) = tm_lvars_at d e.
Proof. exact (snd value_tm_lvars_at_shift_under_mutual e d k). Qed.

Lemma value_lvars_at_bound0_under d :
  value_lvars_at (S d) (vbvar 0) = ∅.
Proof.
  cbn [value_lvars_at]. unfold bvar_lvars_at.
  destruct (decide (S d <= 0)); [lia|reflexivity].
Qed.

Lemma tm_lvars_at_tret_bound0_under d :
  tm_lvars_at (S d) (tret (vbvar 0)) = ∅.
Proof. cbn [tm_lvars_at]. apply value_lvars_at_bound0_under. Qed.

Lemma tm_lvars_at_tapp_shift_bound0 e d k :
  k <= d ->
  tm_lvars_at (S d) (tapp_tm (tm_shift k e) (vbvar 0)) ⊆
  tm_lvars_at d e.
Proof.
  induction e in d, k |- *; cbn [tm_shift tapp_tm tm_lvars_at]; intros Hkd.
  - rewrite value_lvars_at_shift_under by lia.
    rewrite value_lvars_at_bound0_under. set_solver.
  - pose proof (IHe2 (S d) (S k) ltac:(lia)) as Hbody.
    rewrite tm_lvars_at_shift_under by lia. set_solver.
  - rewrite value_lvars_at_shift_under by lia.
    cbn [tm_lvars_at].
    rewrite !value_lvars_at_bound0_under. set_solver.
  - rewrite value_lvars_at_shift_under by lia.
    rewrite value_lvars_at_shift_under by lia.
    cbn [tm_lvars_at].
    rewrite !value_lvars_at_bound0_under. set_solver.
  - rewrite value_lvars_at_shift_under by lia.
    rewrite tm_lvars_at_shift_under by lia.
    rewrite tm_lvars_at_shift_under by lia.
    cbn [tm_lvars_at].
    rewrite !value_lvars_at_bound0_under. set_solver.
Qed.

Lemma tm_lvars_at_tapp_shift0_bound0 e d :
  tm_lvars_at (S d) (tapp_tm (tm_shift 0 e) (vbvar 0)) ⊆
  tm_lvars_at d e.
Proof. apply tm_lvars_at_tapp_shift_bound0. lia. Qed.

Definition lstore_free_part (σ : LStoreT) : StoreT :=
  lstore_to_store σ.

Fixpoint lstore_instantiate_value_split_at
    (d : nat) (σf : StoreT) (σb : gmap nat value) (v : value) : value :=
  match v with
  | vconst _ => v
  | vfvar x =>
      match σf !! x with
      | Some u => u
      | None => v
      end
  | vbvar n =>
      match decide (d <= n) with
      | left _ =>
        match σb !! (n - d) with
        | Some u => u
        | None => v
        end
      | right _ => v
      end
  | vlam s e => vlam s (lstore_instantiate_tm_split_at (S d) σf σb e)
  | vfix Tf vf => vfix Tf (lstore_instantiate_value_split_at (S d) σf σb vf)
  end
with lstore_instantiate_tm_split_at
    (d : nat) (σf : StoreT) (σb : gmap nat value) (e : tm) : tm :=
  match e with
  | tret v => tret (lstore_instantiate_value_split_at d σf σb v)
  | tlete e1 e2 =>
      tlete (lstore_instantiate_tm_split_at d σf σb e1)
        (lstore_instantiate_tm_split_at (S d) σf σb e2)
  | tprim op v => tprim op (lstore_instantiate_value_split_at d σf σb v)
  | tapp v1 v2 =>
      tapp (lstore_instantiate_value_split_at d σf σb v1)
        (lstore_instantiate_value_split_at d σf σb v2)
  | tmatch v et ef =>
      tmatch (lstore_instantiate_value_split_at d σf σb v)
        (lstore_instantiate_tm_split_at d σf σb et)
        (lstore_instantiate_tm_split_at d σf σb ef)
  end.

Definition lstore_instantiate_value_at
    (d : nat) (σ : LStoreT) (v : value) : value :=
  lstore_instantiate_value_split_at d (lstore_free_part σ) (lstore_bound_part σ) v.

Definition lstore_instantiate_tm_at
    (d : nat) (σ : LStoreT) (e : tm) : tm :=
  lstore_instantiate_tm_split_at d (lstore_free_part σ) (lstore_bound_part σ) e.

Definition lstore_instantiate_tm (σ : LStoreT) (e : tm) : tm :=
  lstore_instantiate_tm_at 0 σ e.

Ltac fold_lstore_instantiate_at :=
  repeat match goal with
  | H : context[lstore_instantiate_tm_split_at ?d
        (lstore_free_part ?s) (lstore_bound_part ?s) ?e] |- _ =>
      change (lstore_instantiate_tm_split_at d
        (lstore_free_part s) (lstore_bound_part s) e)
        with (lstore_instantiate_tm_at d s e) in H
  | |- context[lstore_instantiate_tm_split_at ?d
        (lstore_free_part ?s) (lstore_bound_part ?s) ?e] =>
      change (lstore_instantiate_tm_split_at d
        (lstore_free_part s) (lstore_bound_part s) e)
        with (lstore_instantiate_tm_at d s e)
  | H : context[lstore_instantiate_value_split_at ?d
        (lstore_free_part ?s) (lstore_bound_part ?s) ?v] |- _ =>
      change (lstore_instantiate_value_split_at d
        (lstore_free_part s) (lstore_bound_part s) v)
        with (lstore_instantiate_value_at d s v) in H
  | |- context[lstore_instantiate_value_split_at ?d
        (lstore_free_part ?s) (lstore_bound_part ?s) ?v] =>
      change (lstore_instantiate_value_split_at d
        (lstore_free_part s) (lstore_bound_part s) v)
        with (lstore_instantiate_value_at d s v)
  end.

Lemma lstore_free_part_lift_free (σ : StoreT) :
  lstore_free_part (lstore_lift_free σ : LStoreT) = σ.
Proof.
  change ((lstore_free_part (lstore_lift_free σ : LStoreT) : gmap atom value) =
    (σ : gmap atom value)).
  apply map_eq. intros x.
  unfold lstore_free_part.
  rewrite lstore_to_store_lookup, lstore_lift_free_lookup_free.
  reflexivity.
Qed.

Lemma lc_lstore_lift_free (σ : StoreT) :
  lc_lstore (lstore_lift_free σ : LStoreT).
Proof.
  unfold lc_lstore, lc_lvars. intros v Hv.
  rewrite dom_lstore_lift_free in Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [x [Heq _]].
  subst v. cbn [lc_logic_var_key]. exact I.
Qed.

Lemma lstore_bound_part_empty_of_lc σ :
  lc_lstore σ ->
  lstore_bound_part σ = ∅.
Proof.
  intros Hlc.
  apply map_eq. intros k.
  rewrite ContextStore.StoreInterface.lstore_bound_part_lookup, lookup_empty.
  apply eq_None_not_Some. intros [v Hlookup].
  assert (Hbound : LVBound k ∈ dom (σ : gmap logic_var value)).
  { rewrite elem_of_dom. eauto. }
  unfold lc_lstore, lc_lvars in Hlc.
  specialize (Hlc (LVBound k) Hbound).
  exact Hlc.
Qed.

Lemma lstore_instantiate_restrict_lvars_at_mutual :
  (forall v d (σ : LStoreT) X,
      value_lvars_at d v ⊆ X ->
      lstore_instantiate_value_at d (storeA_restrict σ X) v =
      lstore_instantiate_value_at d σ v) *
  (forall e d (σ : LStoreT) X,
      tm_lvars_at d e ⊆ X ->
      lstore_instantiate_tm_at d (storeA_restrict σ X) e =
      lstore_instantiate_tm_at d σ e).
Proof.
  apply value_tm_mutind;
    cbn [value_lvars_at tm_lvars_at lstore_instantiate_value_at
      lstore_instantiate_tm_at lstore_instantiate_value_split_at
      lstore_instantiate_tm_split_at]; intros; try reflexivity.
  - unfold lstore_free_part.
    rewrite lstore_to_store_restrict_lookup by set_solver.
    reflexivity.
  - 
    destruct (decide (d <= n)) as [Hdn|Hdn]; [|reflexivity].
    assert (Hbound_in : LVBound (n - d) ∈ X).
    {
      apply H.
      unfold bvar_lvars_at.
      destruct (decide (d <= n)); [set_solver|lia].
    }
    rewrite lstore_bound_part_restrict_lookup by exact Hbound_in.
    reflexivity.
  - f_equal. apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal; [apply H | apply H0]; set_solver.
  - f_equal. apply H. exact H0.
  - f_equal; [apply H | apply H0]; set_solver.
  - f_equal; [apply H | apply H0 | apply H1]; set_solver.
Qed.

Lemma lstore_instantiate_tm_at_restrict_lvars e d (σ : LStoreT) X :
  tm_lvars_at d e ⊆ X ->
  lstore_instantiate_tm_at d (storeA_restrict σ X) e =
  lstore_instantiate_tm_at d σ e.
Proof.
  exact (snd lstore_instantiate_restrict_lvars_at_mutual e d σ X).
Qed.

Lemma lstore_instantiate_tm_restrict_lvars e (σ : LStoreT) X :
  tm_lvars e ⊆ X ->
  lstore_instantiate_tm (storeA_restrict σ X) e =
  lstore_instantiate_tm σ e.
Proof.
  apply lstore_instantiate_tm_at_restrict_lvars.
Qed.

Lemma lstore_instantiate_value_at_fvar d σ y :
  lstore_instantiate_value_at d σ (vfvar y) =
  match lstore_free_part σ !! y with
  | Some u => u
  | None => vfvar y
  end.
Proof. reflexivity. Qed.

Lemma lstore_lift_free_insert x v (σ : StoreT) :
  (lstore_lift_free (<[x := v]> σ) : LStoreT) =
  <[LVFree x := v]> (lstore_lift_free σ : LStoreT).
Proof.
  unfold lstore_lift_free.
  change (storeA_map_key LVFree (<[x := v]> σ) =
    <[LVFree x := v]> (storeA_map_key LVFree σ : gmap logic_var value)).
  apply storeA_map_key_insert.
  intros a b Hab. inversion Hab. reflexivity.
Qed.

Lemma lstore_instantiate_split_restrict_mutual :
  (forall v d (σf : StoreT) σb X,
      fv_value v ⊆ X ->
      lstore_instantiate_value_split_at d (store_restrict σf X) σb v =
      lstore_instantiate_value_split_at d σf σb v) *
  (forall e d (σf : StoreT) σb X,
      fv_tm e ⊆ X ->
      lstore_instantiate_tm_split_at d (store_restrict σf X) σb e =
      lstore_instantiate_tm_split_at d σf σb e).
Proof.
  apply value_tm_mutind;
    cbn [fv_value fv_tm lstore_instantiate_value_split_at
      lstore_instantiate_tm_split_at]; intros; try reflexivity.
  - change (match ((storeA_restrict σf X : gmap atom value) !! x) with
            | Some u => u
            | None => vfvar x
            end =
            match (σf : gmap atom value) !! x with
            | Some u => u
            | None => vfvar x
            end).
    assert (Hx : x ∈ X) by set_solver.
    replace (((storeA_restrict σf X : gmap atom value) !! x))
      with ((σf : gmap atom value) !! x); [reflexivity|].
    destruct (σf !! x) as [v|] eqn:Hlook.
    + symmetry.
      replace ((σf : gmap atom value) !! x) with (Some v)
        by (symmetry; exact Hlook).
  apply (storeA_restrict_lookup_some_2 _ _ _ _ Hlook Hx).
    + symmetry.
      replace ((σf : gmap atom value) !! x) with (@None value)
        by (symmetry; exact Hlook).
      apply storeA_restrict_lookup_none_l. exact Hlook.
  - f_equal. apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal; [apply H | apply H0]; set_solver.
  - f_equal. apply H. exact H0.
  - f_equal; [apply H | apply H0]; set_solver.
  - f_equal; [apply H | apply H0 | apply H1]; set_solver.
Qed.

Lemma lstore_instantiate_tm_split_restrict_fv d (σf : StoreT) σb e X :
  fv_tm e ⊆ X ->
  lstore_instantiate_tm_split_at d (store_restrict σf X) σb e =
  lstore_instantiate_tm_split_at d σf σb e.
Proof.
  exact (snd lstore_instantiate_split_restrict_mutual e d σf σb X).
Qed.

Lemma lstore_instantiate_split_empty_bound_mutual :
  (forall v d σf,
      closed_env σf ->
      lstore_instantiate_value_split_at d σf ∅ v = subst_map σf v) *
  (forall e d σf,
      closed_env σf ->
      lstore_instantiate_tm_split_at d σf ∅ e = subst_map σf e).
Proof.
  apply value_tm_mutind;
    cbn [lstore_instantiate_value_split_at lstore_instantiate_tm_split_at
      ];
    intros.
  - match goal with
    | |- vconst ?c = _ =>
        change (vconst c = m{σf} (vconst c));
        rewrite (msubst_fresh σf (vconst c)) by set_solver; reflexivity
    end.
  - match goal with
    | |- context [vfvar ?x] =>
        destruct (σf !! x) as [u|] eqn:Hlookup
    end.
    + replace (match σf !! x with Some u0 => u0 | None => vfvar x end) with u
        by (destruct (σf !! x) as [u'|] eqn:Hlookup'; congruence).
      rewrite (subst_map_fvar_lookup_closed σf x u);
        [reflexivity | assumption | exact Hlookup].
    + replace (match σf !! x with Some u => u | None => vfvar x end)
        with (vfvar x)
        by (destruct (σf !! x) as [u'|] eqn:Hlookup'; congruence).
      change (vfvar x = subst_map σf (vfvar x)).
      symmetry. apply subst_map_value_fresh.
      apply not_elem_of_dom in Hlookup. cbn [stale stale_value_inst fv_value].
      set_solver.
	  - match goal with
	    | |- _ = subst_map ?σf (vbvar ?n) =>
	        destruct (decide (d <= n)); try rewrite lookup_empty; symmetry;
	        apply subst_map_value_fresh; set_solver
	    end.
  - rewrite subst_map_vlam. f_equal. apply H. exact H0.
  - rewrite subst_map_vfix. f_equal. apply H. exact H0.
  - rewrite subst_map_ret. f_equal. apply H. exact H0.
  - rewrite subst_map_lete. f_equal; [apply H | apply H0]; exact H1.
  - rewrite subst_map_tprim. f_equal. apply H. exact H0.
  - rewrite subst_map_tapp. f_equal; [apply H | apply H0]; exact H1.
  - rewrite subst_map_tmatch. repeat f_equal;
      [apply H | apply H0 | apply H1]; exact H2.
Qed.

Lemma lstore_instantiate_tm_split_empty_bound d σf e :
  closed_env σf ->
  lstore_instantiate_tm_split_at d σf ∅ e = subst_map σf e.
Proof. exact (snd lstore_instantiate_split_empty_bound_mutual e d σf). Qed.

Lemma lstore_instantiate_split_insert_open_mutual :
  (forall v d x vx (σf : StoreT),
      lc_env σf ->
      lc_value vx ->
      x ∉ dom σf ∪ fv_value v ->
      lstore_instantiate_value_split_at d
        (map_insert (M:=gmap atom value) x vx (σf : gmap atom value)) ∅
        (open_value d (vfvar x) v) =
      open_value d vx
        (lstore_instantiate_value_split_at (S d) σf ∅ v)) *
  (forall e d x vx (σf : StoreT),
      lc_env σf ->
      lc_value vx ->
      x ∉ dom σf ∪ fv_tm e ->
      lstore_instantiate_tm_split_at d
        (map_insert (M:=gmap atom value) x vx (σf : gmap atom value)) ∅
        (open_tm d (vfvar x) e) =
      open_tm d vx
        (lstore_instantiate_tm_split_at (S d) σf ∅ e)).
Proof.
  apply value_tm_mutind;
    cbn [open_value open_tm fv_value fv_tm
      lstore_instantiate_value_split_at lstore_instantiate_tm_split_at];
    intros; try reflexivity.
  - destruct (decide (x0 = x)) as [->|Hneq].
    + set_solver.
    + unfold map_insert.
      rewrite (lookup_partial_alter_ne (M:=gmap atom) (A:=value)
        (fun _ : option value => Some vx) (σf : gmap atom value) x0 x)
        by congruence.
	      destruct ((σf : gmap atom value) !! x) as [u|] eqn:Hlookup.
	      * replace (match (σf : gmap atom value) !! x with
	                   | Some u0 => u0
	                   | None => vfvar x
	                   end) with u by (rewrite Hlookup; reflexivity).
	        symmetry. apply open_rec_lc_value.
	        eapply (lc_env_lookup σf x u); eauto.
	      * replace (match (σf : gmap atom value) !! x with
	                   | Some u0 => u0
	                   | None => vfvar x
	                   end) with (vfvar x) by (rewrite Hlookup; reflexivity).
	        cbn [open_value]. reflexivity.
  - destruct (decide (d = n)) as [->|Hneq].
    + cbn [lstore_instantiate_value_split_at].
      unfold map_insert.
      rewrite (lookup_partial_alter_eq (M:=gmap atom) (A:=value)
        (fun _ : option value => Some vx) (σf : gmap atom value) x).
      destruct (decide (S n <= n)) as [Hbad|_]; [lia|].
      cbn [open_value]. rewrite decide_True by reflexivity.
      reflexivity.
    + cbn [lstore_instantiate_value_split_at].
      destruct (decide (d <= n)) as [Hd|Hd];
        destruct (decide (S d <= n)) as [HS|HS];
        rewrite ?lookup_empty; cbn [open_value];
        destruct (decide (d = n)) as [Heq|Heq]; try congruence; reflexivity.
  - f_equal. apply H; set_solver.
  - f_equal. apply H; set_solver.
  - f_equal. apply H; set_solver.
  - f_equal; [apply H | apply H0]; set_solver.
  - f_equal. apply H; set_solver.
  - f_equal; [apply H | apply H0]; set_solver.
  - f_equal; [apply H | apply H0 | apply H1]; set_solver.
Qed.

Lemma lstore_instantiate_tm_split_insert_open
    e d x vx (σf : StoreT) :
  lc_env σf ->
  lc_value vx ->
  x ∉ dom σf ∪ fv_tm e ->
  lstore_instantiate_tm_split_at d
    (map_insert (M:=gmap atom value) x vx (σf : gmap atom value)) ∅
    (open_tm d (vfvar x) e) =
  open_tm d vx
    (lstore_instantiate_tm_split_at (S d) σf ∅ e).
Proof.
  exact (snd lstore_instantiate_split_insert_open_mutual e d x vx σf).
Qed.

Lemma lstore_instantiate_tm_at_lc_lstore d σ e :
  lc_lstore σ ->
  closed_env (lstore_free_part σ) ->
  lstore_instantiate_tm_at d σ e = subst_map (lstore_free_part σ) e.
Proof.
  intros Hlc Hclosed.
  unfold lstore_instantiate_tm_at.
  rewrite lstore_bound_part_empty_of_lc by exact Hlc.
  apply lstore_instantiate_tm_split_empty_bound. exact Hclosed.
Qed.

Lemma match_left_observation_facts x et ef X :
  X = fv_tm (tmatch (vfvar x) et ef) ->
  fv_tm et ⊆ X /\
  fv_tm (tmatch (vfvar x) et ef) ⊆ X /\
  x ∈ X.
Proof.
  intros ->.
  cbn [fv_tm fv_value].
  repeat split; better_set_solver.
Qed.

Lemma match_right_observation_facts x et ef X :
  X = fv_tm (tmatch (vfvar x) et ef) ->
  fv_tm ef ⊆ X /\
  fv_tm (tmatch (vfvar x) et ef) ⊆ X /\
  x ∈ X.
Proof.
  intros ->.
  cbn [fv_tm fv_value].
  repeat split; better_set_solver.
Qed.

Lemma soundness_match_left_observation_facts x et ef X :
  X = fv_tm (tmatch (vfvar x) et ef) ->
  fv_tm et ⊆ X /\
  fv_tm (tmatch (vfvar x) et ef) ⊆ X /\
  x ∈ X.
Proof. apply match_left_observation_facts. Qed.

Lemma soundness_match_right_observation_facts x et ef X :
  X = fv_tm (tmatch (vfvar x) et ef) ->
  fv_tm ef ⊆ X /\
  fv_tm (tmatch (vfvar x) et ef) ⊆ X /\
  x ∈ X.
Proof. apply match_right_observation_facts. Qed.

End TermDenotation.
