(** * BasicDenotation.Term

    Totality and result extensions for core terms. *)

From Stdlib Require Import Logic.ClassicalDescription Logic.ClassicalEpsilon.
From CoreLang Require Import BasicTyping BasicTypingProps Instantiation InstantiationProps
  LocallyNamelessProps OperationalProps SmallStep.
From ChoiceAlgebra Require Import Resource ResourceCore ResourceExtensionCore.
From ChoiceLogic Require Import Formula.
From ChoiceTypeLanguage Require Import Interface.
From ChoiceBasicDenotation Require Import StoreTyping.

Section TermDenotation.

Local Notation StoreT := (Store (V:=value)) (only parsing).
Local Notation LStoreT := (LStore (V:=value)) (only parsing).
Local Notation WorldT := (World (V:=value)) (only parsing).
Local Notation LWorldT := (LWorld (V:=value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V:=value)) (only parsing).
Local Notation FiberExtensionT := (fiber_extension (V:=value)) (only parsing).
Local Notation lstore_bound_part := (@lstore_bound_part value) (only parsing).

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

Lemma value_lvars_depth v d :
  lvars_at_depth d (value_lvars v) = value_lvars_at d v.
Proof.
  unfold value_lvars. rewrite value_lvars_at_depth.
  replace (0 + d) with d by lia. reflexivity.
Qed.

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
    rewrite lvars_open_unfold, gset_swap_singleton.
    change (key_swap (LVBound k) (LVFree y) (LVBound k)) with
      (logic_var_open k y (LVBound k)).
    rewrite logic_var_open_unfold, eq_swap_l.
    reflexivity.
  - destruct (decide (d <= n)) as [Hdn|Hdn].
    + cbn [value_lvars_at]. unfold bvar_lvars_at. rewrite decide_True by exact Hdn.
	      rewrite lvars_open_unfold, gset_swap_singleton.
	      rewrite key_swap_fresh.
	      * reflexivity.
      * intros Heq. inversion Heq. lia.
      * discriminate.
    + cbn [value_lvars_at]. unfold bvar_lvars_at. rewrite decide_False by exact Hdn.
      rewrite lvars_open_unfold, gset_swap_empty. reflexivity.
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
    intros; try solve [rewrite lvars_open_unfold, gset_swap_empty; reflexivity].
  - rewrite lvars_open_unfold. symmetry. apply gset_swap_fresh.
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
    rewrite !lvars_open_unfold, <- gset_swap_union. reflexivity.
  - apply H. exact H0.
  - rewrite H by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite H0 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite !lvars_open_unfold, <- gset_swap_union. reflexivity.
  - rewrite H by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite H0 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite H1 by (rewrite ?lvars_fv_union in *; set_solver).
    rewrite !lvars_open_unfold, <- !gset_swap_union. set_solver.
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

Lemma value_tm_open_no_bv_mutual :
  (forall v d k x,
      k ∉ lvars_bv (value_lvars_at d v) ->
      open_value (d + k) (vfvar x) v = v) *
  (forall e d k x,
      k ∉ lvars_bv (tm_lvars_at d e) ->
      open_tm (d + k) (vfvar x) e = e).
Proof.
  apply value_tm_mutind; cbn [value_lvars_at tm_lvars_at open_value open_tm];
    intros.
  - reflexivity.
  - reflexivity.
  - unfold bvar_lvars_at in H.
    destruct (decide (d <= n)) as [Hdn|Hdn].
    + destruct (decide (d + k = n)) as [Heq|Hne].
      * exfalso. apply H. rewrite lvars_bv_elem, elem_of_singleton.
        f_equal. lia.
      * destruct (decide (d + k = n)); [congruence|reflexivity].
    + destruct (decide (d + k = n)); [lia|reflexivity].
  - f_equal.
    replace (S (d + k)) with (S d + k) by lia.
    apply H. exact H0.
  - f_equal.
    replace (S (d + k)) with (S d + k) by lia.
    apply H. exact H0.
  - f_equal. apply H. exact H0.
  - f_equal.
    + apply H. rewrite lvars_bv_union in H1. set_solver.
    + replace (S (d + k)) with (S d + k) by lia.
      apply H0. rewrite lvars_bv_union in H1. set_solver.
  - f_equal. apply H. exact H0.
  - f_equal.
    + apply H. rewrite lvars_bv_union in H1. set_solver.
    + apply H0. rewrite lvars_bv_union in H1. set_solver.
  - f_equal.
    + apply H. rewrite !lvars_bv_union in H2. set_solver.
    + apply H0. rewrite !lvars_bv_union in H2. set_solver.
    + apply H1. rewrite !lvars_bv_union in H2. set_solver.
Qed.

Lemma value_open_no_bv k x v :
  k ∉ lvars_bv (value_lvars v) ->
  open_value k (vfvar x) v = v.
Proof.
  change k with (0 + k) at 1.
  apply (fst value_tm_open_no_bv_mutual).
Qed.

Lemma tm_open_no_bv k x e :
  k ∉ lvars_bv (tm_lvars e) ->
  open_tm k (vfvar x) e = e.
Proof.
  change k with (0 + k) at 1.
  apply (snd value_tm_open_no_bv_mutual).
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

Lemma tm_lvars_lc_eq_atoms e :
  lc_tm e ->
  tm_lvars e = lvars_of_atoms (fv_tm e).
Proof.
  intros Hlc.
  apply set_eq. intros v. split.
  - intros Hv.
    pose proof (proj1 (lc_lvars_no_bv (tm_lvars e))
      (tm_lvars_lc e Hlc)) as Hbv.
    pose proof (lvars_bv_empty_subset_of_atoms_fv (tm_lvars e) Hbv v Hv) as Hin.
    rewrite tm_lvars_fv in Hin. exact Hin.
  - intros Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [x [-> Hx]].
    apply lvars_fv_elem.
    rewrite tm_lvars_fv. exact Hx.
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

Lemma tm_lvars_tlete_open_body_fresh_result e1 e2 x y :
  lc_tm (tlete e1 e2) ->
  x <> y ->
  x ∉ fv_tm e2 ->
  LVFree y ∉ tm_lvars (tlete e1 e2) ->
  LVFree y ∉ tm_lvars (e2 ^^ x).
Proof.
  intros Hlc Hxy Hx Hfresh Hy.
  pose proof (tm_lvars_tlete_open_body_subset e1 e2 x Hlc Hx) as Hsub.
  specialize (Hsub _ Hy) as Hy'.
  rewrite elem_of_union, elem_of_singleton in Hy'.
  destruct Hy' as [Hy'|Hy']; [exact (Hfresh Hy')|].
  inversion Hy'. congruence.
Qed.

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
    rewrite !lstore_to_store_lookup.
    destruct (((σ : gmap logic_var value) !! LVFree x)) as [u|] eqn:Hlook.
    + assert (((storeA_restrict σ X : gmap logic_var value) !! LVFree x) =
        Some u) as Hrestrict.
      { apply storeA_restrict_lookup_some_2; [exact Hlook|set_solver]. }
      rewrite Hrestrict. reflexivity.
    + assert (((storeA_restrict σ X : gmap logic_var value) !! LVFree x) =
        None) as Hrestrict.
      { apply storeA_restrict_lookup_none_l. exact Hlook. }
      rewrite Hrestrict. reflexivity.
  - 
    rewrite !lstore_bound_part_lookup.
    destruct (decide (d <= n)) as [Hdn|Hdn]; [|reflexivity].
    assert (Hbound_in : LVBound (n - d) ∈ X).
    {
      apply H.
      unfold bvar_lvars_at.
      destruct (decide (d <= n)); [set_solver|lia].
    }
    destruct (((σ : gmap logic_var value) !! LVBound (n - d))) as [u|] eqn:Hlook.
    + assert (((storeA_restrict σ X : gmap logic_var value) !! LVBound (n - d)) =
        Some u) as Hrestrict.
      { apply storeA_restrict_lookup_some_2; [exact Hlook|exact Hbound_in]. }
      rewrite Hrestrict. reflexivity.
    + assert (((storeA_restrict σ X : gmap logic_var value) !! LVBound (n - d)) =
        None) as Hrestrict.
      { apply storeA_restrict_lookup_none_l. exact Hlook. }
      rewrite Hrestrict. reflexivity.
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

Lemma lstore_bound_part_empty_of_lc σ :
  lc_lstore σ ->
  lstore_bound_part σ = ∅.
Proof.
  intros Hlc.
  apply map_eq. intros k.
  rewrite ChoicePrelude.StoreInterfaceCore.lstore_bound_part_lookup, lookup_empty.
  apply eq_None_not_Some. intros [v Hlookup].
  assert (Hbound : LVBound k ∈ dom (σ : gmap logic_var value)).
  { rewrite elem_of_dom. eauto. }
  unfold lc_lstore, lc_lvars in Hlc.
  specialize (Hlc (LVBound k) Hbound).
  exact Hlc.
Qed.

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
  - rewrite store_restrict_lookup.
    destruct (decide (x ∈ X)); [reflexivity|set_solver].
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

Lemma lstore_instantiate_value_split_empty_bound d σf v :
  closed_env σf ->
  lstore_instantiate_value_split_at d σf ∅ v = subst_map σf v.
Proof. exact (fst lstore_instantiate_split_empty_bound_mutual v d σf). Qed.

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
      destruct (σf !! x) as [u|] eqn:Hlookup.
      * change (match (σf : gmap atom value) !! x with
                | Some u0 => u0
                | None => vfvar x
                end = open_value d vx u).
        replace (match (σf : gmap atom value) !! x with
                 | Some u0 => u0
                 | None => vfvar x
                 end) with u.
        symmetry. apply open_rec_lc_value.
        eapply lc_env_lookup; eauto.
        change ((σf : gmap atom value) !! x = Some u) in Hlookup.
        destruct ((σf : gmap atom value) !! x) eqn:Hlook.
        -- injection Hlookup as ->. reflexivity.
        -- rewrite Hlookup in Hlook. discriminate.
      * replace (match (σf : gmap atom value) !! x with
                 | Some u0 => u0
                 | None => vfvar x
                 end) with (vfvar x).
        -- cbn [open_value]. reflexivity.
        -- change ((σf : gmap atom value) !! x = None) in Hlookup.
           destruct ((σf : gmap atom value) !! x) eqn:Hlook;
             [rewrite Hlookup in Hlook; discriminate | reflexivity].
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

Lemma lstore_instantiate_value_at_lc_lstore d σ v :
  lc_lstore σ ->
  closed_env (lstore_free_part σ) ->
  lstore_instantiate_value_at d σ v = subst_map (lstore_free_part σ) v.
Proof.
  intros Hlc Hclosed.
  unfold lstore_instantiate_value_at.
  rewrite lstore_bound_part_empty_of_lc by exact Hlc.
  apply lstore_instantiate_value_split_empty_bound. exact Hclosed.
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

Definition expr_eval_in_store (σ : LStoreT) (e : tm) (v : value) : Prop :=
  lstore_instantiate_tm σ e →* tret v.

Definition expr_eval_in_atom_store (σ : StoreT) (e : tm) (v : value) : Prop :=
  expr_eval_in_store (lstore_lift_free σ) e v.

Lemma lstore_instantiate_tm_no_bvars σ e :
  lc_lstore σ ->
  closed_env (lstore_to_store σ) ->
  lstore_instantiate_tm σ e = subst_map (lstore_to_store σ) e.
Proof.
  intros Hlc Hclosed.
  unfold lstore_instantiate_tm.
  change (lstore_to_store σ) with (lstore_free_part σ).
  apply lstore_instantiate_tm_at_lc_lstore; assumption.
Qed.

Lemma expr_eval_in_store_no_bvars_iff σ e v :
  lc_lstore σ ->
  closed_env (lstore_to_store σ) ->
  expr_eval_in_store σ e v <->
  subst_map (lstore_to_store σ) e →* tret v.
Proof.
  intros Hlc Hclosed.
  unfold expr_eval_in_store.
  rewrite lstore_instantiate_tm_no_bvars by (exact Hlc || exact Hclosed).
  reflexivity.
Qed.

Lemma expr_eval_in_atom_store_restrict_fv σ e v :
  closed_env σ ->
  expr_eval_in_atom_store (store_restrict σ (fv_tm e)) e v <->
  expr_eval_in_atom_store σ e v.
Proof.
  intros Hclosed.
  unfold expr_eval_in_atom_store.
  rewrite !expr_eval_in_store_no_bvars_iff.
  - rewrite !lstore_free_part_lift_free.
    change (store_restrict σ (fv_tm e)) with
      (map_restrict value σ (fv_tm e)).
    rewrite !subst_map_tm_eq_msubst.
    rewrite (msubst_restrict σ (fv_tm e) e Hclosed ltac:(set_solver)).
    reflexivity.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact Hclosed.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free.
    apply closed_env_restrict. exact Hclosed.
Qed.

Lemma expr_eval_in_atom_store_restrict_fv_subset σ e v X :
  fv_tm e ⊆ X ->
  expr_eval_in_atom_store (store_restrict σ X) e v <->
  expr_eval_in_atom_store σ e v.
Proof.
  intros Hfv.
  unfold expr_eval_in_atom_store, expr_eval_in_store,
    lstore_instantiate_tm, lstore_instantiate_tm_at.
  rewrite !lstore_free_part_lift_free.
  rewrite !lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  rewrite lstore_instantiate_tm_split_restrict_fv by exact Hfv.
  reflexivity.
Qed.

Lemma expr_eval_in_atom_store_restrict_fv_closed_on σ e v :
  closed_env (store_restrict σ (fv_tm e)) ->
  expr_eval_in_atom_store (store_restrict σ (fv_tm e)) e v <->
  expr_eval_in_atom_store σ e v.
Proof.
  intros _.
  apply expr_eval_in_atom_store_restrict_fv_subset. set_solver.
Qed.

Lemma expr_eval_in_atom_store_restrict_fv_exact σ e v :
  expr_eval_in_atom_store (store_restrict σ (fv_tm e)) e v <->
  expr_eval_in_atom_store σ e v.
Proof.
  apply expr_eval_in_atom_store_restrict_fv_subset. set_solver.
Qed.

Lemma expr_eval_in_atom_store_agree_on_fv σ1 σ2 e v :
  store_restrict σ1 (fv_tm e) = store_restrict σ2 (fv_tm e) ->
  expr_eval_in_atom_store σ1 e v <->
  expr_eval_in_atom_store σ2 e v.
Proof.
  intros Hagree.
  rewrite <- (expr_eval_in_atom_store_restrict_fv_exact σ1 e v).
  rewrite <- (expr_eval_in_atom_store_restrict_fv_exact σ2 e v).
  rewrite Hagree. reflexivity.
Qed.

Lemma store_insert_restrict_agree_on_open_fv
    (σ : StoreT) X e x vx :
  fv_tm e ⊆ X ->
  x ∉ X ->
  x ∉ dom (σ : gmap atom value) ->
  store_restrict (σ ∪ ({[x := vx]} : StoreT))
    (fv_tm (open_tm 0 (vfvar x) e)) =
  store_restrict (<[x := vx]> (store_restrict σ X))
    (fv_tm (open_tm 0 (vfvar x) e)).
Proof.
  intros HfvX HxX Hxσ.
  apply storeA_map_eq. intros z.
  change (((store_restrict (σ ∪ ({[x := vx]} : StoreT))
      (fv_tm (open_tm 0 (vfvar x) e)) : gmap atom value) !! z) =
    ((store_restrict (<[x := vx]> (store_restrict σ X))
      (fv_tm (open_tm 0 (vfvar x) e)) : gmap atom value) !! z)).
  rewrite !store_restrict_lookup.
  destruct (decide (z ∈ fv_tm (open_tm 0 (vfvar x) e))) as [Hzopen|Hzopen];
    [|reflexivity].
  pose proof (open_fv_tm e (vfvar x) 0) as Hopen.
  cbn [fv_value] in Hopen.
  destruct (decide (z = x)) as [->|Hzx].
  - assert ((σ : gmap atom value) !! x = None) as Hσx.
    { apply not_elem_of_dom. exact Hxσ. }
    change ((((σ : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! x) =
      ((<[x := vx]> (store_restrict σ X : gmap atom value) : gmap atom value) !! x)).
    transitivity ((({[x := vx]} : gmap atom value) !! x)).
    + apply lookup_union_r. exact Hσx.
    + transitivity (Some vx).
      * change ((<[x := vx]> (∅ : StoreT)) !! x = Some vx).
        apply storeA_lookup_insert.
      * symmetry. apply storeA_lookup_insert.
  - assert (HzX : z ∈ X).
    { set_solver. }
    destruct ((σ : gmap atom value) !! z) as [vz|] eqn:Hσz.
    + change ((((σ : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! z) =
        ((<[x := vx]> (store_restrict σ X : gmap atom value) : gmap atom value) !! z)).
      transitivity (Some vz).
      * transitivity ((σ : gmap atom value) !! z).
        -- apply lookup_union_l'. exists vz. exact Hσz.
        -- rewrite Hσz. reflexivity.
      * symmetry.
        transitivity ((store_restrict σ X : StoreT) !! z).
        -- apply storeA_lookup_insert_ne. congruence.
        -- apply storeA_restrict_lookup_some_2; [exact Hσz|exact HzX].
    + change ((((σ : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! z) =
        ((<[x := vx]> (store_restrict σ X : gmap atom value) : gmap atom value) !! z)).
      transitivity (@None value).
      * transitivity ((({[x := vx]} : StoreT) !! z)).
        -- apply lookup_union_r. exact Hσz.
        -- change ((<[x := vx]> (∅ : StoreT)) !! z = None).
           transitivity ((∅ : StoreT) !! z).
           ++ apply storeA_lookup_insert_ne. congruence.
           ++ reflexivity.
      * symmetry.
        transitivity ((store_restrict σ X : StoreT) !! z).
        -- apply storeA_lookup_insert_ne. congruence.
        -- apply storeA_restrict_lookup_none_l. exact Hσz.
Qed.

(** [expr_total_on e m] is the lworld-level totality predicate consumed by
    Logic qualifiers.  [LVFree x] entries instantiate free variables and
    [LVBound k] entries open locally-nameless bound variables. *)
Definition expr_total_on (e : tm) (m : LWorldT) : Prop :=
  tm_lvars e ⊆ worldA_dom m /\
  forall σ,
    worldA_stores m σ ->
    exists v, expr_eval_in_store σ e v.

(** Atom worlds use the same lstore semantics through the free-lvar lift. *)
Definition expr_total_on_atom_world (e : tm) (m : WfWorldT) : Prop :=
  expr_total_on e (res_lift_free m : LWorldT).

Lemma expr_total_on_atom_world_subst_map_iff e (m : WfWorldT) :
  lc_tm e ->
  (forall σ, (m : WorldT) σ -> closed_env σ) ->
  expr_total_on_atom_world e m <->
  fv_tm e ⊆ world_dom (m : WorldT) /\
  forall σ,
    (m : WorldT) σ ->
    exists v, subst_map σ e →* tret v.
Proof.
  intros Hlc Hclosed.
  unfold expr_total_on_atom_world, expr_total_on.
  split.
  - intros [Hdom Htotal].
    split.
    + rewrite (tm_lvars_lc_eq_atoms e Hlc) in Hdom.
      rewrite res_lift_free_dom in Hdom.
      intros x Hx.
      assert (LVFree x ∈ lvars_of_atoms (fv_tm e)).
      { unfold lvars_of_atoms. apply elem_of_map. exists x. split; [reflexivity|exact Hx]. }
      specialize (Hdom _ H).
      unfold lvars_of_atoms in Hdom.
      apply elem_of_map in Hdom as [y [Heq Hy]].
      inversion Heq. subst y. exact Hy.
    + intros σ Hσ.
      pose proof (Htotal (lstore_lift_free σ)) as Hτ.
      assert (Hlift : worldA_stores (res_lift_free m : LWorldT) (lstore_lift_free σ)).
      { exists σ. split; [exact Hσ|reflexivity]. }
      specialize (Hτ Hlift).
      destruct Hτ as [v Heval]. exists v.
      unfold expr_eval_in_store in Heval.
      rewrite lstore_instantiate_tm_no_bvars in Heval.
      * rewrite lstore_free_part_lift_free in Heval. exact Heval.
      * apply lc_lstore_lift_free.
      * rewrite lstore_free_part_lift_free. apply Hclosed. exact Hσ.
  - intros [Hdom Htotal].
    split.
    + rewrite (tm_lvars_lc_eq_atoms e Hlc), res_lift_free_dom.
      unfold lvars_of_atoms.
      intros v Hv.
      apply elem_of_map in Hv as [x [-> Hx]].
      apply elem_of_map. exists x. split; [reflexivity|].
      apply Hdom. exact Hx.
    + intros τ Hτ.
      destruct Hτ as [σ [Hσ ->]].
      destruct (Htotal σ Hσ) as [v Heval]. exists v.
      unfold expr_eval_in_store.
      rewrite lstore_instantiate_tm_no_bvars.
      * rewrite lstore_free_part_lift_free. exact Heval.
      * apply lc_lstore_lift_free.
      * rewrite lstore_free_part_lift_free. apply Hclosed. exact Hσ.
Qed.

Definition expr_result_at_store (e : tm) (x : logic_var) (σ : LStoreT) : Prop :=
  x ∉ tm_lvars e /\
  exists v,
    σ !! x = Some v /\
    expr_eval_in_store σ e v.

(** A result world contains both the input variables of [e] and the fresh
    result variable [x].  Each store in that world binds [x] to a value obtained
    by evaluating [e] in the same store.  As with totality, no explicit store
    restriction is baked into the definition: [e] cannot inspect keys outside
    [tm_lvars e], while [x ∉ tm_lvars e] keeps the result cell separate from the
    input cells. *)
Definition expr_result_at_world (e : tm) (x : logic_var) (m : LWorldT) : Prop :=
  x ∉ tm_lvars e /\
  tm_lvars e ∪ {[x]} ⊆ worldA_dom m /\
  forall σ,
    worldA_stores m σ ->
    expr_result_at_store e x σ.

Lemma expr_eval_in_store_restrict_lvars e (σ : LStoreT) X v :
  tm_lvars e ⊆ X ->
  expr_eval_in_store (storeA_restrict σ X) e v <->
  expr_eval_in_store σ e v.
Proof.
  intros HX.
  unfold expr_eval_in_store.
  rewrite lstore_instantiate_tm_restrict_lvars by exact HX.
  reflexivity.
Qed.

Lemma expr_result_at_store_restrict_lvars e x (σ : LStoreT) X :
  tm_lvars e ∪ {[x]} ⊆ X ->
  expr_result_at_store e x σ ->
  expr_result_at_store e x (storeA_restrict σ X).
Proof.
  intros HX [Hx [v [Hlookup Heval]]].
  split; [exact Hx|].
  exists v. split.
  - apply storeA_restrict_lookup_some_2; [exact Hlookup|set_solver].
  - apply (proj2 (expr_eval_in_store_restrict_lvars e σ X v ltac:(set_solver))).
    exact Heval.
Qed.

Lemma lstore_lift_free_restrict_fv_lvars_eq (σ : StoreT) D :
  lc_lvars D ->
  storeA_restrict (lstore_lift_free (storeA_restrict σ (lvars_fv D)) : LStoreT) D =
  storeA_restrict (lstore_lift_free σ : LStoreT) D.
Proof.
  intros Hlc.
  apply storeA_map_eq. intros z.
  change (((storeA_restrict
      (lstore_lift_free (store_restrict σ (lvars_fv D)) : LStoreT) D
        : gmap logic_var value) !! z) =
    ((storeA_restrict (lstore_lift_free σ : LStoreT) D
        : gmap logic_var value) !! z)).
  destruct (decide (z ∈ D)) as [HzD|HzD].
  2:{
    transitivity (@None value).
    - apply storeA_restrict_lookup_none_r. exact HzD.
    - symmetry. apply storeA_restrict_lookup_none_r. exact HzD.
  }
  destruct z as [k|y].
  - exfalso. exact (Hlc (LVBound k) HzD).
  - assert (HyD : y ∈ lvars_fv D).
    { apply lvars_fv_elem. exact HzD. }
    destruct ((σ : gmap atom value) !! y) as [u|] eqn:Hσy.
    + transitivity (Some u).
      * apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free.
        apply storeA_restrict_lookup_some_2; [exact Hσy|exact HyD].
      * symmetry. apply storeA_restrict_lookup_some_2; [|exact HzD].
        rewrite lstore_lift_free_lookup_free. exact Hσy.
    + transitivity (@None value).
      * apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free.
        apply storeA_restrict_lookup_none_l. exact Hσy.
      * symmetry. apply storeA_restrict_lookup_none_l.
        rewrite lstore_lift_free_lookup_free. exact Hσy.
Qed.

Lemma expr_result_at_world_lworld_on_lift e x
    (m : WfWorldT)
    (Hlc : lc_lvars (tm_lvars e ∪ {[x]}))
    (Hsub : lvars_fv (tm_lvars e ∪ {[x]}) ⊆ world_dom (m : WorldT)) :
  expr_result_at_world e x (res_lift_free m : LWorldT) ->
  expr_result_at_world e x
    (@lw value _ (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub)).
Proof.
  intros [Hx [Hdom Hstores]].
  split; [exact Hx|]. split.
  - change (tm_lvars e ∪ {[x]} ⊆
      lworld_dom (@lw value _ (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub))).
    rewrite (@lw_dom value (tm_lvars e ∪ {[x]})
      (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub)).
    set_solver.
  - intros τ Hτ.
    unfold lworld_on_lift in Hτ.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hτ.
    destruct Hτ as [τ0 [Hτ0 Hτrestrict]]. subst τ.
    destruct Hτ0 as [σr [Hσr ->]].
    simpl in Hσr.
    destruct Hσr as [σm [Hσm Hσr]]. subst σr.
    replace (storeA_restrict
        (lstore_lift_free (storeA_restrict σm
          (lvars_fv (tm_lvars e ∪ {[x]}))) : LStoreT)
        (tm_lvars e ∪ {[x]}))
      with (storeA_restrict (lstore_lift_free σm : LStoreT)
        (tm_lvars e ∪ {[x]})).
    2:{
      symmetry.
      apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    apply expr_result_at_store_restrict_lvars.
    + set_solver.
    + apply Hstores. exists σm. split; [exact Hσm|reflexivity].
Qed.

Definition expr_result_output_world (e : tm) (x : atom) (σ : StoreT) : WfWorldT.
Proof.
  destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
    as [Hex | _].
  - destruct (constructive_indefinite_description _ Hex) as [v _].
    exact (exist _ (singleton_world ({[x := v]} : StoreT))
      (wf_singleton_world ({[x := v]} : StoreT))).
  - exact (exist _ (singleton_world ({[x := inhabitant]} : StoreT))
      (wf_singleton_world ({[x := inhabitant]} : StoreT))).
Defined.

Definition expr_result_extension
    (e : tm) (x : atom) (Hfresh : x ∉ fv_tm e) : FiberExtensionT.
Proof.
  refine (mk_fiber_extension (fv_tm e) {[x]}
    (fun σ => expr_result_output_world e x σ) _ _ _).
  - set_solver.
  - intros σ Hσ. unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
      as [Hex | _].
    + destruct (constructive_indefinite_description _ Hex) as [v _].
      unfold world_dom, singleton_world. simpl.
      change (dom ({[x := v]} : gmap atom value) = {[x]}).
      apply dom_singleton_L.
    + unfold world_dom, singleton_world. simpl.
      change (dom ({[x := inhabitant]} : gmap atom value) = {[x]}).
      apply dom_singleton_L.
  - intros σ Hσ. unfold expr_result_output_world.
    destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
      as [Hex | _].
    + destruct (constructive_indefinite_description _ Hex) as [v _].
      exists ({[x := v]} : StoreT). simpl. reflexivity.
    + exists ({[x := inhabitant]} : StoreT). simpl. reflexivity.
Defined.

Definition expr_total_lqual (e : tm) : logic_qualifier :=
  lqual (tm_lvars e)
    (fun w => expr_total_on e (@lw value _ w : LWorldT)).

Definition expr_total_formula (e : tm) : Formula :=
  FAtom (expr_total_lqual e).

Lemma formula_fv_expr_total_formula e :
  formula_fv (expr_total_formula e) = lvars_fv (tm_lvars e).
Proof.
  cbn [expr_total_formula expr_total_lqual formula_fv formula_lvars
    lqual_lvars lqual_fv lqual_dom].
  reflexivity.
Qed.

Definition expr_result_lqual (e : tm) (x : logic_var) : logic_qualifier :=
  lqual (tm_lvars e ∪ {[x]})
    (fun w => expr_result_at_world e x (@lw value _ w : LWorldT)).

Definition expr_result_formula (e : tm) (x : logic_var) : Formula :=
  FAtom (expr_result_lqual e x).

Lemma formula_fv_expr_result_formula e x :
  formula_fv (expr_result_formula e x) =
  lvars_fv (tm_lvars e ∪ {[x]}).
Proof. reflexivity. Qed.

Lemma lstore_swap_lookup_inv_value a b (σ : LStoreT) z :
  ((lstore_swap a b σ : gmap logic_var value) !! z) =
  ((σ : gmap logic_var value) !! key_swap a b z).
Proof.
  unfold lstore_swap, lstore_rekey.
  change ((storeA_swap a b σ : gmap logic_var value) !! z =
    (σ : gmap logic_var value) !! key_swap a b z).
  apply storeA_swap_lookup_inv.
Qed.

Lemma lstore_instantiate_open_back_mutual :
  (forall v d k y σ,
      y ∉ fv_value v ->
      lvars_open k y (value_lvars_at d v) ⊆ dom (σ : gmap logic_var value) ->
      lstore_instantiate_value_at d
        (lstore_swap (LVBound k) (LVFree y) σ) v =
      lstore_instantiate_value_at d σ
        (open_value (d + k) (vfvar y) v)) *
  (forall e d k y σ,
      y ∉ fv_tm e ->
      lvars_open k y (tm_lvars_at d e) ⊆ dom (σ : gmap logic_var value) ->
      lstore_instantiate_tm_at d
        (lstore_swap (LVBound k) (LVFree y) σ) e =
      lstore_instantiate_tm_at d σ
        (open_tm (d + k) (vfvar y) e)).
Proof.
  apply value_tm_mutind;
    cbn [lstore_instantiate_value_at lstore_instantiate_tm_at
      lstore_instantiate_value_split_at lstore_instantiate_tm_split_at
      open_value open_tm fv_value fv_tm value_lvars_at tm_lvars_at];
    intros; try reflexivity.
  - unfold lstore_free_part.
    rewrite !lstore_to_store_lookup, lstore_swap_lookup_inv_value.
    rewrite key_swap_fresh by (set_solver || congruence).
    reflexivity.
  - destruct (decide (d + k = n)) as [Heq|Hneq].
    + subst n.
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      rewrite lstore_bound_part_lookup, lstore_swap_lookup_inv_value.
      replace (d + k - d) with k by lia.
      rewrite key_swap_l.
      cbn [lstore_instantiate_value_split_at].
      unfold lstore_free_part. rewrite lstore_to_store_lookup.
      destruct ((σ : gmap logic_var value) !! LVFree y) as [u|] eqn:Hlook;
        [reflexivity|].
      exfalso.
      assert (LVFree y ∈ dom (σ : gmap logic_var value)).
      {
        apply H0.
        unfold bvar_lvars_at.
        rewrite decide_True by lia.
        replace (d + k - d) with k by lia.
        rewrite lvars_open_unfold, gset_swap_singleton.
        rewrite key_swap_l.
        apply elem_of_singleton. reflexivity.
      }
      apply not_elem_of_dom in Hlook. exact (Hlook H1).
    + destruct (decide (d <= n)) as [Hdn|Hdn].
      * rewrite lstore_bound_part_lookup, lstore_swap_lookup_inv_value.
        rewrite key_swap_fresh.
        -- cbn [lstore_instantiate_value_split_at].
           rewrite decide_True by exact Hdn.
           rewrite lstore_bound_part_lookup. reflexivity.
        -- intros Heq. inversion Heq. lia.
        -- discriminate.
      * cbn [lstore_instantiate_value_split_at].
        rewrite decide_False by exact Hdn.
        reflexivity.
  - f_equal.
    replace (S d + k) with (S (d + k)) by lia.
    apply H; assumption.
  - f_equal.
    replace (S d + k) with (S (d + k)) by lia.
    apply H; assumption.
  - f_equal.
    match goal with
    | |- lstore_instantiate_value_split_at d _ _ ?v =
         lstore_instantiate_value_split_at d _ _
           (open_value (d + k) (vfvar y) ?v) =>
        change (lstore_instantiate_value_at d
          (lstore_swap (LVBound k) (LVFree y) σ) v =
        lstore_instantiate_value_at d σ (open_value (d + k) (vfvar y) v))
    end.
    apply H; assumption.
  - change (lstore_instantiate_tm_split_at d
        (lstore_free_part (lstore_swap (LVBound k) (LVFree y) σ))
        (StoreInterfaceCore.lstore_bound_part
          (lstore_swap (LVBound k) (LVFree y) σ)) e1)
      with (lstore_instantiate_tm_at d
        (lstore_swap (LVBound k) (LVFree y) σ) e1).
    change (lstore_instantiate_tm_split_at d (lstore_free_part σ)
        (StoreInterfaceCore.lstore_bound_part σ)
        (open_tm (d + k) (vfvar y) e1))
      with (lstore_instantiate_tm_at d σ
        (open_tm (d + k) (vfvar y) e1)).
    rewrite H.
    2:{ set_solver. }
    2:{ set_solver. }
    f_equal.
    replace (S d + k) with (S (d + k)) by lia.
    apply H0.
    + set_solver.
    + set_solver.
  - f_equal.
    match goal with
    | |- lstore_instantiate_value_split_at d _ _ ?v =
         lstore_instantiate_value_split_at d _ _
           (open_value (d + k) (vfvar y) ?v) =>
        change (lstore_instantiate_value_at d
          (lstore_swap (LVBound k) (LVFree y) σ) v =
        lstore_instantiate_value_at d σ (open_value (d + k) (vfvar y) v))
    end.
    apply H; assumption.
  - f_equal.
    + match goal with
      | |- lstore_instantiate_value_split_at d _ _ ?v =
           lstore_instantiate_value_split_at d _ _
             (open_value (d + k) (vfvar y) ?v) =>
          change (lstore_instantiate_value_at d
            (lstore_swap (LVBound k) (LVFree y) σ) v =
          lstore_instantiate_value_at d σ (open_value (d + k) (vfvar y) v))
      end.
      apply H; set_solver.
    + match goal with
      | |- lstore_instantiate_value_split_at d _ _ ?v =
           lstore_instantiate_value_split_at d _ _
             (open_value (d + k) (vfvar y) ?v) =>
          change (lstore_instantiate_value_at d
            (lstore_swap (LVBound k) (LVFree y) σ) v =
          lstore_instantiate_value_at d σ (open_value (d + k) (vfvar y) v))
      end.
      apply H0; set_solver.
  - f_equal.
    + match goal with
      | |- lstore_instantiate_value_split_at d _ _ ?v =
           lstore_instantiate_value_split_at d _ _
             (open_value (d + k) (vfvar y) ?v) =>
          change (lstore_instantiate_value_at d
            (lstore_swap (LVBound k) (LVFree y) σ) v =
          lstore_instantiate_value_at d σ (open_value (d + k) (vfvar y) v))
      end.
      apply H; set_solver.
    + match goal with
      | |- lstore_instantiate_tm_split_at d _ _ ?e =
           lstore_instantiate_tm_split_at d _ _
             (open_tm (d + k) (vfvar y) ?e) =>
          change (lstore_instantiate_tm_at d
            (lstore_swap (LVBound k) (LVFree y) σ) e =
          lstore_instantiate_tm_at d σ (open_tm (d + k) (vfvar y) e))
      end.
      apply H0; set_solver.
    + match goal with
      | |- lstore_instantiate_tm_split_at d _ _ ?e =
           lstore_instantiate_tm_split_at d _ _
             (open_tm (d + k) (vfvar y) ?e) =>
          change (lstore_instantiate_tm_at d
            (lstore_swap (LVBound k) (LVFree y) σ) e =
          lstore_instantiate_tm_at d σ (open_tm (d + k) (vfvar y) e))
      end.
      apply H1; set_solver.
Qed.

Lemma lstore_instantiate_tm_insert_open
    e x vx (σ : StoreT) :
  store_closed σ ->
  lc_value vx ->
  x ∉ dom σ ∪ fv_tm e ->
  lstore_instantiate_tm
    (<[LVFree x := vx]> (lstore_lift_free σ : LStoreT) : LStoreT)
    (open_tm 0 (vfvar x) e) =
  open_tm 0 vx
    (lstore_instantiate_tm_at 1 (lstore_lift_free σ : LStoreT) e).
Proof.
  intros [_ Hlcenv] Hvx_lc Hfresh.
  rewrite <- lstore_lift_free_insert.
  unfold lstore_instantiate_tm.
  unfold lstore_instantiate_tm_at.
  rewrite !lstore_free_part_lift_free.
  rewrite !lstore_bound_part_empty_of_lc by apply lc_lstore_lift_free.
  change (lstore_instantiate_tm_split_at 0
      (map_insert (M:=gmap atom value) x vx (σ : gmap atom value)) ∅
      (open_tm 0 (vfvar x) e) =
    open_tm 0 vx
      (lstore_instantiate_tm_split_at 1 (σ : StoreT) ∅ e)).
  apply lstore_instantiate_tm_split_insert_open; set_solver.
Qed.

Lemma lstore_instantiate_tm_open_back k y e σ :
  y ∉ fv_tm e ->
  lvars_open k y (tm_lvars e) ⊆ dom (σ : gmap logic_var value) ->
  lstore_instantiate_tm (lstore_swap (LVBound k) (LVFree y) σ) e =
  lstore_instantiate_tm σ (open_tm k (vfvar y) e).
Proof.
  intros Hy Hdom.
  unfold lstore_instantiate_tm.
  change k with (0 + k) at 1.
  apply (snd lstore_instantiate_open_back_mutual); exact Hy || exact Hdom.
Qed.

Lemma expr_eval_in_store_open_back_iff k y e v σ :
  y ∉ fv_tm e ->
  lvars_open k y (tm_lvars e) ⊆ dom (σ : gmap logic_var value) ->
  expr_eval_in_store (lstore_swap (LVBound k) (LVFree y) σ) e v <->
  expr_eval_in_store σ (open_tm k (vfvar y) e) v.
Proof.
  intros Hy Hdom.
  unfold expr_eval_in_store.
  rewrite lstore_instantiate_tm_open_back by (exact Hy || exact Hdom).
  reflexivity.
Qed.

Lemma expr_total_on_open_back_iff k y e
    (w : LWorldOn (V:=value) (lvars_open k y (tm_lvars e))) :
  y ∉ fv_tm e ->
  expr_total_on e
    (@lw value _ (lworld_on_open_back k y (tm_lvars e) w)) <->
  expr_total_on (open_tm k (vfvar y) e) (@lw value _ w).
Proof.
  intros Hy.
  unfold expr_total_on.
  rewrite tm_lvars_open by exact Hy.
  split; intros [_ Hstores].
  - split.
    + change (worldA_dom (@lw value _ w : LWorldT)) with
        (lworld_dom (@lw value _ w)).
      rewrite (@lw_dom value _ w). set_solver.
    + intros τ Hτ.
      pose proof (Hstores (lstore_swap (LVBound k) (LVFree y) τ)) as Hres.
      assert (Hτswap :
        worldA_stores
          (@lw value _ (lworld_on_open_back k y (tm_lvars e) w) : LWorldT)
          (lstore_swap (LVBound k) (LVFree y) τ)).
      {
        unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_stores].
        exists τ. split; [exact Hτ | reflexivity].
      }
      specialize (Hres Hτswap).
      destruct Hres as [v Heval]. exists v.
      assert (Hτdom :
        lvars_open k y (tm_lvars e) ⊆ dom (τ : gmap logic_var value)).
      {
        pose proof (wfworldA_store_dom (@lw value _ w) τ Hτ) as Hdomτ.
        change (dom (τ : gmap logic_var value) =
          lworld_dom (@lw value _ w)) in Hdomτ.
        rewrite Hdomτ, (@lw_dom value _ w). set_solver.
      }
      apply expr_eval_in_store_open_back_iff in Heval;
        [exact Heval | exact Hy | exact Hτdom].
  - split.
    + unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_dom].
      rewrite lworld_dom_lres_swap, (@lw_dom value _ w).
      rewrite lvars_open_unfold, gset_swap_involutive. set_solver.
    + intros σ Hσ.
      unfold lworld_on_open_back in Hσ. cbn [lw lraw_world raw_worldA worldA_stores] in Hσ.
      destruct Hσ as [σ0 [Hσ0 Hswap]]. subst σ.
      destruct (Hstores σ0 Hσ0) as [v Heval]. exists v.
      assert (Hσ0dom :
        lvars_open k y (tm_lvars e) ⊆ dom (σ0 : gmap logic_var value)).
      {
        pose proof (wfworldA_store_dom (@lw value _ w) σ0 Hσ0) as Hdomσ0.
        change (dom (σ0 : gmap logic_var value) =
          lworld_dom (@lw value _ w)) in Hdomσ0.
        rewrite Hdomσ0, (@lw_dom value _ w). set_solver.
      }
      apply expr_eval_in_store_open_back_iff; [exact Hy | exact Hσ0dom | exact Heval].
Qed.

Lemma formula_open_expr_total_formula k y e :
  y ∉ fv_tm e ->
  formula_open k y (expr_total_formula e) =
  expr_total_formula (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold expr_total_formula, expr_total_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - symmetry. apply tm_lvars_open. exact Hy.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    transitivity (expr_total_on (open_tm k (vfvar y) e) (@lw value _ w1)).
    + apply expr_total_on_open_back_iff. exact Hy.
    + rewrite Hlw. reflexivity.
Qed.

Lemma expr_result_at_store_open_back_iff k y e z σ :
  y ∉ fv_tm e ->
  lvars_open k y (tm_lvars e) ⊆ dom (σ : gmap logic_var value) ->
  expr_result_at_store e z (lstore_swap (LVBound k) (LVFree y) σ) <->
  expr_result_at_store
    (open_tm k (vfvar y) e) (logic_var_open k y z) σ.
Proof.
  intros Hy Hdom.
  unfold expr_result_at_store.
  rewrite tm_lvars_open by exact Hy.
  split; intros [Hz [v [Hlookup Heval]]].
  - split.
    + rewrite lvars_open_unfold, gset_swap_elem.
      rewrite logic_var_open_unfold, eq_swap_involutive.
      exact Hz.
    + exists v. split.
      * rewrite lstore_swap_lookup_inv_value in Hlookup.
        change (key_swap (LVBound k) (LVFree y) z) with
          (logic_var_open k y z) in Hlookup.
        exact Hlookup.
      * apply expr_eval_in_store_open_back_iff in Heval;
          [exact Heval | exact Hy | exact Hdom].
  - split.
    + rewrite lvars_open_unfold, gset_swap_elem in Hz.
      rewrite logic_var_open_unfold, eq_swap_involutive in Hz.
      exact Hz.
    + exists v. split.
      * change ((lstore_swap (LVBound k) (LVFree y) σ : gmap logic_var value) !! z = Some v).
        rewrite lstore_swap_lookup_inv_value.
        change (key_swap (LVBound k) (LVFree y) z) with (logic_var_open k y z).
        exact Hlookup.
      * apply expr_eval_in_store_open_back_iff; [exact Hy | exact Hdom | exact Heval].
Qed.

Lemma expr_result_at_world_open_back_iff k y e z
    (w : LWorldOn (V:=value) (lvars_open k y (tm_lvars e ∪ {[z]}))) :
  y ∉ fv_tm e ->
  expr_result_at_world e z
    (@lw value _ (lworld_on_open_back k y (tm_lvars e ∪ {[z]}) w)) <->
  expr_result_at_world
    (open_tm k (vfvar y) e) (logic_var_open k y z)
    (@lw value _ w).
Proof.
  intros Hy.
  unfold expr_result_at_world.
  rewrite tm_lvars_open by exact Hy.
  split; intros [Hz [_ Hstores]].
  - split.
    + rewrite lvars_open_unfold, gset_swap_elem.
      rewrite logic_var_open_unfold, eq_swap_involutive.
      exact Hz.
    + split.
      * change (worldA_dom (@lw value _ w : LWorldT)) with
          (lworld_dom (@lw value _ w)).
        rewrite (@lw_dom value _ w). set_solver.
      * intros τ Hτ.
        pose proof (Hstores (lstore_swap (LVBound k) (LVFree y) τ)) as Hres.
        assert (Hσswap :
          worldA_stores
            (@lw value _ (lworld_on_open_back k y (tm_lvars e ∪ {[z]}) w) : LWorldT)
            (lstore_swap (LVBound k) (LVFree y) τ)).
        {
          unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_stores].
          exists τ. split; [exact Hτ | reflexivity].
        }
        specialize (Hres Hσswap).
        assert (Hτdom :
          lvars_open k y (tm_lvars e) ⊆ dom (τ : gmap logic_var value)).
        {
          pose proof (wfworldA_store_dom (@lw value _ w) τ Hτ) as Hdomτ.
          change (dom (τ : gmap logic_var value) =
            lworld_dom (@lw value _ w)) in Hdomτ.
          rewrite Hdomτ, (@lw_dom value _ w).
          set_solver.
        }
        apply expr_result_at_store_open_back_iff in Hres;
          [exact Hres | exact Hy | exact Hτdom].
  - split.
    + rewrite lvars_open_unfold, gset_swap_elem in Hz.
      rewrite logic_var_open_unfold, eq_swap_involutive in Hz.
      exact Hz.
    + split.
      * change (tm_lvars e ∪ {[z]} ⊆
          worldA_dom
            (@lw value _ (lworld_on_open_back k y (tm_lvars e ∪ {[z]}) w) : LWorldT)).
        unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_dom].
        rewrite lworld_dom_lres_swap, (@lw_dom value _ w).
        rewrite lvars_open_unfold, gset_swap_involutive. set_solver.
      * intros σ Hσ.
        unfold lworld_on_open_back in Hσ. cbn [lw lraw_world raw_worldA worldA_stores] in Hσ.
        destruct Hσ as [σ0 [Hσ0 Hswap]]. subst σ.
        assert (Hσ0dom :
          lvars_open k y (tm_lvars e) ⊆ dom (σ0 : gmap logic_var value)).
        {
          pose proof (wfworldA_store_dom (@lw value _ w) σ0 Hσ0) as Hdomσ0.
          change (dom (σ0 : gmap logic_var value) =
            lworld_dom (@lw value _ w)) in Hdomσ0.
          rewrite Hdomσ0, (@lw_dom value _ w).
          set_solver.
        }
        apply expr_result_at_store_open_back_iff; [exact Hy | exact Hσ0dom |].
        apply Hstores. exact Hσ0.
Qed.

Lemma tm_lvars_open_result_domain k y e z :
  y ∉ fv_tm e ->
  lvars_open k y (tm_lvars e ∪ {[z]}) =
  tm_lvars (open_tm k (vfvar y) e) ∪ {[logic_var_open k y z]}.
Proof.
  intros Hy.
  rewrite lvars_open_unfold, gset_swap_union, <- lvars_open_unfold.
  rewrite tm_lvars_open by exact Hy.
  rewrite gset_swap_singleton.
  change (key_swap (LVBound k) (LVFree y) z) with (logic_var_open k y z).
  reflexivity.
Qed.

Lemma formula_open_expr_result_formula k y e z :
  y ∉ fv_tm e ->
  formula_open k y (expr_result_formula e z) =
  expr_result_formula
    (open_tm k (vfvar y) e) (logic_var_open k y z).
Proof.
  intros Hy.
  unfold expr_result_formula, expr_result_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - apply tm_lvars_open_result_domain. exact Hy.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    transitivity (expr_result_at_world
      (open_tm k (vfvar y) e) (logic_var_open k y z)
      (@lw value _ w1)).
    + apply expr_result_at_world_open_back_iff. exact Hy.
    + rewrite Hlw. reflexivity.
Qed.

Lemma expr_result_extension_shape e x Hfresh :
  ext_in (expr_result_extension e x Hfresh) = fv_tm e /\
  ext_out (expr_result_extension e x Hfresh) = {[x]}.
Proof.
  unfold expr_result_extension, ext_in, ext_out, mk_fiber_extension.
  simpl. split; reflexivity.
Qed.

Record expr_result_extension_witness
    (e : tm) (x : atom) (Fx : FiberExtensionT) : Prop := {
  expr_result_extension_witness_fresh : x ∉ fv_tm e;
  expr_result_extension_witness_shape :
    ext_in Fx = fv_tm e /\ ext_out Fx = {[x]};
  expr_result_extension_witness_rel :
    forall σ,
      dom σ = fv_tm e ->
      ext_rel Fx σ (expr_result_output_world e x σ);
}.

Lemma expr_result_extension_witness_exists e x :
  x ∉ fv_tm e ->
  exists Fx, expr_result_extension_witness e x Fx.
Proof.
  intros Hfresh.
  exists (expr_result_extension e x Hfresh).
  constructor.
  - exact Hfresh.
  - apply expr_result_extension_shape.
  - intros σ Hdom.
    unfold expr_result_extension, ext_rel, mk_fiber_extension,
      mk_fiber_extension_rel.
    simpl. reflexivity.
Qed.

Lemma expr_result_extension_apply_total_store e x F σ w v :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  expr_eval_in_atom_store σ e v ->
  (w : WorldT) ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Heval.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (proj2 (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) ({[x := v]} : StoreT)
    HdomF Hrel Hcanonical)) as Hto.
  apply Hto.
  unfold expr_result_output_world.
  destruct (excluded_middle_informative (exists v0, expr_eval_in_atom_store σ e v0))
    as [Hex | Hnone].
  - destruct (constructive_indefinite_description _ Hex) as [v0 Heval0].
    assert (v0 = v).
    {
      unfold expr_eval_in_atom_store, expr_eval_in_store in *.
      eapply steps_result_unique; eauto.
    }
    subst v0. simpl. reflexivity.
  - exfalso. apply Hnone. exists v. exact Heval.
Qed.

Lemma expr_result_extension_apply_total_iff e x F σ w :
  expr_result_extension_witness e x F ->
  dom σ = fv_tm e ->
  ext_rel F σ w ->
  (exists v, expr_eval_in_atom_store σ e v) ->
  forall σout,
    (w : WorldT) σout <->
    exists v, expr_eval_in_atom_store σ e v /\ σout = ({[x := v]} : StoreT).
Proof.
  intros Hwitness Hdom Hrel Htotal σout.
  destruct Hwitness as [Hfresh [Hin Hout] Hwrel].
  pose proof (Hwrel σ Hdom) as Hcanonical.
  assert (HdomF : dom σ = extA_in F).
  { unfold ext_in in Hin. rewrite Hin. exact Hdom. }
  pose proof (extA_rel_extensional F σ w
    (expr_result_output_world e x σ) σout HdomF Hrel Hcanonical) as Hext.
  split.
  - intros Hw.
    apply Hext in Hw.
    unfold expr_result_output_world in Hw.
    destruct (excluded_middle_informative (exists v, expr_eval_in_atom_store σ e v))
      as [Hex | Hnone].
    + destruct (constructive_indefinite_description _ Hex) as [v Hv].
      exists v. split; [exact Hv|].
      simpl in Hw. subst σout. reflexivity.
    + exfalso. apply Hnone. exact Htotal.
  - intros [v [Heval ->]].
    eapply expr_result_extension_apply_total_store; eauto.
    constructor; [exact Hfresh|split; assumption|exact Hwrel].
Qed.

Lemma result_extension_has_ltype_from_basic_world
    (Σ : lty_env) (T : ty) (e1 : tm) (m mx : WfWorldT)
    (Fx : FiberExtensionT) (x : atom) :
  LVFree x ∉ dom Σ ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  res_models mx (basic_world_formula (<[LVFree x := T]> Σ)) ->
  extension_has_ltype (<[LVFree x := T]> ∅) (res_restrict m (ext_in Fx)) Fx.
Proof.
  intros HxΣ Hwitness Hext Hmx_basic.
  destruct Hwitness as [Hx_fv [Hin Hout] Hrel].
  apply basic_world_formula_models_iff in Hmx_basic as [_ [_ Hmx_typed]].
  unfold extension_has_ltype.
  split.
  - simpl. pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
    unfold ext_in in Hin_sub. set_solver.
  - split.
    + intros [k|y] Hy; cbn [lc_logic_var_key]; [|exact I].
      change (LVBound k ∈ dom ({[LVFree x := T]} : gmap logic_var ty)) in Hy.
      rewrite dom_singleton_L in Hy. set_solver.
    + split.
      * change (lvars_fv (dom ({[LVFree x := T]} : gmap logic_var ty)) = ext_out Fx).
        rewrite dom_singleton_L.
        rewrite lvars_fv_singleton_free.
        rewrite Hout. set_solver.
      * intros σout mout Hσout HF.
        unfold lworld_has_type, worldA_has_type.
        split.
        -- change (dom ({[LVFree x := T]} : gmap logic_var ty) ⊆
             worldA_dom (res_lift_free mout : LWorldT)).
           rewrite dom_singleton_L, res_lift_free_dom.
           pose proof (extA_rel_dom Fx σout mout) as Hdom_mout.
           assert (dom (σout : gmap atom value) = ext_in Fx) as Hσout_dom.
           {
             simpl in Hσout.
             destruct Hσout as [σm [Hσm Hrestrict]].
             rewrite <- Hrestrict.
             change (dom (store_restrict σm (ext_in Fx) : gmap atom value) = ext_in Fx).
             rewrite store_restrict_dom.
             pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
             unfold ext_in in Hin_sub.
             pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
             change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
             rewrite Hσm_dom. set_solver.
           }
           specialize (Hdom_mout Hσout_dom HF).
           change (world_dom (mout : WorldT) = ext_out Fx) in Hdom_mout.
           intros v Hv.
           rewrite elem_of_singleton in Hv. subst v.
           unfold lvars_of_atoms. apply elem_of_map.
           exists x. split; [reflexivity|].
           change (x ∈ world_dom (mout : WorldT)).
           rewrite Hdom_mout, Hout. set_solver.
        -- intros τ Hτ.
           destruct Hτ as [σe [Hσe ->]].
           intros v U u HΣout Hu.
           change (((<[LVFree x := T]> (∅ : lty_env) : lty_env)
             : gmap logic_var ty) !! v = Some U) in HΣout.
           destruct v as [k|y].
           ++ change ((<[LVFree x := T]> (∅ : gmap logic_var ty) : gmap logic_var ty) !!
                LVBound k = Some U) in HΣout.
              rewrite lookup_insert_ne in HΣout by discriminate.
              rewrite lookup_empty in HΣout. discriminate.
           ++ change ((<[LVFree x := T]> (∅ : gmap logic_var ty) : gmap logic_var ty) !!
                LVFree y = Some U) in HΣout.
              destruct (decide (y = x)) as [->|Hyx].
              ** rewrite lookup_insert in HΣout.
                 destruct (decide (LVFree x = LVFree x)) as [_|Hneq];
                   [|congruence].
                 injection HΣout as ->.
                 change (((lstore_lift_free σe : LStoreT) : gmap logic_var value) !!
                   LVFree x = Some u) in Hu.
                 rewrite lstore_lift_free_lookup_free in Hu.
                 simpl in Hσout.
                 destruct Hσout as [σm [Hσm Hrestrict]].
                 rewrite <- Hrestrict in HF.
                 assert (Hmx_store :
                   (mx : WorldT) (σm ∪ σe)).
                 {
                   apply (proj2 (resA_extend_by_store_iff m Fx mx
                     (σm ∪ σe) Hext)).
                   exists σm, mout, σe. repeat split; try assumption.
                 }
                 assert (Hx_not_m : σm !! x = None).
                 {
                   change (((σm : gmap atom value) !! x) = None).
	                   apply not_elem_of_dom.
	                   pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh.
	                   change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh.
	                   rewrite Hout in Hfresh.
                   pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
                   change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
                   rewrite Hσm_dom.
                   set_solver.
                 }
                 destruct Hmx_typed as [_ Hstores_typed].
                 specialize (Hstores_typed (lstore_lift_free (σm ∪ σe))).
                 assert (Hlift_mx :
                   worldA_stores (res_lift_free mx : LWorldT)
                     (lstore_lift_free (σm ∪ σe))).
                 { exists (σm ∪ σe). split; [exact Hmx_store|reflexivity]. }
	                 specialize (Hstores_typed Hlift_mx).
	                 eapply (Hstores_typed (LVFree x) U u).
	                 --- change ((<[LVFree x := U]> (Σ : gmap logic_var ty)
	                        : gmap logic_var ty) !! LVFree x = Some U).
	                     rewrite lookup_insert.
	                     destruct (decide (LVFree x = LVFree x)); [reflexivity|congruence].
                 --- change (((lstore_lift_free (σm ∪ σe) : LStoreT)
                        : gmap logic_var value) !! LVFree x = Some u).
                     rewrite lstore_lift_free_lookup_free.
                     change (((σm : gmap atom value) ∪ (σe : gmap atom value)) !! x = Some u).
                     rewrite storeA_lookup_union_Some_raw.
                     right. split; [exact Hx_not_m|exact Hu].
              ** rewrite lookup_insert_ne in HΣout by congruence.
                 rewrite lookup_empty in HΣout. discriminate.
Qed.

Lemma expr_eval_in_atom_store_tlete_elim_core e1 e2 x σ v :
  store_closed σ ->
  x ∉ dom σ ∪ fv_tm e2 ->
  expr_eval_in_atom_store σ (tlete e1 e2) v ->
  exists vx,
    expr_eval_in_atom_store σ e1 vx /\
    expr_eval_in_atom_store (<[x := vx]> σ) (open_tm 0 (vfvar x) e2) v.
Proof.
  intros Hclosed Hfresh Heval.
  unfold expr_eval_in_atom_store, expr_eval_in_store in *.
  rewrite lstore_instantiate_tm_no_bvars in Heval.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in Heval.
  rewrite subst_map_lete in Heval.
  apply reduction_lete in Heval as [vx [He1 He2]].
  exists vx. split.
  - rewrite lstore_instantiate_tm_no_bvars.
    + rewrite lstore_free_part_lift_free. exact He1.
    + apply lc_lstore_lift_free.
    + rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - pose proof (steps_regular2 _ _ He1) as Hret.
    apply lc_ret_iff_value in Hret as Hvx_lc.
    rewrite lstore_lift_free_insert.
    rewrite lstore_instantiate_tm_insert_open by
      (try exact Hclosed; try exact Hvx_lc; exact Hfresh).
    rewrite lstore_instantiate_tm_at_lc_lstore.
    + rewrite lstore_free_part_lift_free. exact He2.
    + apply lc_lstore_lift_free.
    + rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
Qed.

Lemma expr_eval_in_atom_store_tlete_intro_core e1 e2 x σ vx v :
  store_closed σ ->
  x ∉ dom σ ∪ fv_tm e2 ->
  body_tm (lstore_instantiate_tm_at 1 (lstore_lift_free σ : LStoreT) e2) ->
  expr_eval_in_atom_store σ e1 vx ->
  expr_eval_in_atom_store (<[x := vx]> σ) (open_tm 0 (vfvar x) e2) v ->
  expr_eval_in_atom_store σ (tlete e1 e2) v.
Proof.
  intros Hclosed Hfresh Hbody He1 He2.
  unfold expr_eval_in_atom_store, expr_eval_in_store in *.
  rewrite lstore_instantiate_tm_no_bvars in He1.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in He1.
  pose proof (steps_regular2 _ _ He1) as Hret.
  apply lc_ret_iff_value in Hret as Hvx_lc.
  rewrite lstore_lift_free_insert in He2.
  rewrite lstore_instantiate_tm_insert_open in He2 by
    (try exact Hclosed; try exact Hvx_lc; exact Hfresh).
  rewrite lstore_instantiate_tm_at_lc_lstore in He2.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in He2.
  rewrite lstore_instantiate_tm_at_lc_lstore in Hbody.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free in Hbody.
  rewrite lstore_instantiate_tm_no_bvars.
  2:{ apply lc_lstore_lift_free. }
  2:{ rewrite lstore_free_part_lift_free. exact (proj1 Hclosed). }
  rewrite lstore_free_part_lift_free, subst_map_lete.
  eapply reduction_lete_intro; eauto.
Qed.

Lemma expr_eval_in_atom_store_tlete_intro_closed_on e1 e2 x σ vx v :
  store_closed (store_restrict σ (fv_tm (tlete e1 e2))) ->
  lc_tm (tlete e1 e2) ->
  x ∉ dom σ ∪ fv_tm e2 ->
  expr_eval_in_atom_store (store_restrict σ (fv_tm (tlete e1 e2))) e1 vx ->
  expr_eval_in_atom_store
    (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
    (open_tm 0 (vfvar x) e2) v ->
  expr_eval_in_atom_store σ (tlete e1 e2) v.
Proof.
  intros Hclosed Hlc Hfresh He1 He2.
  apply (proj1 (expr_eval_in_atom_store_restrict_fv_closed_on
    σ (tlete e1 e2) v (proj1 Hclosed))).
  eapply expr_eval_in_atom_store_tlete_intro_core.
  - exact Hclosed.
  - intros Hbad. apply Hfresh.
    apply elem_of_union in Hbad as [Hbad|Hbad].
    + apply elem_of_union. left.
      apply elem_of_dom in Hbad as [u Hlook].
      apply store_restrict_lookup_some in Hlook as [_ Hlook].
      apply elem_of_dom_2 in Hlook. exact Hlook.
    + apply elem_of_union. right. exact Hbad.
  - apply lc_lete_iff_body in Hlc as [_ Hbody].
    rewrite lstore_instantiate_tm_at_lc_lstore.
    + rewrite lstore_free_part_lift_free.
      eapply body_tm_msubst.
      * exact (proj1 Hclosed).
      * exact (proj2 Hclosed).
      * exact Hbody.
    + apply lc_lstore_lift_free.
    + rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
  - exact He1.
  - exact He2.
Qed.

Lemma expr_eval_in_atom_store_tlete_elim_closed_on e1 e2 x σ v :
  store_closed (store_restrict σ (fv_tm (tlete e1 e2))) ->
  x ∉ fv_tm (tlete e1 e2) ->
  x ∉ fv_tm e2 ->
  expr_eval_in_atom_store σ (tlete e1 e2) v ->
  exists vx,
    expr_eval_in_atom_store (store_restrict σ (fv_tm e1)) e1 vx /\
    expr_eval_in_atom_store
      (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
      (e2 ^^ x) v.
Proof.
  intros Hclosed Hxlet Hxe2 Heval.
  set (σT := store_restrict σ (fv_tm (tlete e1 e2))).
  assert (HevalT : expr_eval_in_atom_store σT (tlete e1 e2) v).
  {
    subst σT.
    apply (proj2 (expr_eval_in_atom_store_restrict_fv_closed_on
      σ (tlete e1 e2) v (proj1 Hclosed))).
    exact Heval.
  }
  assert (HfreshT : x ∉ dom (σT : gmap atom value) ∪ fv_tm e2).
  {
    subst σT.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - rewrite store_restrict_dom in Hbad. set_solver.
    - exact (Hxe2 Hbad).
  }
  destruct (expr_eval_in_atom_store_tlete_elim_core e1 e2 x σT v
    Hclosed HfreshT HevalT) as [vx [He1T He2]].
  exists vx. split; [|exact He2].
  assert (Hagree :
    store_restrict σT (fv_tm e1) =
    store_restrict (store_restrict σ (fv_tm e1)) (fv_tm e1)).
  {
    subst σT.
    rewrite (store_restrict_twice_subset σ (fv_tm (tlete e1 e2)) (fv_tm e1)).
    - rewrite store_restrict_twice_same. reflexivity.
    - cbn [fv_tm]. set_solver.
  }
  apply (proj1 (expr_eval_in_atom_store_agree_on_fv
    σT (store_restrict σ (fv_tm e1)) e1 vx Hagree)).
  exact He1T.
Qed.

Lemma expr_total_on_tlete_elim_e1 e1 e2 (m : WfWorldT) :
  (forall σ, (m : WorldT) σ -> store_closed σ) ->
  expr_total_on_atom_world (tlete e1 e2) m ->
  expr_total_on_atom_world e1 m.
Proof.
  intros Hclosed Htotal.
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal as [Hdom Hstores].
  split.
  - cbn [tm_lvars tm_lvars_at] in Hdom. set_solver.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (Hstores (lstore_lift_free σ)) as [v Heval].
    { exists σ. split; [exact Hσ|reflexivity]. }
    pose (x := fresh_for (dom σ ∪ fv_tm e2)).
    assert (Hfresh : x ∉ dom σ ∪ fv_tm e2).
    { unfold x. apply fresh_for_not_in. }
    destruct (expr_eval_in_atom_store_tlete_elim_core
      e1 e2 x σ v (Hclosed σ Hσ) Hfresh Heval) as [vx [He1 _]].
    exists vx. exact He1.
Qed.

Lemma expr_eval_in_atom_store_tlete_elim e1 e2 x σ v :
  store_closed σ ->
  x ∉ dom σ ∪ fv_tm e2 ->
  expr_eval_in_atom_store σ (tlete e1 e2) v ->
  exists vx,
    expr_eval_in_atom_store σ e1 vx /\
    expr_eval_in_atom_store (<[x := vx]> σ) (open_tm 0 (vfvar x) e2) v.
Proof.
  apply expr_eval_in_atom_store_tlete_elim_core.
Qed.

Lemma expr_eval_in_atom_store_tlete_intro e1 e2 x σ vx v :
  store_closed σ ->
  x ∉ dom σ ∪ fv_tm e2 ->
  body_tm (lstore_instantiate_tm_at 1 (lstore_lift_free σ : LStoreT) e2) ->
  expr_eval_in_atom_store σ e1 vx ->
  expr_eval_in_atom_store (<[x := vx]> σ) (open_tm 0 (vfvar x) e2) v ->
  expr_eval_in_atom_store σ (tlete e1 e2) v.
Proof.
  apply expr_eval_in_atom_store_tlete_intro_core.
Qed.

Lemma expr_total_formula_models_iff e (m : WfWorldT) :
  res_models m (expr_total_formula e) <->
  logic_qualifier_denote (expr_total_lqual e) m.
Proof.
  unfold res_models, expr_total_formula.
  cbn [formula_measure res_models_fuel].
  split; [tauto |].
  intros Hden. split; [| exact Hden].
  destruct Hden as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma expr_total_formula_to_atom_world e (m : WfWorldT) :
  res_models m (expr_total_formula e) ->
  expr_total_on_atom_world e m.
Proof.
  intros Hmodels.
  apply expr_total_formula_models_iff in Hmodels.
  unfold expr_total_lqual, logic_qualifier_denote in Hmodels.
  destruct Hmodels as [Hlc [Hsub Htotal]].
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal as [_ Hstores].
  split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply Hsub. apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    assert (HτD :
        (@lw value _ (lworld_on_lift (tm_lvars e) m Hlc Hsub) : LWorldT)
        (storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e))).
    {
      unfold lworld_on_lift.
      cbn [lw lraw_world raw_worldA worldA_stores].
      exists (lstore_lift_free (storeA_restrict σ (lvars_fv (tm_lvars e))) : LStoreT).
      split.
      - exists (storeA_restrict σ (lvars_fv (tm_lvars e))). split.
        + change ((res_restrict m (lvars_fv (tm_lvars e)) : WorldT)
            (storeA_restrict σ (lvars_fv (tm_lvars e)))).
          exists σ. split; [exact Hσ|reflexivity].
        + reflexivity.
      - apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    destruct (Hstores _ HτD) as [v Heval].
    exists v.
    apply (proj1 (expr_eval_in_store_restrict_lvars e
      (lstore_lift_free σ : LStoreT) (tm_lvars e) v ltac:(set_solver))).
    exact Heval.
Qed.

Lemma expr_total_atom_world_to_formula e (m : WfWorldT) :
  expr_total_on_atom_world e m ->
  res_models m (expr_total_formula e).
Proof.
  intros Htotal.
  apply expr_total_formula_models_iff.
  unfold expr_total_lqual, logic_qualifier_denote.
  destruct Htotal as [Hdom Hstores].
  assert (Hlc : lc_lvars (tm_lvars e)).
  {
    unfold lc_lvars. intros v Hv.
    specialize (Hdom _ Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]].
    destruct v as [k|b]; [discriminate|exact I].
  }
  assert (Hsub : lvars_fv (tm_lvars e) ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    assert (LVFree a ∈ tm_lvars e) as HaD.
    { apply lvars_fv_elem. exact Ha. }
    specialize (Hdom _ HaD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [b [Heq Hb]].
    inversion Heq. subst b. exact Hb.
  }
  exists Hlc, Hsub.
  unfold expr_total_on_atom_world, expr_total_on in Hstores.
  split.
  - unfold lworld_on_lift. cbn. intros v Hv.
    apply elem_of_intersection. split; [|exact Hv].
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply elem_of_intersection. split.
      * apply Hsub. apply lvars_fv_elem. exact Hv.
      * apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    unfold lworld_on_lift in Hτ.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hτ.
    destruct Hτ as [τ0 [Hτ0 Hrestrict]]. subst τ.
    destruct Hτ0 as [σr [Hσr ->]].
    destruct Hσr as [σ [Hσ Hσr_eq]].
    subst σr.
    destruct (Hstores (lstore_lift_free σ)) as [v Heval].
    { exists σ. split; [exact Hσ|reflexivity]. }
    exists v.
    replace (storeA_restrict
        (lstore_lift_free (storeA_restrict σ (lvars_fv (tm_lvars e))) : LStoreT)
        (tm_lvars e))
      with (storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e)).
    2:{
      symmetry. apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    apply (proj2 (expr_eval_in_store_restrict_lvars e
      (lstore_lift_free σ : LStoreT) (tm_lvars e) v ltac:(set_solver))).
    exact Heval.
Qed.

Lemma expr_total_formula_tlete_intro_from_result_extension
    (Σ : lty_env) T e1 e2 x (m mx : WfWorldT) Fx :
  LVFree x ∉ dom Σ ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ T ->
  res_models m (basic_world_formula Σ) ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by m Fx mx ->
  res_models m (expr_total_formula e1) ->
  res_models mx (expr_total_formula (e2 ^^ x)) ->
  res_models m (expr_total_formula (tlete e1 e2)).
Proof.
  intros HxΣ Hty Hbasic HFx Hext Htotal1 Htotal2.
  apply expr_total_atom_world_to_formula.
  pose proof (typing_tm_lc _ _ _ Hty) as Hlc_let.
  assert (Hfv_let : fv_tm (tlete e1 e2) ⊆ lvars_fv (dom Σ)).
  {
    pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv_atom.
    pose proof (lty_env_to_atom_env_dom_subset Σ) as Hdom.
    unfold lty_env_atom_dom in Hdom. set_solver.
  }
  pose proof (expr_total_formula_to_atom_world _ _ Htotal1) as Htotal1_atom.
  pose proof (expr_total_formula_to_atom_world _ _ Htotal2) as Htotal2_atom.
  pose proof Hbasic as Hbasic_den.
  apply basic_world_formula_models_iff in Hbasic_den as [_ [HΣdom _]].
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal1_atom as [_ Htotal1_stores].
  destruct Htotal2_atom as [_ Htotal2_stores].
  split.
  - rewrite (tm_lvars_lc_eq_atoms _ Hlc_let), res_lift_free_dom.
    unfold lvars_of_atoms.
    intros v Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    apply elem_of_map. exists a. split; [reflexivity|].
    apply HΣdom. apply Hfv_let. exact Ha.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (Htotal1_stores (lstore_lift_free σ)) as [vx He1].
    { exists σ. split; [exact Hσ|reflexivity]. }
    destruct HFx as [Hx_fv [Hin Hout] Hrel].
    assert (Hx_dom : x ∉ dom (σ : gmap atom value)).
    {
      pose proof (res_extend_by_output_fresh m Fx mx Hext) as Hfresh.
      change (ext_out Fx ## world_dom (m : WorldT)) in Hfresh.
      pose proof (wfworldA_store_dom m σ Hσ) as Hσdom.
      change (dom (σ : gmap atom value) = world_dom (m : WorldT)) in Hσdom.
      rewrite Hσdom.
      rewrite Hout in Hfresh. set_solver.
    }
    assert (Hx_let : x ∉ fv_tm (tlete e1 e2)).
    {
      intros Hx.
      apply HxΣ.
      apply lvars_fv_elem.
      apply Hfv_let in Hx.
      exact Hx.
    }
    assert (Hx_e2 : x ∉ fv_tm e2).
    { cbn [fv_tm] in Hx_let. set_solver. }
    set (σX := store_restrict σ (fv_tm e1)).
    assert (HσX_dom : dom (σX : gmap atom value) = fv_tm e1).
    {
      subst σX. rewrite store_restrict_dom.
      pose proof (res_extend_by_input_dom m Fx mx Hext) as Hin_sub.
      unfold ext_in in Hin_sub. rewrite <- Hin.
      pose proof (wfworldA_store_dom m σ Hσ) as Hσdom.
      change (dom (σ : gmap atom value) = world_dom (m : WorldT)) in Hσdom.
      rewrite Hσdom. set_solver.
    }
    assert (HFrel : ext_rel Fx σX (expr_result_output_world e1 x σX)).
    { subst σX. apply Hrel. exact HσX_dom. }
    assert (He1X : expr_eval_in_atom_store σX e1 vx).
    {
      subst σX.
      apply (proj2 (expr_eval_in_atom_store_restrict_fv_exact σ e1 vx)).
      exact He1.
    }
    pose proof (expr_result_extension_apply_total_iff
      e1 x Fx σX (expr_result_output_world e1 x σX)
      {| expr_result_extension_witness_fresh := Hx_fv;
         expr_result_extension_witness_shape := conj Hin Hout;
         expr_result_extension_witness_rel := Hrel |}
      HσX_dom HFrel (ex_intro _ vx He1X) ({[x := vx]} : StoreT)) as Hout_store.
    assert (Hσe :
      (expr_result_output_world e1 x σX : WorldT) ({[x := vx]} : StoreT)).
    {
      apply Hout_store.
      exists vx. split; [exact He1X|reflexivity].
    }
    assert (Hmx_store :
      (mx : WorldT) (σ ∪ ({[x := vx]} : StoreT))).
    {
      apply (proj2 (resA_extend_by_store_iff m Fx mx _ Hext)).
      exists σ, (expr_result_output_world e1 x σX), ({[x := vx]} : StoreT).
      split; [exact Hσ|].
      split.
      - replace (storeA_restrict σ (extA_in Fx)) with σX.
        + exact HFrel.
        + subst σX. unfold ext_in in Hin. rewrite Hin. reflexivity.
      - split; [exact Hσe|reflexivity].
    }
    destruct (Htotal2_stores (lstore_lift_free (σ ∪ ({[x := vx]} : StoreT))))
      as [v He2_union].
    { exists (σ ∪ ({[x := vx]} : StoreT)). split; [exact Hmx_store|reflexivity]. }
    assert (He2_insert :
      expr_eval_in_atom_store
        (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ x) v).
    {
      assert (Hagree :
        store_restrict (σ ∪ ({[x := vx]} : StoreT)) (fv_tm (e2 ^^ x)) =
        store_restrict (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
          (fv_tm (e2 ^^ x))).
      {
        apply store_insert_restrict_agree_on_open_fv.
        - cbn [fv_tm] in Hfv_let. set_solver.
        - exact Hx_let.
        - exact Hx_dom.
      }
      apply (proj1 (expr_eval_in_atom_store_agree_on_fv
        (σ ∪ ({[x := vx]} : StoreT))
        (<[x := vx]> (store_restrict σ (fv_tm (tlete e1 e2))))
        (e2 ^^ x) v Hagree)).
      exact He2_union.
    }
    exists v.
    eapply expr_eval_in_atom_store_tlete_intro_closed_on.
    + assert (Hsub_atoms :
        lvars_of_atoms (fv_tm (tlete e1 e2)) ⊆ dom Σ).
      {
        unfold lvars_of_atoms. intros lv Hlv.
        apply elem_of_map in Hlv as [a [-> Ha]].
        apply lvars_fv_elem. apply Hfv_let. exact Ha.
      }
      exact ((basic_world_formula_wfworld_closed_on_atoms
        Σ (fv_tm (tlete e1 e2)) m Hsub_atoms Hbasic) σ Hσ).
    + exact Hlc_let.
    + intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
      * exact (Hx_dom Hbad).
      * exact (Hx_e2 Hbad).
    + apply (proj2 (expr_eval_in_atom_store_restrict_fv_subset
        σ e1 vx (fv_tm (tlete e1 e2)) ltac:(cbn [fv_tm]; set_solver))).
      exact He1.
    + exact He2_insert.
Qed.

Lemma expr_result_formula_models_iff e x (m : WfWorldT) :
  res_models m (expr_result_formula e x) <->
  logic_qualifier_denote (expr_result_lqual e x) m.
Proof.
  unfold res_models, expr_result_formula.
  cbn [formula_measure res_models_fuel].
  split; [tauto |].
  intros Hden. split; [| exact Hden].
  destruct Hden as [_ [Hsub _]].
  exact Hsub.
Qed.

Lemma expr_result_formula_to_atom_world e x (m : WfWorldT) :
  res_models m (expr_result_formula e x) ->
  expr_result_at_world e x (res_lift_free m : LWorldT).
Proof.
  intros Hmodels.
  apply expr_result_formula_models_iff in Hmodels.
  unfold expr_result_lqual, logic_qualifier_denote in Hmodels.
  destruct Hmodels as [Hlc [Hsub Hresult]].
  destruct Hresult as [Hx [Hdom Hstores]].
  split; [exact Hx|]. split.
  - rewrite res_lift_free_dom.
    intros v Hv.
    destruct v as [k|a].
    + exfalso. exact (Hlc _ Hv).
    + unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply Hsub. apply lvars_fv_elem. exact Hv.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    assert (HτD :
        (@lw value _ (lworld_on_lift (tm_lvars e ∪ {[x]}) m Hlc Hsub) : LWorldT)
        (storeA_restrict (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[x]}))).
    {
      unfold lworld_on_lift.
      cbn [lw lraw_world raw_worldA worldA_stores].
      exists (lstore_lift_free
        (storeA_restrict σ (lvars_fv (tm_lvars e ∪ {[x]}))) : LStoreT).
      split.
      - exists (storeA_restrict σ (lvars_fv (tm_lvars e ∪ {[x]}))). split.
        + change ((res_restrict m (lvars_fv (tm_lvars e ∪ {[x]})) : WorldT)
            (storeA_restrict σ (lvars_fv (tm_lvars e ∪ {[x]})))).
          exists σ. split; [exact Hσ|reflexivity].
        + reflexivity.
      - apply lstore_lift_free_restrict_fv_lvars_eq. exact Hlc.
    }
    specialize (Hstores _ HτD).
    destruct Hstores as [Hx' [v [Hlookup Heval]]].
    split; [exact Hx'|].
    exists v. split.
    + apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
      exact Hlookup.
    + apply (proj1 (expr_eval_in_store_restrict_lvars e
        (lstore_lift_free σ : LStoreT) (tm_lvars e ∪ {[x]}) v
        ltac:(set_solver))).
      exact Heval.
Qed.

Lemma expr_result_atom_world_to_formula e x (m : WfWorldT) :
  expr_result_at_world e x (res_lift_free m : LWorldT) ->
  res_models m (expr_result_formula e x).
Proof.
  intros Hres.
  apply expr_result_formula_models_iff.
  unfold expr_result_lqual, logic_qualifier_denote.
  destruct Hres as [Hx [Hdom Hstores]].
  assert (Hlc : lc_lvars (tm_lvars e ∪ {[x]})).
  {
    unfold lc_lvars. intros v Hv.
    specialize (Hdom _ Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]].
    destruct v as [k|b]; [discriminate|exact I].
  }
  assert (Hsub :
      lvars_fv (tm_lvars e ∪ {[x]}) ⊆ world_dom (m : WorldT)).
  {
    intros y Hy.
    assert (LVFree y ∈ tm_lvars e ∪ {[x]}) as HyD.
    { apply lvars_fv_elem. exact Hy. }
    specialize (Hdom _ HyD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Heq Ha]].
    inversion Heq. subst a. exact Ha.
  }
  exists Hlc, Hsub.
  apply expr_result_at_world_lworld_on_lift.
  exact (conj Hx (conj Hdom Hstores)).
Qed.

Lemma expr_result_extension_world_models_closed
    e x F (m mx : WfWorldT) :
  wfworld_closed_on (fv_tm e) m ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  expr_result_at_world e (LVFree x) (res_lift_free mx : LWorldT).
Proof.
  intros Hclosed Hwitness Hext Htotal.
  destruct Hwitness as [Hx_fresh [Hin Hout] Hrel].
  unfold ext_in in Hin.
  unfold ext_out in Hout.
  destruct Htotal as [Htotal_dom Htotal_eval].
  split.
  - intros Hxin.
    apply Hx_fresh.
    rewrite <- tm_lvars_fv.
    apply lvars_fv_elem. exact Hxin.
  - split.
    + rewrite res_lift_free_dom.
      pose proof (res_extend_by_dom m F mx Hext) as Hmx_dom.
      replace (lvars_of_atoms (world_dom mx)) with
        (lvars_of_atoms (world_dom m ∪ {[x]})).
      2:{ rewrite Hmx_dom, Hout. reflexivity. }
      intros z Hz.
      apply elem_of_union in Hz as [Hz|Hz].
      * specialize (Htotal_dom _ Hz).
        rewrite res_lift_free_dom in Htotal_dom.
        unfold lvars_of_atoms in *.
        apply elem_of_map in Htotal_dom as [a [-> Ha]].
        apply elem_of_map. exists a. split; [reflexivity|set_solver].
      * rewrite elem_of_singleton in Hz. subst z.
        unfold lvars_of_atoms. apply elem_of_map.
        exists x. split; [reflexivity|set_solver].
    + intros τ Hτ.
    destruct Hτ as [σx [Hσx ->]].
    apply (proj1 (resA_extend_by_store_iff m F mx σx Hext)) in Hσx.
    destruct Hσx as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
    unfold expr_result_at_store.
    split.
    * intros Hxin.
      apply Hx_fresh.
      rewrite <- tm_lvars_fv.
      apply lvars_fv_elem. exact Hxin.
    * destruct (Htotal_eval (lstore_lift_free σm)) as [v Heval_m].
      { exists σm. split; [exact Hσm|reflexivity]. }
      assert (Hclosed_restrict :
        closed_env (store_restrict σm (fv_tm e))).
      { exact (proj1 (Hclosed σm Hσm)). }
      assert (Heval_restrict :
        expr_eval_in_atom_store (store_restrict σm (fv_tm e)) e v).
      {
        apply (proj2 (expr_eval_in_atom_store_restrict_fv_closed_on
          σm e v Hclosed_restrict)).
        exact Heval_m.
      }
      assert (Hproj_dom :
        dom (store_restrict σm (fv_tm e) : gmap atom value) = fv_tm e).
      {
        rewrite store_restrict_dom.
        pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
        unfold ext_in in Hin_sub.
        pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
        change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
        rewrite Hσm_dom, <- Hin. set_solver.
      }
      pose proof (expr_result_extension_apply_total_iff
        e x F (store_restrict σm (fv_tm e)) we
        {| expr_result_extension_witness_fresh := Hx_fresh;
           expr_result_extension_witness_shape := conj Hin Hout;
           expr_result_extension_witness_rel := Hrel |}
        Hproj_dom
        ltac:(unfold ext_rel; rewrite <- Hin; exact HF)
        (ex_intro _ v Heval_restrict) σe) as Hwe.
      apply Hwe in Hσe as [u [Heval_u ->]].
      exists u. split.
      -- change (((lstore_lift_free (σm ∪ ({[x := u]} : StoreT)) : LStoreT)
          : gmap logic_var value) !! LVFree x = Some u).
        rewrite lstore_lift_free_lookup_free.
        change (((σm : gmap atom value) ∪ ({[x := u]} : gmap atom value)) !! x =
          Some u).
        apply storeA_lookup_union_Some_raw. right.
        split.
        ++ apply eq_None_not_Some. intros [w Hlook].
           pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh_out.
           change (ext_out F ## world_dom (m : WorldT)) in Hfresh_out.
           unfold ext_out in Hfresh_out.
           pose proof (wfworldA_store_dom m σm Hσm) as Hσm_dom.
           change (dom (σm : gmap atom value) = world_dom (m : WorldT)) in Hσm_dom.
           change (((σm : gmap atom value) !! x) = Some w) in Hlook.
           apply elem_of_dom_2 in Hlook.
           rewrite Hσm_dom in Hlook.
           rewrite Hout in Hfresh_out.
           set_solver.
        ++ change ((<[x := u]> (∅ : StoreT)) !! x = Some u).
           apply storeA_lookup_insert.
      -- assert (Hrestrict_union :
          store_restrict (σm ∪ ({[x := u]} : StoreT)) (fv_tm e) =
          store_restrict σm (fv_tm e)).
        {
          apply storeA_restrict_union_ignore_r.
          pose proof (dom_singleton_L (M:=gmap atom) x u) as Hdom_single.
          change (dom (({[x := u]} : StoreT) : gmap atom value) = {[x]})
            in Hdom_single.
          rewrite Hdom_single. set_solver.
        }
        assert (Hclosed_union :
          closed_env (store_restrict (σm ∪ ({[x := u]} : StoreT)) (fv_tm e))).
        { rewrite Hrestrict_union. exact Hclosed_restrict. }
        apply (proj1 (expr_eval_in_atom_store_restrict_fv_closed_on
          (σm ∪ ({[x := u]} : StoreT)) e u Hclosed_union)).
        rewrite Hrestrict_union. exact Heval_u.
Qed.

Lemma expr_result_extension_world_models
    (Σ : lty_env) e x F (m mx : WfWorldT) :
  lvars_of_atoms (fv_tm e) ⊆ dom Σ ->
  res_models m (basic_world_formula Σ) ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  expr_result_at_world e (LVFree x) (res_lift_free mx : LWorldT).
Proof.
  intros Hfv Hbasic HF Hext Htotal.
  eapply expr_result_extension_world_models_closed; eauto.
  eapply basic_world_formula_wfworld_closed_on_atoms; eauto.
Qed.

Lemma expr_result_formula_of_result_extends (Σ : lty_env) e x m F mx :
  lvars_of_atoms (fv_tm e) ⊆ dom Σ ->
  res_models m (basic_world_formula Σ) ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  res_models mx (expr_result_formula e (LVFree x)).
Proof.
  intros Hfv Hbasic HF Hext Htotal.
  pose proof (expr_result_extension_world_models
    Σ e x F m mx Hfv Hbasic HF Hext Htotal) as Hres.
  apply expr_result_formula_models_iff.
  unfold expr_result_lqual, logic_qualifier_denote.
  destruct Hres as [Hx [Hdom Hstores]].
  assert (Hlc : lc_lvars (tm_lvars e ∪ {[LVFree x]})).
  {
    unfold lc_lvars. intros v Hv.
    destruct v as [k|y]; [|exact I].
    exfalso.
    specialize (Hdom (LVBound k) Hv).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Hbad _]]. discriminate.
  }
  assert (Hsub :
      lvars_fv (tm_lvars e ∪ {[LVFree x]}) ⊆ world_dom (mx : WorldT)).
  {
    intros y Hy.
    assert (LVFree y ∈ tm_lvars e ∪ {[LVFree x]}) as HyD.
    { apply lvars_fv_elem. exact Hy. }
    specialize (Hdom (LVFree y) HyD).
    rewrite res_lift_free_dom in Hdom.
    unfold lvars_of_atoms in Hdom.
    apply elem_of_map in Hdom as [a [Heq Ha]].
    inversion Heq. subst a. exact Ha.
  }
  exists Hlc, Hsub.
  apply expr_result_at_world_lworld_on_lift.
  exact (conj Hx (conj Hdom Hstores)).
Qed.

Lemma expr_result_at_world_tlete_elim_body_ext
    (e1 e2 : tm) (x y : atom) (my mxy : WfWorldT) (Fx : FiberExtensionT) :
  lc_tm (tlete e1 e2) ->
  x <> y ->
  x ∉ fv_tm e2 ->
  wfworld_closed_on (fv_tm (tlete e1 e2)) my ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by my Fx mxy ->
  expr_result_at_world (tlete e1 e2) (LVFree y)
    (res_lift_free my : LWorldT) ->
  expr_result_at_world (e2 ^^ x) (LVFree y)
    (res_lift_free mxy : LWorldT).
Proof.
  intros Hlc Hxy Hxe2 Hclosed Hwitness Hext Hres.
  destruct Hres as [Hyfresh [Hdom_my Hstores_my]].
  destruct Hwitness as [Hx_fv [Hin Hout] Hrel].
  assert (Hxlet : x ∉ fv_tm (tlete e1 e2)).
  { cbn [fv_tm]. set_solver. }
  split.
  - eapply tm_lvars_tlete_open_body_fresh_result; eauto.
  - split.
    + rewrite res_lift_free_dom.
      pose proof (res_extend_by_dom my Fx mxy Hext) as Hdom_mxy.
      change (world_dom (mxy : WorldT) =
        world_dom (my : WorldT) ∪ ext_out Fx) in Hdom_mxy.
      change (tm_lvars (e2 ^^ x) ∪ {[LVFree y]} ⊆
        lvars_of_atoms (world_dom (mxy : WorldT))).
      rewrite Hdom_mxy, Hout.
      intros z Hz.
      apply elem_of_union in Hz as [Hz|Hz].
      * pose proof (tm_lvars_tlete_open_body_subset e1 e2 x Hlc Hxe2 _ Hz)
          as Hz'.
        rewrite elem_of_union, elem_of_singleton in Hz'.
        destruct Hz' as [Hz'|Hz'].
        -- specialize (Hdom_my z ltac:(set_solver)).
           rewrite res_lift_free_dom in Hdom_my.
           unfold lvars_of_atoms in *.
           apply elem_of_map in Hdom_my as [a [-> Ha]].
           apply elem_of_map. exists a. split; [reflexivity|set_solver].
        -- inversion Hz'. subst z.
           unfold lvars_of_atoms. apply elem_of_map.
           exists x. split; [reflexivity|set_solver].
      * rewrite elem_of_singleton in Hz. subst z.
        specialize (Hdom_my (LVFree y) ltac:(set_solver)).
        rewrite res_lift_free_dom in Hdom_my.
        unfold lvars_of_atoms in *.
        apply elem_of_map in Hdom_my as [a [Heq Ha]].
        inversion Heq. subst a.
        apply elem_of_map. exists y. split; [reflexivity|set_solver].
    + intros τ Hτ.
      destruct Hτ as [σxy [Hσxy ->]].
      apply (proj1 (resA_extend_by_store_iff my Fx mxy σxy Hext)) in Hσxy.
      destruct Hσxy as [σm [we [σe [Hσm [HF [Hσe ->]]]]]].
      specialize (Hstores_my (lstore_lift_free σm)).
      assert (Hlift_my :
        worldA_stores (res_lift_free my : LWorldT) (lstore_lift_free σm)).
      { exists σm. split; [exact Hσm|reflexivity]. }
      specialize (Hstores_my Hlift_my).
      destruct Hstores_my as [_ [v [Hy_lookup_lift Heval_tlet]]].
      rewrite lstore_lift_free_lookup_free in Hy_lookup_lift.
      assert (Hclosed_σm :
        store_closed (store_restrict σm (fv_tm (tlete e1 e2)))).
      { exact (Hclosed σm Hσm). }
      destruct (expr_eval_in_atom_store_tlete_elim_closed_on
        e1 e2 x σm v Hclosed_σm Hxlet Hxe2 Heval_tlet)
        as [vx [He1_restrict He2_insert]].
      set (σX := store_restrict σm (fv_tm e1)).
      assert (HσX_dom : dom (σX : gmap atom value) = fv_tm e1).
      {
        subst σX. rewrite store_restrict_dom.
        pose proof (wfworldA_store_dom my σm Hσm) as Hσm_dom.
        change (dom (σm : gmap atom value) =
          world_dom (my : WorldT)) in Hσm_dom.
        pose proof (res_extend_by_input_dom my Fx mxy Hext) as Hin_sub.
        unfold ext_in in Hin. rewrite Hin in Hin_sub.
        rewrite Hσm_dom. set_solver.
      }
      assert (HFσX : ext_rel Fx σX we).
      {
        subst σX.
        replace (store_restrict σm (fv_tm e1))
          with (store_restrict σm (ext_in Fx)) by
          (unfold ext_in; unfold ext_in in Hin; rewrite Hin; reflexivity).
        exact HF.
      }
      pose proof (expr_result_extension_apply_total_iff
        e1 x Fx σX we
        {| expr_result_extension_witness_fresh := Hx_fv;
           expr_result_extension_witness_shape := conj Hin Hout;
           expr_result_extension_witness_rel := Hrel |}
        HσX_dom HFσX (ex_intro _ vx He1_restrict) σe) as Hσe_iff.
      apply Hσe_iff in Hσe as [u [He1_u ->]].
      assert (Hu_eq : u = vx).
      {
        unfold expr_eval_in_atom_store, expr_eval_in_store in He1_u, He1_restrict.
        eapply steps_result_unique; eauto.
      }
      subst u.
      split.
      * eapply tm_lvars_tlete_open_body_fresh_result; eauto.
      * exists v. split.
        -- change (((lstore_lift_free (σm ∪ ({[x := vx]} : StoreT)) : LStoreT)
              : gmap logic_var value) !! LVFree y = Some v).
           rewrite lstore_lift_free_lookup_free.
           change (((σm : gmap atom value) ∪ ({[x := vx]} : gmap atom value)) !! y =
             Some v).
           transitivity ((σm : gmap atom value) !! y).
           ++ apply lookup_union_l'. exists v. exact Hy_lookup_lift.
           ++ exact Hy_lookup_lift.
        -- assert (Hx_dom : x ∉ dom (σm : gmap atom value)).
           {
             pose proof (res_extend_by_output_fresh my Fx mxy Hext) as Hfresh_out.
             change (ext_out Fx ## world_dom (my : WorldT)) in Hfresh_out.
             pose proof (wfworldA_store_dom my σm Hσm) as Hσm_dom.
             change (dom (σm : gmap atom value) =
               world_dom (my : WorldT)) in Hσm_dom.
             rewrite Hout in Hfresh_out.
             rewrite Hσm_dom. set_solver.
           }
           assert (Hagree :
             store_restrict
               (<[x := vx]> (store_restrict σm (fv_tm (tlete e1 e2))))
               (fv_tm (e2 ^^ x)) =
             store_restrict (σm ∪ ({[x := vx]} : StoreT)) (fv_tm (e2 ^^ x))).
           {
             symmetry.
             apply store_insert_restrict_agree_on_open_fv.
             - cbn [fv_tm]. set_solver.
             - exact Hxlet.
             - exact Hx_dom.
           }
           apply (proj1 (expr_eval_in_atom_store_agree_on_fv
             (<[x := vx]> (store_restrict σm (fv_tm (tlete e1 e2))))
             (σm ∪ ({[x := vx]} : StoreT))
             (e2 ^^ x) v Hagree)).
           exact He2_insert.
Qed.

Lemma expr_result_formula_tlete_elim_body_from_result_extension
    (e1 e2 : tm) (x y : atom) (my mxy : WfWorldT) (Fx : FiberExtensionT) :
  lc_tm (tlete e1 e2) ->
  x <> y ->
  x ∉ fv_tm e2 ->
  wfworld_closed_on (fv_tm (tlete e1 e2)) my ->
  expr_result_extension_witness e1 x Fx ->
  res_extend_by my Fx mxy ->
  res_models my (expr_result_formula (tlete e1 e2) (LVFree y)) ->
  res_models mxy (expr_result_formula (e2 ^^ x) (LVFree y)).
Proof.
  intros Hlc Hxy Hxe2 Hclosed Hwitness Hext Hmodels.
  apply expr_result_atom_world_to_formula.
  eapply expr_result_at_world_tlete_elim_body_ext; eauto.
  apply expr_result_formula_to_atom_world. exact Hmodels.
Qed.

End TermDenotation.
