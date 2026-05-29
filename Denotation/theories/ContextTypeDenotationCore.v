(** * Denotation.ContextTypeDenotationCore

    Core helpers for the recursive context-type denotation.

    This file contains formula multi-open support and relevant-environment
    utilities used by [ContextTypeDenotationDefinition].  The old typed-forall,
    continuation, closed-resource, and obligation syntax sugar is gone; the
    recursive denotation uses the component formulas supplied by
    [ContextBasicDenotation] directly. *)

From Denotation Require Import Notation.
From ContextBase Require Import BaseTactics.

Section ContextTypeDenotation.

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
      rewrite lty_env_open_one_insert.
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

Lemma arrow_body_relevant_lvars_subset
    τx τr e_src e_body y :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  denot_relevant_lvars (cty_open 0 y τr) e_body ∖ {[LVFree y]} ⊆
  denot_relevant_lvars (CTArrow τx τr) e_src.
Proof.
  intros Hτ He.
  unfold denot_relevant_lvars.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma arrow_body_relevant_env_agree
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]} ⊆
    context_ty_lvars_at 1 τr ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hτ He.
  apply lty_env_restrict_lvars_insert_denot_relevant_env_eq.
  eapply arrow_body_relevant_lvars_subset; eauto.
Qed.

Lemma arrow_body_relevant_env_agree_from_basic_context_ty
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He.
  apply arrow_body_relevant_env_agree; [|exact He].
  apply context_ty_lvars_open_body_without_fresh_closed
    with (D := (dom (Σsrc : gmap logic_var ty) : gset logic_var)).
  - exact Hlc.
  - exact HyΣ.
  - destruct Hbasic as [Hvars _].
    cbn [context_ty_lvars context_ty_lvars_at] in Hvars.
    set_solver.
Qed.

Lemma wand_body_relevant_env_agree_from_basic_context_ty
    (Σsrc : lty_env) Ty y τx τr e_src e_body :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTWand τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  lty_env_restrict_lvars
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTWand τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body) =
  lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He.
  change (denot_relevant_env Σsrc (CTWand τx τr) e_src)
    with (denot_relevant_env Σsrc (CTArrow τx τr) e_src).
  apply arrow_body_relevant_env_agree_from_basic_context_ty.
  - exact Hlc.
  - exact HyΣ.
  - change (basic_context_ty_lvars
      (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr)).
    exact Hbasic.
  - exact He.
Qed.

Lemma basic_world_formula_arrow_body_from_source_and_arg
    (Σsrc : lty_env) Ty y τx τr e_src e_body (m : WfWorldT) :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTArrow τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  m ⊨ basic_world_formula (denot_relevant_env Σsrc (CTArrow τx τr) e_src) ->
  m ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env) ->
  m ⊨ basic_world_formula
    (denot_relevant_env (<[LVFree y := Ty]> Σsrc)
      (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He Hsrc Hy.
  pose proof (basic_world_formula_union
    (denot_relevant_env Σsrc (CTArrow τx τr) e_src)
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env)
    m Hsrc Hy) as Hunion.
  eapply basic_world_formula_subenv; [|exact Hunion].
  intros v Tv Hlook.
  pose proof (arrow_body_relevant_env_agree_from_basic_context_ty
    Σsrc Ty y τx τr e_src e_body Hlc HyΣ Hbasic He) as Hagree.
  change ((lty_env_restrict_lvars (<[LVFree y := Ty]> Σsrc)
    (denot_relevant_lvars (cty_open 0 y τr) e_body) : lty_env) !!
    v = Some Tv) in Hlook.
  rewrite <- Hagree in Hlook.
  unfold lty_env_restrict_lvars in Hlook.
  change ((storeA_restrict
    (<[LVFree y := Ty]>
      (denot_relevant_env Σsrc (CTArrow τx τr) e_src))
    (denot_relevant_lvars (cty_open 0 y τr) e_body)
    : gmap logic_var ty) !! v = Some Tv) in Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  assert (Hyrel : LVFree y ∉ dom
    (denot_relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)).
  {
    intros Hyrel.
    change (LVFree y ∈ dom
      ((denot_relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)
        : gmap logic_var ty)) in Hyrel.
    apply elem_of_dom in Hyrel as [Ty' Hrel].
    unfold denot_relevant_env, lty_env_restrict_lvars in Hrel.
    change ((storeA_restrict Σsrc
      (denot_relevant_lvars (CTArrow τx τr) e_src)
      : gmap logic_var ty) !! LVFree y = Some Ty') in Hrel.
    apply storeA_restrict_lookup_some in Hrel as [_ HΣ].
    apply HyΣ. eapply elem_of_dom_2. exact HΣ.
  }
  change ((((denot_relevant_env Σsrc (CTArrow τx τr) e_src : lty_env)
    : gmap logic_var ty) ∪
    (<[LVFree y := Ty]> (∅ : gmap logic_var ty))) !! v = Some Tv).
  change (<[LVFree y := Ty]> (∅ : gmap logic_var ty))
    with ({[LVFree y := Ty]} : gmap logic_var ty).
  rewrite storeA_union_singleton_insert_fresh by exact Hyrel.
  exact Hlook.
Qed.

Lemma basic_world_formula_wand_body_from_source_and_arg
    (Σsrc : lty_env) Ty y τx τr e_src e_body (m : WfWorldT) :
  lc_lvars (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  LVFree y ∉ (dom (Σsrc : gmap logic_var ty) : gset logic_var) ->
  basic_context_ty_lvars
    (dom (Σsrc : gmap logic_var ty) : gset logic_var) (CTWand τx τr) ->
  tm_lvars e_body ∖ {[LVFree y]} ⊆ tm_lvars e_src ->
  m ⊨ basic_world_formula (denot_relevant_env Σsrc (CTWand τx τr) e_src) ->
  m ⊨ basic_world_formula
    ((<[LVFree y := Ty]> (∅ : gmap logic_var ty)) : lty_env) ->
  m ⊨ basic_world_formula
    (denot_relevant_env (<[LVFree y := Ty]> Σsrc)
      (cty_open 0 y τr) e_body).
Proof.
  intros Hlc HyΣ Hbasic He Hsrc Hy.
  change (denot_relevant_env Σsrc (CTWand τx τr) e_src)
    with (denot_relevant_env Σsrc (CTArrow τx τr) e_src) in Hsrc.
  eapply basic_world_formula_arrow_body_from_source_and_arg; eauto.
Qed.

Lemma lvars_at_depth_denot_relevant_env_subset d Σ τ e :
  lvars_at_depth d (dom (denot_relevant_env Σ τ e)) ⊆
  lvars_at_depth d (dom Σ) ∪ context_ty_lvars_at d τ ∪ tm_lvars_at d e.
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
  change (lvars_at_depth d
    (dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e))) ⊆
    lvars_at_depth d (dom Σ) ∪ context_ty_lvars_at d τ ∪ tm_lvars_at d e).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth d (dom Σ ∩ (context_ty_lvars τ ∪ tm_lvars e))).
  { reflexivity. }
  transitivity (lvars_at_depth d (dom Σ) ∩
    lvars_at_depth d (context_ty_lvars τ ∪ tm_lvars e)).
  - intros v Hv.
    apply lvars_at_depth_elem in Hv as [u [Hu Huv]].
    apply elem_of_intersection in Hu as [HuΣ HuD].
    apply elem_of_intersection. split; apply lvars_at_depth_elem;
      exists u; split; assumption.
  - rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
    set_solver.
Qed.

Lemma lvars_at_depth_denot_relevant_env_subset_relevant d Σ τ e :
  lvars_at_depth d (dom (denot_relevant_env Σ τ e)) ⊆
  context_ty_lvars_at d τ ∪ tm_lvars_at d e.
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
  change (lvars_at_depth d
    (dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e))) ⊆
    context_ty_lvars_at d τ ∪ tm_lvars_at d e).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth d (context_ty_lvars τ ∪ tm_lvars e)).
  - apply lvars_at_depth_mono. set_solver.
  - rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
    set_solver.
Qed.

Lemma lvars_at_depth_denot_relevant_typed_bind_subset d Σ T τ e :
  lvars_at_depth (S d)
    (dom (denot_relevant_env (typed_lty_env_bind Σ T) τ e)) ⊆
  lvars_at_depth d (dom Σ).
Proof.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  change (lvars_at_depth (S d)
    (dom (storeA_restrict
      (typed_lty_env_bind Σ T : gmap logic_var ty)
      (denot_relevant_lvars τ e))) ⊆
    lvars_at_depth d (dom Σ)).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T))).
  - apply lvars_at_depth_mono. intros v Hv.
    apply elem_of_intersection in Hv as [Hv _]. exact Hv.
  - rewrite lvars_at_depth_typed_lty_env_bind. reflexivity.
Qed.

Lemma lvars_at_depth_arrow_arg_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_arrow_body_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTArrow τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars τr (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  pose proof (tm_lvars_at_tapp_shift0_bound0 e 0) as Htapp.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_wand_arg_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars (cty_shift 0 τx) (tret (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTWand τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTWand τx τr) e) as Hrel.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_wand_body_lift_support_subset Σ τx τr e :
  lvars_at_depth 1
    (dom (typed_lty_env_bind
      (denot_relevant_env Σ (CTWand τx τr) e) (erase_ty τx)) ∪
     denot_relevant_lvars τr (tapp_tm (tm_shift 0 e) (vbvar 0))) ⊆
  dom Σ ∪ denot_relevant_lvars (CTWand τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_denot_relevant_env_subset_relevant
    0 Σ (CTWand τx τr) e) as Hrel.
  pose proof (tm_lvars_at_tapp_shift0_bound0 e 0) as Htapp.
  unfold denot_relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma lvars_at_depth_restrict_typed_bind_subset d Σ T D :
  lvars_at_depth (S d)
    (dom (lty_env_restrict_lvars (typed_lty_env_bind Σ T) D)) ⊆
  lvars_at_depth d (dom Σ).
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_at_depth (S d)
    (dom (storeA_restrict
      (typed_lty_env_bind Σ T : gmap logic_var ty) D)) ⊆
    lvars_at_depth d (dom Σ)).
  rewrite storeA_restrict_dom.
  transitivity (lvars_at_depth (S d) (dom (typed_lty_env_bind Σ T))).
  - apply lvars_at_depth_mono. intros v Hv.
    apply elem_of_intersection in Hv as [Hv _]. exact Hv.
  - rewrite lvars_at_depth_typed_lty_env_bind. reflexivity.
Qed.

Lemma lvars_at_depth_dom_singleton_bound0_succ d T :
  lvars_at_depth (S d) (dom (<[LVBound 0 := T]> (∅ : lty_env))) = ∅.
Proof.
  rewrite dom_insert_L, dom_empty_L, lvars_at_depth_union.
  rewrite lvars_at_depth_singleton_bound0_succ, lvars_at_depth_empty.
  set_solver.
Qed.

Lemma context_ty_lvars_shift_free_notin k x τ :
  LVFree x ∉ context_ty_lvars τ ->
  LVFree x ∉ context_ty_lvars (cty_shift k τ).
Proof.
  intros Hfresh Hin.
  apply Hfresh. apply lvars_fv_elem.
  apply lvars_fv_elem in Hin.
  change (x ∈ fv_cty (cty_shift k τ)) in Hin.
  rewrite cty_shift_fv in Hin. exact Hin.
Qed.

End ContextTypeDenotation.
