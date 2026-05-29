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

#[local] Instance open_commute_formula_eq :
  OpenCommute FormulaT formula_open eq.
Proof.
  constructor. intros i j x y φ Hij Hxy.
  apply formula_open_commute_fresh; assumption.
Qed.

Definition formula_open_env (η : gmap nat atom) (φ : FormulaT) : FormulaT :=
  map_fold (fun k x acc => formula_open k x acc) φ η.

Lemma formula_open_env_empty φ :
  formula_open_env ∅ φ = φ.
Proof.
  unfold formula_open_env. rewrite map_fold_empty. reflexivity.
Qed.

Lemma formula_open_env_singleton k x φ :
  formula_open_env (<[k := x]> ∅) φ = formula_open k x φ.
Proof.
  unfold formula_open_env.
  change (<[k := x]> (∅ : gmap nat atom)) with ({[k := x]} : gmap nat atom).
  rewrite map_fold_singleton. reflexivity.
Qed.

Lemma formula_open_env_insert_fresh η k x φ :
  η !! k = None ->
  open_env_avoids_atom x η ->
  open_env_values_inj η ->
  formula_open_env (<[k := x]> η) φ =
  formula_open k x (formula_open_env η φ).
Proof.
  intros Hfresh Havoid Hinj.
  unfold formula_open_env.
  apply (open_map_fold_insert_fresh_eq formula_open); assumption.
Qed.

Lemma formula_open_env_true η :
  formula_open_env η FTrue = FTrue.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) FTrue η = FTrue)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_false η :
  formula_open_env η FFalse = FFalse.
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) FFalse η = FFalse)
    _ _ η).
  - rewrite map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH. rewrite Hfold, IH. reflexivity.
Qed.

Lemma formula_open_env_and η φ ψ :
  formula_open_env η (FAnd φ ψ) =
  FAnd (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FAnd φ ψ) η =
      FAnd
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_or η φ ψ :
  formula_open_env η (FOr φ ψ) =
  FOr (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FOr φ ψ) η =
      FOr
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_impl η φ ψ :
  formula_open_env η (FImpl φ ψ) =
  FImpl (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FImpl φ ψ) η =
      FImpl
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_star η φ ψ :
  formula_open_env η (FStar φ ψ) =
  FStar (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FStar φ ψ) η =
      FStar
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_wand η φ ψ :
  formula_open_env η (FWand φ ψ) =
  FWand (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FWand φ ψ) η =
      FWand
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_plus η φ ψ :
  formula_open_env η (FPlus φ ψ) =
  FPlus (formula_open_env η φ) (formula_open_env η ψ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FPlus φ ψ) η =
      FPlus
        (map_fold (fun k x acc => formula_open k x acc) φ η)
        (map_fold (fun k x acc => formula_open k x acc) ψ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_over η φ :
  formula_open_env η (FOver φ) =
  FOver (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FOver φ) η =
      FOver (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_under η φ :
  formula_open_env η (FUnder φ) =
  FUnder (formula_open_env η φ).
Proof.
  unfold formula_open_env.
  refine (fin_maps.map_fold_ind
    (fun η => map_fold (fun k x acc => formula_open k x acc) (FUnder φ) η =
      FUnder (map_fold (fun k x acc => formula_open k x acc) φ η)) _ _ η).
  - rewrite !map_fold_empty. reflexivity.
  - intros k x η' Hfresh Hfold IH.
    rewrite !Hfold. cbn [formula_open]. rewrite IH. reflexivity.
Qed.

Lemma formula_open_env_fibvars η D φ :
  open_env_fresh_for_lvars η D ->
  formula_open_env η (FFibVars D φ) =
  FFibVars (lvars_open_env η D) (formula_open_env η φ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, lvars_open_env_empty.
    reflexivity.
  - intros Henv.
    pose proof (open_env_fresh_for_lvars_insert_head η k x D Hfresh Henv)
      as Hhead.
    pose proof (open_env_fresh_for_lvars_insert_tail η k x D Hfresh Henv)
      as Htail.
    unfold formula_open_env.
    rewrite !Hfold.
    fold (formula_open_env η (FFibVars D φ)).
    fold (formula_open_env η φ).
    rewrite IH by exact Htail.
    cbn [formula_open].
    rewrite lvars_open_env_insert_fresh by (exact Hfresh || exact Hhead).
    reflexivity.
Qed.
Lemma formula_open_env_forall η φ :
  open_env_values_inj η ->
  formula_open_env η (FForall φ) =
  FForall (formula_open_env ((kmap S η)) φ).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - intros _. rewrite formula_open_env_empty, kmap_empty,
      formula_open_env_empty.
    reflexivity.
  - intros Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hfresh Hinj)
      as [Hinjη Havoid].
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by exact Hinjη.
    cbn [formula_open].
    rewrite open_env_lift_insert.
    rewrite formula_open_env_insert_fresh
      by (try better_base_solver;
          try apply open_env_values_inj_lift; assumption).
    reflexivity.
Qed.

Lemma formula_open_env_context_ty_wf_formula η Σ τ :
  open_env_fresh_for_lvars η (dom Σ ∪ context_ty_lvars τ) ->
  open_env_values_inj η ->
  formula_open_env η (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_lvars η Σ) (open_cty_env η τ).
Proof.
  revert Σ τ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty,
      open_cty_env_empty. reflexivity.
  - intros Σ τ Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ context_ty_lvars τ) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_context_ty_wf_formula.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv | exact Hfresh]. }
    rewrite open_cty_env_insert_fresh by assumption.
    reflexivity.
Qed.

Lemma formula_open_env_basic_world_formula η Σ :
  open_env_fresh_for_lvars η (dom Σ) ->
  open_env_values_inj η ->
  formula_open_env η (basic_world_formula Σ) =
  basic_world_formula (lty_env_open_lvars η Σ).
Proof.
  revert Σ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty. reflexivity.
  - intros Σ Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_basic_world_formula.
    rewrite lty_env_open_lvars_insert_fresh by assumption.
    reflexivity.
Qed.

Lemma formula_open_env_expr_basic_typing_formula η Σ e T :
  open_env_fresh_for_lvars η (dom Σ ∪ tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env η (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_lvars η Σ) (open_tm_env η e) T.
Proof.
  revert Σ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ e _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty.
    rewrite map_fold_empty. reflexivity.
  - intros Σ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_basic_typing_formula.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      2:{ eapply open_env_fresh_for_lvars_mono.
          - intros v Hv. apply elem_of_union_r. exact Hv.
          - exact Hfreshη. }
      assert (HΣfv : lvars_fv (dom (lty_env_open_lvars η Σ)) ⊆
                     lvars_fv (lvars_open_env η (dom Σ))).
      {
        rewrite lty_env_open_lvars_dom.
        - unfold lvars_open_env. set_solver.
        - eapply open_env_fresh_for_lvars_mono;
            [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfreshη].
      }
      intros Hbad. apply Hhead.
      rewrite lvars_open_env_union, lvars_fv_union.
      apply elem_of_union.
      apply elem_of_union in Hbad as [Hbad|Hbad].
      - left. apply HΣfv. exact Hbad.
      - right. exact Hbad.
    }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfresh]. }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

Lemma formula_open_env_expr_total_formula η e :
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env η (expr_total_formula e) =
  expr_total_formula (open_tm_env η e).
Proof.
  revert e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros e _ _.
    rewrite formula_open_env_empty.
    rewrite map_fold_empty. reflexivity.
  - intros e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (tm_lvars e) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2: exact Hinjη.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_total_formula.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      - exact Hhead.
      - exact Hfreshη.
    }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

Lemma formula_open_env_expr_result_formula η e z :
  open_env_fresh_for_lvars η (tm_lvars e ∪ {[z]}) ->
  open_env_values_inj η ->
  formula_open_env η (expr_result_formula e z) =
  expr_result_formula (open_tm_env η e) (logic_var_open_env η z).
Proof.
  revert e z.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros e z _ _.
    rewrite formula_open_env_empty.
    rewrite map_fold_empty.
    better_base_solver.
  - intros e z Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (tm_lvars e ∪ {[z]}) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2: exact Hinjη.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_result_formula.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (tm_lvars e ∪ {[z]}) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      - intros Hbad. apply Hhead.
        rewrite lvars_open_env_union, lvars_fv_union.
        apply elem_of_union_l. exact Hbad.
      - eapply open_env_fresh_for_lvars_mono.
        + intros v Hv. apply elem_of_union_l. exact Hv.
        + exact Hfreshη.
    }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    rewrite logic_var_open_env_insert_fresh.
    { reflexivity. }
    { exact Hnone. }
    { pose proof (open_env_fresh_for_lvars_insert_head η k x
        (tm_lvars e ∪ {[z]}) Hnone Hfresh) as Hhead.
      intros Hz.
      apply Hhead.
      rewrite lvars_open_env_union, lvars_fv_union.
      apply elem_of_union_r.
      apply lvars_fv_elem.
      unfold lvars_open_env.
      apply elem_of_map.
      exists z. split; [symmetry; exact Hz|set_solver]. }
Qed.

Lemma type_qualifier_formula_open_env η q :
  open_env_fresh_for_lvars η (qual_vars q) ->
  open_env_values_inj η ->
  formula_open_env η (type_qualifier_formula q) =
  type_qualifier_formula (qual_open_env η q).
Proof.
  revert q.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros q _ _.
    rewrite formula_open_env_empty, qual_open_env_empty. reflexivity.
  - intros q Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (qual_vars q) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite type_qualifier_formula_open.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (qual_vars q) Hnone Hfresh) as Hhead.
      unfold qual_dom.
      rewrite qual_open_env_vars by exact Hfreshη.
      exact Hhead.
    }
    rewrite qual_open_env_insert_fresh by assumption.
    reflexivity.
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

Lemma open_tm_env_lift_shift0 η e :
  open_tm_env ((kmap S η)) (tm_shift 0 e) =
  tm_shift 0 (open_tm_env η e).
Proof.
  induction η as [|k x η Hfresh Hfold IH] using fin_maps.map_fold_ind.
  - rewrite kmap_empty.
    rewrite !map_fold_empty. reflexivity.
  - rewrite open_env_lift_insert.
    rewrite open_tm_env_insert_fresh_plain by better_base_solver.
    rewrite IH.
    rewrite open_tm_env_insert_fresh_plain by exact Hfresh.
    rewrite <- (tm_shift_open_tm_fvar (open_tm_env η e) k 0 x ltac:(lia)).
    reflexivity.
Qed.

Lemma formula_open_expr_result_formula_shift0_under_core k y e :
  y ∉ fv_tm e ->
  formula_open (S k) y (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula (tm_shift 0 (open_tm k (vfvar y) e)) (LVBound 0).
Proof.
  intros Hy.
  rewrite formula_open_expr_result_formula.
  - rewrite tm_shift_open_tm_fvar by lia.
    replace (logic_var_open (S k) y (LVBound 0)) with (LVBound 0).
    + reflexivity.
    + unfold swap. repeat destruct decide; try lia; try congruence.
  - rewrite tm_shift_fv. exact Hy.
Qed.

Lemma formula_open_env_lift_expr_result_formula_shift0_core η e :
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env ((kmap S η))
    (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula (tm_shift 0 (open_tm_env η e)) (LVBound 0).
Proof.
  revert e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros e _ _.
    rewrite kmap_empty, formula_open_env_empty.
    rewrite map_fold_empty. reflexivity.
  - intros e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (tm_lvars e) Hnone Hfresh) as Hfreshη.
    rewrite open_env_lift_insert.
    rewrite formula_open_env_insert_fresh.
    2:{ better_base_solver. }
    2:{ better_base_solver. }
    2:{ apply open_env_values_inj_lift. exact Hinjη. }
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_result_formula_shift0_under_core.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env; [exact Hhead|exact Hfreshη].
    }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
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

Definition lty_env_restrict_lvars (Σ : lty_env) (D : lvset) : lty_env :=
  storeA_restrict Σ D.

Definition denot_relevant_lvars (τ : context_ty) (e : tm) : lvset :=
  context_ty_lvars τ ∪ tm_lvars e.

Definition denot_relevant_env (Σ : lty_env) (τ : context_ty) (e : tm) : lty_env :=
  lty_env_restrict_lvars Σ (denot_relevant_lvars τ e).

Lemma denot_relevant_env_dom_subset_direct (Σ : lty_env) τ e :
  dom (denot_relevant_env Σ τ e : lty_env) ⊆
  dom (Σ : gmap logic_var ty).
Proof.
  intros v Hv.
  change (v ∈ dom ((denot_relevant_env Σ τ e : lty_env)
    : gmap logic_var ty)) in Hv.
  apply elem_of_dom in Hv as [T Hlookup].
  unfold denot_relevant_env, lty_env_restrict_lvars in Hlookup.
  change ((storeA_restrict Σ (denot_relevant_lvars τ e)
    : gmap logic_var ty) !! v = Some T) in Hlookup.
  apply storeA_restrict_lookup_some in Hlookup as [_ Hlookup].
  eapply elem_of_dom_2. exact Hlookup.
Qed.

Lemma denot_relevant_env_lookup_mono_context
    (Σ : lty_env) τsmall τbig e v T :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  denot_relevant_env Σ τsmall e !! v = Some T ->
  denot_relevant_env Σ τbig e !! v = Some T.
Proof.
  intros Hτ Hlookup.
  unfold denot_relevant_env, lty_env_restrict_lvars,
    denot_relevant_lvars in Hlookup |- *.
  change ((storeA_restrict (Σ : gmap logic_var ty)
    (context_ty_lvars τsmall ∪ tm_lvars e)) !! v = Some T) in Hlookup.
  change ((storeA_restrict (Σ : gmap logic_var ty)
    (context_ty_lvars τbig ∪ tm_lvars e)) !! v = Some T).
  apply storeA_restrict_lookup_some in Hlookup as [Hv HΣ].
  apply storeA_restrict_lookup_some_2; [exact HΣ | set_solver].
Qed.

Lemma denot_relevant_env_dom_mono_context
    (Σ : lty_env) τsmall τbig e :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  dom (denot_relevant_env Σ τsmall e) ⊆
  dom (denot_relevant_env Σ τbig e).
Proof.
  intros Hτ v Hv.
  change (v ∈ dom ((denot_relevant_env Σ τsmall e : lty_env)
    : gmap logic_var ty)) in Hv.
  apply elem_of_dom in Hv as [T Hlookup].
  change (v ∈ dom ((denot_relevant_env Σ τbig e : lty_env)
    : gmap logic_var ty)).
  apply elem_of_dom. exists T.
  eapply denot_relevant_env_lookup_mono_context; eauto.
Qed.

Lemma basic_world_formula_denot_relevant_mono_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τbig e) ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τsmall e).
Proof.
  intros Hτ Hworld.
  apply basic_world_formula_models_iff in Hworld
    as [Hlc_big [Hscope_big Htyped_big]].
  apply basic_world_formula_models_iff.
  pose proof (denot_relevant_env_dom_mono_context Σ τsmall τbig e Hτ)
    as Hdom.
  split.
  - intros v Hv. apply Hlc_big. exact (Hdom v Hv).
  - split.
    + intros a Ha.
      apply Hscope_big.
      apply lvars_fv_elem in Ha.
      apply lvars_fv_elem. exact (Hdom (LVFree a) Ha).
    + unfold lworld_has_type, worldA_has_type in Htyped_big |- *.
      destruct Htyped_big as [Hdom_big Hstores_big].
      split.
      * intros v Hv. apply Hdom_big. exact (Hdom v Hv).
      * intros σ Hσ v T val HΣv Hσv.
        eapply Hstores_big; [exact Hσ| |exact Hσv].
        eapply denot_relevant_env_lookup_mono_context; eauto.
Qed.

Lemma denot_relevant_lvars_open k y τ e :
  y ∉ fv_tm e ->
  lvars_open k y (denot_relevant_lvars τ e) =
  denot_relevant_lvars (cty_open k y τ) (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold denot_relevant_lvars.
  rewrite lvars_open_union.
  rewrite cty_open_vars.
  rewrite tm_lvars_open by exact Hy.
  reflexivity.
Qed.

Lemma denot_relevant_env_open_one k y Σ τ e :
  y ∉ fv_tm e ->
  lty_env_open_one k y (denot_relevant_env Σ τ e) =
  denot_relevant_env (lty_env_open_one k y Σ)
    (cty_open k y τ) (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold denot_relevant_env, lty_env_restrict_lvars, lty_env_open_one.
  rewrite <- denot_relevant_lvars_open by exact Hy.
  symmetry. apply storeA_restrict_swap.
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

Lemma denot_relevant_lvars_open_env η τ e :
  open_env_fresh_for_lvars η (denot_relevant_lvars τ e) ->
  denot_relevant_lvars (open_cty_env η τ) (open_tm_env η e) =
  lvars_open_env η (denot_relevant_lvars τ e).
Proof.
  intros Hfresh.
  unfold denot_relevant_lvars.
  rewrite context_ty_lvars_open_cty_env.
  2:{
    apply (open_env_fresh_for_lvars_mono η
      (context_ty_lvars τ) (denot_relevant_lvars τ e)).
    - unfold denot_relevant_lvars. set_solver.
    - exact Hfresh.
  }
  rewrite tm_lvars_open_tm_env.
  2:{
    apply (open_env_fresh_for_lvars_mono η
      (tm_lvars e) (denot_relevant_lvars τ e)).
    - unfold denot_relevant_lvars. set_solver.
    - exact Hfresh.
  }
	  better_base_solver.
Qed.

Lemma denot_relevant_env_open_env η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e) ->
  open_env_values_inj η ->
  lty_env_open_lvars η (denot_relevant_env Σ τ e) =
  denot_relevant_env (lty_env_open_lvars η Σ)
    (open_cty_env η τ) (open_tm_env η e).
Proof.
  revert Σ τ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ e _ _.
    rewrite lty_env_open_lvars_empty, open_cty_env_empty.
    rewrite (lty_env_open_lvars_empty Σ).
    rewrite map_fold_empty. reflexivity.
  - intros Σ τ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    assert (Hfreshη :
      open_env_fresh_for_lvars η (dom Σ ∪ denot_relevant_lvars τ e)).
    { eapply open_env_fresh_for_lvars_insert_tail; eassumption. }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{
      eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      unfold denot_relevant_env, lty_env_restrict_lvars.
      intros v Hv.
      change (v ∈ dom (storeA_restrict (Σ : gmap logic_var ty)
        (denot_relevant_lvars τ e) : gmap logic_var ty)) in Hv.
      apply elem_of_dom in Hv as [Tv Hlook].
      apply storeA_restrict_lookup_some in Hlook as [Hvrel HΣv].
      apply elem_of_union.
      left. change (v ∈ dom (Σ : gmap logic_var ty)).
      eapply elem_of_dom_2. exact HΣv.
    }
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite open_cty_env_insert_fresh by (exact Hnone || exact Havoid || exact Hinjη).
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{
      eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
      intros v Hv. set_solver.
    }
    rewrite denot_relevant_env_open_one.
    + reflexivity.
    + rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      * pose proof (open_env_fresh_for_lvars_insert_head η k x
          (dom Σ ∪ denot_relevant_lvars τ e) Hnone Hfresh) as Hhead.
        intros Hbad. apply Hhead.
        eapply lvars_fv_mono; [|exact Hbad].
        apply lvars_open_env_mono.
        unfold denot_relevant_lvars. set_solver.
      * eapply open_env_fresh_for_lvars_mono; [|exact Hfreshη].
        unfold denot_relevant_lvars. set_solver.
Qed.

Lemma lty_env_restrict_lvars_closed Σ D :
  lty_env_closed Σ ->
  lty_env_closed (lty_env_restrict_lvars Σ D).
Proof.
  intros Hclosed.
  unfold lty_env_closed in *.
  intros v Hv.
  unfold lty_env_restrict_lvars in Hv.
  change (v ∈ dom
    (storeA_restrict (Σ : gmap logic_var ty) D : gmap logic_var ty)) in Hv.
  pose proof (storeA_restrict_dom (Σ : lty_env) D) as Hdom_restrict.
  change (dom (storeA_restrict (Σ : gmap logic_var ty) D : gmap logic_var ty) =
    dom (Σ : gmap logic_var ty) ∩ D) in Hdom_restrict.
  rewrite Hdom_restrict in Hv.
  apply elem_of_intersection in Hv as [Hv _].
  exact (Hclosed v Hv).
Qed.

Lemma denot_relevant_env_closed Σ τ e :
  lty_env_closed Σ ->
  lty_env_closed (denot_relevant_env Σ τ e).
Proof.
  apply lty_env_restrict_lvars_closed.
Qed.

Lemma lty_env_to_atom_env_restrict_lvars_lookup Σ D x :
  LVFree x ∈ D ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) !! x =
  lty_env_to_atom_env Σ !! x.
Proof.
  intros HxD.
  rewrite !lvar_store_to_atom_store_lookup.
  unfold lty_env_restrict_lvars.
  destruct ((Σ : gmap logic_var ty) !! LVFree x) as [T|] eqn:HΣ.
  - apply storeA_restrict_lookup_some_2; assumption.
  - apply storeA_restrict_lookup_none_l. exact HΣ.
Qed.

Lemma basic_typing_lty_env_to_atom_env_restrict_lvars Σ D e T :
  tm_lvars e ⊆ D ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (lty_env_restrict_lvars Σ D) ⊢ₑ e ⋮ T.
Proof.
  intros Hsub Hty.
  eapply basic_typing_env_agree_tm; [exact Hty |].
  intros x Hx.
  apply lty_env_to_atom_env_restrict_lvars_lookup.
  apply Hsub.
  apply lvars_fv_elem.
  rewrite tm_lvars_fv. exact Hx.
Qed.

Lemma basic_typing_lty_env_to_atom_env_denot_relevant_env Σ τ e T :
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  lty_env_to_atom_env (denot_relevant_env Σ τ e) ⊢ₑ e ⋮ T.
Proof.
  intros Hty.
  unfold denot_relevant_env, denot_relevant_lvars.
  eapply basic_typing_lty_env_to_atom_env_restrict_lvars; [|exact Hty].
  set_solver.
Qed.

Lemma lty_env_restrict_lvars_fv_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv D.
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_fv (dom (storeA_restrict (Σ : gmap logic_var ty) D)) ⊆
    lvars_fv D).
  rewrite storeA_restrict_dom.
  apply lvars_fv_mono. set_solver.
Qed.

Lemma lty_env_restrict_lvars_fv_dom_subset Σ D :
  lvars_fv (dom (lty_env_restrict_lvars Σ D)) ⊆ lvars_fv (dom Σ).
Proof.
  unfold lty_env_restrict_lvars.
  change (lvars_fv (dom (storeA_restrict (Σ : gmap logic_var ty) D)) ⊆
    lvars_fv (dom Σ)).
  rewrite storeA_restrict_dom.
  apply lvars_fv_mono. set_solver.
Qed.

Lemma lty_env_restrict_lvars_insert_fresh Σ D x T :
  LVFree x ∉ D ->
  lty_env_restrict_lvars (<[LVFree x := T]> Σ) D =
  lty_env_restrict_lvars Σ D.
Proof.
  intros HxD.
  unfold lty_env_restrict_lvars.
  change (storeA_restrict (<[LVFree x := T]> (Σ : gmap logic_var ty)) D =
    storeA_restrict (Σ : gmap logic_var ty) D).
  unfold storeA_restrict.
  apply map_restrict_insert_notin. exact HxD.
Qed.

Lemma denot_relevant_env_fv_subset Σ τ e :
  lvars_fv (dom (denot_relevant_env Σ τ e)) ⊆
  fv_cty τ ∪ fv_tm e.
Proof.
  unfold denot_relevant_env, denot_relevant_lvars.
  transitivity (lvars_fv (context_ty_lvars τ ∪ tm_lvars e)).
  - apply lty_env_restrict_lvars_fv_subset.
  - rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
Qed.

Lemma denot_relevant_env_eq_of_tm_lvars_eq
    (Σ : lty_env) τ e e' :
  tm_lvars e = tm_lvars e' ->
  denot_relevant_env Σ τ e = denot_relevant_env Σ τ e'.
Proof.
  intros Heq.
  unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
  rewrite Heq. reflexivity.
Qed.

Lemma denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq
    (Σ : lty_env) τ e_src e_tgt (m : WfWorldT) :
  tm_lvars e_tgt = tm_lvars e_src ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ e_src) ->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ e_src) e_src (erase_ty τ) ->
  wfworld_closed_on (fv_tm e_tgt) m.
Proof.
  intros Hlvars Hworld Hbasic.
  eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
  unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
  change (lvars_of_atoms (fv_tm e_tgt) ⊆
    dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e_src))).
  rewrite storeA_restrict_dom.
  intros v Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [a [-> Ha]].
  apply elem_of_intersection. split.
  - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
      as [Hsub _].
    assert (Ha_lvars : LVFree a ∈ tm_lvars e_src).
    {
      rewrite <- Hlvars.
      apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
    }
    specialize (Hsub _ Ha_lvars).
    unfold denot_relevant_env, denot_relevant_lvars,
      lty_env_restrict_lvars in Hsub.
    change (LVFree a ∈ dom
      (storeA_restrict (Σ : gmap logic_var ty)
        (context_ty_lvars τ ∪ tm_lvars e_src))) in Hsub.
    rewrite storeA_restrict_dom in Hsub.
    apply elem_of_intersection in Hsub as [HaΣ _].
    exact HaΣ.
  - apply elem_of_union_r.
    rewrite <- Hlvars.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
Qed.

Lemma denot_relevant_basic_world_typing_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ basic_world_formula (denot_relevant_env Σ τ e) ->
  m ⊨ expr_basic_typing_formula
    (denot_relevant_env Σ τ e) e (erase_ty τ) ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  eapply denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq.
  reflexivity.
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

Lemma denot_relevant_lvars_insert_fresh x τ e :
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  LVFree x ∉ denot_relevant_lvars τ e.
Proof.
  intros Hxτ Hxe.
  unfold denot_relevant_lvars.
  pose proof (tm_lvars_free_notin_of_fv x e Hxe).
  set_solver.
Qed.

Lemma denot_relevant_env_insert_fresh Σ τ e x T :
  LVFree x ∉ context_ty_lvars τ ->
  x ∉ fv_tm e ->
  denot_relevant_env (<[LVFree x := T]> Σ) τ e =
  denot_relevant_env Σ τ e.
Proof.
  intros Hxτ Hxe.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  change (storeA_restrict
    (<[LVFree x := T]> (Σ : gmap logic_var ty))
    (denot_relevant_lvars τ e) =
    storeA_restrict (Σ : gmap logic_var ty)
      (denot_relevant_lvars τ e)).
  unfold storeA_restrict.
  apply map_restrict_insert_notin.
  apply denot_relevant_lvars_insert_fresh; assumption.
Qed.

Lemma lty_env_restrict_lvars_insert_denot_relevant_env_eq
    Σ τ e X y T :
  X ∖ {[LVFree y]} ⊆ denot_relevant_lvars τ e ->
  lty_env_restrict_lvars
    (<[LVFree y := T]> (denot_relevant_env Σ τ e)) X =
  lty_env_restrict_lvars (<[LVFree y := T]> Σ) X.
Proof.
  intros Hsub.
  unfold lty_env_restrict_lvars, denot_relevant_env.
  apply storeA_map_eq. intros v.
  change ((storeA_restrict
    (<[LVFree y := T]>
      (storeA_restrict (Σ : gmap logic_var ty) (denot_relevant_lvars τ e)
        : gmap logic_var ty)) X : gmap logic_var ty) !! v =
    (storeA_restrict (<[LVFree y := T]> (Σ : gmap logic_var ty)) X
      : gmap logic_var ty) !! v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := T]>
      (storeA_restrict (Σ : gmap logic_var ty) (denot_relevant_lvars τ e)
        : gmap logic_var ty)) X v).
  rewrite (storeA_restrict_lookup
    (<[LVFree y := T]> (Σ : gmap logic_var ty)) X v).
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  destruct (decide (v = LVFree y)) as [->|Hvy].
  - rewrite !lookup_insert_eq. reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    unfold lty_env_restrict_lvars.
    rewrite storeA_restrict_lookup.
    destruct (decide (v ∈ denot_relevant_lvars τ e)) as [_|Hvrel].
    + reflexivity.
    + exfalso. apply Hvrel. apply Hsub. set_solver.
Qed.

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
