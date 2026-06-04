(** * BasicDenotation.TermOpen

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Import TermSyntax TermEval.
From ContextBase Require Import BaseTactics.

Section TermDenotation.

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
  ((σ : gmap logic_var value) !! swap a b z).
Proof.
  unfold lstore_swap, lstore_rekey.
  change ((storeA_swap a b σ : gmap logic_var value) !! z =
    (σ : gmap logic_var value) !! swap a b z).
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
    base_swap_normalize.
    reflexivity.
  - destruct (decide (d + k = n)) as [Heq|Hneq].
    + subst n.
      destruct (decide (d <= d + k)) as [_|Hbad]; [|lia].
      rewrite lstore_bound_part_lookup, lstore_swap_lookup_inv_value.
      replace (d + k - d) with k by lia.
      rewrite swap_l.
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
        rewrite set_swap_singleton.
        rewrite swap_l.
        apply elem_of_singleton. reflexivity.
      }
      apply not_elem_of_dom in Hlook. exact (Hlook H1).
    + destruct (decide (d <= n)) as [Hdn|Hdn].
      * rewrite lstore_bound_part_lookup, lstore_swap_lookup_inv_value.
        rewrite swap_fresh.
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
        (StoreInterface.lstore_bound_part
          (lstore_swap (LVBound k) (LVFree y) σ)) e1)
      with (lstore_instantiate_tm_at d
        (lstore_swap (LVBound k) (LVFree y) σ) e1).
    change (lstore_instantiate_tm_split_at d (lstore_free_part σ)
        (StoreInterface.lstore_bound_part σ)
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
      pose proof (Hstores (lstore_swap (LVBound k) (LVFree y) τ)
        (lworld_on_open_back_store_swap_member k y (tm_lvars e) w τ Hτ))
        as Hres.
      destruct Hres as [v Heval]. exists v.
      assert (Hτdom :
        lvars_open k y (tm_lvars e) ⊆ dom (τ : gmap logic_var value)).
      {
        rewrite (lworld_on_store_dom_eq _ w τ Hτ). set_solver.
      }
      apply expr_eval_in_store_open_back_iff in Heval;
        [exact Heval | exact Hy | exact Hτdom].
  - split.
    + unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_dom].
      rewrite lworld_dom_lres_swap, (@lw_dom value _ w).
      better_base_solver.
    + intros σ Hσ.
      apply lworld_on_open_back_store_swap_inv in Hσ as [σ0 [Hσ0 ->]].
      destruct (Hstores σ0 Hσ0) as [v Heval]. exists v.
      assert (Hσ0dom :
        lvars_open k y (tm_lvars e) ⊆ dom (σ0 : gmap logic_var value)).
      {
        rewrite (lworld_on_store_dom_eq _ w σ0 Hσ0). set_solver.
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
    + rewrite set_swap_elem.
      base_swap_normalize.
      exact Hz.
    + exists v. split.
      * rewrite lstore_swap_lookup_inv_value in Hlookup.
        change (swap (LVBound k) (LVFree y) z) with
          (logic_var_open k y z) in Hlookup.
        exact Hlookup.
      * apply expr_eval_in_store_open_back_iff in Heval;
          [exact Heval | exact Hy | exact Hdom].
  - split.
    + rewrite set_swap_elem in Hz.
      base_swap_normalize.
      exact Hz.
    + exists v. split.
      * change ((lstore_swap (LVBound k) (LVFree y) σ : gmap logic_var value) !! z = Some v).
        rewrite lstore_swap_lookup_inv_value.
        change (swap (LVBound k) (LVFree y) z) with (logic_var_open k y z).
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
    + rewrite set_swap_elem.
      base_swap_normalize.
      exact Hz.
    + split.
      * change (worldA_dom (@lw value _ w : LWorldT)) with
          (lworld_dom (@lw value _ w)).
        rewrite (@lw_dom value _ w). set_solver.
      * intros τ Hτ.
        pose proof (Hstores (lstore_swap (LVBound k) (LVFree y) τ)
          (lworld_on_open_back_store_swap_member
            k y (tm_lvars e ∪ {[z]}) w τ Hτ)) as Hres.
        assert (Hτdom :
          lvars_open k y (tm_lvars e) ⊆ dom (τ : gmap logic_var value)).
        {
          rewrite (lworld_on_store_dom_eq _ w τ Hτ). set_solver.
        }
        apply expr_result_at_store_open_back_iff in Hres;
          [exact Hres | exact Hy | exact Hτdom].
  - split.
    + rewrite set_swap_elem in Hz.
      base_swap_normalize.
      exact Hz.
    + split.
      * change (tm_lvars e ∪ {[z]} ⊆
          worldA_dom
            (@lw value _ (lworld_on_open_back k y (tm_lvars e ∪ {[z]}) w) : LWorldT)).
        unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_dom].
        rewrite lworld_dom_lres_swap, (@lw_dom value _ w).
        rewrite set_swap_involutive.
        reflexivity.
      * intros σ Hσ.
        apply lworld_on_open_back_store_swap_inv in Hσ as [σ0 [Hσ0 ->]].
        assert (Hσ0dom :
          lvars_open k y (tm_lvars e) ⊆ dom (σ0 : gmap logic_var value)).
        {
          rewrite (lworld_on_store_dom_eq _ w σ0 Hσ0). set_solver.
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
  unfold set_swap.
  rewrite set_map_union_L, set_map_singleton_L.
  pose proof (tm_lvars_open k y e Hy) as Hopen.
  unfold set_swap in Hopen.
  rewrite Hopen.
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

Lemma formula_open_expr_result_formula_shift0 y e :
  lc_tm e ->
  y ∉ fv_tm e ->
  formula_open 0 y (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula e (LVFree y).
Proof.
  intros Hlc Hy.
  rewrite formula_open_expr_result_formula.
  - rewrite open_tm_shift0_lc by exact Hlc.
    replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
    reflexivity.
    unfold swap.
    repeat destruct decide; try lia; try congruence.
  - rewrite tm_shift_fv. exact Hy.
Qed.

Lemma open_expr_result_shift0_lvars_lc y e :
  lc_lvars (tm_lvars e) ->
  y ∉ fv_tm e ->
  formula_open 0 y (expr_result_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula e (LVFree y).
Proof.
  intros Hlc Hy.
  rewrite formula_open_expr_result_formula.
  - rewrite open_tm_shift0_lvars_lc by exact Hlc.
    replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
    reflexivity.
    unfold swap.
    repeat destruct decide; try lia; try congruence.
  - rewrite tm_shift_fv. exact Hy.
Qed.

Lemma open_expr_result_shift0_under_core k y e :
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

Lemma open_env_lift_expr_result_shift0_core η e :
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
    rewrite open_expr_result_shift0_under_core.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env; [exact Hhead|exact Hfreshη].
    }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

End TermDenotation.
