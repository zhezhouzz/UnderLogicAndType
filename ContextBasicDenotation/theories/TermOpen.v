(** * BasicDenotation.TermOpen

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Export TermEval.
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
      better_base_solver.
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
    + rewrite set_swap_elem in Hz.
      base_swap_normalize.
      exact Hz.
    + split.
      * change (tm_lvars e ∪ {[z]} ⊆
          worldA_dom
            (@lw value _ (lworld_on_open_back k y (tm_lvars e ∪ {[z]}) w) : LWorldT)).
      unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_dom].
      rewrite lworld_dom_lres_swap, (@lw_dom value _ w).
      better_base_solver.
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

End TermDenotation.
