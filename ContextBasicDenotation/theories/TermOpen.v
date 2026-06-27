(** * BasicDenotation.TermOpen

    Split out from [Term.v] to keep individual proof files small. *)

From ContextBasicDenotation Require Import Notation StoreTyping.
From ContextBasicDenotation Require Import TermSyntax TermEval.
From ContextBase Require Import BaseTactics.
From ContextQualifier Require Import Qualifier.
From CoreLang Require Import StrongNormalization.

Section TermDenotation.

Definition expr_result_qual (e : tm) (x : logic_var) : qualifier (V := value) :=
  tqual (tm_lvars e ∪ {[x]})
    (fun s => expr_result_at_store e x (lso_store s)).

Definition expr_result_formula_at (D : lvset) (e : tm) (x : logic_var)
    : Formula :=
  FFibVars D (FAtom (expr_result_qual e x)).

Definition expr_result_formula (e : tm) (x : logic_var) : Formula :=
  expr_result_formula_at (tm_lvars e) e x.

Definition expr_result_atom_formula (e : tm) (x : logic_var) : Formula :=
  FAtom (expr_result_qual e x).

Lemma formula_fv_expr_result_formula_at D e x :
  formula_fv (expr_result_formula_at D e x) =
  lvars_fv D ∪ lvars_fv (tm_lvars e ∪ {[x]}).
Proof.
  unfold expr_result_formula_at, expr_result_qual.
  rewrite formula_fv_fibvars, formula_fv_atom.
  unfold qual_dom, qual_vars.
  set_solver.
Qed.

Definition expr_result_formula_on (X : aset) (e : tm) (x : logic_var)
    : Formula :=
  expr_result_formula_at (lvars_of_atoms X) e x.

Lemma formula_fv_expr_result_formula e x :
  formula_fv (expr_result_formula e x) =
  lvars_fv (tm_lvars e ∪ {[x]}).
Proof.
  unfold expr_result_formula, expr_result_formula_at, expr_result_qual.
  rewrite formula_fv_fibvars, formula_fv_atom.
  unfold qual_dom, qual_vars.
  rewrite <- lvars_fv_union.
  f_equal. set_solver.
Qed.

Lemma formula_fv_expr_result_atom_formula e x :
  formula_fv (expr_result_atom_formula e x) =
  lvars_fv (tm_lvars e ∪ {[x]}).
Proof.
  unfold expr_result_atom_formula, expr_result_qual.
  rewrite formula_fv_atom.
  unfold qual_dom, qual_vars.
  reflexivity.
Qed.

Lemma formula_fv_expr_result_formula_on X e x :
  formula_fv (expr_result_formula_on X e x) =
  X ∪ lvars_fv (tm_lvars e ∪ {[x]}).
Proof.
  unfold expr_result_formula_on, expr_result_formula_at, expr_result_qual.
  rewrite formula_fv_fibvars, formula_fv_atom.
  unfold qual_dom, qual_vars.
  rewrite lvars_fv_of_atoms.
  set_solver.
Qed.

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
	  - f_equal.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H; set_solver.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H0; set_solver.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H1; set_solver.
	  - f_equal.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H; set_solver.
	    + match goal with
	      | |- lstore_instantiate_tm_split_at d _ _ ?e =
	           lstore_instantiate_tm_split_at d _ _
	             (open_tm (d + k) (vfvar y) ?e) =>
	          change (lstore_instantiate_tm_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) e =
	          lstore_instantiate_tm_at d σ
	            (open_tm (d + k) (vfvar y) e))
	      end.
	      apply H0; set_solver.
	    + replace (d + k + 3) with (d + 3 + k) by lia.
	      match goal with
	      | |- lstore_instantiate_tm_split_at (d + 3) _ _ ?e =
	           lstore_instantiate_tm_split_at (d + 3) _ _
	             (open_tm (d + 3 + k) (vfvar y) ?e) =>
	          change (lstore_instantiate_tm_at (d + 3)
	            (lstore_swap (LVBound k) (LVFree y) σ) e =
	          lstore_instantiate_tm_at (d + 3) σ
	            (open_tm (d + 3 + k) (vfvar y) e))
	      end.
	      apply H1; set_solver.
	  - f_equal.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H; set_solver.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H0; set_solver.
	  - f_equal.
	    + match goal with
	      | |- lstore_instantiate_value_split_at d _ _ ?v =
	           lstore_instantiate_value_split_at d _ _
	             (open_value (d + k) (vfvar y) ?v) =>
	          change (lstore_instantiate_value_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) v =
	          lstore_instantiate_value_at d σ
	            (open_value (d + k) (vfvar y) v))
	      end.
	      apply H; set_solver.
	    + match goal with
	      | |- lstore_instantiate_tm_split_at d _ _ ?e =
	           lstore_instantiate_tm_split_at d _ _
	             (open_tm (d + k) (vfvar y) ?e) =>
	          change (lstore_instantiate_tm_at d
	            (lstore_swap (LVBound k) (LVFree y) σ) e =
	          lstore_instantiate_tm_at d σ
	            (open_tm (d + k) (vfvar y) e))
	      end.
	      apply H0; set_solver.
	    + replace (d + k + 2) with (d + 2 + k) by lia.
	      match goal with
	      | |- lstore_instantiate_tm_split_at (d + 2) _ _ ?e =
	           lstore_instantiate_tm_split_at (d + 2) _ _
	             (open_tm (d + 2 + k) (vfvar y) ?e) =>
	          change (lstore_instantiate_tm_at (d + 2)
	            (lstore_swap (LVBound k) (LVFree y) σ) e =
	          lstore_instantiate_tm_at (d + 2) σ
	            (open_tm (d + 2 + k) (vfvar y) e))
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

Lemma expr_strong_total_open_back_iff k y e σ :
  y ∉ fv_tm e ->
  lvars_open k y (tm_lvars e) ⊆ dom (σ : gmap logic_var value) ->
  must_terminating
    (lstore_instantiate_tm (lstore_swap (LVBound k) (LVFree y) σ) e) <->
  must_terminating
    (lstore_instantiate_tm σ (open_tm k (vfvar y) e)).
Proof.
  intros Hy Hdom.
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
	      assert (Hτdom :
	        lvars_open k y (tm_lvars e) ⊆ dom (τ : gmap logic_var value)).
	      {
	        rewrite (lworld_on_store_dom_eq _ w τ Hτ). set_solver.
	      }
	      apply expr_strong_total_open_back_iff in Hres;
	        [exact Hres | exact Hy | exact Hτdom].
  - split.
    + unfold lworld_on_open_back. cbn [lw lraw_world raw_worldA worldA_dom].
      rewrite lworld_dom_lres_swap, (@lw_dom value _ w).
      better_base_solver.
	    + intros σ Hσ.
	      apply lworld_on_open_back_store_swap_inv in Hσ as [σ0 [Hσ0 ->]].
	      pose proof (Hstores σ0 Hσ0) as Hsn.
	      assert (Hσ0dom :
	        lvars_open k y (tm_lvars e) ⊆ dom (σ0 : gmap logic_var value)).
	      {
	        rewrite (lworld_on_store_dom_eq _ w σ0 Hσ0). set_solver.
	      }
	      apply expr_strong_total_open_back_iff; [exact Hy | exact Hσ0dom | exact Hsn].
Qed.

Lemma formula_open_expr_total_formula k y e :
  y ∉ fv_tm e ->
  formula_open k y (expr_total_formula e) =
  expr_total_formula (open_tm k (vfvar y) e).
Proof.
  intros Hy.
  unfold expr_total_formula, expr_total_qual.
  rewrite formula_open_fiber_atom.
  apply f_equal.
  apply qual_ext.
  - symmetry. apply tm_lvars_open. exact Hy.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    split; intros Hsn.
    + apply expr_strong_total_open_back_iff in Hsn.
      * change (must_terminating
          (lstore_instantiate_tm (lso_store s2)
            (open_tm k (vfvar y) e))).
        rewrite <- Hs. exact Hsn.
      * exact Hy.
      * change (lvars_open k y (tm_lvars e) ⊆
          dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). reflexivity.
    + apply expr_strong_total_open_back_iff.
      * exact Hy.
      * change (lvars_open k y (tm_lvars e) ⊆
          dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). reflexivity.
      * change (must_terminating
          (lstore_instantiate_tm (lso_store s1)
            (open_tm k (vfvar y) e))).
        rewrite Hs. exact Hsn.
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
  unfold expr_result_formula, expr_result_formula_at, expr_result_qual.
  rewrite formula_open_fibvars, formula_open_atom.
  apply f_equal2.
  - pose proof (tm_lvars_open k y e Hy) as Hopen.
    unfold set_swap in Hopen. symmetry. exact Hopen.
  - apply f_equal.
    apply qual_ext.
    + apply tm_lvars_open_result_domain. exact Hy.
    + intros s1 s2 Hs. cbn [qual_prop qual_lvars].
      split; intros Hres.
      * apply expr_result_at_store_open_back_iff in Hres.
        -- change (expr_result_at_store
             (open_tm k (vfvar y) e) (logic_var_open k y z)
             (lso_store s2)).
           rewrite <- Hs. exact Hres.
        -- exact Hy.
        -- change (lvars_open k y (tm_lvars e) ⊆
             dom (lso_store s1 : LStoreT)).
           rewrite (lso_dom s1). set_solver.
      * apply expr_result_at_store_open_back_iff.
        -- exact Hy.
        -- change (lvars_open k y (tm_lvars e) ⊆
             dom (lso_store s1 : LStoreT)).
           rewrite (lso_dom s1). set_solver.
        -- change (expr_result_at_store
             (open_tm k (vfvar y) e) (logic_var_open k y z)
             (lso_store s1)).
           rewrite Hs. exact Hres.
Qed.

Lemma formula_open_expr_result_atom_formula k y e z :
  y ∉ fv_tm e ->
  formula_open k y (expr_result_atom_formula e z) =
  expr_result_atom_formula
    (open_tm k (vfvar y) e) (logic_var_open k y z).
Proof.
  intros Hy.
  unfold expr_result_atom_formula, expr_result_qual.
  rewrite formula_open_atom.
  apply f_equal.
  apply qual_ext.
  - apply tm_lvars_open_result_domain. exact Hy.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    split; intros Hres.
    + apply expr_result_at_store_open_back_iff in Hres.
      * change (expr_result_at_store
           (open_tm k (vfvar y) e) (logic_var_open k y z)
           (lso_store s2)).
        rewrite <- Hs. exact Hres.
      * exact Hy.
      * change (lvars_open k y (tm_lvars e) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
    + apply expr_result_at_store_open_back_iff.
      * exact Hy.
      * change (lvars_open k y (tm_lvars e) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
      * change (expr_result_at_store
           (open_tm k (vfvar y) e) (logic_var_open k y z)
           (lso_store s1)).
        rewrite Hs. exact Hres.
Qed.

Lemma formula_open_expr_result_formula_at k y D e z :
  y ∉ fv_tm e ->
  formula_open k y (expr_result_formula_at D e z) =
  expr_result_formula_at (lvars_open k y D)
    (open_tm k (vfvar y) e) (logic_var_open k y z).
Proof.
  intros Hy.
  unfold expr_result_formula_at, expr_result_qual.
  rewrite formula_open_fibvars, formula_open_atom.
  apply f_equal2; [reflexivity|].
  apply f_equal.
  apply qual_ext.
  - apply tm_lvars_open_result_domain. exact Hy.
  - intros s1 s2 Hs. cbn [qual_prop qual_lvars].
    split; intros Hres.
    + apply expr_result_at_store_open_back_iff in Hres.
      * change (expr_result_at_store
           (open_tm k (vfvar y) e) (logic_var_open k y z)
           (lso_store s2)).
        rewrite <- Hs. exact Hres.
      * exact Hy.
      * change (lvars_open k y (tm_lvars e) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
    + apply expr_result_at_store_open_back_iff.
      * exact Hy.
      * change (lvars_open k y (tm_lvars e) ⊆
           dom (lso_store s1 : LStoreT)).
        rewrite (lso_dom s1). set_solver.
      * change (expr_result_at_store
           (open_tm k (vfvar y) e) (logic_var_open k y z)
           (lso_store s1)).
        rewrite Hs. exact Hres.
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

Lemma formula_open_expr_result_formula_at_shift0 y D e :
  lc_lvars D ->
  y ∉ lvars_fv D ->
  lc_tm e ->
  y ∉ fv_tm e ->
  formula_open 0 y
    (expr_result_formula_at D (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula_at D e (LVFree y).
Proof.
  intros HlcD HyD Hlc Hy.
  rewrite formula_open_expr_result_formula_at.
  - rewrite open_tm_shift0_lc by exact Hlc.
    replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
    + rewrite lvars_open_fresh_index; [reflexivity| |exact HyD].
      intros Hbad. rewrite lvars_bv_elem in Hbad.
      exact (HlcD (LVBound 0) Hbad).
    + unfold swap. repeat destruct decide; try lia; try congruence.
  - rewrite tm_shift_fv. exact Hy.
Qed.

Lemma formula_open_expr_result_atom_formula_shift0 y e :
  lc_tm e ->
  y ∉ fv_tm e ->
  formula_open 0 y
    (expr_result_atom_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_atom_formula e (LVFree y).
Proof.
  intros Hlc Hy.
  rewrite formula_open_expr_result_atom_formula.
  - rewrite open_tm_shift0_lc by exact Hlc.
    replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
    reflexivity.
    unfold swap.
    repeat destruct decide; try lia; try congruence.
  - rewrite tm_shift_fv. exact Hy.
Qed.

Lemma formula_msubst_store_open_expr_result_formula_shift0 σ y e :
  lc_tm e ->
  y ∉ fv_tm e ->
  y ∉ dom (σ : StoreT) ->
  formula_msubst_store σ
    (formula_open 0 y (expr_result_formula (tm_shift 0 e) (LVBound 0))) =
  formula_open 0 y
    (formula_msubst_store σ
      (expr_result_formula (tm_shift 0 e) (LVBound 0))).
Proof.
  intros _ _ Hyσ.
  apply formula_msubst_store_open_fresh. exact Hyσ.
Qed.

Lemma formula_msubst_store_expr_result_formula_shift0 y σ e :
  lc_tm e ->
  y ∉ fv_tm e ->
  y ∉ dom (σ : StoreT) ->
  formula_msubst_store σ
    (formula_open 0 y
      (expr_result_formula (tm_shift 0 e) (LVBound 0))) =
  formula_msubst_store σ (expr_result_formula e (LVFree y)).
Proof.
  intros Hlc Hy _.
  rewrite formula_open_expr_result_formula_shift0; eauto.
Qed.

Lemma formula_msubst_store_expr_result_atom_formula_shift0 y σ e :
  lc_tm e ->
  y ∉ fv_tm e ->
  y ∉ dom (σ : StoreT) ->
  formula_msubst_store σ
    (formula_open 0 y
      (expr_result_atom_formula (tm_shift 0 e) (LVBound 0))) =
  formula_msubst_store σ (expr_result_atom_formula e (LVFree y)).
Proof.
  intros Hlc Hy _.
  rewrite formula_open_expr_result_atom_formula_shift0; eauto.
Qed.

Lemma formula_msubst_store_expr_result_formula_restrict
    σ e y :
  y ∉ dom (σ : StoreT) ->
  formula_msubst_store σ (expr_result_formula e (LVFree y)) =
  formula_msubst_store (store_restrict σ (fv_tm e))
    (expr_result_formula e (LVFree y)).
Proof.
  intros Hyσ.
  unfold formula_msubst_store, expr_result_formula, expr_result_formula_at, expr_result_qual.
  cbn [formula_mlsubst].
  apply f_equal2.
  - rewrite !dom_lstore_lift_free.
    apply set_eq. intros v.
    rewrite !elem_of_difference.
    split.
    + intros [HvD Hnot]. split; [exact HvD|].
      intros Hbad. apply Hnot.
      destruct v as [k|x].
      * unfold lvars_of_atoms in Hbad.
        apply elem_of_map in Hbad as [? [Hbad _]]. discriminate.
      * unfold lvars_of_atoms in Hbad |- *.
        apply elem_of_map in Hbad as [a [Heq Ha]].
        inversion Heq. subst a.
        apply elem_of_map. exists x. split; [reflexivity|].
        change (x ∈ dom (σ : StoreT)).
        rewrite storeA_restrict_dom in Ha.
        apply elem_of_intersection in Ha as [Hx _]. exact Hx.
    + intros [HvD Hnot]. split; [exact HvD|].
      intros Hbad. apply Hnot.
      destruct v as [k|x].
      * unfold lvars_of_atoms in Hbad.
        apply elem_of_map in Hbad as [? [Hbad _]]. discriminate.
      * unfold lvars_of_atoms in Hbad |- *.
        apply elem_of_map in Hbad as [a [Heq Ha]].
        inversion Heq. subst a.
        apply elem_of_map. exists x. split; [reflexivity|].
        rewrite storeA_restrict_dom.
        apply elem_of_intersection. split; [exact Ha|].
        rewrite <- tm_lvars_fv.
        apply lvars_fv_elem. exact HvD.
  - apply f_equal.
    apply qual_ext.
    + cbn [qual_mlsubst qual_lvars].
      rewrite !dom_lstore_lift_free.
      apply set_eq. intros v.
      rewrite !elem_of_difference.
      split.
      * intros [HvD Hnot]. split; [exact HvD|].
        intros Hbad. apply Hnot.
        destruct v as [k|x].
        -- unfold lvars_of_atoms in Hbad.
           apply elem_of_map in Hbad as [? [Hbad _]]. discriminate.
        -- unfold lvars_of_atoms in Hbad |- *.
           apply elem_of_map in Hbad as [a [Heq Ha]].
           inversion Heq. subst a.
           apply elem_of_map. exists x. split; [reflexivity|].
           change (x ∈ dom (σ : StoreT)).
           rewrite storeA_restrict_dom in Ha.
           apply elem_of_intersection in Ha as [Hx _]. exact Hx.
      * intros [HvD Hnot]. split; [exact HvD|].
        intros Hbad. apply Hnot.
        destruct v as [k|x].
        -- unfold lvars_of_atoms in Hbad.
           apply elem_of_map in Hbad as [? [Hbad _]]. discriminate.
        -- unfold lvars_of_atoms in Hbad |- *.
           apply elem_of_map in Hbad as [a [Heq Ha]].
           inversion Heq. subst a.
           apply elem_of_map. exists x. split; [reflexivity|].
           rewrite storeA_restrict_dom.
           apply elem_of_intersection. split; [exact Ha|].
           apply elem_of_union in HvD as [HvD|HvD].
           ++ rewrite <- tm_lvars_fv.
              apply lvars_fv_elem. exact HvD.
           ++ assert (x = y) as -> by better_set_solver.
              exfalso. exact (Hyσ Ha).
    + intros s1 s2 Hs. cbn [qual_prop qual_lvars qual_mlsubst].
      split; intros Hres.
      * enough (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
            (lstore_lift_free σ) s1 =
          lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
            (lstore_lift_free (store_restrict σ (fv_tm e))) s2) as Heq.
        { rewrite <- Heq. exact Hres. }
        destruct s1 as [s1 Hdom1], s2 as [s2 Hdom2].
        cbn in Hs. subst s2.
        apply lstore_on_ext.
        unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
        apply storeA_map_eq. intros v.
        destruct ((s1 : LStoreT) !! v) as [w|] eqn:Hs1.
        { rewrite (lookup_union_l' (M:=gmap logic_var) (A:=value)
              (s1 : LStoreT)
              (storeA_restrict (lstore_lift_free σ : LStoreT)
                 (tm_lvars e ∪ {[LVFree y]})) v)
            by (eexists; exact Hs1).
          rewrite (lookup_union_l' (M:=gmap logic_var) (A:=value)
              (s1 : LStoreT)
              (storeA_restrict
                 (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
                 (tm_lvars e ∪ {[LVFree y]})) v)
            by (eexists; exact Hs1).
          reflexivity. }
        rewrite (lookup_union_r (M:=gmap logic_var) (A:=value)
            (s1 : LStoreT)
            (storeA_restrict (lstore_lift_free σ : LStoreT)
               (tm_lvars e ∪ {[LVFree y]})) v Hs1).
        rewrite (lookup_union_r (M:=gmap logic_var) (A:=value)
            (s1 : LStoreT)
            (storeA_restrict
               (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
               (tm_lvars e ∪ {[LVFree y]})) v Hs1).
        change (((storeA_restrict (lstore_lift_free σ : LStoreT)
             (tm_lvars e ∪ {[LVFree y]}) : LStoreT) !! v) =
          ((storeA_restrict
             (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
             (tm_lvars e ∪ {[LVFree y]}) : LStoreT) !! v)).
        rewrite (@storeA_restrict_lookup value logic_var _ _
          (lstore_lift_free σ : LStoreT)
          (tm_lvars e ∪ {[LVFree y]}) v).
        rewrite (@storeA_restrict_lookup value logic_var _ _
          (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
          (tm_lvars e ∪ {[LVFree y]}) v).
        destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [HvD|HvD];
          [|reflexivity].
        destruct v as [k|x].
        -- rewrite !lstore_lift_free_lookup_bound. reflexivity.
        -- rewrite !lstore_lift_free_lookup_free.
           destruct ((σ : StoreT) !! x) as [vx|] eqn:Hσx.
           ++ destruct (decide (x ∈ fv_tm e)) as [Hxe|Hxe].
              ** transitivity (Some vx).
                 --- exact Hσx.
                 --- symmetry. apply storeA_restrict_lookup_some_2;
                       [exact Hσx|exact Hxe].
              ** apply elem_of_union in HvD as [HvD|HvD].
                 --- exfalso. apply Hxe.
                     rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact HvD.
                 --- assert (x = y) as -> by better_set_solver.
                     exfalso. apply Hyσ.
                     change (y ∈ dom (σ : gmap atom value)).
                     rewrite elem_of_dom.
                     exists vx. exact Hσx.
           ++ transitivity (@None value).
              ** exact Hσx.
              ** symmetry. apply storeA_restrict_lookup_none_l. exact Hσx.
      * enough (lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
            (lstore_lift_free (store_restrict σ (fv_tm e))) s2 =
          lstore_on_mlsubst_back (tm_lvars e ∪ {[LVFree y]})
            (lstore_lift_free σ) s1) as Heq.
        { rewrite <- Heq. exact Hres. }
        destruct s1 as [s1 Hdom1], s2 as [s2 Hdom2].
        cbn in Hs. subst s2.
        apply lstore_on_ext.
        unfold lstore_on_mlsubst_back. cbn [lso_store storeAO_store].
        apply storeA_map_eq. intros v.
        destruct ((s1 : LStoreT) !! v) as [w|] eqn:Hs1.
        { rewrite (lookup_union_l' (M:=gmap logic_var) (A:=value)
              (s1 : LStoreT)
              (storeA_restrict
                 (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
                 (tm_lvars e ∪ {[LVFree y]})) v)
            by (eexists; exact Hs1).
          rewrite (lookup_union_l' (M:=gmap logic_var) (A:=value)
              (s1 : LStoreT)
              (storeA_restrict (lstore_lift_free σ : LStoreT)
                 (tm_lvars e ∪ {[LVFree y]})) v)
            by (eexists; exact Hs1).
          reflexivity. }
        rewrite (lookup_union_r (M:=gmap logic_var) (A:=value)
            (s1 : LStoreT)
            (storeA_restrict
               (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
               (tm_lvars e ∪ {[LVFree y]})) v Hs1).
        rewrite (lookup_union_r (M:=gmap logic_var) (A:=value)
            (s1 : LStoreT)
            (storeA_restrict (lstore_lift_free σ : LStoreT)
               (tm_lvars e ∪ {[LVFree y]})) v Hs1).
        change (((storeA_restrict
             (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
             (tm_lvars e ∪ {[LVFree y]}) : LStoreT) !! v) =
          ((storeA_restrict (lstore_lift_free σ : LStoreT)
             (tm_lvars e ∪ {[LVFree y]}) : LStoreT) !! v)).
        rewrite (@storeA_restrict_lookup value logic_var _ _
          (lstore_lift_free (store_restrict σ (fv_tm e)) : LStoreT)
          (tm_lvars e ∪ {[LVFree y]}) v).
        rewrite (@storeA_restrict_lookup value logic_var _ _
          (lstore_lift_free σ : LStoreT)
          (tm_lvars e ∪ {[LVFree y]}) v).
        destruct (decide (v ∈ tm_lvars e ∪ {[LVFree y]})) as [HvD|HvD];
          [|reflexivity].
        destruct v as [k|x].
        -- rewrite !lstore_lift_free_lookup_bound. reflexivity.
        -- rewrite !lstore_lift_free_lookup_free.
           destruct ((σ : StoreT) !! x) as [vx|] eqn:Hσx.
           ++ destruct (decide (x ∈ fv_tm e)) as [Hxe|Hxe].
              ** transitivity (Some vx).
                 --- apply storeA_restrict_lookup_some_2;
                       [exact Hσx|exact Hxe].
                 --- symmetry. exact Hσx.
              ** apply elem_of_union in HvD as [HvD|HvD].
                 --- exfalso. apply Hxe.
                     rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact HvD.
                 --- assert (x = y) as -> by better_set_solver.
                     exfalso. apply Hyσ.
                     change (y ∈ dom (σ : gmap atom value)).
                     rewrite elem_of_dom.
                     exists vx. exact Hσx.
           ++ transitivity (@None value).
              ** apply storeA_restrict_lookup_none_l. exact Hσx.
              ** symmetry. exact Hσx.
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

Lemma open_expr_result_atom_shift0_under_core k y e :
  y ∉ fv_tm e ->
  formula_open (S k) y
    (expr_result_atom_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_atom_formula (tm_shift 0 (open_tm k (vfvar y) e)) (LVBound 0).
Proof.
  intros Hy.
  rewrite formula_open_expr_result_atom_formula.
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

Lemma open_env_lift_expr_result_at_shift0_core η D e :
  open_env_fresh_for_lvars (kmap S η) D ->
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env ((kmap S η))
    (expr_result_formula_at D (tm_shift 0 e) (LVBound 0)) =
  expr_result_formula_at (lvars_open_env (kmap S η) D)
    (tm_shift 0 (open_tm_env η e)) (LVBound 0).
Proof.
  revert D e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros D e _ _ _.
    rewrite kmap_empty, formula_open_env_empty.
    rewrite map_fold_empty, lvars_open_env_empty. reflexivity.
  - intros D e HfreshD Hfreshe Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    rewrite open_env_lift_insert in HfreshD.
    pose proof (open_env_fresh_for_lvars_insert_tail (kmap S η) (S k) x
      D ltac:(apply open_env_lift_lookup_none; exact Hnone)
      HfreshD) as HfreshDη.
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (tm_lvars e) Hnone Hfreshe) as Hfresheη.
    rewrite open_env_lift_insert.
    rewrite formula_open_env_insert_fresh.
    2:{ better_base_solver. }
    2:{ better_base_solver. }
    2:{ apply open_env_values_inj_lift. exact Hinjη. }
    rewrite IH by (exact HfreshDη || exact Hfresheη || exact Hinjη).
    rewrite formula_open_expr_result_formula_at.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (tm_lvars e) Hnone Hfreshe) as Hhead.
      rewrite tm_shift_fv.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env; [exact Hhead|exact Hfresheη].
    }
    rewrite tm_shift_open_tm_fvar by lia.
    replace (logic_var_open (S k) x (LVBound 0)) with (LVBound 0).
    2:{ unfold swap. repeat destruct decide; try lia; try congruence. }
    rewrite lvars_open_env_insert_fresh.
    2:{ apply open_env_lift_lookup_none. exact Hnone. }
    2:{
      eapply (open_env_fresh_for_lvars_insert_head (kmap S η) (S k) x D).
      - apply open_env_lift_lookup_none. exact Hnone.
      - exact HfreshD.
    }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

Lemma open_env_lift_expr_result_atom_shift0_core η e :
  open_env_fresh_for_lvars η (tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env ((kmap S η))
    (expr_result_atom_formula (tm_shift 0 e) (LVBound 0)) =
  expr_result_atom_formula (tm_shift 0 (open_tm_env η e)) (LVBound 0).
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
    rewrite open_expr_result_atom_shift0_under_core.
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

Notation "'FResult' '[' e '⇓' x ']'" := (expr_result_formula e x)
  (at level 10, e at level 9, x at level 9,
   format "FResult [ e  ⇓  x ]") : formula_scope.
