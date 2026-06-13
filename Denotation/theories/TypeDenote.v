(** * Denotation.TypeDenote *)

From Denotation Require Import Notation.

Section TypeDenote.

Definition ty_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (FAnd (expr_basic_typing_formula Σ e (erase_ty τ))
            (expr_total_formula e))).

Definition ty_static_guard_formula
    (Σ : lty_env) (τ : context_ty) (e : tm) : FormulaT :=
  FAnd (context_ty_wf_formula Σ τ)
    (FAnd (basic_world_formula Σ)
      (expr_basic_typing_formula Σ e (erase_ty τ))).

Definition arrow_value_denote_gas_with
    (denote : nat -> lty_env -> context_ty -> tm -> FormulaT)
    (gas : nat) (Σ : lty_env) (τx τr : context_ty) (ef : tm) :
    FormulaT :=
  let Σx := typed_lty_env_bind Σ (erase_ty τx) in
  FForall
    (FImpl
      (denote gas Σx
        (cty_shift 0 τx) (tret (vbvar 0)))
      (denote gas Σx τr
        (tapp_tm (tm_shift 0 ef) (vbvar 0)))).

Definition wand_value_denote_gas_with
    (denote : nat -> lty_env -> context_ty -> tm -> FormulaT)
    (gas : nat) (Σ : lty_env) (τx τr : context_ty) (ef : tm) :
    FormulaT :=
  let Σx := typed_lty_env_bind Σ (erase_ty τx) in
  FBWand 1
    (denote gas Σx
      (cty_shift 0 τx) (tret (vbvar 0)))
    (denote gas Σx τr
      (tapp_tm (tm_shift 0 ef) (vbvar 0))).

Fixpoint ty_denote_gas
    (gas : nat) (Σ : lty_env) (τ : context_ty) (e : tm)
    {struct gas} : FormulaT :=
  let Σg := relevant_env Σ τ e in
  FAnd
    (ty_guard_formula Σg τ e)
    (match gas with
    | 0 => FTrue
    | S gas' =>
      match τ with
      | CTOver b φ =>
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FOver (FAtom φ))))
      | CTUnder b φ =>
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FFibVars (qual_vars φ ∖ {[LVBound 0]})
                (FUnder (FAtom φ))))
      | CTInter τ1 τ2 =>
          FAnd
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTUnion τ1 τ2 =>
          FOr
            (ty_denote_gas gas' Σ τ1 e)
            (ty_denote_gas gas' Σ τ2 e)
      | CTSum τ1 τ2 =>
          let Σr := typed_lty_env_bind Σg (erase_ty τ1) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (FPlus
                (ty_denote_gas gas' Σr
                  (cty_shift 0 τ1) (tret (vbvar 0)))
                (ty_denote_gas gas' Σr
                  (cty_shift 0 τ2) (tret (vbvar 0)))))
      | CTArrow τx τr =>
          let Σf := typed_lty_env_bind Σg (erase_ty (CTArrow τx τr)) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (arrow_value_denote_gas_with ty_denote_gas gas' Σf
                (cty_shift 0 τx) (cty_shift 1 τr)
                (tret (vbvar 0))))
      | CTWand τx τr =>
          let Σf := typed_lty_env_bind Σg (erase_ty (CTWand τx τr)) in
          FForall
            (FImpl
              (expr_result_formula_at (lvars_shift_from 0 (dom Σg))
                (tm_shift 0 e) (LVBound 0))
              (wand_value_denote_gas_with ty_denote_gas gas' Σf
                (cty_shift 0 τx) (cty_shift 1 τr)
                (tret (vbvar 0))))
    end
    end).

Definition arrow_value_denote_gas :=
  arrow_value_denote_gas_with ty_denote_gas.

Definition wand_value_denote_gas :=
  wand_value_denote_gas_with ty_denote_gas.

Lemma open_env_lift_fresh_for_bound0_bind_dom η T :
  open_env_fresh_for_lvars
    (kmap S η)
    (dom (<[LVBound 0 := T]> (∅ : gmap logic_var ty))).
Proof.
  replace (dom (<[LVBound 0 := T]> (∅ : gmap logic_var ty)))
    with ({[LVBound 0]} : lvset)
    by (rewrite dom_insert_L, dom_empty_L; set_solver).
  apply open_env_lift_fresh_for_bound0_singleton.
Qed.

Lemma formula_open_env_denot_guard η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η
    (ty_guard_formula (relevant_env Σ τ e) τ e) =
  ty_guard_formula
    (relevant_env (lty_env_open_lvars η Σ)
      (open_cty_env η τ) (open_tm_env η e))
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  intros Hfresh Hinj.
  unfold ty_guard_formula.
  rewrite !formula_open_env_and.
  rewrite formula_open_env_context_ty_wf_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (relevant_env_dom_subset_direct Σ τ e).
    unfold relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_basic_world_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (relevant_env_dom_subset_direct Σ τ e).
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_expr_basic_typing_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    pose proof (relevant_env_dom_subset_direct Σ τ e).
    unfold relevant_lvars in *.
    set_solver.
  }
  2: exact Hinj.
  rewrite formula_open_env_expr_total_formula.
  2:{
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
    intros v Hv.
    relevant_lvars_norm. better_set_solver.
  }
  2: exact Hinj.
  rewrite relevant_env_open_env by exact Hfresh || exact Hinj.
  rewrite open_cty_env_preserves_erasure.
  reflexivity.
Qed.

Lemma relevant_env_result_domain_open_lift η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  lvars_open_env (kmap S η)
    (lvars_shift_from 0 (dom (relevant_env Σ τ e))) =
  lvars_shift_from 0
    (dom (relevant_env (lty_env_open_lvars η Σ)
      (open_cty_env η τ) (open_tm_env η e))).
Proof.
  intros Hfresh Hinj.
  rewrite <- open_env_shift_from_zero.
  rewrite lvars_open_env_shift_from.
  rewrite <- lty_env_open_lvars_dom.
  rewrite relevant_env_open_env by exact Hfresh || exact Hinj.
  reflexivity.
Unshelve.
  all: first [exact Hfresh | exact Hinj |
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
    intros v Hv;
    pose proof (relevant_env_dom_subset_direct Σ τ e);
    unfold relevant_lvars in *;
    set_solver].
Qed.

Lemma formula_open_env_ty_denote_gas_zero η Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (ty_denote_gas 0 Σ τ e) =
  ty_denote_gas 0
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  intros Hfresh Hinj.
  cbn [ty_denote_gas].
  rewrite formula_open_env_and.
  rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
  rewrite formula_open_env_true.
  reflexivity.
Qed.

Ltac denot_open_env_child_fresh Hfresh :=
  eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
  unfold relevant_lvars;
  intros v Hv; cbn [context_ty_lvars context_ty_lvars_at] in *;
  set_solver.

Ltac denot_open_env_qual_case η Hfresh Hinj φ e :=
  let Hfreshφ := fresh "Hfreshφ" in
  let Hfreshe := fresh "Hfreshe" in
  let HfreshD := fresh "HfreshD" in
  assert (Hfreshφ :
      open_env_fresh_for_lvars ((kmap S η)) (qual_vars φ));
  [ apply open_env_lift_fresh_for_lvars_at_depth1;
    eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
    unfold relevant_lvars;
    cbn [context_ty_lvars context_ty_lvars_at];
    set_solver
  | assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e));
    [ eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
      unfold relevant_lvars; set_solver
    | cbn [ty_denote_gas];
      match goal with
      | |- context [
          expr_result_formula_at
            (lvars_shift_from 0 (dom (relevant_env ?Σ ?τ ?e0)))
            (tm_shift 0 ?e0) (LVBound 0)] =>
          assert (HfreshD :
            open_env_fresh_for_lvars (kmap S η)
              (lvars_shift_from 0 (dom (relevant_env Σ τ e0))));
          [ rewrite <- open_env_shift_from_zero;
            apply open_env_shift_from_fresh_for_lvars;
            eapply open_env_fresh_for_lvars_mono; [|exact Hfresh];
            intros v Hv;
            pose proof (relevant_env_dom_subset_direct Σ τ e0);
            unfold relevant_lvars in *;
            set_solver
          | idtac ]
      end;
      rewrite formula_open_env_and;
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj);
      first [rewrite open_cty_env_over by exact Hinj
            |rewrite open_cty_env_under by exact Hinj];
	      cbn [ty_denote_gas];
	      rewrite formula_open_env_forall by exact Hinj;
	      rewrite !formula_open_env_impl;
	      rewrite open_env_lift_expr_result_at_shift0_core
	        by (exact HfreshD || exact Hfreshe || exact Hinj);
	      rewrite relevant_env_result_domain_open_lift
	        by (exact Hfresh || exact Hinj);
	      first [rewrite open_cty_env_over by exact Hinj
	            |rewrite open_cty_env_under by exact Hinj];
	      rewrite formula_open_env_fibvars;
	      [|eapply open_env_fresh_for_lvars_mono; [|exact Hfreshφ]; set_solver];
	      rewrite open_env_lift_qual_diff_bound0
	        by exact Hfreshφ;
	      first [rewrite formula_open_env_over
	            |rewrite formula_open_env_under];
	      rewrite formula_open_env_atom;
	      reflexivity ] ].

Ltac denot_open_env_binary_case IH Hfresh Hinj :=
  cbn [ty_denote_gas];
  rewrite formula_open_env_and;
  rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj);
  first [rewrite open_cty_env_inter
        |rewrite open_cty_env_union
        |rewrite open_cty_env_sum];
  cbn [ty_denote_gas];
  first [rewrite formula_open_env_and
        |rewrite formula_open_env_or
        |rewrite formula_open_env_plus];
  rewrite (IH _ _ _ _);
  [|denot_open_env_child_fresh Hfresh|exact Hinj];
  rewrite (IH _ _ _ _);
  [reflexivity|denot_open_env_child_fresh Hfresh|exact Hinj].

Lemma sum_result_lift_support_subset Σ τsum τ e T :
  context_ty_lvars τ ⊆ context_ty_lvars τsum ->
  lvars_at_depth 1
    (dom (typed_lty_env_bind (relevant_env Σ τsum e) T) ∪
     relevant_lvars (cty_shift 0 τ) (tret (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars τsum e.
Proof.
  intros Hτsub.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union.
  rewrite lvars_at_depth_typed_lty_env_bind.
  rewrite elem_of_subseteq. intros u Hu.
  rewrite elem_of_union in Hu.
  destruct Hu as [Hu|Hu].
  - pose proof (lvars_at_depth_relevant_env_subset_relevant
      0 Σ τsum e u Hu) as Hrel.
    set_solver.
  - rewrite lvars_at_depth_union in Hu.
    rewrite context_ty_lvars_depth in Hu.
    rewrite tm_lvars_depth in Hu.
    rewrite tm_lvars_at_tret_bound0_under in Hu.
    rewrite context_ty_lvars_at_shift_under in Hu by lia.
    change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ) in Hu.
    set_solver.
Qed.

Lemma arrow_value_arg_lift2_support_subset Σ τx τr e :
  lvars_at_depth 2
    (dom (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty (CTArrow τx τr)))
      (erase_ty (cty_shift 0 τx))) ∪
     relevant_lvars (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite !lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite !context_ty_lvars_at_shift_under by lia.
  rewrite tm_lvars_at_tret_bound0_under.
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma arrow_value_body_lift2_support_subset Σ τx τr e :
  lvars_at_depth 2
    (dom (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTArrow τx τr) e)
        (erase_ty (CTArrow τx τr)))
      (erase_ty (cty_shift 0 τx))) ∪
     relevant_lvars (cty_shift 1 τr)
       (tapp_tm (tret (vbvar 1)) (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTArrow τx τr) e.
Proof.
  rewrite lvars_at_depth_union.
  rewrite !lvars_at_depth_typed_lty_env_bind.
  pose proof (lvars_at_depth_relevant_env_subset_relevant
    0 Σ (CTArrow τx τr) e) as Hrel.
  unfold relevant_lvars.
  rewrite lvars_at_depth_union, context_ty_lvars_depth, tm_lvars_depth.
  rewrite context_ty_lvars_at_shift_under by lia.
  cbn [tm_lvars_at value_lvars_at].
  unfold bvar_lvars_at.
  repeat (destruct decide; try lia).
  cbn [context_ty_lvars context_ty_lvars_at].
  set_solver.
Qed.

Lemma wand_value_arg_lift2_support_subset Σ τx τr e :
  lvars_at_depth 2
    (dom (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e)
        (erase_ty (CTWand τx τr)))
      (erase_ty (cty_shift 0 τx))) ∪
     relevant_lvars (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTWand τx τr) e.
Proof.
  change (relevant_env Σ (CTWand τx τr) e)
    with (relevant_env Σ (CTArrow τx τr) e).
  change (erase_ty (CTWand τx τr)) with (erase_ty (CTArrow τx τr)).
  change (relevant_lvars (CTWand τx τr) e)
    with (relevant_lvars (CTArrow τx τr) e).
  apply arrow_value_arg_lift2_support_subset.
Qed.

Lemma wand_value_body_lift2_support_subset Σ τx τr e :
  lvars_at_depth 2
    (dom (typed_lty_env_bind
      (typed_lty_env_bind
        (relevant_env Σ (CTWand τx τr) e)
        (erase_ty (CTWand τx τr)))
      (erase_ty (cty_shift 0 τx))) ∪
     relevant_lvars (cty_shift 1 τr)
       (tapp_tm (tret (vbvar 1)) (vbvar 0))) ⊆
  dom Σ ∪ relevant_lvars (CTWand τx τr) e.
Proof.
  change (relevant_env Σ (CTWand τx τr) e)
    with (relevant_env Σ (CTArrow τx τr) e).
  change (erase_ty (CTWand τx τr)) with (erase_ty (CTArrow τx τr)).
  change (relevant_lvars (CTWand τx τr) e)
    with (relevant_lvars (CTArrow τx τr) e).
  apply arrow_value_body_lift2_support_subset.
Qed.

Lemma expr_result_shift0_bound0_lvars_subset e d :
  formula_lvars_at (S d)
    (expr_result_formula (tm_shift 0 e) (LVBound 0)) ⊆
  tm_lvars_at d e.
Proof.
  unfold expr_result_formula, expr_result_formula_at, expr_result_qual.
  cbn [formula_lvars_at qual_vars qual_lvars].
  rewrite lvars_at_depth_union.
  rewrite tm_lvars_depth.
  rewrite tm_lvars_at_shift_under by lia.
  rewrite ?lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma expr_result_atom_shift0_bound0_lvars_subset e d :
  formula_lvars_at (S d)
    (expr_result_atom_formula (tm_shift 0 e) (LVBound 0)) ⊆
  tm_lvars_at d e.
Proof.
  unfold expr_result_atom_formula, expr_result_qual.
  cbn [formula_lvars_at qual_vars qual_lvars].
  rewrite lvars_at_depth_union.
  rewrite tm_lvars_depth.
  rewrite tm_lvars_at_shift_under by lia.
  rewrite ?lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma formula_open_env_ty_denote_gas η gas Σ τ e :
  open_env_fresh_for_lvars η (dom Σ ∪ relevant_lvars τ e) ->
  open_env_values_inj η ->
  formula_open_env η (ty_denote_gas gas Σ τ e) =
  ty_denote_gas gas
    (lty_env_open_lvars η Σ)
    (open_cty_env η τ)
    (open_tm_env η e).
Proof.
  revert Σ τ e η.
  induction gas as [|gas IH]; intros Σ τ e η Hfresh Hinj.
  - apply formula_open_env_ty_denote_gas_zero; assumption.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr].
    + denot_open_env_qual_case η Hfresh Hinj φ e.
    + denot_open_env_qual_case η Hfresh Hinj φ e.
    + denot_open_env_binary_case IH Hfresh Hinj.
    + denot_open_env_binary_case IH Hfresh Hinj.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (relevant_env Σ (CTSum τ1 τ2) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (relevant_env_dom_subset_direct Σ (CTSum τ1 τ2) e).
        set_solver.
      }
	      assert (Hfresh_res :
	        open_env_fresh_for_lvars ((kmap S η))
	          (lvars_shift_from 0
	            (dom (relevant_env Σ (CTSum τ1 τ2) e)))).
	      {
	        rewrite <- open_env_shift_from_zero.
	        apply open_env_shift_from_fresh_for_lvars.
	        exact HfreshΣg.
	      }
	      assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e)).
	      {
	        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
	        unfold relevant_lvars. set_solver.
	      }
      assert (Hfresh_l :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1)) ∪
           relevant_lvars (cty_shift 0 τ1) (tret (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        eapply sum_result_lift_support_subset.
        cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
      }
      assert (Hfresh_r :
        open_env_fresh_for_lvars ((kmap S η))
          (dom (typed_lty_env_bind
            (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1)) ∪
           relevant_lvars (cty_shift 0 τ2) (tret (vbvar 0)))).
      {
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        eapply sum_result_lift_support_subset.
        cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
      }
      cbn [ty_denote_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_sum by exact Hinj.
      cbn [ty_denote_gas].
      rewrite formula_open_env_forall by exact Hinj.
	      rewrite formula_open_env_impl.
	      rewrite open_env_lift_expr_result_at_shift0_core.
	      2: exact Hfresh_res.
	      2: exact Hfreshe.
	      2: exact Hinj.
	      rewrite relevant_env_result_domain_open_lift
	        by (exact Hfresh || exact Hinj).
	      rewrite open_cty_env_sum by exact Hinj.
	      rewrite formula_open_env_plus.
      rewrite (IH
        (typed_lty_env_bind
          (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_l.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1))
        (cty_shift 0 τ2) (tret (vbvar 0)) ((kmap S η))).
      2: exact Hfresh_r.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift by exact HfreshΣg.
      rewrite relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_sum by exact Hinj.
      rewrite open_cty_env_preserves_erasure.
      rewrite !open_cty_env_lift_shift0_exact by
        (try exact Hinj; apply open_env_values_inj_lift; exact Hinj).
      rewrite !open_tm_env_lift_tret_bound0.
      reflexivity.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (relevant_env Σ (CTArrow τx τr) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (relevant_env_dom_subset_direct Σ (CTArrow τx τr) e).
        set_solver.
      }
      assert (Hfresh_res :
        open_env_fresh_for_lvars ((kmap S η))
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e)))).
      {
        rewrite <- open_env_shift_from_zero.
        apply open_env_shift_from_fresh_for_lvars.
        exact HfreshΣg.
      }
      assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e)).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold relevant_lvars. set_solver.
      }
      assert (Hfresh_arg :
        open_env_fresh_for_lvars (kmap S (kmap S η))
          (dom (typed_lty_env_bind
            (typed_lty_env_bind
              (relevant_env Σ (CTArrow τx τr) e)
              (erase_ty (CTArrow τx τr)))
            (erase_ty (cty_shift 0 τx))) ∪
           relevant_lvars (cty_shift 0 (cty_shift 0 τx))
             (tret (vbvar 0)))).
      {
        apply open_env_lift2_fresh_for_lvars_at_depth2.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply arrow_value_arg_lift2_support_subset.
      }
      assert (Hfresh_body :
        open_env_fresh_for_lvars (kmap S (kmap S η))
          (dom (typed_lty_env_bind
            (typed_lty_env_bind
              (relevant_env Σ (CTArrow τx τr) e)
              (erase_ty (CTArrow τx τr)))
            (erase_ty (cty_shift 0 τx))) ∪
           relevant_lvars (cty_shift 1 τr)
             (tapp_tm (tret (vbvar 1)) (vbvar 0)))).
      {
        apply open_env_lift2_fresh_for_lvars_at_depth2.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply arrow_value_body_lift2_support_subset.
      }
      cbn [ty_denote_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      cbn [ty_denote_gas].
      rewrite formula_open_env_forall by exact Hinj.
      rewrite formula_open_env_impl.
      rewrite open_env_lift_expr_result_at_shift0_core
        by (exact Hfresh_res || exact Hfreshe || exact Hinj).
      rewrite relevant_env_result_domain_open_lift
        by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      unfold arrow_value_denote_gas_with.
      rewrite formula_open_env_forall.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite formula_open_env_impl.
      rewrite (IH
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e)
            (erase_ty (CTArrow τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))
        (kmap S (kmap S η))).
      2: exact Hfresh_arg.
      2:{ apply open_env_values_inj_lift.
          apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e)
            (erase_ty (CTArrow τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τr)
        (tapp_tm (tret (vbvar 1)) (vbvar 0))
        (kmap S (kmap S η))).
      2: exact Hfresh_body.
      2:{ apply open_env_values_inj_lift.
          apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift.
      2: exact HfreshΣg.
      2:{
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        rewrite lvars_at_depth_typed_lty_env_bind.
        pose proof (lvars_at_depth_relevant_env_subset_relevant
          0 Σ (CTArrow τx τr) e).
        unfold relevant_lvars; cbn [context_ty_lvars context_ty_lvars_at].
        set_solver.
      }
      rewrite relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_arrow by exact Hinj.
      replace (erase_ty (CTArrow τx τr))
        with (erase_ty (CTArrow
          (open_cty_env η τx) (open_cty_env (kmap S η) τr)))
        by (cbn [erase_ty]; rewrite !open_cty_env_preserves_erasure; reflexivity).
      replace (erase_ty (cty_shift 0 τx))
        with (erase_ty (cty_shift 0 (open_cty_env η τx)))
        by (rewrite !cty_shift_preserves_erasure;
            rewrite open_cty_env_preserves_erasure; reflexivity).
      try rewrite !open_cty_env_preserves_erasure.
      rewrite !open_cty_env_lift_shift0_exact by
        (try exact Hinj; apply open_env_values_inj_lift; exact Hinj).
      rewrite <- open_env_lift_by_two.
      rewrite open_cty_env_lift2_shift1_exact by exact Hinj.
      rewrite open_env_lift_by_one.
      rewrite open_env_lift_by_two.
      try rewrite open_tm_env_lift_tret_bound0.
      change (tm_shift 0 (tret (vbvar 0))) with (tret (vbvar 1)).
      try rewrite open_tm_env_lift2_tapp_ret_bound1_bound0.
      reflexivity.
    + assert (HfreshΣg :
        open_env_fresh_for_lvars η
          (dom (relevant_env Σ (CTWand τx τr) e))).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        intros v Hv.
        pose proof (relevant_env_dom_subset_direct Σ (CTWand τx τr) e).
        set_solver.
      }
      assert (Hfresh_res :
        open_env_fresh_for_lvars ((kmap S η))
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTWand τx τr) e)))).
      {
        rewrite <- open_env_shift_from_zero.
        apply open_env_shift_from_fresh_for_lvars.
        exact HfreshΣg.
      }
      assert (Hfreshe : open_env_fresh_for_lvars η (tm_lvars e)).
      {
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        unfold relevant_lvars. set_solver.
      }
      assert (Hfresh_arg :
        open_env_fresh_for_lvars (kmap S (kmap S η))
          (dom (typed_lty_env_bind
            (typed_lty_env_bind
              (relevant_env Σ (CTWand τx τr) e)
              (erase_ty (CTWand τx τr)))
            (erase_ty (cty_shift 0 τx))) ∪
           relevant_lvars (cty_shift 0 (cty_shift 0 τx))
             (tret (vbvar 0)))).
      {
        apply open_env_lift2_fresh_for_lvars_at_depth2.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply wand_value_arg_lift2_support_subset.
      }
      assert (Hfresh_body :
        open_env_fresh_for_lvars (kmap S (kmap S η))
          (dom (typed_lty_env_bind
            (typed_lty_env_bind
              (relevant_env Σ (CTWand τx τr) e)
              (erase_ty (CTWand τx τr)))
            (erase_ty (cty_shift 0 τx))) ∪
           relevant_lvars (cty_shift 1 τr)
             (tapp_tm (tret (vbvar 1)) (vbvar 0)))).
      {
        apply open_env_lift2_fresh_for_lvars_at_depth2.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        apply wand_value_body_lift2_support_subset.
      }
      cbn [ty_denote_gas].
      rewrite formula_open_env_and.
      rewrite formula_open_env_denot_guard by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      cbn [ty_denote_gas].
      rewrite formula_open_env_forall by exact Hinj.
      rewrite formula_open_env_impl.
      rewrite open_env_lift_expr_result_at_shift0_core
        by (exact Hfresh_res || exact Hfreshe || exact Hinj).
      rewrite relevant_env_result_domain_open_lift
        by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      unfold wand_value_denote_gas_with.
      rewrite formula_open_env_fbwand.
      2:{ apply open_env_values_inj_lift. exact Hinj. }
      rewrite !open_env_lift_by_one.
      rewrite (IH
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e)
            (erase_ty (CTWand τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))
        (kmap S (kmap S η))).
      2: exact Hfresh_arg.
      2:{ apply open_env_values_inj_lift.
          apply open_env_values_inj_lift. exact Hinj. }
      rewrite (IH
        (typed_lty_env_bind
          (typed_lty_env_bind
            (relevant_env Σ (CTWand τx τr) e)
            (erase_ty (CTWand τx τr)))
          (erase_ty (cty_shift 0 τx)))
        (cty_shift 1 τr)
        (tapp_tm (tret (vbvar 1)) (vbvar 0))
        (kmap S (kmap S η))).
      2: exact Hfresh_body.
      2:{ apply open_env_values_inj_lift.
          apply open_env_values_inj_lift. exact Hinj. }
      rewrite !typed_lty_env_bind_open_env_lift.
      2: exact HfreshΣg.
      2:{
        apply open_env_lift_fresh_for_lvars_at_depth1.
        eapply open_env_fresh_for_lvars_mono; [|exact Hfresh].
        rewrite lvars_at_depth_typed_lty_env_bind.
        pose proof (lvars_at_depth_relevant_env_subset_relevant
          0 Σ (CTWand τx τr) e).
        unfold relevant_lvars; cbn [context_ty_lvars context_ty_lvars_at].
        set_solver.
      }
      rewrite relevant_env_open_env by (exact Hfresh || exact Hinj).
      rewrite open_cty_env_wand by exact Hinj.
      replace (erase_ty (CTWand τx τr))
        with (erase_ty (CTWand
          (open_cty_env η τx) (open_cty_env (kmap S η) τr)))
        by (cbn [erase_ty]; rewrite !open_cty_env_preserves_erasure; reflexivity).
      replace (erase_ty (cty_shift 0 τx))
        with (erase_ty (cty_shift 0 (open_cty_env η τx)))
        by (rewrite !cty_shift_preserves_erasure;
            rewrite open_cty_env_preserves_erasure; reflexivity).
      try rewrite !open_cty_env_preserves_erasure.
      rewrite !open_cty_env_lift_shift0_exact by
        (try exact Hinj; apply open_env_values_inj_lift; exact Hinj).
      rewrite <- open_env_lift_by_two.
      rewrite open_cty_env_lift2_shift1_exact by exact Hinj.
      rewrite open_env_lift_by_one.
      rewrite open_env_lift_by_two.
      try rewrite open_tm_env_lift_tret_bound0.
      change (tm_shift 0 (tret (vbvar 0))) with (tret (vbvar 1)).
      try rewrite open_tm_env_lift2_tapp_ret_bound1_bound0.
      reflexivity.
Qed.

Definition ty_denote
    (Δ : gmap atom ty) (τ : context_ty) (e : tm) : FormulaT :=
  ty_denote_gas (cty_depth τ) (atom_env_to_lty_env Δ) τ e.

Lemma formula_open_ty_denote_gas_singleton
    k y gas Σ τ e :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  formula_open k y (ty_denote_gas gas Σ τ e) =
  ty_denote_gas gas
    (lty_env_open_one k y Σ)
    (cty_open k y τ)
    (open_tm k (vfvar y) e).
Proof.
  intros HΣ He Hτ.
  assert (HΣfree : LVFree y ∉ dom Σ).
  {
    intros Hbad. apply HΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hfresh :
    open_env_fresh_for_lvars (<[k := y]> ∅)
      (dom Σ ∪ relevant_lvars τ e)).
  {
    apply open_env_fresh_for_lvars_singleton.
    relevant_lvars_norm. better_set_solver.
  }
  pose proof (formula_open_env_ty_denote_gas
    (<[k := y]> ∅) gas Σ τ e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  exact Heq.
Qed.

Lemma ty_denote_gas_env_agree_on gas Σ1 Σ2 τ e X :
  relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  ty_denote_gas gas Σ1 τ e =
  ty_denote_gas gas Σ2 τ e.
Proof.
  induction gas as [|gas IH] in Σ1, Σ2, τ, e, X |- *; intros Hsub Heq.
  - cbn [ty_denote_gas].
    unfold relevant_env, lty_env_restrict_lvars.
    erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
    reflexivity.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [ty_denote_gas].
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + rewrite (IH Σ1 Σ2 τ1 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      rewrite (IH Σ1 Σ2 τ2 e X).
      2: { intros v Hv. apply Hsub.
           unfold relevant_lvars in *.
           cbn [context_ty_lvars context_ty_lvars_at] in *.
           set_solver. }
      2: exact Heq.
      unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
    + unfold relevant_env, lty_env_restrict_lvars.
      erewrite storeA_restrict_eq_mono by (exact Hsub || exact Heq).
      reflexivity.
Qed.

Lemma res_models_ty_denote_gas_env_agree_on
    gas Σ1 Σ2 τ e X (m : WfWorldT) :
  relevant_lvars τ e ⊆ X ->
  lty_env_restrict_lvars Σ1 X = lty_env_restrict_lvars Σ2 X ->
  m ⊨ ty_denote_gas gas Σ1 τ e ->
  m ⊨ ty_denote_gas gas Σ2 τ e.
Proof.
  intros Hsub Heq Hmodels.
  rewrite <- (ty_denote_gas_env_agree_on gas Σ1 Σ2 τ e X Hsub Heq).
  exact Hmodels.
Qed.

End TypeDenote.

Notation "'⟦ty' τ '⟧[' Σ ',' gas ']'" :=
  (ty_denote_gas gas Σ τ)
  (at level 20, τ at level 200, Σ at level 200, gas at level 9,
   only parsing).

Notation "'⟦ty' τ '⟧[' Σ ',' gas ']' e" :=
  (ty_denote_gas gas Σ τ e)
  (at level 20, τ at level 200, Σ at level 200,
   gas at level 9, e at level 20,
   only parsing).

Notation "'⟦ty' τ '⟧[' Δ ']'" :=
  (ty_denote Δ τ)
  (at level 20, τ at level 200, Δ at level 200,
   only parsing).

Notation "'⟦ty' τ '⟧[' Δ ']' e" :=
  (ty_denote Δ τ e)
  (at level 20, τ at level 200, Δ at level 200, e at level 20,
   only parsing).

Notation "'⟦ty⟧[' Σ ',' gas ']' τ" :=
  (ty_denote_gas gas Σ τ)
  (at level 20, Σ at level 200, gas at level 9, τ at level 200,
   format "⟦ty⟧[ Σ ,  gas ]  τ").

Notation "'⟦ty⟧[' Σ ',' gas ']' τ e" :=
  (ty_denote_gas gas Σ τ e)
  (at level 20, Σ at level 200, gas at level 9,
   τ at level 200, e at level 20,
   format "⟦ty⟧[ Σ ,  gas ]  τ  e").

Notation "'⟦ty⟧[' Δ ']' τ" :=
  (ty_denote Δ τ)
  (at level 20, Δ at level 200, τ at level 200,
   format "⟦ty⟧[ Δ ]  τ").

Notation "'⟦ty⟧[' Δ ']' τ e" :=
  (ty_denote Δ τ e)
  (at level 20, Δ at level 200, τ at level 200, e at level 20,
   format "⟦ty⟧[ Δ ]  τ  e").

Notation "'guard[' Σ ']' τ" :=
  (ty_guard_formula Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "guard[ Σ ]  τ").

Notation "'guard[' Σ ']' τ e" :=
  (ty_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "guard[ Σ ]  τ  e").

Notation "'static_guard[' Σ ']' τ" :=
  (ty_static_guard_formula Σ τ)
  (at level 20, Σ at level 200, τ at level 200,
   format "static_guard[ Σ ]  τ").

Notation "'static_guard[' Σ ']' τ e" :=
  (ty_static_guard_formula Σ τ e)
  (at level 20, Σ at level 200, τ at level 200, e at level 20,
   format "static_guard[ Σ ]  τ  e").

Ltac ty_denote_open_one_side :=
  first
    [ assumption
    | relevant_lvars_norm; better_set_solver
    | type_open_env_syntax_norm;
      cbn [fv_tm fv_value value_lvars value_lvars_at];
      rewrite ?fv_tapp_tm, ?tm_shift_fv, ?cty_shift_fv;
      better_set_solver ].

Ltac ty_denote_open_one_norm :=
  repeat match goal with
  | |- context [formula_open 0 ?y
      (ty_denote_gas ?gas ?Σ ?τ ?e)] =>
      rewrite (formula_open_ty_denote_gas_singleton 0 y gas Σ τ e)
        by ty_denote_open_one_side
  end;
  repeat match goal with
  | |- context [open_tm 0 (vfvar ?y) (tret (vbvar 0))] =>
      change (open_tm 0 (vfvar y) (tret (vbvar 0)))
        with (tret (vfvar y))
  end;
  try rewrite ?open_tapp_tm_shift_bvar0_lc by assumption;
  type_open_env_syntax_norm.

Ltac ty_denote_open_one_norm_in H :=
  repeat match type of H with
  | context [formula_open 0 ?y
      (ty_denote_gas ?gas ?Σ ?τ ?e)] =>
      rewrite (formula_open_ty_denote_gas_singleton 0 y gas Σ τ e) in H
        by ty_denote_open_one_side
  end;
  repeat match type of H with
  | context [open_tm 0 (vfvar ?y) (tret (vbvar 0))] =>
      change (open_tm 0 (vfvar y) (tret (vbvar 0)))
        with (tret (vfvar y)) in H
  end;
  try rewrite ?open_tapp_tm_shift_bvar0_lc in H by assumption;
  type_open_env_syntax_norm_in H.

(** ** Free-variable support for denotation formulas *)

Section TypeDenoteSupport.

Ltac rewrite_tm_support :=
  repeat match goal with
  | |- context [lvars_at_depth ?d (tm_lvars ?e)] =>
      rewrite (tm_lvars_depth e d)
  | H : context [lvars_at_depth ?d (tm_lvars ?e)] |- _ =>
      rewrite (tm_lvars_depth e d) in H
  end.

Ltac unfold_formula_lvars_atoms :=
  unfold ty_guard_formula, context_ty_wf_formula, basic_world_formula,
    expr_basic_typing_formula, expr_total_formula, expr_result_formula,
    expr_result_formula_at, expr_result_atom_formula, FFiberAtom;
  cbn [formula_lvars_at];
	  unfold context_ty_wf_qual, basic_world_qual,
	    expr_basic_typing_qual, expr_total_qual, expr_result_qual;
	  cbn [qual_dom qual_vars qual_lvars].

Ltac normalize_denot_formula_lvars :=
  unfold_formula_lvars_atoms;
  repeat rewrite ?lvars_at_depth_union;
  rewrite_tm_support;
  rewrite ?context_ty_lvars_depth;
  rewrite ?tm_lvars_at_shift_under by lia;
  rewrite ?context_ty_lvars_at_shift_under by lia;
  rewrite ?lvars_at_depth_shift_under by lia;
  rewrite ?value_lvars_at_bound0_under;
  rewrite ?tm_lvars_at_tret_bound0_under;
  rewrite ?lvars_at_depth_dom_singleton_bound0_succ;
  rewrite ?lvars_at_depth_singleton_bound0_succ;
  rewrite ?lvars_at_depth_empty;
  cbn [context_ty_lvars_at tm_lvars_at value_lvars_at].

Ltac solve_lvars_element v :=
  repeat match goal with
  | H : context [?n + 1] |- _ =>
      replace (n + 1) with (S n) in H by lia
  end;
  repeat match goal with
  | H : context [lvars_at_depth (S ?d) (lvars_shift_from 0 ?D)] |- _ =>
      rewrite lvars_at_depth_shift_under in H by lia
  | H : context [tm_lvars_at (S ?d) (tm_shift 0 ?e)] |- _ =>
      rewrite tm_lvars_at_shift_under in H by lia
  | H : context [context_ty_lvars_at (S ?d) (cty_shift 0 ?τ)] |- _ =>
      rewrite context_ty_lvars_at_shift_under in H by lia
  | H : context [lvars_at_depth (S ?d) ({[LVBound 0]} : lvset)] |- _ =>
      rewrite lvars_at_depth_singleton_bound0_succ in H
  | H : context [lvars_at_depth (S ?d)
      (dom (<[LVBound 0 := ?T]> (∅ : gmap logic_var ty)))] |- _ =>
      rewrite lvars_at_depth_dom_singleton_bound0_succ in H
  | H : context [lvars_at_depth ?d (∅ : lvset)] |- _ =>
      rewrite lvars_at_depth_empty in H;
      set_unfold in H
  end;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | Hsub : forall w, w ∈ ?A -> _, H : v ∈ ?A |- _ =>
      specialize (Hsub v H)
  end;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  end;
  solve
    [ assumption
    | contradiction
    | match goal with
      | H : ?x ∈ (∅ : lvset) |- _ =>
          rewrite elem_of_empty in H; contradiction
      | H : ?x ∈ ∅ |- _ =>
          rewrite elem_of_empty in H; contradiction
      end
    | left; assumption
    | right; assumption
    | right; left; assumption
    | right; right; assumption ].

Lemma expr_result_shift0_lvars_subset d D e :
  formula_lvars_at (S d)
    (expr_result_formula_at (lvars_shift_from 0 D)
      (tm_shift 0 e) (LVBound 0)) ⊆
  lvars_at_depth d D ∪ tm_lvars_at d e.
Proof.
  unfold expr_result_formula_at, expr_result_qual.
  cbn [formula_lvars_at qual_vars qual_lvars].
  rewrite lvars_at_depth_shift_under by lia.
  rewrite lvars_at_depth_union.
  rewrite (tm_lvars_depth (tm_shift 0 e) (S d)).
  rewrite tm_lvars_at_shift_under by lia.
  rewrite lvars_at_depth_singleton_bound0_succ.
  set_solver.
Qed.

Lemma ty_denote_gas_lvars_subset gas d Σ τ e :
  formula_lvars_at d (ty_denote_gas gas Σ τ e) ⊆
  tm_lvars_at d e ∪ context_ty_lvars_at d τ.
Proof.
  induction gas as [|gas IH] in d, Σ, τ, e |- *.
  - cbn [ty_denote_gas formula_lvars_at].
    normalize_denot_formula_lvars.
    pose proof (lvars_at_depth_relevant_env_subset_relevant d Σ τ e)
      as Hrel.
    assert (Hrel_sub :
      lvars_at_depth d (dom (relevant_env Σ τ e)) ⊆
        tm_lvars_at d e ∪ context_ty_lvars_at d τ).
    {
      intros v Hv. specialize (Hrel v Hv). better_set_solver.
    }
    intros v Hv.
    set_unfold in Hv.
    set_unfold.
    repeat match goal with
    | Hcase : _ \/ _ |- _ => destruct Hcase as [Hcase|Hcase]
    end;
      try solve [specialize (Hrel_sub v Hcase); better_set_solver
        | better_set_solver].
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [ty_denote_gas formula_lvars_at].
    + normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        d Σ (CTOver b φ) e).
      pose proof (expr_result_shift0_lvars_subset d
        (dom (relevant_env Σ (CTOver b φ) e)) e).
      pose proof (lvars_at_depth_mono (S d)
        (qual_vars φ ∖ {[LVBound 0]}) (qual_vars φ)
        ltac:(set_solver)).
      cbn [context_ty_lvars_at].
      better_set_solver.
    + normalize_denot_formula_lvars.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        d Σ (CTUnder b φ) e).
      pose proof (expr_result_shift0_lvars_subset d
        (dom (relevant_env Σ (CTUnder b φ) e)) e).
      pose proof (lvars_at_depth_mono (S d)
        (qual_vars φ ∖ {[LVBound 0]}) (qual_vars φ)
        ltac:(set_solver)).
      cbn [context_ty_lvars_at].
      better_set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        d Σ (CTInter τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
      pose proof (lvars_at_depth_relevant_env_subset_relevant
        d Σ (CTUnion τ1 τ2) e).
      pose proof (IH d Σ τ1 e).
      pose proof (IH d Σ τ2 e).
      cbn [context_ty_lvars_at].
      set_solver.
    + unfold_formula_lvars_atoms.
      repeat rewrite ?lvars_at_depth_union.
      rewrite_tm_support.
	      pose proof (lvars_at_depth_relevant_env_subset_relevant
	        d Σ (CTSum τ1 τ2) e) as Hrel.
	      pose proof (expr_result_shift0_lvars_subset d
	        (dom (relevant_env Σ (CTSum τ1 τ2) e)) e) as Hresult.
	      pose proof (IH (S d)
	        (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
	          (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0))) as Hleft.
      rewrite tm_lvars_at_tret_bound0_under in Hleft.
      rewrite context_ty_lvars_at_shift_under in Hleft by lia.
      pose proof (IH (S d)
        (typed_lty_env_bind (relevant_env Σ (CTSum τ1 τ2) e)
          (erase_ty τ1))
        (cty_shift 0 τ2) (tret (vbvar 0))) as Hright.
      rewrite tm_lvars_at_tret_bound0_under in Hright.
	      rewrite context_ty_lvars_at_shift_under in Hright by lia.
	      cbn [context_ty_lvars_at] in Hrel |- *.
	      replace (d + 1) with (S d) by lia.
	      intros v Hv.
	      set_unfold in Hrel.
	      set_unfold in Hresult.
	      set_unfold in Hleft.
	      set_unfold in Hright.
	      set_unfold in Hv.
	      set_unfold.
	      solve_lvars_element v.
	    + unfold_formula_lvars_atoms.
	      unfold arrow_value_denote_gas_with.
	      repeat rewrite ?lvars_at_depth_union.
	      rewrite_tm_support.
	      pose proof (lvars_at_depth_relevant_env_subset_relevant
	        d Σ (CTArrow τx τr) e) as Hrel.
	      pose proof (expr_result_shift0_lvars_subset d
	        (dom (relevant_env Σ (CTArrow τx τr) e)) e) as Hresult.
	      pose proof (IH (S (S d))
	        (typed_lty_env_bind
	          (typed_lty_env_bind
	            (relevant_env Σ (CTArrow τx τr) e)
	            (erase_ty (CTArrow τx τr)))
	          (erase_ty (cty_shift 0 τx)))
	        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg.
	      rewrite tm_lvars_at_tret_bound0_under in Harg.
	      rewrite context_ty_lvars_at_shift_under in Harg by lia.
	      rewrite context_ty_lvars_at_shift_under in Harg by lia.
	      pose proof (IH (S (S d))
	        (typed_lty_env_bind
	          (typed_lty_env_bind
	            (relevant_env Σ (CTArrow τx τr) e)
	            (erase_ty (CTArrow τx τr)))
	          (erase_ty (cty_shift 0 τx)))
	        (cty_shift 1 τr)
	        (tapp_tm (tret (vbvar 1)) (vbvar 0))) as Hres.
	      rewrite tm_lvars_at_tapp_ret_bound1_bound0_under in Hres.
	      rewrite context_ty_lvars_at_shift_under in Hres by lia.
	      cbn [context_ty_lvars_at] in Hrel |- *.
	      replace (d + 1) with (S d) by lia.
	      intros v Hv.
	      set_unfold in Hrel.
	      set_unfold in Hresult.
	      set_unfold in Harg.
	      set_unfold in Hres.
	      set_unfold in Hv.
	      set_unfold.
	      solve_lvars_element v.
	    + unfold_formula_lvars_atoms.
	      unfold wand_value_denote_gas_with.
	      repeat rewrite ?lvars_at_depth_union.
	      rewrite_tm_support.
	      pose proof (lvars_at_depth_relevant_env_subset_relevant
	        d Σ (CTWand τx τr) e) as Hrel.
	      pose proof (expr_result_shift0_lvars_subset d
	        (dom (relevant_env Σ (CTWand τx τr) e)) e) as Hresult.
	      pose proof (IH (S (S d))
	        (typed_lty_env_bind
	          (typed_lty_env_bind
	            (relevant_env Σ (CTWand τx τr) e)
	            (erase_ty (CTWand τx τr)))
	          (erase_ty (cty_shift 0 τx)))
	        (cty_shift 0 (cty_shift 0 τx)) (tret (vbvar 0))) as Harg.
	      rewrite tm_lvars_at_tret_bound0_under in Harg.
	      rewrite context_ty_lvars_at_shift_under in Harg by lia.
	      rewrite context_ty_lvars_at_shift_under in Harg by lia.
	      pose proof (IH (S (S d))
	        (typed_lty_env_bind
	          (typed_lty_env_bind
	            (relevant_env Σ (CTWand τx τr) e)
	            (erase_ty (CTWand τx τr)))
	          (erase_ty (cty_shift 0 τx)))
	        (cty_shift 1 τr)
	        (tapp_tm (tret (vbvar 1)) (vbvar 0))) as Hres.
	      rewrite tm_lvars_at_tapp_ret_bound1_bound0_under in Hres.
	      rewrite context_ty_lvars_at_shift_under in Hres by lia.
	      cbn [context_ty_lvars_at] in Hrel |- *.
	      replace (d + 1) with (S d) by lia.
	      intros v Hv.
	      set_unfold in Hrel.
	      set_unfold in Hresult.
	      set_unfold in Harg.
	      set_unfold in Hres.
	      set_unfold in Hv.
	      set_unfold.
	      solve_lvars_element v.
Qed.

Lemma ty_denote_gas_fv_subset gas Σ τ e :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆
  fv_tm e ∪ fv_cty τ.
Proof.
  rewrite <- (formula_lvars_at_fv 0).
  transitivity (lvars_fv (relevant_lvars τ e)).
  - apply lvars_fv_mono.
    transitivity (tm_lvars_at 0 e ∪ context_ty_lvars_at 0 τ).
    + apply ty_denote_gas_lvars_subset.
    + change (tm_lvars_at 0 e) with (tm_lvars e).
      change (context_ty_lvars_at 0 τ) with (context_ty_lvars τ).
      relevant_lvars_norm. better_set_solver.
  - relevant_lvars_norm. better_set_solver.
Qed.

Lemma fv_tm_ty_denote_gas_subset_formula gas Σ τ e :
  fv_tm e ⊆ formula_fv (ty_denote_gas gas Σ τ e).
Proof.
  destruct gas; cbn [ty_denote_gas]; unfold ty_guard_formula.
  all: rewrite !formula_fv_and, formula_fv_expr_total_formula, tm_lvars_fv;
    set_solver.
Qed.

Lemma relevant_env_fv_ty_denote_gas_subset_formula gas Σ τ e :
  lvars_fv (dom (relevant_env Σ τ e)) ⊆
  formula_fv (ty_denote_gas gas Σ τ e).
Proof.
  destruct gas; cbn [ty_denote_gas]; unfold ty_guard_formula.
  all: rewrite !formula_fv_and, formula_fv_basic_world_formula;
    set_solver.
Qed.

Lemma ty_denote_gas_scope_of_guard
    gas Σ τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ FAnd
    (context_ty_wf_formula (relevant_env Σ τbig e) τbig)
    (FAnd (basic_world_formula (relevant_env Σ τbig e))
      (FAnd
        (expr_basic_typing_formula (relevant_env Σ τbig e) e
          (erase_ty τbig))
        (expr_total_formula e))) ->
  formula_fv (ty_denote_gas gas Σ τsmall e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hτ Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal_e]]].
  transitivity (fv_tm e ∪ fv_cty τsmall).
  - apply ty_denote_gas_fv_subset.
  - pose proof (res_models_fuel_scoped _ _ _ Htotal_e) as Hscope_e.
    unfold formula_scoped_in_world in Hscope_e.
    rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_e.
    pose proof (context_ty_wf_formula_fv_cty_subset
      (relevant_env Σ τbig e) τbig m Hwf) as Hτbig_fv.
    pose proof (proj1 (basic_world_formula_models_iff
      (relevant_env Σ τbig e) m) Hworld)
      as [_ [Hworld_dom _]].
    assert (Hτsmall_fv : fv_cty τsmall ⊆ fv_cty τbig).
    {
      rewrite <- !context_ty_lvars_fv.
      apply lvars_fv_mono. exact Hτ.
    }
    set_solver.
Qed.

End TypeDenoteSupport.
