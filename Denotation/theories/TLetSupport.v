(** * Denotation.TLetSupport

    Shared support lemmas and tactics for the [tlet] introduction proof. *)

From Denotation Require Import Notation.
From Denotation Require Import ContextTypeDenotationSaturate ContextTypeDenotationTactics.
From ContextAlgebra Require Import ResourceAlgebra.
From ContextLogic Require Import FormulaSyntaxTactics.
From CoreLang Require Import InstantiationProps.
From Stdlib Require Import List.
Import ListNotations.

(** ** Freshness and FV side-condition tactics *)

Ltac tlet_normalize_freshness :=
  repeat match goal with
  | H : LVFree ?y ∉ ?D |- _ =>
      rewrite <- (atom_notin_lvars_fv_iff_free_notin y D) in H
  | |- LVFree ?y ∉ ?D =>
      rewrite <- (atom_notin_lvars_fv_iff_free_notin y D)
  | H : context[stale ?x] |- _ =>
      lazymatch type of x with
      | atom => change (stale x) with ({[x]} : aset) in H
      end
  | |- context[stale ?x] =>
      lazymatch type of x with
      | atom => change (stale x) with ({[x]} : aset)
      end
  end;
  cbn [stale stale_lty_env lty_env_atom_dom stale_tm_inst
       stale_qualifier stale_cty_inst stale_logic_var Stale_atom] in *;
  rewrite ?lvar_store_lvars_fv_dom_insert_free in *;
  rewrite ?lvars_fv_union, ?lvars_fv_singleton_free in *.

Ltac tlet_support_solver :=
  tlet_normalize_freshness;
  match goal with
  | |- ?y ∉ fv_tm (?e ^^ ?x) =>
      intros Hbad;
      pose proof (open_fv_tm e (vfvar x) 0) as Hopen;
      apply Hopen in Hbad; simpl in Hbad;
      tlet_normalize_freshness;
      first [fast_set_solver!! | set_solver]
  | |- _ ∉ _ =>
      first [fast_set_solver!! | set_solver]
  | |- _ ⊆ _ =>
      first [fast_set_solver!! | set_solver]
  | |- _ ## _ =>
      first [fast_set_solver!! | set_solver]
  | |- _ <> _ =>
      first [fast_set_solver!! | set_solver]
  end.

Ltac harvest_tlet_models :=
  repeat match goal with
  | H : ?m ⊨ context_ty_wf_formula ?Σ ?τ |- _ =>
      lazymatch goal with
      | Hscope : lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) |- _ => fail
      | _ =>
          let Hscope := fresh "Hcontext_scope" in
          pose proof (context_ty_wf_formula_scope_dom Σ τ m H) as Hscope
      end
  | H : ?m ⊨ context_ty_wf_formula ?Σ ?τ |- _ =>
      lazymatch goal with
      | Hbasic : basic_context_ty_lvars (dom Σ) τ |- _ => fail
      | _ =>
          let Hbasic := fresh "Hcontext_lvars" in
          pose proof (context_ty_wf_formula_basic_lvars Σ τ m H) as Hbasic
      end
  | H : ?m ⊨ expr_basic_typing_formula ?Σ ?e ?T |- _ =>
      lazymatch goal with
      | Hscope : lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) |- _ => fail
      | _ =>
          let Hscope := fresh "Hexpr_basic_scope" in
          pose proof (expr_basic_typing_formula_scope_dom Σ e T m H) as Hscope
      end
  | H : ?m ⊨ expr_basic_typing_formula ?Σ ?e ?T |- _ =>
      lazymatch goal with
      | Hbasic : basic_tm_has_ltype Σ e T |- _ => fail
      | _ =>
          let Hbasic := fresh "Hexpr_basic_ltype" in
          pose proof (expr_basic_typing_formula_basic_ltype Σ e T m H) as Hbasic
      end
  | H : lty_env_to_atom_env ?Σ ⊢ₑ ?e ⋮ ?T |- _ =>
      lazymatch goal with
      | Hfv : fv_tm e ⊆ lvars_fv (dom Σ) |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_lty" in
          pose proof (basic_typing_lty_env_to_atom_env_fv_subset Σ e T H) as Hfv
      end
  | H : ?Γ ⊢ₑ ?e ⋮ ?T |- _ =>
      lazymatch goal with
      | Hfv : fv_tm e ⊆ dom Γ |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_basic" in
          pose proof (basic_typing_contains_fv_tm Γ e T H) as Hfv
      end
  | Hfresh : LVFree ?x ∉ context_ty_lvars ?τ,
    Hbasic : basic_context_ty_lvars (dom (<[LVFree ?x := ?T]> ?Σ)) ?τ |- _ =>
      lazymatch goal with
      | Hfv : fv_cty τ ⊆ lvars_fv (dom Σ) |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_cty_drop" in
          pose proof (basic_context_ty_lvars_insert_free_fv_drop
            Σ τ x T Hfresh Hbasic) as Hfv
      end
  end;
  repeat match goal with
  | H : basic_context_ty_lvars _ _ |- _ =>
      let Hsub := fresh "Hcontext_lvars_sub" in
      let Hshape := fresh "Hcontext_shape" in
      destruct H as [Hsub Hshape]
  end.

(** ** Formula scoping and model syntax tactics *)

Ltac solve_formula_scoped :=
  solve
  [ eapply res_models_scoped; eassumption
  | unfold formula_scoped_in_world;
    harvest_tlet_models;
    normalize_denotation_formula_fv;
    rewrite ?context_ty_lvars_fv in *;
    rewrite ?lvars_fv_lvars_at_depth in *;
    cbn [fv_tm fv_value] in *;
    tlet_normalize_freshness;
    fast_set_solver!!
  ].

Ltac normalize_tlet_forall_fv :=
  normalize_denotation_formula_fv;
  cbn [formula_lvars basic_world_formula basic_world_lqual
    expr_result_formula expr_result_lqual type_qualifier_formula
    type_qualifier_lqual context_ty_wf_formula context_ty_wf_lqual
    expr_basic_typing_formula expr_basic_typing_lqual
    expr_total_formula expr_total_lqual
    lqual_fvars lqual_lvars lqual_dom];
  repeat match goal with
  | |- context[lvars_fv (formula_lvars (denot_ty_lvar_gas ?gas ?Σ ?τ ?e))] =>
      change (lvars_fv (formula_lvars (denot_ty_lvar_gas gas Σ τ e)))
        with (formula_fv (denot_ty_lvar_gas gas Σ τ e))
  | H : context[lvars_fv (formula_lvars (denot_ty_lvar_gas ?gas ?Σ ?τ ?e))] |- _ =>
      change (lvars_fv (formula_lvars (denot_ty_lvar_gas gas Σ τ e)))
        with (formula_fv (denot_ty_lvar_gas gas Σ τ e)) in H
  end;
  rewrite ?typed_lty_env_bind_lvars_fv_dom;
  rewrite ?lvar_store_lvars_fv_dom_insert_free;
  rewrite ?context_ty_lvars_over_fv, ?context_ty_lvars_under_fv;
  rewrite ?lvars_fv_lvars_at_depth;
  rewrite ?lvars_fv_qual_vars_difference_free, ?lvars_fv_qual_vars;
  rewrite ?lvars_fv_empty;
  normalize_denotation_formula_fv;
  cbn [fv_tm fv_value].

Ltac tlet_lc_solver :=
  solve
  [ constructor
  | eapply basic_typing_regular_tm; eassumption
  | eapply tlet_lc_open_body_from_basic; eassumption
  | eapply tlet_lc_tapp_open_body_from_basic; eassumption
  | apply lc_tapp_tm; [tlet_lc_solver | constructor]
  ].

Ltac solve_tlet_sidecond :=
  first
  [ assumption
  | match goal with
    | H : expr_result_extension_witness _ ?x ?F |- ext_out ?F = {[?x]} =>
        exact (proj2 (expr_result_extension_witness_shape _ _ _ H))
    end
  | tlet_lc_solver
  | tlet_support_solver
  | eauto using
	      lty_env_closed_insert_free,
	      fiber_extension_singleton_output_fresh_in_eq,
	      fiber_extension_singleton_output_fresh_subset,
	      lvars_fv_subset_notin_free
  ].

Ltac solve_tlet_impl_scope :=
  first
  [ eassumption
  | match goal with
    | Hscope : formula_scoped_in_world ?m (FImpl ?p0 (FImpl ?p ?q))
      |- formula_scoped_in_world ?m (FImpl ?p ?q) =>
        eapply formula_scoped_impl_r; exact Hscope
    | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
      |- formula_scoped_in_world ?m ?p =>
        eapply formula_scoped_impl_l; exact Hscope
    | Hscope : formula_scoped_in_world ?m (FImpl ?p ?q)
      |- formula_scoped_in_world ?m ?q =>
        eapply formula_scoped_impl_r; exact Hscope
    | Hscope : formula_scoped_in_world ?m (FAnd ?p ?q)
      |- formula_scoped_in_world ?m ?p =>
        eapply formula_scoped_and_l; exact Hscope
    | Hscope : formula_scoped_in_world ?m (FAnd ?p ?q)
      |- formula_scoped_in_world ?m ?q =>
        eapply formula_scoped_and_r; exact Hscope
    | Hscope : formula_scoped_in_world ?m (FForall ?p)
      |- formula_scoped_in_world ?m ?p =>
        eapply formula_scoped_forall_body; exact Hscope
    | Hscope : formula_scoped_in_world ?m (FFibVars ?D ?p)
      |- formula_scoped_in_world ?m ?p =>
        eapply formula_scoped_fibvars_r; exact Hscope
    end
  | solve_formula_scoped
  ].

Ltac use_models_impl H Hout :=
  lazymatch type of H with
  | res_models ?m (FImpl ?p ?q) =>
      let Harg := fresh "Harg" in
      assert (Harg : m ⊨ p);
      [ | pose proof (res_models_impl_elim m p q H Harg) as Hout;
          clear Harg ]
  | res_models ?m (formula_open ?k ?x (FImpl ?p ?q)) =>
      rewrite formula_open_impl in H;
      use_models_impl H Hout
  end.

Ltac normalize_models_ands_in H :=
  repeat rewrite res_models_and_iff in H.

Ltac normalize_models_ands_goal :=
  repeat rewrite res_models_and_iff.

Ltac destruct_models_formula_hyps :=
  repeat match goal with
  | H : _ ⊨ FAnd _ _ |- _ =>
      rewrite res_models_and_iff in H; destruct H
  | H : res_models _ _ /\ _ |- _ =>
      destruct H
  | H : _ /\ res_models _ _ |- _ =>
      destruct H
  end.

Ltac split_models_formula_goal :=
  repeat match goal with
  | |- _ ⊨ FAnd _ _ =>
      rewrite res_models_and_iff; split
  | |- res_models _ _ /\ _ =>
      split
  | |- _ /\ res_models _ _ =>
      split
  end.

Lemma tlet_arrow_arg_relevant_env_agree
    (Σ : lty_env) T1 x y τx τr e1 e2 :
  lty_env_closed Σ ->
  x <> y ->
  LVFree x ∉ context_ty_lvars τx ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTArrow τx τr) (e2 ^^ x)))
    (denot_relevant_lvars
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2)))
    (denot_relevant_lvars
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
Proof.
  intros HΣ Hxy Hxτx.
  set (X := denot_relevant_lvars
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  assert (HxX : LVFree x ∉ X).
  {
    subst X. unfold denot_relevant_lvars.
    intros HxX.
    apply elem_of_union in HxX as [Hxτ|Hxret].
    - apply lvars_fv_elem in Hxτ.
      pose proof (cty_open_fv_subset 0 y (cty_shift 0 τx) x Hxτ)
        as Hxfv.
      rewrite cty_shift_fv in Hxfv.
      apply elem_of_union in Hxfv as [Hxτfv|Hxyfv].
      + apply Hxτx. apply lvars_fv_elem.
        rewrite context_ty_lvars_fv. exact Hxτfv.
      + set_solver.
    - cbn [tm_lvars tm_lvars_at value_lvars_at] in Hxret.
      set_solver.
  }
  apply storeA_map_eq. intros v.
  unfold lty_env_restrict_lvars.
  change ((storeA_restrict
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTArrow τx τr) (e2 ^^ x))) X : gmap logic_var ty) !! v =
    (storeA_restrict
      (<[LVFree y := erase_ty τx]>
        (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2))) X
      : gmap logic_var ty) !! v).
  rewrite (@storeA_restrict_lookup ty _ _ _
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTArrow τx τr) (e2 ^^ x))) X v).
  rewrite (@storeA_restrict_lookup ty _ _ _
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2))) X v).
  destruct (decide (v ∈ X)) as [HvX|HvX]; [|reflexivity].
  destruct v as [k|z].
  - try reflexivity.
    change (((<[LVFree y := erase_ty τx]>
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTArrow τx τr) (e2 ^^ x) : gmap logic_var ty))
      : gmap logic_var ty) !! LVBound k =
      ((<[LVFree y := erase_ty τx]>
        (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2)
          : gmap logic_var ty)) : gmap logic_var ty) !! LVBound k).
    rewrite !lookup_insert_ne by discriminate.
    transitivity (@None ty).
    + apply lty_env_closed_lookup_bound_none.
      apply denot_relevant_env_closed. apply lty_env_closed_insert_free. exact HΣ.
    + symmetry. apply lty_env_closed_lookup_bound_none.
      apply denot_relevant_env_closed. exact HΣ.
  - change (((<[LVFree y := erase_ty τx]>
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTArrow τx τr) (e2 ^^ x) : gmap logic_var ty))
      : gmap logic_var ty) !! LVFree z =
      ((<[LVFree y := erase_ty τx]>
        (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2)
          : gmap logic_var ty)) : gmap logic_var ty) !! LVFree z).
    destruct (decide (z = y)) as [->|Hzy].
    + rewrite !lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence.
      destruct (decide (z = x)) as [->|Hzx].
      * exfalso. exact (HxX HvX).
      * assert (Hzτx : LVFree z ∈ context_ty_lvars τx).
        {
          unfold X in HvX.
          unfold denot_relevant_lvars in HvX.
          apply elem_of_union in HvX as [Hzτ|Hzret].
          - apply lvars_fv_elem in Hzτ.
            pose proof (cty_open_fv_subset 0 y (cty_shift 0 τx) z Hzτ)
              as Hzfv.
            rewrite cty_shift_fv in Hzfv.
            apply elem_of_union in Hzfv as [Hzτfv|Hzyfv].
            + apply lvars_fv_elem. rewrite context_ty_lvars_fv. exact Hzτfv.
            + set_solver.
          - cbn [tm_lvars tm_lvars_at value_lvars_at] in Hzret.
            set_solver.
        }
        unfold denot_relevant_env, lty_env_restrict_lvars.
        change ((storeA_restrict (<[LVFree x := T1]> Σ)
          (denot_relevant_lvars (CTArrow τx τr) (e2 ^^ x))
          : gmap logic_var ty) !! LVFree z =
          (storeA_restrict Σ
            (denot_relevant_lvars (CTArrow τx τr) (tlete e1 e2))
            : gmap logic_var ty) !! LVFree z).
        rewrite (@storeA_restrict_lookup ty _ _ _
          (<[LVFree x := T1]> Σ)
          (denot_relevant_lvars (CTArrow τx τr) (e2 ^^ x))
          (LVFree z)).
        try rewrite (@storeA_restrict_lookup ty _ _ _
          Σ
          (denot_relevant_lvars (CTArrow τx τr) (tlete e1 e2))
          (LVFree z)).
        destruct (decide (LVFree z ∈ denot_relevant_lvars
          (CTArrow τx τr) (e2 ^^ x))) as [Hzsrc|Hbad].
        2:{ exfalso. apply Hbad. unfold denot_relevant_lvars.
            cbn [context_ty_lvars context_ty_lvars_at]. set_solver. }
        destruct (decide (LVFree z ∈ denot_relevant_lvars
          (CTArrow τx τr) (tlete e1 e2))) as [Hztgt|Hbad].
        2:{ exfalso. apply Hbad. unfold denot_relevant_lvars.
            cbn [context_ty_lvars context_ty_lvars_at]. set_solver. }
	        try rewrite decide_True by assumption.
	        rewrite lookup_insert_ne by congruence.
	        destruct (Σ !! LVFree z) eqn:HΣz.
	        -- symmetry. apply storeA_restrict_lookup_some_2; [exact HΣz|exact Hztgt].
	        -- symmetry. apply storeA_restrict_lookup_none_l. exact HΣz.
Qed.

Lemma tlet_wand_arg_relevant_env_agree
    (Σ : lty_env) T1 x y τx τr e1 e2 :
  lty_env_closed Σ ->
  x <> y ->
  LVFree x ∉ context_ty_lvars τx ->
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTWand τx τr) (e2 ^^ x)))
    (denot_relevant_lvars
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))) =
  lty_env_restrict_lvars
    (<[LVFree y := erase_ty τx]>
      (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2)))
    (denot_relevant_lvars
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
Proof.
  intros HΣ Hxy Hxτx.
  change (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x))
    with (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTArrow τx τr) (e2 ^^ x)).
  change (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
    with (denot_relevant_env Σ (CTArrow τx τr) (tlete e1 e2)).
  apply tlet_arrow_arg_relevant_env_agree; assumption.
Qed.

Lemma tlet_wand_arg_source_from_target
    gas (Σ : lty_env) T1 x y τx τr e1 e2 (n : WfWorldT) :
  lty_env_closed Σ ->
  x <> y ->
  LVFree x ∉ context_ty_lvars τx ->
  y ∉ fv_cty τx ->
  LVFree y ∉ dom
    (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2) : lty_env) ->
  LVFree y ∉ dom
    (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x) : lty_env) ->
  n ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))) ->
  n ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env (<[LVFree x := T1]> Σ)
          (CTWand τx τr) (e2 ^^ x))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0))).
Proof.
  intros HΣ Hxy Hxτx Hyτx Hy_target_rel Hy_source_rel Harg.
  assert (Hclosed_target_rel : lty_env_closed
    (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))).
  { apply denot_relevant_env_closed. exact HΣ. }
  assert (Hclosed_source_rel : lty_env_closed
    (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x))).
  { apply denot_relevant_env_closed. apply lty_env_closed_insert_free. exact HΣ. }
  pose proof (res_models_open_denot_ty_lvar_gas_to_open
    y gas
    (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
    (erase_ty τx) (cty_shift 0 τx) (tret (vbvar 0)) n
    Hy_target_rel Hclosed_target_rel
    ltac:(cbn [fv_tm fv_value]; set_solver)
    ltac:(rewrite cty_shift_fv; exact Hyτx)
    Harg) as Harg_open.
  eapply res_models_open_denot_ty_lvar_gas_from_open;
    [ exact Hy_source_rel
    | exact Hclosed_source_rel
    | cbn [fv_tm fv_value]; set_solver
    | rewrite cty_shift_fv; exact Hyτx
    | ].
  eapply res_models_denot_ty_lvar_gas_env_agree_on
    with (X := denot_relevant_lvars
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  - reflexivity.
  - symmetry.
    apply tlet_wand_arg_relevant_env_agree; assumption.
  - exact Harg_open.
Qed.

Lemma tlet_wand_source_arg_fresh_x
    gas (Σ : lty_env) T1 x y τx τr (e1 e2 : tm) :
  lty_env_closed Σ ->
  x <> y ->
  LVFree x ∉ context_ty_lvars τx ->
  x ∉ formula_fv
    (formula_open 0 y
      (denot_ty_lvar_gas gas
        (typed_lty_env_bind
          (denot_relevant_env (<[LVFree x := T1]> Σ)
            (CTWand τx τr) (e2 ^^ x))
          (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))).
Proof.
  intros _ Hxy Hxτx Hbad.
  pose proof (formula_open_fv_subset 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env (<[LVFree x := T1]> Σ)
          (CTWand τx τr) (e2 ^^ x))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0)))) as Hopen.
  pose proof (Hopen x Hbad) as Hpre_or_y.
  apply elem_of_union in Hpre_or_y as [Hpre | Hy].
  - pose proof (formula_fv_denot_ty_lvar_gas_subset_relevant gas
      (typed_lty_env_bind
        (denot_relevant_env (<[LVFree x := T1]> Σ)
          (CTWand τx τr) (e2 ^^ x))
        (erase_ty τx))
      (cty_shift 0 τx) (tret (vbvar 0)) x Hpre) as Hrel.
	    cbn [fv_tm fv_value] in Hrel.
	    rewrite cty_shift_fv in Hrel.
	    unfold fv_cty in Hrel.
	    apply elem_of_union in Hrel as [Hempty | Hx_fv].
	    + set_solver.
	    + rewrite lvars_fv_elem in Hx_fv.
	      contradiction.
  - apply elem_of_singleton in Hy. congruence.
Qed.

Lemma tlet_wand_source_body_open_for_ih
    gas (Σ : lty_env) T1 x y τx τr e2 (w : WfWorldT) :
  lty_env_closed Σ ->
  x <> y ->
  LVFree x ∉ context_ty_lvars (CTWand τx τr) ->
  LVFree y ∉ dom
    (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x) : lty_env) ->
  LVFree y ∉ dom (<[LVFree x := T1]> Σ : lty_env) ->
  lc_tm (e2 ^^ x) ->
  y ∉ fv_tm (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)) ->
  y ∉ fv_cty τr ->
  basic_context_ty_lvars
    (dom (<[LVFree x := T1]> Σ : lty_env) : gset logic_var)
    (CTWand τx τr) ->
  w ⊨ formula_open 0 y
    (denot_ty_lvar_gas gas
      (typed_lty_env_bind
        (denot_relevant_env (<[LVFree x := T1]> Σ)
          (CTWand τx τr) (e2 ^^ x))
        (erase_ty τx))
      τr
      (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0))) ->
  w ⊨ denot_ty_lvar_gas gas
    (<[LVFree x := T1]> (<[LVFree y := erase_ty τx]> Σ))
    (cty_open 0 y τr)
    ((tapp_tm e2 (vfvar y)) ^^ x).
Proof.
  intros HΣ Hxy Hxfresh Hy_source_rel Hy_insert Hlc_e2x Hy_body_fv Hyτr
    Hbasic_src_rel Hsource_body.
  assert (Hclosed_source_rel : lty_env_closed
    (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x))).
  { apply denot_relevant_env_closed. apply lty_env_closed_insert_free. exact HΣ. }
  pose proof (res_models_open_denot_ty_lvar_gas_to_open
    y gas
    (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x))
    (erase_ty τx) τr
    (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)) w
    Hy_source_rel Hclosed_source_rel Hy_body_fv Hyτr
    Hsource_body) as Hopened.
  cbn [open_tm open_value value_shift] in Hopened.
  assert (Hbody_full :
    w ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := erase_ty τx]>
        (<[LVFree x := T1]> Σ))
      (cty_open 0 y τr)
      (tapp_tm (e2 ^^ x) (vfvar y))).
  {
    eapply res_models_denot_ty_lvar_gas_env_agree_on
      with (X := denot_relevant_lvars (cty_open 0 y τr)
        (tapp_tm (e2 ^^ x) (vfvar y))).
    - reflexivity.
    - apply wand_body_relevant_env_agree_from_basic_context_ty.
      + apply lty_env_closed_insert_free. exact HΣ.
      + exact Hy_insert.
      + exact Hbasic_src_rel.
      + apply tm_lvars_tapp_tm_fvar_without_arg.
    - change (w ⊨ denot_ty_lvar_gas gas
        (<[LVFree y := erase_ty τx]>
          (denot_relevant_env (<[LVFree x := T1]> Σ)
            (CTWand τx τr) (e2 ^^ x)))
        (cty_open 0 y τr)
        (tlete (open_tm 0 (vfvar y) (tm_shift 0 (e2 ^^ x)))
          (tapp (vbvar 0) (vfvar y)))) in Hopened.
      rewrite open_tm_shift0_lc in Hopened by exact Hlc_e2x.
      change (tlete (e2 ^^ x) (tapp (vbvar 0) (vfvar y)))
        with (tapp_tm (e2 ^^ x) (vfvar y)) in Hopened.
      exact Hopened.
  }
  eapply denot_ty_lvar_gas_insert_commute_tapp_open;
    [exact Hxy | exact Hbody_full].
Qed.

Lemma tlet_intro_denotation_gas_zero_support
    (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
    (τ : context_ty) :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ (tlete e1 e2) ⋮ erase_ty τ ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula (denot_relevant_env Σ τ (tlete e1 e2)) ->
  LVFree x ∉ dom Σ ->
  LVFree x ∉ context_ty_lvars τ ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_lvar_gas 0
    (<[LVFree x := T1]> Σ) τ (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas 0 Σ τ (tlete e1 e2).
Proof.
  intros HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx.
  cbn [denot_ty_lvar_gas] in Hmx |- *.
  repeat rewrite res_models_and_iff in Hmx |- *.
  destruct Hmx as [[Hmx_wf [Hmx_world [Hmx_basic Hmx_total]]] _].
  split.
  - split.
    + apply context_ty_wf_formula_models_iff.
      apply basic_world_formula_models_iff in Hbase_world
        as [Hlc_base [Hscope_base _]].
      apply context_ty_wf_formula_models_iff in Hmx_wf
        as [_ [_ [Hvars_mx Hshape]]].
      split; [exact Hlc_base|].
      split; [exact Hscope_base|].
      split; [|exact Hshape].
      intros v Hv.
      assert (Hv_mx : v ∈ dom (denot_relevant_env
        (<[LVFree x := T1]> Σ) τ (e2 ^^ x))).
      { exact (Hvars_mx v Hv). }
      unfold denot_relevant_env, lty_env_restrict_lvars in Hv_mx |- *.
      change (v ∈ dom (storeA_restrict
        ((<[LVFree x := T1]> (Σ : gmap logic_var ty)) : lty_env)
        (denot_relevant_lvars τ (e2 ^^ x)))) in Hv_mx.
      rewrite storeA_restrict_dom in Hv_mx.
      apply elem_of_intersection in Hv_mx as [Hv_insert _].
      change (v ∈ dom (storeA_restrict (Σ : gmap logic_var ty)
        (denot_relevant_lvars τ (tlete e1 e2)))).
      rewrite storeA_restrict_dom.
      apply elem_of_intersection. split.
      { change (v ∈ dom ((<[LVFree x := T1]> (Σ : gmap logic_var ty))
          : gmap logic_var ty)) in Hv_insert.
        rewrite dom_insert_L in Hv_insert.
        apply elem_of_union in Hv_insert as [Hvx|HvΣ].
        - rewrite elem_of_singleton in Hvx. subst v. contradiction.
        - exact HvΣ. }
      { unfold denot_relevant_lvars. set_solver. }
    + split.
      * exact Hbase_world.
      * split.
        -- eapply expr_basic_typing_formula_tlete_intro; [exact Hbase_world|].
           apply basic_typing_lty_env_to_atom_env_denot_relevant_env.
           exact Hlet.
        -- eapply expr_total_formula_tlete_intro_from_result_extension
             with (Σ := denot_relevant_env Σ τ (tlete e1 e2)); eauto.
           ++ unfold denot_relevant_env, lty_env_restrict_lvars.
              change (LVFree x ∉ dom
                (storeA_restrict (Σ : gmap logic_var ty)
                   (denot_relevant_lvars τ (tlete e1 e2)))).
              better_store_solver.
           ++ apply basic_typing_lty_env_to_atom_env_denot_relevant_env.
              exact Hlet.
  - cbn [res_models res_models_fuel formula_measure].
    split; [apply formula_scoped_true_iff; exact I | exact I].
Qed.

(** ** Denotation guard projection tactics *)

Ltac solve_denot_ty_lvar_gas_zero_from_guard Hguard :=
  apply denot_ty_lvar_gas_zero_of_guard;
  repeat rewrite res_models_and_iff;
  exact Hguard.

Ltac solve_denot_ty_lvar_body_scope_from_guard_at gas Σ τ e Hguard :=
  let Hscope := fresh "Hdenot_scope" in
  pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
    gas Σ τ e _ Hguard) as Hscope;
  cbn [denot_ty_lvar_gas] in Hscope;
  eapply formula_scoped_and_r;
  exact Hscope.

Ltac solve_denot_guard_goal Hguard :=
  repeat rewrite res_models_and_iff in Hguard;
  exact Hguard.

Ltac pose_formula_scoped_forall_open_from_dom m n y Hscope Hle Hdom :=
  let Hopened := fresh "Hopened_scope_my" in
  pose proof (formula_scoped_forall_open_res_le
    m n y _ Hscope Hle
    ltac:(rewrite Hdom; set_solver)) as Hopened.

Definition denot_wand_body_formula
    (gas : nat) (Σg : lty_env) (τx τr : context_ty) (e : tm) : FormulaT :=
  let Σx := typed_lty_env_bind Σg (erase_ty τx) in
  FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
    (FWand
      (denot_ty_lvar_gas gas Σx
        (cty_shift 0 τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas Σx τr
        (tapp_tm (tm_shift 0 e) (vbvar 0)))).


Lemma denot_ty_lvar_guard_tapp_tlete_assoc
    (Σ : lty_env) τ e1 e2 y (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y)))) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y)))))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y))))
          (tlete e1 (tapp_tm e2 (vfvar y))) (erase_ty τ))
        (expr_total_formula (tlete e1 (tapp_tm e2 (vfvar y)))))) ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y))) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y))))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y)))
          (tapp_tm (tlete e1 e2) (vfvar y)) (erase_ty τ))
        (expr_total_formula (tapp_tm (tlete e1 e2) (vfvar y))))).
Proof.
  intros Hlc Hguard.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Henv :
    denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y)) =
    denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y)))).
  {
    unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
    rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. reflexivity.
  }
  rewrite Henv.
  split; [exact Hwf|].
  split; [exact Hworld|].
  split.
  - eapply expr_basic_typing_formula_tapp_tm_tlete_assoc; eauto.
  - assert (Hclosed :
      wfworld_closed_on (fv_tm (tapp_tm (tlete e1 e2) (vfvar y))) m).
    {
      eapply denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq.
      - rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. reflexivity.
      - exact Hworld.
      - exact Hbasic.
    }
    eapply expr_total_formula_tapp_tm_tlete_assoc; eauto.
Qed.

Lemma denot_ty_lvar_guard_tapp_tlete_assoc_rev
    (Σ : lty_env) τ e1 e2 y (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y))) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y))))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y)))
          (tapp_tm (tlete e1 e2) (vfvar y)) (erase_ty τ))
        (expr_total_formula (tapp_tm (tlete e1 e2) (vfvar y))))) ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y)))) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y)))))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y))))
          (tlete e1 (tapp_tm e2 (vfvar y))) (erase_ty τ))
        (expr_total_formula (tlete e1 (tapp_tm e2 (vfvar y)))))).
Proof.
  intros Hlc Hguard.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Henv :
    denot_relevant_env Σ τ (tapp_tm (tlete e1 e2) (vfvar y)) =
    denot_relevant_env Σ τ (tlete e1 (tapp_tm e2 (vfvar y)))).
  {
    unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
    rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. reflexivity.
  }
  rewrite <- Henv.
  split; [exact Hwf|].
  split; [exact Hworld|].
  split.
  - eapply expr_basic_typing_formula_tapp_tm_tlete_assoc_rev; eauto.
  - assert (Hclosed :
      wfworld_closed_on (fv_tm (tapp_tm (tlete e1 e2) (vfvar y))) m).
    {
      eapply denot_relevant_basic_world_typing_wfworld_closed_on_term;
        eauto.
    }
    eapply expr_total_formula_tapp_tm_tlete_assoc_rev; eauto.
Qed.

(** ** [tapp]/[tlete] guard transport tactics *)

Ltac solve_tapp_tlete_lvars_assoc :=
  first
  [ rewrite tm_lvars_tapp_tm_tlete_assoc_fvar; reflexivity
  | rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar; reflexivity
  | rewrite tm_lvars_tapp_tlete_assoc_spine; reflexivity
  | rewrite <- tm_lvars_tapp_tlete_assoc_spine; reflexivity
  ].

Ltac solve_tapp_tlete_closed :=
  match goal with
  | Hworld : ?m ⊨ basic_world_formula (denot_relevant_env ?Σ ?τ ?esrc),
    Hbasic : ?m ⊨ expr_basic_typing_formula
      (denot_relevant_env ?Σ ?τ ?esrc) ?esrc (erase_ty ?τ)
    |- wfworld_closed_on (fv_tm ?etgt) ?m =>
      eapply denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq;
      [ solve_tapp_tlete_lvars_assoc | exact Hworld | exact Hbasic ]
  end.

Ltac solve_tapp_tlete_guard_atom :=
  first
  [ eassumption
  | match goal with
    | H : ?m ⊨ context_ty_wf_formula (denot_relevant_env ?Σ ?τ ?esrc) ?τ
      |- ?m ⊨ context_ty_wf_formula (denot_relevant_env ?Σ ?τ ?etgt) ?τ =>
        rewrite (denot_relevant_env_eq_of_tm_lvars_eq Σ τ etgt esrc
          ltac:(solve_tapp_tlete_lvars_assoc));
        exact H
    | H : ?m ⊨ basic_world_formula (denot_relevant_env ?Σ ?τ ?esrc)
      |- ?m ⊨ basic_world_formula (denot_relevant_env ?Σ ?τ ?etgt) =>
        rewrite (denot_relevant_env_eq_of_tm_lvars_eq Σ τ etgt esrc
          ltac:(solve_tapp_tlete_lvars_assoc));
        exact H
    | H : ?m ⊨ expr_basic_typing_formula
        (denot_relevant_env ?Σ ?τ ?esrc) ?esrc ?T
      |- ?m ⊨ expr_basic_typing_formula
        (denot_relevant_env ?Σ ?τ ?etgt) ?etgt ?T =>
        rewrite (denot_relevant_env_eq_of_tm_lvars_eq Σ τ etgt esrc
          ltac:(solve_tapp_tlete_lvars_assoc));
        lazymatch goal with
        | |- ?m ⊨ expr_basic_typing_formula _
            (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) ?T =>
            eapply expr_basic_typing_formula_tapp_tm_tlete_assoc;
            [ eassumption | exact H ]
        | |- ?m ⊨ expr_basic_typing_formula _
            (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) ?T =>
            eapply expr_basic_typing_formula_tapp_tm_tlete_assoc_rev;
            [ eassumption | exact H ]
        | |- ?m ⊨ expr_basic_typing_formula _
            (tapp_tm_fvar_spine
              (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs)) ?T =>
            eapply expr_basic_typing_formula_tapp_tlete_assoc_spine;
            [ eassumption | exact H ]
        end
    end
  | match goal with
    | H : ?m ⊨ expr_total_formula
        (tlete ?e1 (tapp_tm ?e2 (vfvar ?y)))
      |- ?m ⊨ expr_total_formula (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) =>
        eapply expr_total_formula_tapp_tm_tlete_assoc;
        [ solve_tapp_tlete_closed | eassumption | exact H ]
    | H : ?m ⊨ expr_total_formula
        (tapp_tm (tlete ?e1 ?e2) (vfvar ?y))
      |- ?m ⊨ expr_total_formula (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) =>
        eapply expr_total_formula_tapp_tm_tlete_assoc_rev;
        [ solve_tapp_tlete_closed | eassumption | exact H ]
    | H : ?m ⊨ expr_total_formula
        (tapp_tm_fvar_spine
          (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (?z :: ?zs))
      |- ?m ⊨ expr_total_formula
        (tapp_tm_fvar_spine
          (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs)) =>
        eapply expr_total_formula_tapp_tlete_assoc_spine;
        [ solve_tapp_tlete_closed | eassumption | exact H ]
    end
  ].

Ltac solve_tapp_tlete_guard_assoc :=
  destruct_models_formula_hyps;
  split_models_formula_goal;
  [ solve_tapp_tlete_guard_atom
  | solve_tapp_tlete_guard_atom
  | solve_tapp_tlete_guard_atom
  | solve_tapp_tlete_guard_atom
  ].

(** ** Denotation opening transport tactics *)

Ltac transport_open_denot_in H :=
  lazymatch type of H with
  | res_models ?m
      (formula_open 0 ?y
        (denot_ty_lvar_gas ?gas (typed_lty_env_bind ?Σ ?T) ?τ ?e)) =>
      let Hopened := fresh H "_opened" in
      pose proof (res_models_open_denot_ty_lvar_gas_to_open
        y gas Σ T τ e m
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        H) as Hopened;
      clear H; rename Hopened into H;
      cbn [open_tm open_value value_shift] in H
  | res_models ?m
      (formula_open ?k ?y
        (denot_ty_lvar_gas ?gas ?Σ ?τ ?e)) =>
      let Hopened := fresh H "_opened" in
      pose proof (res_models_open_denot_ty_lvar_gas_to_open_at
        k y gas Σ τ e m
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        H) as Hopened;
      clear H; rename Hopened into H;
      cbn [open_tm open_value value_shift] in H
  | _ => idtac
  end.

Lemma denot_ty_lvar_guard_tapp_tlete_assoc_spine
    (Σ : lty_env) τ e1 e2 y z zs (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env Σ τ
        (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env Σ τ
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env Σ τ
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))
          (erase_ty τ))
        (expr_total_formula
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))))) ->
  m ⊨ FAnd
    (context_ty_wf_formula
      (denot_relevant_env Σ τ
        (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs))) τ)
    (FAnd
      (basic_world_formula
        (denot_relevant_env Σ τ
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs))))
      (FAnd
        (expr_basic_typing_formula
          (denot_relevant_env Σ τ
            (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs))
          (erase_ty τ))
        (expr_total_formula
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs))))).
Proof.
  intros Hlc Hguard.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf [Hworld [Hbasic Htotal]]].
  assert (Henv :
    denot_relevant_env Σ τ
      (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) =
    denot_relevant_env Σ τ
      (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))).
  {
    unfold denot_relevant_env, lty_env_restrict_lvars, denot_relevant_lvars.
    rewrite tm_lvars_tapp_tlete_assoc_spine. reflexivity.
  }
  rewrite Henv.
  split; [exact Hwf|].
  split; [exact Hworld|].
  split.
  - eapply expr_basic_typing_formula_tapp_tlete_assoc_spine; eauto.
  - assert (Hclosed :
      wfworld_closed_on
        (fv_tm (tapp_tm_fvar_spine
          (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs))) m).
    {
      eapply denot_relevant_basic_world_typing_wfworld_closed_on_term_of_lvars_eq.
      - rewrite tm_lvars_tapp_tlete_assoc_spine. reflexivity.
      - exact Hworld.
      - exact Hbasic.
    }
    eapply expr_total_formula_tapp_tlete_assoc_spine; eauto.
Qed.

Lemma denot_ty_lvar_gas_tapp_tlete_assoc_spine
    gas (Σ : lty_env) τ e1 e2 y z zs (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm (tlete e1 e2) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)).
Proof.
  revert Σ τ e1 e2 y z zs m.
  induction gas as [|gas IH]; intros Σ τ e1 e2 y z zs m HΣ Hlc Hm.
  - cbn [denot_ty_lvar_gas] in Hm |- *.
    repeat rewrite res_models_and_iff in Hm |- *.
    destruct Hm as [Hguard Htrue].
    split.
    + solve_tapp_tlete_guard_assoc.
    + exact Htrue.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas] in Hm |- *;
      repeat rewrite res_models_and_iff in Hm |- *;
      destruct Hm as [Hguard Hbody];
      split.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_map_same_fv m φsrc)
      end.
      * apply set_eq. intros a.
        normalize_denotation_formula_fv.
        rewrite !tm_shift_fv;
        try rewrite <- fv_tm_tapp_tlete_assoc_spine;
        try rewrite <- tm_lvars_tapp_tlete_assoc_spine;
        tauto.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTOver b φ)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm_fvar_spine
            (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) ∪
          fv_tm (tapp_tm_fvar_spine
            (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)) ∪
          qual_dom φ ∪ lvars_fv (dom Σ)).
        intros a Ha F my HFin HFout Hext Hopen.
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite formula_open_expr_result_formula_shift0 in Hopen.
        2:{ apply lc_tapp_tm_fvar_spine.
            apply lc_tlete_tapp_tm_assoc_source. exact Hlc. }
        2:{ set_solver. }
        rewrite formula_open_expr_result_formula_shift0.
        2:{ apply lc_tapp_tm_fvar_spine.
            apply lc_tapp_tm; [exact Hlc | constructor]. }
        2:{ set_solver. }
        pose proof (res_models_fuel_scoped _ _ _ Hopen) as Hscope_src.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_outer : formula_scoped_in_world my G)
        end.
        {
          unfold formula_scoped_in_world in *.
          normalize_denotation_formula_fv_in Hscope_src.
          normalize_denotation_formula_fv.
          try rewrite fv_tm_tapp_tlete_assoc_spine.
          exact Hscope_src.
        }
        eapply res_models_impl2_intro; [exact Hscope_tgt_outer|].
        intros Hbasic Hresult.
        eapply res_models_impl2_elim; [exact Hopen | exact Hbasic |].
        eapply expr_result_formula_tapp_tlete_assoc_spine_rev.
        -- rewrite fv_tm_tapp_tlete_assoc_spine.
           eapply denot_ty_lvar_guard_wfworld_closed_on_term_le.
           ++ eapply res_extend_by_le; exact Hext.
           ++ repeat rewrite res_models_and_iff. exact Hguard.
        -- exact Hlc.
        -- exact Hresult.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_map_same_fv m φsrc)
      end.
      * apply set_eq. intros a.
        normalize_denotation_formula_fv.
        rewrite !tm_shift_fv;
        try rewrite <- fv_tm_tapp_tlete_assoc_spine;
        try rewrite <- tm_lvars_tapp_tlete_assoc_spine;
        tauto.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnder b φ)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm_fvar_spine
            (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) ∪
          fv_tm (tapp_tm_fvar_spine
            (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)) ∪
          qual_dom φ ∪ lvars_fv (dom Σ)).
        intros a Ha F my HFin HFout Hext Hopen.
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite formula_open_expr_result_formula_shift0 in Hopen.
        2:{ apply lc_tapp_tm_fvar_spine.
            apply lc_tlete_tapp_tm_assoc_source. exact Hlc. }
        2:{ set_solver. }
        rewrite formula_open_expr_result_formula_shift0.
        2:{ apply lc_tapp_tm_fvar_spine.
            apply lc_tapp_tm; [exact Hlc | constructor]. }
        2:{ set_solver. }
        pose proof (res_models_fuel_scoped _ _ _ Hopen) as Hscope_src.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_outer : formula_scoped_in_world my G)
        end.
        {
          unfold formula_scoped_in_world in *.
          normalize_denotation_formula_fv_in Hscope_src.
          normalize_denotation_formula_fv.
          try rewrite fv_tm_tapp_tlete_assoc_spine.
          exact Hscope_src.
        }
        eapply res_models_impl2_intro; [exact Hscope_tgt_outer|].
        intros Hbasic Hresult.
        eapply res_models_impl2_elim; [exact Hopen | exact Hbasic |].
        eapply expr_result_formula_tapp_tlete_assoc_spine_rev.
        -- rewrite fv_tm_tapp_tlete_assoc_spine.
           eapply denot_ty_lvar_guard_wfworld_closed_on_term_le.
           ++ eapply res_extend_by_le; exact Hext.
           ++ repeat rewrite res_models_and_iff. exact Hguard.
        -- exact Hlc.
        -- exact Hresult.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + repeat rewrite res_models_and_iff in Hbody |- *.
      destruct Hbody as [H1 H2].
      split; [eapply IH | eapply IH]; eauto.
    + solve_tapp_tlete_guard_assoc.
    + pose proof (res_models_fuel_scoped _ _ _ Hbody) as Hscope.
      eapply res_models_or_transport_between_worlds
        with (m := m) (φa := denot_ty_lvar_gas gas Σ τ1
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))
          (φb := denot_ty_lvar_gas gas Σ τ2
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))).
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnion τ1 τ2)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_or_l.
        eapply formula_scoped_and_r. exact Hscope_full.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnion τ1 τ2)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_or_r.
        eapply formula_scoped_and_r. exact Hscope_full.
      * intros Hτ1. eapply IH; eauto.
      * intros Hτ2. eapply IH; eauto.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + pose proof (res_models_fuel_scoped _ _ _ Hbody) as Hscope.
      apply res_models_plus_iff in Hbody as
        [m1 [m2 [Hdef [Hle [H1 H2]]]]].
      * eapply res_models_plus_intro_from_models; [exact Hle| |].
        -- eapply IH; eauto.
        -- eapply IH; eauto.
      * exact Hscope.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_full_world_map m φsrc)
      end.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTArrow τx τr)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm_fvar_spine
            (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) ∪
          fv_tm (tapp_tm_fvar_spine
            (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)) ∪
          fv_cty τx ∪ fv_cty τr ∪ lvars_fv (dom Σ)).
        intros a Ha my Hdom Hrestrict Hopen.
        pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTArrow τx τr)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full_my.
        cbn [denot_ty_lvar_gas] in Hscope_full_my.
        pose proof (formula_scoped_and_r _ _ _ Hscope_full_my)
          as Htarget_forall_scope.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hopened_scope_my : formula_scoped_in_world my G)
        end.
        {
          eapply formula_scoped_open_from_fv.
          unfold formula_scoped_in_world in Htarget_forall_scope.
          rewrite Hdom.
          set_solver.
        }
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        repeat rewrite formula_open_impl in Hopened_scope_my.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite ?formula_open_basic_world_bind0 in Hopened_scope_my
          by tlet_support_solver.
        eapply res_models_impl2_intro; [exact Hopened_scope_my|].
        intros Hbasic Harg.
        assert (Henv_arrow :
          denot_relevant_env Σ (CTArrow τx τr)
            (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) =
          denot_relevant_env Σ (CTArrow τx τr)
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))).
        {
          unfold denot_relevant_env, denot_relevant_lvars,
            lty_env_restrict_lvars.
          rewrite tm_lvars_tapp_tlete_assoc_spine. reflexivity.
        }
        rewrite Henv_arrow in Harg.
        pose proof (res_models_impl2_elim _ _ _ _ Hopen Hbasic Harg) as Hres.
        pose proof (res_models_open_denot_ty_lvar_gas_to_open
          a gas
          (denot_relevant_env Σ (CTArrow τx τr)
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))
          (erase_ty τx) τr
          (tapp_tm
            (tm_shift 0
              (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))
            (vbvar 0))
          my
          ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
            change (LVFree a ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
              (denot_relevant_lvars (CTArrow τx τr)
                (tapp_tm_fvar_spine
                  (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))));
            rewrite storeA_restrict_dom;
            intros Hadom; apply elem_of_intersection in Hadom as [HaΣ _];
            apply Ha; repeat (apply elem_of_union_r);
            apply lvars_fv_elem; exact HaΣ)
          ltac:(apply denot_relevant_env_closed; exact HΣ)
          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
          ltac:(set_solver)
          Hres) as Hres_opened.
        clear Hres. rename Hres_opened into Hres.
        rewrite open_tapp_tm_fvar_spine_shift_bvar0_lc in Hres
          by (apply lc_tapp_tm_fvar_spine;
              apply lc_tlete_tapp_tm_assoc_source; exact Hlc).
        eapply IH in Hres.
        3:{ exact Hlc. }
        2:{
          apply lty_env_closed_insert_free.
          apply denot_relevant_env_closed. exact HΣ.
        }
        rewrite <- Henv_arrow in Hres.
        replace (tapp_tm_fvar_spine
            (tapp_tm (tlete e1 e2) (vfvar y)) (a :: z :: zs))
          with (open_tm 0 (vfvar a)
            (tapp_tm
              (tm_shift 0
                (tapp_tm_fvar_spine
                  (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
              (vbvar 0))) in Hres by
          (rewrite open_tapp_tm_fvar_spine_shift_bvar0_lc by
            (apply lc_tapp_tm_fvar_spine;
             apply lc_tapp_tm; [exact Hlc | constructor]);
           reflexivity).
        pose proof (res_models_open_denot_ty_lvar_gas_from_open
          a gas
          (denot_relevant_env Σ (CTArrow τx τr)
            (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
          (erase_ty τx) τr
          (tapp_tm
            (tm_shift 0
              (tapp_tm_fvar_spine
                (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
            (vbvar 0))
          my
          ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
            change (LVFree a ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
              (denot_relevant_lvars (CTArrow τx τr)
                (tapp_tm_fvar_spine
                  (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))));
            rewrite storeA_restrict_dom;
            intros Hadom; apply elem_of_intersection in Hadom as [HaΣ _];
            apply Ha; repeat (apply elem_of_union_r);
            apply lvars_fv_elem; exact HaΣ)
          ltac:(apply denot_relevant_env_closed; exact HΣ)
          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
          ltac:(set_solver)
          Hres) as Hres_formula.
        clear Hres. rename Hres_formula into Hres.
        exact Hres.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_full_world_map m φsrc)
      end.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTWand τx τr)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm_fvar_spine
            (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) ∪
          fv_tm (tapp_tm_fvar_spine
            (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)) ∪
          fv_cty τx ∪ fv_cty τr ∪ lvars_fv (dom Σ)).
        intros a Ha my Hdom Hrestrict Hopen.
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite !formula_open_wand in Hopen |- *.
        pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTWand τx τr)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full_my.
        cbn [denot_ty_lvar_gas] in Hscope_full_my.
        pose proof (formula_scoped_and_r _ _ _ Hscope_full_my)
          as Htarget_forall_scope.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_outer : formula_scoped_in_world my G)
        end.
        {
          change (formula_scoped_in_world my
            (formula_open 0 a
              (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
                (FWand
                  (denot_ty_lvar_gas gas
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTWand τx τr)
                        (tapp_tm_fvar_spine
                          (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
                      (erase_ty τx))
                    (cty_shift 0 τx) (tret (vbvar 0)))
                  (denot_ty_lvar_gas gas
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTWand τx τr)
                        (tapp_tm_fvar_spine
                          (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
                      (erase_ty τx))
                    τr
                    (tapp_tm
                      (tm_shift 0
                        (tapp_tm_fvar_spine
                          (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
                      (vbvar 0))))))).
          eapply formula_scoped_open_from_fv.
          unfold formula_scoped_in_world in Htarget_forall_scope.
          formula_fv_syntax_norm_in Htarget_forall_scope.
          formula_fv_syntax_norm.
          rewrite Hdom.
          set_solver.
        }
        eapply res_models_impl_intro; [exact Hscope_tgt_outer|].
        intros Hbasic.
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hwand.
        pose proof (res_models_fuel_scoped _ _ _ Hwand) as Hscope_src_wand.
        pose proof (proj1 (res_models_wand_iff my _ _ Hscope_src_wand) Hwand)
          as Hwand_elim.
        clear Hwand. rename Hwand_elim into Hwand.
        pose proof (formula_scoped_impl_r _ _ _ Hscope_tgt_outer)
             as Hscope_tgt_wand.
        apply (proj2 (res_models_wand_iff _ _ _ Hscope_tgt_wand)).
        intros n1 Hc Harg.
        assert (Henv_wand :
          denot_relevant_env Σ (CTWand τx τr)
            (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) =
          denot_relevant_env Σ (CTWand τx τr)
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))).
        {
          unfold denot_relevant_env, denot_relevant_lvars,
            lty_env_restrict_lvars.
          rewrite tm_lvars_tapp_tlete_assoc_spine. reflexivity.
        }
        rewrite Henv_wand in Harg.
        pose proof (Hwand n1 Hc Harg) as Hres.
        pose proof (res_models_open_denot_ty_lvar_gas_to_open
          a gas
          (denot_relevant_env Σ (CTWand τx τr)
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))
          (erase_ty τx) τr
          (tapp_tm
            (tm_shift 0
              (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))
            (vbvar 0))
          (res_product n1 my Hc)
          ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
            change (LVFree a ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
              (denot_relevant_lvars (CTWand τx τr)
                (tapp_tm_fvar_spine
                  (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs)))));
            rewrite storeA_restrict_dom;
            intros Hadom; apply elem_of_intersection in Hadom as [HaΣ _];
            apply Ha; repeat (apply elem_of_union_r);
            apply lvars_fv_elem; exact HaΣ)
          ltac:(apply denot_relevant_env_closed; exact HΣ)
          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
          ltac:(set_solver)
          Hres) as Hres_opened.
        clear Hres. rename Hres_opened into Hres.
        rewrite open_tapp_tm_fvar_spine_shift_bvar0_lc in Hres
          by (apply lc_tapp_tm_fvar_spine;
              apply lc_tlete_tapp_tm_assoc_source; exact Hlc).
        eapply IH in Hres.
        3:{ exact Hlc. }
        2:{
          apply lty_env_closed_insert_free.
          apply denot_relevant_env_closed. exact HΣ.
        }
        rewrite <- Henv_wand in Hres.
        replace (tapp_tm_fvar_spine
            (tapp_tm (tlete e1 e2) (vfvar y)) (a :: z :: zs))
          with (open_tm 0 (vfvar a)
            (tapp_tm
              (tm_shift 0
                (tapp_tm_fvar_spine
                  (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
              (vbvar 0))) in Hres by
          (rewrite open_tapp_tm_fvar_spine_shift_bvar0_lc by
            (apply lc_tapp_tm_fvar_spine;
             apply lc_tapp_tm; [exact Hlc | constructor]);
           reflexivity).
        pose proof (res_models_open_denot_ty_lvar_gas_from_open
          a gas
          (denot_relevant_env Σ (CTWand τx τr)
            (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
          (erase_ty τx) τr
          (tapp_tm
            (tm_shift 0
              (tapp_tm_fvar_spine
                (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))
            (vbvar 0))
          (res_product n1 my Hc)
          ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
            change (LVFree a ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
              (denot_relevant_lvars (CTWand τx τr)
                (tapp_tm_fvar_spine
                  (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)))));
            rewrite storeA_restrict_dom;
            intros Hadom; apply elem_of_intersection in Hadom as [HaΣ _];
            apply Ha; repeat (apply elem_of_union_r);
            apply lvars_fv_elem; exact HaΣ)
          ltac:(apply denot_relevant_env_closed; exact HΣ)
          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
          ltac:(set_solver)
          Hres) as Hres_formula.
        clear Hres. rename Hres_formula into Hres.
        exact Hres.
      * exact Hbody.
Qed.

Lemma denot_ty_lvar_gas_tapp_tlete_assoc_under_tapp
    gas (Σ : lty_env) τ e1 e2 y z (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm (tlete e1 e2) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tapp_tm (tlete e1 (tapp_tm e2 (vfvar y))) (vfvar z)) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tapp_tm (tapp_tm (tlete e1 e2) (vfvar y)) (vfvar z)).
Proof.
  intros HΣ Hlc Hm.
  change (tapp_tm (tlete e1 (tapp_tm e2 (vfvar y))) (vfvar z))
    with (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) [z]) in Hm.
  change (tapp_tm (tapp_tm (tlete e1 e2) (vfvar y)) (vfvar z))
    with (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) [z]).
  eapply denot_ty_lvar_gas_tapp_tlete_assoc_spine; eauto.
Qed.

Lemma denot_ty_lvar_gas_tapp_tlete_assoc
    gas (Σ : lty_env) τ e1 e2 y (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_tm (tlete e1 e2) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tlete e1 (tapp_tm e2 (vfvar y))) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tapp_tm (tlete e1 e2) (vfvar y)).
Proof.
  revert Σ τ e1 e2 y m.
  induction gas as [|gas IH]; intros Σ τ e1 e2 y m HΣ Hlc Hm.
  - cbn [denot_ty_lvar_gas] in Hm |- *.
    repeat rewrite res_models_and_iff in Hm |- *.
    destruct Hm as [Hguard Htrue].
    split.
    + solve_tapp_tlete_guard_assoc.
    + exact Htrue.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas] in Hm |- *;
      repeat rewrite res_models_and_iff in Hm |- *;
      destruct Hm as [Hguard Hbody];
      split.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_map_same_fv m φsrc)
      end.
      * apply set_eq. intros a.
        normalize_denotation_formula_fv.
        rewrite !tm_shift_fv;
        try rewrite <- fv_tm_tapp_tm_tlete_assoc;
        try rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar;
        tauto.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTOver b φ)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm (tlete e1 e2) (vfvar y)) ∪
          fv_tm (tlete e1 (tapp_tm e2 (vfvar y))) ∪
          qual_dom φ ∪ lvars_fv (dom Σ)).
        intros z Hz F my HFin HFout Hext Hopen.
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite formula_open_expr_result_formula_shift0 in Hopen.
        2:{ apply lc_tlete_tapp_tm_assoc_source. exact Hlc. }
        2:{ set_solver. }
        rewrite formula_open_expr_result_formula_shift0.
        2:{ apply lc_tapp_tm; [exact Hlc | constructor]. }
        2:{ set_solver. }
        pose proof (res_models_fuel_scoped _ _ _ Hopen) as Hscope_src.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_outer : formula_scoped_in_world my G)
        end.
        {
          unfold formula_scoped_in_world in *.
          normalize_denotation_formula_fv_in Hscope_src.
          normalize_denotation_formula_fv.
          try rewrite fv_tm_tapp_tm_tlete_assoc.
          exact Hscope_src.
        }
        eapply res_models_impl2_intro; [exact Hscope_tgt_outer|].
        intros Hbasic Hresult.
        eapply res_models_impl2_elim; [exact Hopen | exact Hbasic |].
        eapply expr_result_formula_tapp_tm_tlete_assoc_rev.
        -- rewrite fv_tm_tapp_tm_tlete_assoc.
           eapply denot_ty_lvar_guard_wfworld_closed_on_term_le.
           ++ eapply res_extend_by_le; exact Hext.
           ++ repeat rewrite res_models_and_iff. exact Hguard.
        -- exact Hlc.
        -- exact Hresult.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_map_same_fv m φsrc)
      end.
      * apply set_eq. intros a.
        normalize_denotation_formula_fv.
        rewrite !tm_shift_fv;
        try rewrite <- fv_tm_tapp_tm_tlete_assoc;
        try rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar;
        tauto.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnder b φ)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm (tlete e1 e2) (vfvar y)) ∪
          fv_tm (tlete e1 (tapp_tm e2 (vfvar y))) ∪
          qual_dom φ ∪ lvars_fv (dom Σ)).
        intros z Hz F my HFin HFout Hext Hopen.
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite formula_open_expr_result_formula_shift0 in Hopen.
        2:{ apply lc_tlete_tapp_tm_assoc_source. exact Hlc. }
        2:{ set_solver. }
        rewrite formula_open_expr_result_formula_shift0.
        2:{ apply lc_tapp_tm; [exact Hlc | constructor]. }
        2:{ set_solver. }
        pose proof (res_models_fuel_scoped _ _ _ Hopen) as Hscope_src.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_outer : formula_scoped_in_world my G)
        end.
        {
          unfold formula_scoped_in_world in *.
          normalize_denotation_formula_fv_in Hscope_src.
          normalize_denotation_formula_fv.
          try rewrite fv_tm_tapp_tm_tlete_assoc.
          exact Hscope_src.
        }
        eapply res_models_impl2_intro; [exact Hscope_tgt_outer|].
        intros Hbasic Hresult.
        eapply res_models_impl2_elim; [exact Hopen | exact Hbasic |].
        eapply expr_result_formula_tapp_tm_tlete_assoc_rev.
        -- rewrite fv_tm_tapp_tm_tlete_assoc.
           eapply denot_ty_lvar_guard_wfworld_closed_on_term_le.
           ++ eapply res_extend_by_le; exact Hext.
           ++ repeat rewrite res_models_and_iff. exact Hguard.
        -- exact Hlc.
        -- exact Hresult.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + repeat rewrite res_models_and_iff in Hbody |- *.
      destruct Hbody as [H1 H2].
      split; [eapply IH | eapply IH]; eauto.
    + solve_tapp_tlete_guard_assoc.
    + pose proof (res_models_fuel_scoped _ _ _ Hbody) as Hscope.
      eapply res_models_or_transport_between_worlds
        with (m := m) (φa := denot_ty_lvar_gas gas Σ τ1
          (tlete e1 (tapp_tm e2 (vfvar y))))
          (φb := denot_ty_lvar_gas gas Σ τ2
          (tlete e1 (tapp_tm e2 (vfvar y)))).
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnion τ1 τ2)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_or_l.
        eapply formula_scoped_and_r. exact Hscope_full.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnion τ1 τ2)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_or_r.
        eapply formula_scoped_and_r. exact Hscope_full.
      * intros Hτ1. eapply IH; eauto.
      * intros Hτ2. eapply IH; eauto.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + pose proof (res_models_fuel_scoped _ _ _ Hbody) as Hscope.
      apply res_models_plus_iff in Hbody as
        [m1 [m2 [Hdef [Hle [H1 H2]]]]].
      * eapply res_models_plus_intro_from_models; [exact Hle| |].
        -- eapply IH; eauto.
        -- eapply IH; eauto.
      * exact Hscope.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_full_world_map m φsrc)
      end.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTArrow τx τr)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm (tlete e1 e2) (vfvar y)) ∪
          fv_tm (tlete e1 (tapp_tm e2 (vfvar y))) ∪
          fv_cty τx ∪ fv_cty τr ∪ lvars_fv (dom Σ)).
        intros z Hz my Hdom Hrestrict Hopen.
        pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTArrow τx τr)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full_my.
        cbn [denot_ty_lvar_gas] in Hscope_full_my.
        pose proof (formula_scoped_and_r _ _ _ Hscope_full_my)
          as Htarget_forall_scope.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hopened_scope_my : formula_scoped_in_world my G)
        end.
        {
          eapply formula_scoped_open_from_fv.
          unfold formula_scoped_in_world in Htarget_forall_scope.
          rewrite Hdom.
          set_solver.
        }
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        repeat rewrite formula_open_impl in Hopened_scope_my.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite ?formula_open_basic_world_bind0 in Hopened_scope_my
          by tlet_support_solver.
        eapply res_models_impl2_intro; [exact Hopened_scope_my|].
        intros Hbasic Harg.
        assert (Henv_arrow :
          denot_relevant_env Σ (CTArrow τx τr)
            (tapp_tm (tlete e1 e2) (vfvar y)) =
          denot_relevant_env Σ (CTArrow τx τr)
            (tlete e1 (tapp_tm e2 (vfvar y)))).
        {
          unfold denot_relevant_env, denot_relevant_lvars,
            lty_env_restrict_lvars.
          rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. reflexivity.
        }
        rewrite Henv_arrow in Harg.
        pose proof (res_models_impl2_elim _ _ _ _ Hopen Hbasic Harg) as Hres.
        pose proof (res_models_open_denot_ty_lvar_gas_to_open
          z gas
          (denot_relevant_env Σ (CTArrow τx τr)
            (tlete e1 (tapp_tm e2 (vfvar y))))
          (erase_ty τx) τr
          (tapp_tm (tm_shift 0 (tlete e1 (tapp_tm e2 (vfvar y)))) (vbvar 0))
          my
          ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
            change (LVFree z ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
              (denot_relevant_lvars (CTArrow τx τr)
                (tlete e1 (tapp_tm e2 (vfvar y))))));
            rewrite storeA_restrict_dom;
            intros Hzdom; apply elem_of_intersection in Hzdom as [HzΣ _];
            apply Hz; repeat (apply elem_of_union_r);
            apply lvars_fv_elem; exact HzΣ)
          ltac:(apply denot_relevant_env_closed; exact HΣ)
          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
          ltac:(set_solver)
          Hres) as Hres_opened.
        clear Hres. rename Hres_opened into Hres.
        cbn [open_tm open_value value_shift] in Hres.
        rewrite open_tapp_tm_shift_bvar0_lc in Hres
          by (apply lc_tlete_tapp_tm_assoc_source; exact Hlc).
        eapply denot_ty_lvar_gas_tapp_tlete_assoc_under_tapp in Hres.
        3:{ exact Hlc. }
        2:{
          apply lty_env_closed_insert_free.
          apply denot_relevant_env_closed. exact HΣ.
        }
        rewrite <- Henv_arrow in Hres.
        replace (tapp_tm (tapp_tm (tlete e1 e2) (vfvar y)) (vfvar z))
          with (open_tm 0 (vfvar z)
            (tapp_tm (tm_shift 0 (tapp_tm (tlete e1 e2) (vfvar y))) (vbvar 0)))
          in Hres by
          (rewrite open_tapp_tm_shift_bvar0_lc by
            (apply lc_tapp_tm; [exact Hlc | constructor]);
           reflexivity).
        pose proof (res_models_open_denot_ty_lvar_gas_from_open
          z gas
          (denot_relevant_env Σ (CTArrow τx τr)
            (tapp_tm (tlete e1 e2) (vfvar y)))
          (erase_ty τx) τr
          (tapp_tm (tm_shift 0 (tapp_tm (tlete e1 e2) (vfvar y))) (vbvar 0))
          my
          ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
            change (LVFree z ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
              (denot_relevant_lvars (CTArrow τx τr)
                (tapp_tm (tlete e1 e2) (vfvar y)))));
            rewrite storeA_restrict_dom;
            intros Hzdom; apply elem_of_intersection in Hzdom as [HzΣ _];
            apply Hz; repeat (apply elem_of_union_r);
            apply lvars_fv_elem; exact HzΣ)
          ltac:(apply denot_relevant_env_closed; exact HΣ)
          ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
          ltac:(set_solver)
          Hres) as Hres_formula.
        clear Hres. rename Hres_formula into Hres.
        exact Hres.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_full_world_map m φsrc)
      end.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTWand τx τr)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_and_r; exact Hscope_full.
      * exists (fv_tm (tapp_tm (tlete e1 e2) (vfvar y)) ∪
          fv_tm (tlete e1 (tapp_tm e2 (vfvar y))) ∪
          fv_cty τx ∪ fv_cty τr ∪ lvars_fv (dom Σ)).
        intros z Hz my Hdom Hrestrict Hopen.
        repeat rewrite formula_open_impl in Hopen.
        repeat rewrite formula_open_impl.
        rewrite ?formula_open_basic_world_bind0 in Hopen |- *
          by tlet_support_solver.
        rewrite !formula_open_wand in Hopen |- *.
        pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTWand τx τr)
          (tapp_tm (tlete e1 e2) (vfvar y)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc)) as Hscope_full_my.
        cbn [denot_ty_lvar_gas] in Hscope_full_my.
        pose proof (formula_scoped_and_r _ _ _ Hscope_full_my)
          as Htarget_forall_scope.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_outer : formula_scoped_in_world my G)
        end.
        {
          change (formula_scoped_in_world my
            (formula_open 0 z
              (FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
                (FWand
                  (denot_ty_lvar_gas gas
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTWand τx τr)
                        (tapp_tm (tlete e1 e2) (vfvar y)))
                      (erase_ty τx))
                    (cty_shift 0 τx) (tret (vbvar 0)))
                  (denot_ty_lvar_gas gas
                    (typed_lty_env_bind
                      (denot_relevant_env Σ (CTWand τx τr)
                        (tapp_tm (tlete e1 e2) (vfvar y)))
                      (erase_ty τx))
                    τr
                    (tapp_tm
                      (tm_shift 0 (tapp_tm (tlete e1 e2) (vfvar y)))
                      (vbvar 0))))))).
          eapply formula_scoped_open_from_fv.
          unfold formula_scoped_in_world in Htarget_forall_scope.
          formula_fv_syntax_norm_in Htarget_forall_scope.
          formula_fv_syntax_norm.
          rewrite Hdom.
          set_solver.
        }
        eapply res_models_impl_intro; [exact Hscope_tgt_outer|].
        intros Hbasic.
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hwand.
        pose proof (res_models_fuel_scoped _ _ _ Hwand) as Hscope_src_wand.
        pose proof (proj1 (res_models_wand_iff my _ _ Hscope_src_wand) Hwand)
          as Hwand_elim.
        clear Hwand. rename Hwand_elim into Hwand.
        pose proof (formula_scoped_impl_r _ _ _ Hscope_tgt_outer)
             as Hscope_tgt_wand.
        apply (proj2 (res_models_wand_iff _ _ _ Hscope_tgt_wand)).
        intros n1 Hc Harg.
              assert (Henv_wand :
                denot_relevant_env Σ (CTWand τx τr)
                  (tapp_tm (tlete e1 e2) (vfvar y)) =
                denot_relevant_env Σ (CTWand τx τr)
                  (tlete e1 (tapp_tm e2 (vfvar y)))).
              {
                unfold denot_relevant_env, denot_relevant_lvars,
                  lty_env_restrict_lvars.
                rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. reflexivity.
	              }
	              rewrite Henv_wand in Harg.
	              pose proof (Hwand n1 Hc Harg) as Hres.
	              pose proof (res_models_open_denot_ty_lvar_gas_to_open
	                z gas
	                (denot_relevant_env Σ (CTWand τx τr)
	                  (tlete e1 (tapp_tm e2 (vfvar y))))
	                (erase_ty τx) τr
	                (tapp_tm (tm_shift 0 (tlete e1 (tapp_tm e2 (vfvar y)))) (vbvar 0))
	                (res_product n1 my Hc)
	                ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
	                  change (LVFree z ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
	                    (denot_relevant_lvars (CTWand τx τr)
	                      (tlete e1 (tapp_tm e2 (vfvar y))))));
	                  rewrite storeA_restrict_dom;
	                  intros Hzdom; apply elem_of_intersection in Hzdom as [HzΣ _];
	                  apply Hz; repeat (apply elem_of_union_r);
	                  apply lvars_fv_elem; exact HzΣ)
	                ltac:(apply denot_relevant_env_closed; exact HΣ)
	                ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
	                ltac:(set_solver)
	                Hres) as Hres_opened.
	              clear Hres. rename Hres_opened into Hres.
	              cbn [open_tm open_value value_shift] in Hres.
	              rewrite open_tapp_tm_shift_bvar0_lc in Hres
	                by (apply lc_tlete_tapp_tm_assoc_source; exact Hlc).
	              eapply denot_ty_lvar_gas_tapp_tlete_assoc_under_tapp in Hres.
	              3:{ exact Hlc. }
	              2:{
	                apply lty_env_closed_insert_free.
	                apply denot_relevant_env_closed. exact HΣ.
	              }
	              rewrite <- Henv_wand in Hres.
	              replace (tapp_tm (tapp_tm (tlete e1 e2) (vfvar y)) (vfvar z))
	                with (open_tm 0 (vfvar z)
	                  (tapp_tm (tm_shift 0 (tapp_tm (tlete e1 e2) (vfvar y))) (vbvar 0)))
	                in Hres by
	                (rewrite open_tapp_tm_shift_bvar0_lc by
	                  (apply lc_tapp_tm; [exact Hlc | constructor]);
	                 reflexivity).
	              pose proof (res_models_open_denot_ty_lvar_gas_from_open
	                z gas
	                (denot_relevant_env Σ (CTWand τx τr)
	                  (tapp_tm (tlete e1 e2) (vfvar y)))
	                (erase_ty τx) τr
	                (tapp_tm (tm_shift 0 (tapp_tm (tlete e1 e2) (vfvar y))) (vbvar 0))
	                (res_product n1 my Hc)
	                ltac:(unfold denot_relevant_env, lty_env_restrict_lvars;
	                  change (LVFree z ∉ dom (storeA_restrict (Σ : gmap logic_var ty)
	                    (denot_relevant_lvars (CTWand τx τr)
	                      (tapp_tm (tlete e1 e2) (vfvar y)))));
	                  rewrite storeA_restrict_dom;
	                  intros Hzdom; apply elem_of_intersection in Hzdom as [HzΣ _];
	                  apply Hz; repeat (apply elem_of_union_r);
	                  apply lvars_fv_elem; exact HzΣ)
	                ltac:(apply denot_relevant_env_closed; exact HΣ)
	                ltac:(rewrite fv_tapp_tm, tm_shift_fv; cbn [fv_value]; set_solver)
	                ltac:(set_solver)
	                Hres) as Hres_formula.
	              clear Hres. rename Hres_formula into Hres.
	              exact Hres.
      * exact Hbody.
Qed.
Lemma tlet_intro_denotation_wand_case
    gas (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
    τx τr :
  (forall (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
     (m mx : WfWorldT) (Fx : FiberExtensionT) (x : atom)
     (τ : context_ty),
    lty_env_closed Σ ->
    lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
    lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ ->
    expr_result_extension_witness e1 x Fx ->
    m ⊨ expr_total_formula e1 ->
    m ⊨ basic_world_formula (denot_relevant_env Σ τ (tlete e1 e2)) ->
    LVFree x ∉ dom Σ ∪ context_ty_lvars τ ->
    res_extend_by m Fx mx ->
    mx ⊨ denot_ty_lvar_gas gas (<[LVFree x := T1]> Σ) τ (e2 ^^ x) ->
    m ⊨ denot_ty_lvar_gas gas Σ τ (tlete e1 e2)) ->
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e1 ⋮ T1 ->
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTWand τx τr) ->
  expr_result_extension_witness e1 x Fx ->
  m ⊨ expr_total_formula e1 ->
  m ⊨ basic_world_formula
    (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2)) ->
  LVFree x ∉ dom Σ ∪ context_ty_lvars (CTWand τx τr) ->
  res_extend_by m Fx mx ->
  mx ⊨ denot_ty_lvar_gas (S gas)
    (<[LVFree x := T1]> Σ) (CTWand τx τr) (e2 ^^ x) ->
  m ⊨ denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) (tlete e1 e2).
Proof.
  intros IH HΣ He1 Hlet HFx Htotal Hbase_world Hfresh Hext Hmx.
  cbn [denot_ty_lvar_gas] in Hmx |- *.
  normalize_models_ands_in Hmx; normalize_models_ands_goal.
  destruct Hmx as [Hmx_guard Hmx_wand_body].
  assert (HxΣ : LVFree x ∉ dom Σ) by tlet_support_solver.
  assert (Hxτ : LVFree x ∉ context_ty_lvars (CTWand τx τr))
    by tlet_support_solver.
  pose proof (tlet_intro_denotation_gas_zero_support
    Σ T1 e1 e2 m mx Fx x (CTWand τx τr)
    HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext
    ltac:(solve_denot_ty_lvar_gas_zero_from_guard Hmx_guard))
    as Hm_zero.
  pose proof (denot_ty_lvar_gas_guard_of_zero _ _ _ _ Hm_zero)
    as Hguard_m.
  assert (Hbody_scope_m :
    formula_scoped_in_world m
      (FForall
        (FImpl
          (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
          (FWand
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
                (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0)))
            (denot_ty_lvar_gas gas
              (typed_lty_env_bind
                (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
                (erase_ty τx))
              τr
              (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0))))))).
  { solve_denot_ty_lvar_body_scope_from_guard_at
      (S gas) Σ (CTWand τx τr) (tlete e1 e2) Hguard_m. }
  split.
  - solve_denot_guard_goal Hguard_m.
	- refine (res_models_forall_ext_transport
	    m mx Fx _ _ Hbody_scope_m Hext _ Hmx_wand_body).
	  exists (lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
	    fv_cty τx ∪ fv_cty τr ∪ {[x]}).
	  intros y Hy my myx Hle Hdom_my HmyFx Hmyx_body.
	  assert (Htarget_open_scope :
	    formula_scoped_in_world my
	      (formula_open 0 y
	        (denot_wand_body_formula gas
	          (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
	          τx τr (tlete e1 e2)))).
	  {
	    unfold denot_wand_body_formula.
	    eapply formula_scoped_forall_open_res_le;
	      [exact Hbody_scope_m | exact Hle | rewrite Hdom_my; set_solver].
	  }
	  assert (Hxy : x <> y).
	  { intros ->. apply Hy. fast_set_solver!!. }
	  assert (Hxτx : LVFree x ∉ context_ty_lvars τx).
	  {
	    cbn [context_ty_lvars context_ty_lvars_at] in Hfresh.
	    fast_set_solver!!.
	  }
	  assert (Hyτx : y ∉ fv_cty τx) by fast_set_solver!!.
	  assert (Hyτr : y ∉ fv_cty τr) by fast_set_solver!!.
	  assert (Hy_target_rel : LVFree y ∉ dom
	    (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2) : lty_env)).
	  {
	    intros HyD. apply Hy.
	    assert (Hyfv : y ∈ lvars_fv (dom
	      (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2) : lty_env))).
	    { apply lvars_fv_elem. exact HyD. }
	    pose proof (denot_relevant_env_fv_subset
	      Σ (CTWand τx τr) (tlete e1 e2)) as Hrel.
	    pose proof (Hrel y Hyfv) as Hyrel.
	    unfold fv_cty, context_ty_lvars in *.
	    cbn [fv_cty context_ty_lvars context_ty_lvars_at fv_tm] in Hyrel.
	    try rewrite lvars_fv_union in Hyrel.
	    try rewrite !context_ty_lvars_fv_at in Hyrel.
	    clear - Hy Hyrel. set_solver.
	  }
	  assert (Hy_source_rel : LVFree y ∉ dom
	    (denot_relevant_env (<[LVFree x := T1]> Σ)
	      (CTWand τx τr) (e2 ^^ x) : lty_env)).
	  {
	    intros HyD. apply Hy.
	    assert (Hyfv : y ∈ lvars_fv (dom
	      (denot_relevant_env (<[LVFree x := T1]> Σ)
	        (CTWand τx τr) (e2 ^^ x) : lty_env))).
	    { apply lvars_fv_elem. exact HyD. }
	    pose proof (denot_relevant_env_fv_subset
	      (<[LVFree x := T1]> Σ) (CTWand τx τr) (e2 ^^ x)) as Hrel.
	    pose proof (Hrel y Hyfv) as Hyrel.
	    pose proof (open_fv_tm e2 (vfvar x) 0 y) as Hopen.
	    unfold fv_cty, context_ty_lvars in *.
	    cbn [fv_cty context_ty_lvars context_ty_lvars_at fv_value] in Hyrel, Hopen.
	    try rewrite lvars_fv_union in Hyrel.
	    try rewrite !context_ty_lvars_fv_at in Hyrel.
	    clear - Hy Hyrel Hopen. set_solver.
	  }
	  assert (Hy_insert : LVFree y ∉ dom (<[LVFree x := T1]> Σ : lty_env)).
	  {
	    change (LVFree y ∉ dom
	      ((<[LVFree x := T1]> (Σ : gmap logic_var ty)) : gmap logic_var ty)).
	    rewrite dom_insert_L.
	    intros Hybad. apply Hy.
		    apply elem_of_union in Hybad as [Hyx | HyΣ].
		    - apply elem_of_singleton in Hyx. inversion Hyx. congruence.
		    - assert (HyΣfv : y ∈ lvars_fv (dom (Σ : gmap logic_var ty))).
		      { rewrite lvars_fv_elem. exact HyΣ. }
		      set_solver.
		  }
	  assert (Hlc_e2x : lc_tm (e2 ^^ x)).
	  { eapply tlet_lc_open_body_from_basic; exact Hlet. }
	  assert (Hy_body_fv :
	    y ∉ fv_tm (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0))).
	  {
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_value].
	    intros Hybad.
	    apply elem_of_union in Hybad as [Hye2x | Hyempty].
	    - pose proof (open_fv_tm e2 (vfvar x) 0 y Hye2x) as Hcases.
	      cbn [fv_value] in Hcases.
	      apply Hy. fast_set_solver!!.
	    - set_solver.
	  }
	  assert (Hbasic_src_rel :
	    basic_context_ty_lvars
	      (dom (<[LVFree x := T1]> Σ : lty_env) : gset logic_var)
	      (CTWand τx τr)).
	  {
	    pose proof Hmx_guard as Hmx_guard_parts.
	    repeat rewrite res_models_and_iff in Hmx_guard_parts.
	    destruct Hmx_guard_parts as [Hmx_wf _].
	    pose proof (context_ty_wf_formula_basic_lvars _ _ _ Hmx_wf)
	      as Hbasic_rel.
	    eapply basic_context_ty_lvars_mono; [|exact Hbasic_rel].
	    apply denot_relevant_env_dom_subset_direct.
	  }
	  unfold denot_wand_body_formula in Htarget_open_scope, Hmyx_body |- *.
	  rewrite formula_open_impl in Hmyx_body |- *.
	  rewrite formula_open_wand in Hmyx_body |- *.
	  rewrite ?formula_open_basic_world_bind0 in Hmyx_body |- * by tlet_support_solver.
	  eapply res_models_impl_intro; [exact Htarget_open_scope|].
	  intros Hbasic.
	  pose proof (res_models_impl_elim _ _ _ Hmyx_body
	    ltac:(eapply res_models_extend_mono; [exact HmyFx | exact Hbasic]))
	    as Hsource_wand.
	  pose proof (formula_scoped_impl_r _ _ _ Htarget_open_scope)
	    as Hscope_target_wand.
	  eapply res_models_wand_intro; [exact Hscope_target_wand|].
	  intros n Hc Harg.
	  set (source_arg :=
	    formula_open 0 y
	      (denot_ty_lvar_gas gas
	        (typed_lty_env_bind
	          (denot_relevant_env (<[LVFree x := T1]> Σ)
	            (CTWand τx τr) (e2 ^^ x))
	          (erase_ty τx))
	        (cty_shift 0 τx) (tret (vbvar 0)))).
	  set (source_body :=
	    formula_open 0 y
	      (denot_ty_lvar_gas gas
	        (typed_lty_env_bind
	          (denot_relevant_env (<[LVFree x := T1]> Σ)
	            (CTWand τx τr) (e2 ^^ x))
	          (erase_ty τx))
	        τr
	        (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)))).
	  change (myx ⊨ FWand source_arg source_body) in Hsource_wand.
	  pose proof (tlet_wand_arg_source_from_target
	    gas Σ T1 x y τx τr e1 e2 n
	    HΣ Hxy Hxτx
	    Hyτx Hy_target_rel Hy_source_rel Harg) as Harg_source_n.
	  change (n ⊨ source_arg) in Harg_source_n.
	  set (n0 := res_restrict n (formula_fv source_arg)).
	  assert (Harg_source_n0 : n0 ⊨ source_arg).
	  { subst n0. apply res_models_restrict_fv. exact Harg_source_n. }
	  assert (Hout_source_arg : extA_out Fx ## formula_fv source_arg).
	  {
	    pose proof (proj2 (expr_result_extension_witness_shape _ _ _ HFx))
	      as HoutFx.
	    unfold ext_out in HoutFx.
	    pose proof (tlet_wand_source_arg_fresh_x
	      gas Σ T1 x y τx τr e1 e2 HΣ Hxy Hxτx) as Hxfv.
	    rewrite HoutFx. set_solver.
	  }
	  assert (Hc0_my : world_compat n0 my).
	  { subst n0. eapply world_compat_le_l; [apply res_restrict_le | exact Hc]. }
	  assert (Hc0_myx : world_compat n0 myx).
	  {
	    eapply world_compat_restrict_l_extend_by_fresh;
	      [exact Hout_source_arg | exact HmyFx | exact Hc].
	  }
	  pose proof (res_models_wand_elim n0 myx Hc0_myx
	    source_arg source_body Hsource_wand Harg_source_n0)
	    as Hsource_body_prod.
	  assert (Hsource_body_for_ih :
	    res_product n0 myx Hc0_myx ⊨ denot_ty_lvar_gas gas
	      (<[LVFree x := T1]> (<[LVFree y := erase_ty τx]> Σ))
	      (cty_open 0 y τr)
	      ((tapp_tm e2 (vfvar y)) ^^ x)).
	  {
	    subst source_body.
	    eapply tlet_wand_source_body_open_for_ih.
	    - exact HΣ.
	    - exact Hxy.
	    - cbn [context_ty_lvars context_ty_lvars_at] in Hfresh |- *.
	      fast_set_solver!!.
	    - exact Hy_source_rel.
	    - exact Hy_insert.
	    - exact Hlc_e2x.
	    - exact Hy_body_fv.
	    - exact Hyτr.
	    - exact Hbasic_src_rel.
	    - exact Hsource_body_prod.
	  }
	  assert (Hout_n0_dom : extA_out Fx ## world_dom (n0 : WorldT)).
	  {
	    subst n0.
	    pose proof (proj2 (expr_result_extension_witness_shape _ _ _ HFx))
	      as HoutFx.
	    unfold ext_out in HoutFx.
	    unfold world_dom, res_restrict. simpl.
	    rewrite HoutFx in Hout_source_arg.
	    set_solver.
	  }
	  pose proof (res_extend_by_product_r_fresh n0 my myx Fx
	    Hc0_my Hc0_myx Hout_n0_dom HmyFx) as Hprod_ext.
	  assert (Hbasic_src_rel0 :
	    basic_context_ty_lvars (dom (Σ : gmap logic_var ty) : gset logic_var)
	      (CTWand τx τr)).
	  {
	    destruct Hbasic_src_rel as [Hvars Hshape]. split; [|exact Hshape].
	    intros v Hv.
	    specialize (Hvars v Hv).
	    change (v ∈ dom ((<[LVFree x := T1]> (Σ : gmap logic_var ty))
	      : gmap logic_var ty)) in Hvars.
	    rewrite dom_insert_L in Hvars.
	    apply elem_of_union in Hvars as [Hvx|HvΣ]; [|exact HvΣ].
	    apply elem_of_singleton in Hvx. subst v.
	    exfalso. apply Hfresh. apply elem_of_union_r. exact Hv.
	  }
	  assert (HlcΣ : lc_lvars (dom (Σ : gmap logic_var ty) : gset logic_var)).
	  { exact HΣ. }
	  assert (HyΣ : LVFree y ∉ (dom (Σ : gmap logic_var ty) : gset logic_var)).
	  {
	    intros HyΣ.
	    assert (Hyfv : y ∈ lvars_fv (dom (Σ : gmap logic_var ty) : gset logic_var)).
	    { apply lvars_fv_elem. exact HyΣ. }
	    apply Hy.
	    fast_set_solver!!.
	  }
	  assert (Hclosed_Σy : lty_env_closed (<[LVFree y := erase_ty τx]> Σ)).
	  { apply lty_env_closed_insert_free. exact HΣ. }
	  assert (He1_Σy :
	    lty_env_to_atom_env (<[LVFree y := erase_ty τx]> Σ) ⊢ₑ e1 ⋮ T1).
	  {
	    apply basic_typing_lty_env_insert_free_away; [tlet_support_solver|exact He1].
	  }
	  assert (Hlet_Σy :
	    lty_env_to_atom_env (<[LVFree y := erase_ty τx]> Σ) ⊢ₑ
	      tlete e1 (tapp_tm e2 (vfvar y)) ⋮ erase_ty (cty_open 0 y τr)).
	  {
	    rewrite cty_open_preserves_erasure.
	    apply basic_typing_tapp_tm_tlete_assoc_rev.
	    eapply basic_typing_tapp_tm.
	    - apply basic_typing_lty_env_insert_free_away; [tlet_support_solver|exact Hlet].
	    - constructor.
	      apply lty_env_to_atom_env_insert_free_lookup_eq.
	  }
	  assert (Htotal_prod :
	    res_product n0 my Hc0_my ⊨ expr_total_formula e1).
	  {
	    eapply res_models_kripke.
	    - etransitivity.
	      + exact Hle.
	      + apply res_product_le_r.
	    - exact Htotal.
	  }
	  assert (Hbase_world_prod :
	    res_product n0 my Hc0_my ⊨ basic_world_formula
	      (denot_relevant_env (<[LVFree y := erase_ty τx]> Σ)
	        (cty_open 0 y τr) (tlete e1 (tapp_tm e2 (vfvar y))))).
	  {
	    eapply basic_world_formula_wand_body_from_source_and_arg.
	    - exact HlcΣ.
	    - exact HyΣ.
	    - exact Hbasic_src_rel0.
	    - apply tm_lvars_tlet_tapp_tm_fvar_without_arg.
	    - eapply res_models_kripke.
	      + apply res_product_le_r.
	      + eapply res_models_kripke; [exact Hle|exact Hbase_world].
	    - eapply res_models_kripke.
	      + apply res_product_le_r.
	      + rewrite formula_open_basic_world_formula in Hbasic.
	        rewrite lvar_store_open_one_bound0_singleton in Hbasic.
	        exact Hbasic.
	  }
	  assert (Hfresh_x_Σy :
	    LVFree x ∉ dom (<[LVFree y := erase_ty τx]> Σ) ∪
	      context_ty_lvars (cty_open 0 y τr)).
	  {
	    intros Hbad.
	    apply elem_of_union in Hbad as [Hdom|Hτ].
	    - change (LVFree x ∈ dom ((<[LVFree y := erase_ty τx]>
	        (Σ : gmap logic_var ty)) : gmap logic_var ty)) in Hdom.
	      rewrite dom_insert_L in Hdom.
		      apply elem_of_union in Hdom as [Hyx|HxΣ_dom].
		      + apply elem_of_singleton in Hyx. inversion Hyx. congruence.
		      + cbn [context_ty_lvars context_ty_lvars_at] in Hfresh.
		        fast_set_solver!!.
	    - assert (Hdiff :
	        LVFree x ∈ context_ty_lvars (cty_open 0 y τr) ∖ {[LVFree y]}).
	      { set_solver. }
	      pose proof (context_ty_lvars_open_body_without_fresh_closed
	        (dom (Σ : gmap logic_var ty) : gset logic_var) τr y
	        HlcΣ HyΣ ltac:(destruct Hbasic_src_rel0 as [Hvars _];
	          cbn [context_ty_lvars context_ty_lvars_at] in Hvars |- *;
	          set_solver)) as Hsubset.
	      specialize (Hsubset _ Hdiff).
	      cbn [context_ty_lvars context_ty_lvars_at] in Hfresh.
	      fast_set_solver!!.
	  }
	  pose proof (IH (<[LVFree y := erase_ty τx]> Σ) T1 e1
	    (tapp_tm e2 (vfvar y))
	    (res_product n0 my Hc0_my) (res_product n0 myx Hc0_myx)
	    Fx x (cty_open 0 y τr)
	    Hclosed_Σy He1_Σy Hlet_Σy HFx Htotal_prod Hbase_world_prod
	    Hfresh_x_Σy Hprod_ext Hsource_body_for_ih) as HIH_result.
	  assert (Htarget_body_small :
	    res_product n0 my Hc0_my ⊨ formula_open 0 y
	      (denot_ty_lvar_gas gas
	        (typed_lty_env_bind
	          (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
	          (erase_ty τx))
	        τr
	        (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)))).
	  {
	    assert (Hassoc :
	      res_product n0 my Hc0_my ⊨ denot_ty_lvar_gas gas
	        (<[LVFree y := erase_ty τx]> Σ)
	        (cty_open 0 y τr)
	        (tapp_tm (tlete e1 e2) (vfvar y))).
	    {
	      eapply denot_ty_lvar_gas_tapp_tlete_assoc.
	      - exact Hclosed_Σy.
	      - eapply typing_tm_lc. exact Hlet.
	      - exact HIH_result.
	    }
	    pose proof (res_models_denot_ty_lvar_gas_env_agree_on
	      gas (<[LVFree y := erase_ty τx]> Σ)
	      (<[LVFree y := erase_ty τx]>
	        (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2)))
	      (cty_open 0 y τr) (tapp_tm (tlete e1 e2) (vfvar y))
	      (denot_relevant_lvars (cty_open 0 y τr)
	        (tapp_tm (tlete e1 e2) (vfvar y)))
	      (res_product n0 my Hc0_my)
	      ltac:(intros v Hv; exact Hv)
	      ltac:(symmetry;
	        eapply wand_body_relevant_env_agree_from_basic_context_ty;
	        [exact HlcΣ|exact HyΣ|exact Hbasic_src_rel0|
	         apply tm_lvars_tapp_tm_fvar_without_arg])
	      Hassoc) as Henv.
	    replace (tapp_tm (tlete e1 e2) (vfvar y)) with
	      (open_tm 0 (vfvar y)
	        (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0))) in Henv.
	    2:{
	      rewrite open_tapp_tm_shift_bvar0_lc.
	      - reflexivity.
	      - eapply typing_tm_lc. exact Hlet.
	    }
	    eapply res_models_open_denot_ty_lvar_gas_from_open.
	    - exact Hy_target_rel.
	    - apply denot_relevant_env_closed. exact HΣ.
	    - rewrite fv_tapp_tm, tm_shift_fv. cbn [fv_value].
	      fast_set_solver!!.
	    - exact Hyτr.
	    - exact Henv.
	  }
		  eapply res_models_kripke; [|exact Htarget_body_small].
		  eapply res_product_le_mono; [apply res_restrict_le|reflexivity].
Qed.

(** ** Formula-open normalization *)

Ltac normalize_formula_open_syntax :=
  rewrite ?formula_open_impl in *;
  rewrite ?formula_open_fibvars in *;
  rewrite ?formula_open_over in *;
  rewrite ?formula_open_under in *;
  rewrite ?formula_open_basic_world_formula in *;
  rewrite ?typed_lty_env_bind_open_current_base in * by solve_tlet_sidecond;
  rewrite ?typed_lty_env_bind_open_current in * by solve_tlet_sidecond;
  rewrite ?formula_open_basic_world_bind0 in * by solve_tlet_sidecond;
  rewrite ?formula_open_expr_result_formula_shift0 in * by solve_tlet_sidecond;
  rewrite ?lvars_open_qual_vars_difference_bound0 in *;
  rewrite ?type_qualifier_formula_open in * by solve_tlet_sidecond.
