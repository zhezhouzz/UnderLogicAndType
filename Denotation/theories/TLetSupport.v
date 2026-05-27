(** * Denotation.TLetSupport

    Shared support lemmas and tactics for the [tlet] introduction proof. *)

From Denotation Require Import Notation.
From Denotation Require Import ContextTypeDenotation.

Ltac normalize_formula_fv :=
  repeat first
    [ rewrite formula_fv_true | rewrite formula_fv_false
    | rewrite formula_fv_and | rewrite formula_fv_or
    | rewrite formula_fv_impl | rewrite formula_fv_star
    | rewrite formula_fv_wand | rewrite formula_fv_plus
    | rewrite formula_fv_forall | rewrite formula_fv_over
    | rewrite formula_fv_under | rewrite formula_fv_fibvars ];
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_context_ty_wf_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  cbn [formula_fv formula_lvars];
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms, ?lvars_fv_singleton_free;
  repeat first
    [ rewrite formula_fv_true | rewrite formula_fv_false
    | rewrite formula_fv_and | rewrite formula_fv_or
    | rewrite formula_fv_impl | rewrite formula_fv_star
    | rewrite formula_fv_wand | rewrite formula_fv_plus
    | rewrite formula_fv_forall | rewrite formula_fv_over
    | rewrite formula_fv_under | rewrite formula_fv_fibvars ];
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_context_ty_wf_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms, ?lvars_fv_singleton_free.

Lemma fiber_extension_singleton_out_fresh_in
    (F : FiberExtensionT) y :
  ext_out F = {[y]} ->
  y ∉ ext_in F.
Proof.
  intros Hout.
  pose proof (extA_disjoint F) as Hdisj.
  unfold ext_out, ext_in in *.
  rewrite Hout in Hdisj. set_solver.
Qed.

Lemma tlet_forall_fresh_from_input
    (F : FiberExtensionT) y X :
  ext_in F = X ->
  ext_out F = {[y]} ->
  y ∉ X.
Proof.
  intros HFin HFout.
  rewrite <- HFin. eapply fiber_extension_singleton_out_fresh_in; eauto.
Qed.

Lemma tlet_fresh_tm_from_forall_input
    (F : FiberExtensionT) y X e :
  ext_in F = X ->
  ext_out F = {[y]} ->
  fv_tm e ⊆ X ->
  y ∉ fv_tm e.
Proof.
  intros HFin HFout Hsub.
  pose proof (tlet_forall_fresh_from_input F y X HFin HFout).
  set_solver.
Qed.

Lemma tlet_fresh_lty_env_from_forall_input
    (F : FiberExtensionT) y X (Σ : lty_env) :
  ext_in F = X ->
  ext_out F = {[y]} ->
  lvars_fv (dom Σ) ⊆ X ->
  LVFree y ∉ dom Σ.
Proof.
  intros HFin HFout Hsub Hy.
  pose proof (tlet_forall_fresh_from_input F y X HFin HFout) as HyX.
  apply HyX, Hsub. apply lvars_fv_elem. exact Hy.
Qed.

Lemma tlet_atom_notin_lvars_fv_iff_free_notin y (D : lvset) :
  y ∉ lvars_fv D ↔ LVFree y ∉ D.
Proof.
  rewrite lvars_fv_elem. tauto.
Qed.

Lemma tlet_lvars_fv_empty :
  lvars_fv (∅ : lvset) = ∅.
Proof.
  apply set_eq. intros x. rewrite lvars_fv_elem. set_solver.
Qed.

Lemma tlet_lvars_fv_dom_insert_free (Σ : lty_env) x T :
  lvars_fv (dom (<[LVFree x := T]> Σ)) =
  {[x]} ∪ lvars_fv (dom Σ).
Proof.
  change (lvars_fv (dom ((<[LVFree x := T]> (Σ : gmap logic_var ty)) :
    gmap logic_var ty)) = {[x]} ∪ lvars_fv (dom (Σ : gmap logic_var ty))).
  rewrite dom_insert_L, lvars_fv_union, lvars_fv_singleton_free.
  set_solver.
Qed.

Lemma tlet_lvars_fv_subset_insert_free_drop
    (D : lvset) (Σ : lty_env) x T :
  LVFree x ∉ D ->
  D ⊆ dom (<[LVFree x := T]> Σ) ->
  lvars_fv D ⊆ lvars_fv (dom Σ).
Proof.
  intros Hfresh Hsub y Hy.
  rewrite lvars_fv_elem in Hy |- *.
  specialize (Hsub (LVFree y) Hy).
  change (LVFree y ∈ dom
    ((<[LVFree x := T]> (Σ : gmap logic_var ty)) :
      gmap logic_var ty)) in Hsub.
  rewrite dom_insert_L in Hsub.
  destruct (decide (y = x)) as [-> | Hneq].
  - exfalso. exact (Hfresh Hy).
  - set_solver.
Qed.

Lemma tlet_context_ty_lvars_insert_free_fv_drop
    (Σ : lty_env) τ x T :
  LVFree x ∉ context_ty_lvars τ ->
  basic_context_ty_lvars (dom (<[LVFree x := T]> Σ)) τ ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hfresh [Hsub _].
  rewrite <- context_ty_lvars_fv.
  eapply tlet_lvars_fv_subset_insert_free_drop; eauto.
Qed.

Lemma tlet_fresh_qualifier_from_forall_input
    (F : FiberExtensionT) y X (φ : type_qualifier) :
  ext_in F = X ->
  ext_out F = {[y]} ->
  qual_dom φ ⊆ X ->
  y ∉ qual_dom φ.
Proof.
  intros HFin HFout Hsub.
  pose proof (tlet_forall_fresh_from_input F y X HFin HFout).
  set_solver.
Qed.

Ltac tlet_normalize_freshness :=
  repeat match goal with
  | H : LVFree ?y ∉ ?D |- _ =>
      rewrite <- (tlet_atom_notin_lvars_fv_iff_free_notin y D) in H
  | |- LVFree ?y ∉ ?D =>
      rewrite <- (tlet_atom_notin_lvars_fv_iff_free_notin y D)
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
  rewrite ?tlet_lvars_fv_dom_insert_free in *;
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

Ltac solve_formula_fv_subset :=
  repeat match goal with
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
  | |- context[fv_tm (open_tm ?k ?u ?e)] =>
      lazymatch goal with
      | Hfv : fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_open" in
          pose proof (open_fv_tm e u k) as Hfv
      end
  | H : context[fv_tm (open_tm ?k ?u ?e)] |- _ =>
      lazymatch goal with
      | Hfv : fv_tm (open_tm k u e) ⊆ fv_value u ∪ fv_tm e |- _ => fail
      | _ =>
          let Hfv := fresh "Hfv_open" in
          pose proof (open_fv_tm e u k) as Hfv
      end
  end;
  normalize_formula_fv;
  cbn [fv_tm fv_value] in *;
  tlet_normalize_freshness;
  set_solver.

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
          pose proof (tlet_context_ty_lvars_insert_free_fv_drop
            Σ τ x T Hfresh Hbasic) as Hfv
      end
  end;
  repeat match goal with
  | H : basic_context_ty_lvars _ _ |- _ =>
      let Hsub := fresh "Hcontext_lvars_sub" in
      let Hshape := fresh "Hcontext_shape" in
      destruct H as [Hsub Hshape]
  end.

Ltac solve_formula_scoped :=
  solve
  [ eapply res_models_scoped; eassumption
  | unfold formula_scoped_in_world;
    harvest_tlet_models;
    normalize_formula_fv;
    rewrite ?context_ty_lvars_fv in *;
    rewrite ?lvars_fv_lvars_at_depth in *;
    cbn [fv_tm fv_value] in *;
    tlet_normalize_freshness;
    fast_set_solver!!
  ].

Lemma formula_lvars_fv_basic_world_formula Σ :
  lvars_fv (formula_lvars (basic_world_formula Σ)) = lvars_fv (dom Σ).
Proof.
  change (lvars_fv (formula_lvars (basic_world_formula Σ)))
    with (formula_fv (basic_world_formula Σ)).
  apply formula_fv_basic_world_formula.
Qed.

Lemma formula_lvars_fv_expr_result_formula e x :
  lvars_fv (formula_lvars (expr_result_formula e x)) =
  lvars_fv (tm_lvars e ∪ {[x]}).
Proof.
  change (lvars_fv (formula_lvars (expr_result_formula e x)))
    with (formula_fv (expr_result_formula e x)).
  apply formula_fv_expr_result_formula.
Qed.

Lemma formula_lvars_fv_type_qualifier_formula φ :
  lvars_fv (formula_lvars (type_qualifier_formula φ)) = qual_dom φ.
Proof.
  change (lvars_fv (formula_lvars (type_qualifier_formula φ)))
    with (formula_fv (type_qualifier_formula φ)).
  apply formula_fv_type_qualifier_formula.
Qed.

Ltac normalize_tlet_forall_fv :=
  rewrite ?formula_fv_true, ?formula_fv_false;
  rewrite ?formula_fv_and, ?formula_fv_or, ?formula_fv_impl;
  rewrite ?formula_fv_star, ?formula_fv_wand, ?formula_fv_plus;
  rewrite ?formula_fv_forall, ?formula_fv_over, ?formula_fv_under,
    ?formula_fv_fibvars;
  rewrite ?formula_fv_basic_world_formula;
  rewrite ?formula_fv_context_ty_wf_formula;
  rewrite ?formula_fv_expr_basic_typing_formula;
  rewrite ?formula_fv_expr_total_formula;
  rewrite ?formula_fv_expr_result_formula;
  rewrite ?formula_fv_type_qualifier_formula;
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
  rewrite ?tlet_lvars_fv_dom_insert_free;
  rewrite ?context_ty_lvars_over_fv, ?context_ty_lvars_under_fv;
  rewrite ?tm_shift_fv, ?cty_shift_fv;
  rewrite ?tm_lvars_fv;
  rewrite ?lvars_fv_lvars_at_depth;
  rewrite ?lvars_fv_qual_vars_difference_free, ?lvars_fv_qual_vars;
  rewrite ?lvars_fv_union, ?lvars_fv_of_atoms, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?lvars_fv_difference_singleton_free,
    ?tlet_lvars_fv_empty;
  rewrite ?tm_lvars_fv;
  cbn [fv_tm fv_value].

Lemma tlet_over_fib_formula_fresh_x x y b φ :
  LVFree x ∉ context_ty_lvars (CTOver b φ) ->
  x <> y ->
  x ∉ formula_fv
    (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
      (FOver (type_qualifier_formula (φ ^q^ y)))).
Proof.
  intros Hfresh Hxy.
  normalize_tlet_forall_fv.
  pose proof (context_ty_over_fresh_open_qual_dom x y b φ Hfresh Hxy).
  set_solver.
Qed.

Lemma tlet_under_fib_formula_fresh_x x y b φ :
  LVFree x ∉ context_ty_lvars (CTUnder b φ) ->
  x <> y ->
  x ∉ formula_fv
    (FFibVars (qual_vars (φ ^q^ y) ∖ {[LVFree y]})
      (FUnder (type_qualifier_formula (φ ^q^ y)))).
Proof.
  intros Hfresh Hxy.
  normalize_tlet_forall_fv.
  pose proof (context_ty_under_fresh_open_qual_dom x y b φ Hfresh Hxy).
  set_solver.
Qed.

Lemma tlet_arrow_result_env_term_subset Σ T1 x e1 e2 τx τr :
  lty_env_to_atom_env Σ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τr) ->
  lvars_fv (dom (typed_lty_env_bind Σ (erase_ty τx))) ∪
    fv_tm (tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)) ⊆
  lvars_fv (dom (typed_lty_env_bind (<[LVFree x := T1]> Σ) (erase_ty τx))) ∪
    fv_tm (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)).
Proof.
  intros Hlet.
  pose proof (basic_typing_lty_env_to_atom_env_fv_subset _ _ _ Hlet) as Hfv_let.
  transitivity (lvars_fv (dom (typed_lty_env_bind Σ (erase_ty τx))) ∪
    fv_tm (tlete e1 e2)).
  - rewrite (fv_tapp_tm (tm_shift 0 (tlete e1 e2)) (vbvar 0)).
    rewrite (tm_shift_fv 0 (tlete e1 e2)).
    cbn [fv_value].
    set_solver.
  - rewrite ?typed_lty_env_bind_lvars_fv_dom, ?tlet_lvars_fv_dom_insert_free.
    fast_set_solver!!.
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

Lemma formula_fv_denot_ty_lvar_gas_scope_from_guard
    gas Σ τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ FAnd
    (context_ty_wf_formula (denot_relevant_env Σ τbig e) τbig)
    (FAnd (basic_world_formula (denot_relevant_env Σ τbig e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τbig e) e
          (erase_ty τbig))
        (expr_total_formula e))) ->
  formula_fv (denot_ty_lvar_gas gas Σ τsmall e) ⊆ world_dom (m : WorldT).
Proof.
  intros Hτ Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf [Hworld [_ Htotal_e]]].
  transitivity (fv_tm e ∪ fv_cty τsmall).
  - apply formula_fv_denot_ty_lvar_gas_subset_relevant.
  - pose proof (res_models_fuel_scoped _ _ _ Htotal_e) as Hscope_e.
    unfold formula_scoped_in_world in Hscope_e.
    rewrite formula_fv_expr_total_formula, tm_lvars_fv in Hscope_e.
    pose proof (context_ty_wf_formula_fv_cty_subset
      (denot_relevant_env Σ τbig e) τbig m Hwf) as Hτbig_fv.
    pose proof (proj1 (basic_world_formula_models_iff
      (denot_relevant_env Σ τbig e) m) Hworld) as [_ [Hworld_dom _]].
    assert (Hτsmall_fv : fv_cty τsmall ⊆ fv_cty τbig).
    {
      rewrite <- !context_ty_lvars_fv.
      apply lvars_fv_mono. exact Hτ.
    }
    set_solver.
Qed.


Lemma tlet_lc_open_body_from_lc e1 e2 x :
  lc_tm (tlete e1 e2) ->
  lc_tm (e2 ^^ x).
Proof.
  intros Hlc.
  apply lc_lete_iff_body in Hlc as [_ Hbody].
  apply body_open_tm; [exact Hbody | constructor].
Qed.

Lemma tlet_lc_open_body_from_basic Γ e1 e2 T x :
  Γ ⊢ₑ tlete e1 e2 ⋮ T ->
  lc_tm (e2 ^^ x).
Proof.
  intros Htyped.
  eapply tlet_lc_open_body_from_lc.
  eapply basic_typing_regular_tm. exact Htyped.
Qed.

Lemma tlet_lc_tapp_open_body_from_basic Γ e1 e2 T x y :
  Γ ⊢ₑ tlete e1 e2 ⋮ T ->
  lc_tm (tapp_tm (e2 ^^ x) (vfvar y)).
Proof.
  intros Htyped.
  apply lc_tapp_tm; [eapply tlet_lc_open_body_from_basic; eauto | constructor].
Qed.

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
	      tlet_forall_fresh_from_input,
	      tlet_fresh_tm_from_forall_input,
	      tlet_fresh_lty_env_from_forall_input,
	      tlet_fresh_qualifier_from_forall_input
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

Ltac intro_models_impl H :=
  match goal with
  | |- ?m ⊨ FImpl ?p ?q =>
      eapply res_models_impl_intro;
      [solve_tlet_impl_scope
      | intro H]
  end.

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

Ltac normalize_models_ands :=
  normalize_models_ands_goal.

Lemma open_tapp_tm_fvar_lc_arg e x y :
  open_tm 0 (vfvar x) (tapp_tm e (vfvar y)) =
  tapp_tm (open_tm 0 (vfvar x) e) (vfvar y).
Proof.
  apply open_tapp_tm_lc_arg. constructor.
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

Lemma denot_ty_lvar_gas_insert_commute_tapp_open
    gas (Σ : lty_env) x y T1 Ty τ e2 (m : WfWorldT) :
  x <> y ->
  m ⊨ denot_ty_lvar_gas gas
      (<[LVFree y := Ty]> (<[LVFree x := T1]> Σ))
      τ (tapp_tm (e2 ^^ x) (vfvar y)) ->
  m ⊨ denot_ty_lvar_gas gas
      (<[LVFree x := T1]> (<[LVFree y := Ty]> Σ))
      τ ((tapp_tm e2 (vfvar y)) ^^ x).
Proof.
  intros Hxy Hm.
  rewrite lty_env_insert_free_commute by exact Hxy.
  change (((tapp_tm e2 (vfvar y)) ^^ x)) with
    (open_tm 0 (vfvar x) (tapp_tm e2 (vfvar y))).
  rewrite open_tapp_tm_fvar_lc_arg.
  exact Hm.
Qed.

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
        change (((<[LVFree x := T1]> (Σ : gmap logic_var ty))
          : gmap logic_var ty) !! LVFree z =
          (storeA_restrict Σ
            (denot_relevant_lvars (CTArrow τx τr) (tlete e1 e2))
            : gmap logic_var ty) !! LVFree z).
        try rewrite decide_True by assumption.
        rewrite lookup_insert_ne by congruence.
        destruct (Σ !! LVFree z) eqn:HΣz.
        -- symmetry.
           replace (Σ !! LVFree z) with (Some t) by (symmetry; exact HΣz).
           apply storeA_restrict_lookup_some_2; [exact HΣz|exact Hztgt].
        -- symmetry.
           replace (Σ !! LVFree z) with (@None ty) by (symmetry; exact HΣz).
           apply storeA_restrict_lookup_none_l. exact HΣz.
Qed.

Lemma lvars_open0_difference_subset_depth1
    (D L : lvset) y :
  lc_lvars D ->
  LVFree y ∉ D ->
  lvars_at_depth 1 L ⊆ D ->
  lvars_open 0 y L ∖ {[LVFree y]} ⊆ lvars_at_depth 1 L.
Proof.
  intros Hlc HyD Hdepth u Hu.
  apply elem_of_difference in Hu as [Hu Hyu].
  rewrite lvars_open_unfold in Hu.
  apply elem_of_gset_swap in Hu.
  change (key_swap (LVBound 0) (LVFree y) u ∈ L) with
    (logic_var_open 0 y u ∈ L) in Hu.
  destruct u as [k|z].
  - destruct k as [|k].
    + rewrite logic_var_open_unfold in Hu.
      unfold eq_swap in Hu.
      destruct (decide (LVBound 0 = LVBound 0)) as [_|Hbad]; [|congruence].
      exfalso. apply HyD.
      apply Hdepth.
      apply lvars_at_depth_elem.
      exists (LVFree y). split; [exact Hu|reflexivity].
    + rewrite logic_var_open_unfold in Hu.
      unfold eq_swap in Hu.
      destruct (decide (LVBound (S k) = LVBound 0)) as [Hbad|_];
        [inversion Hbad|].
      destruct (decide (LVBound (S k) = LVFree y)) as [Hbad|_];
          [discriminate|].
      assert (Hbad : LVBound k ∈ D).
      {
        apply Hdepth.
        apply lvars_at_depth_elem.
        exists (LVBound (S k)). split; [exact Hu|].
        cbn [logic_var_at_depth].
        rewrite decide_True by lia.
        replace (S k - 1) with k by lia.
        reflexivity.
      }
      exfalso. exact (Hlc (LVBound k) Hbad).
  - destruct (decide (z = y)) as [->|Hzy].
    + exfalso. apply Hyu. set_solver.
    + rewrite logic_var_open_unfold in Hu.
      unfold eq_swap in Hu.
      destruct (decide (LVFree z = LVBound 0)) as [Hbad|_];
        [discriminate|].
      destruct (decide (LVFree z = LVFree y)) as [Hbad|_];
        [inversion Hbad; congruence|].
      apply lvars_at_depth_elem.
      exists (LVFree z). split; [exact Hu|reflexivity].
Qed.

Lemma context_ty_lvars_open_body_without_fresh_closed
    (D : lvset) τ y :
  lc_lvars D ->
  LVFree y ∉ D ->
  context_ty_lvars_at 1 τ ⊆ D ->
  context_ty_lvars (cty_open 0 y τ) ∖ {[LVFree y]} ⊆
  context_ty_lvars_at 1 τ.
Proof.
  intros Hlc HyD Hτ.
  rewrite cty_open_vars.
  unfold context_ty_open_lvars.
  rewrite <- (context_ty_lvars_depth τ 1).
  eapply lvars_open0_difference_subset_depth1 with (D := D).
  - exact Hlc.
  - exact HyD.
  - rewrite context_ty_lvars_depth. exact Hτ.
Qed.

Lemma tm_lvars_tapp_tm_fvar_without_arg e y :
  tm_lvars (tapp_tm e (vfvar y)) ∖ {[LVFree y]} ⊆ tm_lvars e.
Proof.
  unfold tapp_tm, tm_lvars.
  cbn [tm_lvars_at value_lvars_at value_shift].
  unfold bvar_lvars_at.
  destruct (decide (1 <= 0)); [lia|].
  set_solver.
Qed.

Lemma tm_lvars_tlet_tapp_tm_fvar_without_arg e1 e2 y :
  tm_lvars (tlete e1 (tapp_tm e2 (vfvar y))) ∖ {[LVFree y]} ⊆
  tm_lvars (tlete e1 e2).
Proof.
  unfold tapp_tm, tm_lvars.
  cbn [tm_lvars_at value_lvars_at value_shift].
  unfold bvar_lvars_at.
  destruct (decide (2 <= 0)); [lia|].
  destruct (decide (2 <= 1)); [lia|].
  set_solver.
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

Lemma lty_env_open_one_bound0_singleton y T :
  lty_env_open_one 0 y
    ((<[LVBound 0 := T]> (∅ : gmap logic_var ty)) : lty_env) =
  ((<[LVFree y := T]> (∅ : gmap logic_var ty)) : lty_env).
Proof.
  rewrite lty_env_open_one_insert.
  replace (logic_var_open 0 y (LVBound 0)) with (LVFree y).
  - replace (lty_env_open_one 0 y (∅ : lty_env)) with
      ((∅ : gmap logic_var ty) : lty_env).
    reflexivity.
    unfold lty_env_open_one.
    apply (storeA_rekey_empty (V := ty) (K := logic_var)
      (logic_var_open 0 y)).
  - rewrite logic_var_open_unfold.
    unfold eq_swap. repeat destruct decide; try lia; try congruence.
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

Lemma denot_ty_lvar_gas_tapp_tlete_assoc
    gas (Σ : lty_env) τ e1 e2 y (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tlete e1 (tapp_tm e2 (vfvar y))) ->
  m ⊨ denot_ty_lvar_gas gas Σ τ
    (tapp_tm (tlete e1 e2) (vfvar y)).
Proof.
  (* Operational associativity for the derived application form:
     applying the result of [let e1 in e2] to [y] is observationally the
     same as evaluating [e1] first and then applying the opened body.  This
     should be proved below the context-type denotation layer from the small-step
     let decomposition/recomposition lemmas, and then lifted through the
     recursive denotation by gas induction.

     Proof plan, serving the top-level Arrow case:

     1. Prove or reuse the operational equivalence already available in
        BasicDenotation:
        [expr_eval_in_atom_store_tapp_tm_tlete_assoc] and its FV/support
        companions say that
        [tlete e1 (tapp_tm e2 (vfvar y))] and
        [tapp_tm (tlete e1 e2) (vfvar y)] have the same observable results
        on every store, under the local closedness premise.

     2. Lift that operational equivalence through the formula atoms in
        [denot_ty_lvar_gas]:
        - [expr_basic_typing_formula] should be transported using the same
          basic typing derivation shape, or a small basic-typing congruence
          for this derived application associativity.
        - [expr_total_formula] and [expr_result_formula] should use the
          operational equivalence wrappers from BasicDenotation.

     3. Induct on [gas] and destruct [τ].  The guard part is transported by
        step 2.  Inter/Union/Sum recurse directly.  Over/Under/Arrow/Wand
        use the fact that the recursive body formulas only inspect the same
        FV after rewriting the term by the operational equivalence; any
        world-transport side conditions should be discharged with the existing
        FV upper-bound/scope helpers rather than by unfolding models.

     4. This lemma is used at the end of the Arrow branch of
        [tlet_intro_denotation], after the IH has produced the denotation for
        [tlete e1 (tapp_tm e2 (vfvar y))].  Its only job there is to change
        the result term into the canonical Arrow result
        [tapp_tm (tlete e1 e2) (vfvar y)]. *)
Admitted.

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
  (* The wand branch follows the Arrow branch's forall/extension transport,
     but the body uses separating implication, so the commuting proof must
     additionally transport through [res_product].  This is intentionally
     isolated as the remaining Wand-specific proof obligation rather than
     leaving an anonymous hole in the main [tlet] theorem.

     Proof plan, mirroring the proved Arrow branch:

     1. Normalize the premise
        [mx ⊨ denot_ty_lvar_gas (S gas) ... (CTWand τx τr) (e2 ^^ x)]
        into its guard and forall/wand body with [normalize_models_ands] and
        the existing formula-open/open-env normalizers.  The guard obligations
        are the same shape as Arrow: context-type wf, basic world, basic
        typing, and totality for [tlete e1 e2].

     2. Use [res_models_forall_ext_transport] in the same way as Arrow to
        align the forall witness [y] and the result extension [Fx].  The
        basic-world premise for the freshly introduced argument should be
        solved with the existing typed-extension/basic-world helpers, not by
        re-proving resource typing inline.

     3. For the wand body, open the wand hypothesis with the transported
        argument denotation.  Compared with Arrow, the extra work is only the
        separating-implication resource split/product:
        transport the left resource through the argument denotation, then use
        the recursive IH on the right/resource result world.  Any commuting
        between [my #> Fx] and [mx #> Fy] should reuse the same extension
        transport lemmas already used by Arrow.

     4. The result side should then be converted back with
        [res_models_open_denot_ty_lvar_gas_from_open] and, if the term shape
        is [tlete e1 (tapp_tm e2 (vfvar y))], finish with
        [denot_ty_lvar_gas_tapp_tlete_assoc].

     5. Keep the proof local to Wand.  Do not create broad new infrastructure
        unless a subgoal is genuinely shared with Arrow/Over or already exists
        one layer lower. *)
Admitted.

Ltac open_formula_syntax_step :=
  rewrite ?formula_open_impl;
  rewrite ?formula_open_fibvars;
  rewrite ?formula_open_over;
  rewrite ?formula_open_under;
  rewrite ?formula_open_context_ty_wf_formula;
  rewrite ?formula_open_expr_total_formula by solve_tlet_sidecond;
  rewrite ?formula_open_basic_world_bind0 by solve_tlet_sidecond;
  rewrite ?formula_open_basic_world_formula;
  rewrite ?formula_open_expr_result_formula_shift0 by solve_tlet_sidecond;
  rewrite ?formula_open_expr_result_formula by solve_tlet_sidecond;
  rewrite ?lvars_open_qual_vars_difference_bound0;
  rewrite ?type_qualifier_formula_open by solve_tlet_sidecond;
  rewrite ?open_tapp_tm_fvar_lc_arg.

Ltac normalize_open_denot_goal :=
  idtac;
  rewrite ?open_tapp_tm_fvar_lc_arg.

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

Ltac transport_open_denot_from_open_in H :=
  lazymatch type of H with
  | res_models ?m
      (denot_ty_lvar_gas ?gas (<[LVFree ?y := ?T]> ?Σ)
        (cty_open 0 ?y ?τ) (open_tm 0 (vfvar ?y) ?e)) =>
      let Hclosed := fresh H "_formula_open" in
      pose proof (res_models_open_denot_ty_lvar_gas_from_open
        y gas Σ T τ e m
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        H) as Hclosed;
      clear H; rename Hclosed into H
  | res_models ?m
      (denot_ty_lvar_gas ?gas
        (lty_env_open_one ?k ?y ?Σ)
        (cty_open ?k ?y ?τ)
        (open_tm ?k (vfvar ?y) ?e)) =>
      let Hclosed := fresh H "_formula_open" in
      pose proof (res_models_open_denot_ty_lvar_gas_from_open_at
        k y gas Σ τ e m
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        ltac:(solve_tlet_sidecond)
        H) as Hclosed;
      clear H; rename Hclosed into H
  | _ => idtac
  end.

Ltac normalize_open_denot_in H :=
  transport_open_denot_in H;
  rewrite ?open_tapp_tm_fvar_lc_arg in H.

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

Lemma tlet_extensions_commute_obligation
    (m mx my mxy : WfWorldT) (Fx Fy : FiberExtensionT) :
  res_extend_by m Fx mx ->
  res_extend_by m Fy my ->
  res_extend_by mx Fy mxy ->
  res_extend_by my Fx mxy.
Proof.
  intros Hmx Hmy Hmxy.
  apply (proj1 (res_extend_by_commute_input_widen
    m mx Fx Fy Fy my mxy Hmx Hmy
    (fiber_extension_input_widen_to_refl Fy)
    ltac:(eapply res_extend_by_input_dom; exact Hmxy))).
  exact Hmxy.
Qed.

Lemma tlet_extensions_commute_widened_obligation
    (m mx my mxy : WfWorldT) (Fx Fy : FiberExtensionT) X :
  res_extend_by m Fx mx ->
  res_extend_by m Fy my ->
  res_extend_by_input_widened_to mx Fy X mxy ->
  res_extend_by my Fx mxy.
Proof.
  intros Hmx Hmy [Fywide [Hwid [_ Hmxy]]].
  apply (proj1 (res_extend_by_commute_input_widen
    m mx Fx Fy Fywide my mxy Hmx Hmy Hwid
    ltac:(eapply res_extend_by_input_dom; exact Hmxy))).
  exact Hmxy.
Qed.

Lemma tlet_arrow_arg_extend_obligation
    gas (Σ : lty_env) x y T1 Ty τx
    (my mxy : WfWorldT) (Fx : FiberExtensionT) :
  LVFree x ∉ dom Σ ->
  x <> y ->
  LVFree x ∉ context_ty_lvars τx ->
  extension_has_ltype (<[LVFree x := T1]> ∅)
    (res_restrict my (ext_in Fx)) Fx ->
  res_extend_by my Fx mxy ->
  my ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := Ty]> Σ)
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)) ->
  mxy ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := Ty]> (<[LVFree x := T1]> Σ))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)).
Proof.
  intros HxΣ Hxy Hxτx HFx_ty Hext Hmy.
  rewrite <- lty_env_insert_free_commute by exact Hxy.
  assert (HxΣy : LVFree x ∉
    dom ((<[LVFree y := Ty]> (Σ : gmap logic_var ty))
      : gmap logic_var ty)).
  { rewrite dom_insert_L. set_solver. }
  assert (Hxτopen :
    LVFree x ∉ context_ty_lvars (cty_open 0 y (cty_shift 0 τx))).
  { apply context_ty_lvars_open_shift_fresh; assumption. }
  assert (Hmxy_old : mxy ⊨ denot_ty_lvar_gas gas
    (<[LVFree y := Ty]> Σ)
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y))).
  {
    eapply res_models_extend_mono; [exact Hext | exact Hmy].
  }
  eapply denot_ty_lvar_gas_insert_fresh_lty_env; eauto.
  cbn [fv_tm fv_value]. set_solver.
Qed.

Ltac solve_tlet_guard :=
  match goal with
  | |- _ ⊨ context_ty_wf_formula _ _ =>
      eapply context_ty_wf_formula_drop_fresh_lvar; eauto; solve_tlet_sidecond
  | |- _ ⊨ basic_world_formula _ =>
      eapply basic_world_formula_drop_result_extension; eauto; solve_tlet_sidecond
  | |- _ ⊨ expr_basic_typing_formula _ (tlete _ _) _ =>
      eapply expr_basic_typing_formula_tlete_intro; eauto;
      eapply basic_world_formula_drop_result_extension; eauto; solve_tlet_sidecond
  | |- _ ⊨ expr_total_formula (tlete _ _) =>
      eapply expr_total_formula_tlete_intro_from_result_extension; eauto;
      first
        [ eapply basic_world_formula_drop_result_extension; eauto;
          solve_tlet_sidecond
        | solve_tlet_sidecond ]
  | |- formula_scoped_in_world _ _ =>
      solve_formula_scoped
  end.
