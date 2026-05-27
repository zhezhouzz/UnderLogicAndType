(** * Denotation.TLetSupport

    Shared support lemmas and tactics for the [tlet] introduction proof. *)

From Denotation Require Import Notation.
From Denotation Require Import ContextTypeDenotation ContextTypeDenotationTactics.
From ContextAlgebra Require Import ResourceAlgebraPullback.
From ContextLogic Require Import FormulaSyntaxTactics.
From CoreLang Require Import InstantiationProps.
From Stdlib Require Import List.
Import ListNotations.

Ltac normalize_formula_fv :=
  normalize_denotation_formula_fv.

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
  rewrite ?tlet_lvars_fv_dom_insert_free;
  rewrite ?context_ty_lvars_over_fv, ?context_ty_lvars_under_fv;
  rewrite ?lvars_fv_lvars_at_depth;
  rewrite ?lvars_fv_qual_vars_difference_free, ?lvars_fv_qual_vars;
  rewrite ?tlet_lvars_fv_empty;
  normalize_denotation_formula_fv;
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
    normalize_denotation_formula_fv_in Hscope_e.
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

Lemma tm_lvars_tapp_tm_fvar e y :
  tm_lvars (tapp_tm e (vfvar y)) = tm_lvars e ∪ {[LVFree y]}.
Proof.
  unfold tapp_tm, tm_lvars.
  cbn [tm_lvars_at value_lvars_at value_shift].
  unfold bvar_lvars_at.
  destruct (decide (1 <= 0)); [lia|].
  set_solver.
Qed.

Fixpoint tapp_tm_fvar_spine (e : tm) (ys : list atom) : tm :=
  match ys with
  | [] => e
  | y :: ys' => tapp_tm (tapp_tm_fvar_spine e ys') (vfvar y)
  end.

Lemma fv_tm_tapp_tm_fvar_spine e ys :
  fv_tm (tapp_tm_fvar_spine e ys) = fv_tm e ∪ list_to_set ys.
Proof.
  induction ys as [|y ys IH]; cbn [tapp_tm_fvar_spine].
  - set_solver.
  - rewrite fv_tapp_tm, IH. cbn [fv_value].
    set_solver.
Qed.

Lemma tm_lvars_tapp_tm_fvar_spine e ys :
  tm_lvars (tapp_tm_fvar_spine e ys) =
  tm_lvars e ∪ lvars_of_atoms (list_to_set ys).
Proof.
  induction ys as [|y ys IH]; cbn [tapp_tm_fvar_spine].
  - cbn [list_to_set]. unfold lvars_of_atoms. rewrite set_map_empty. set_solver.
  - rewrite tm_lvars_tapp_tm_fvar, IH.
    cbn [list_to_set].
    unfold lvars_of_atoms.
    rewrite set_map_union_L, set_map_singleton_L.
    set_solver.
Qed.

Lemma fv_tm_tapp_tlete_assoc_spine e1 e2 y ys :
  fv_tm (tapp_tm_fvar_spine
    (tapp_tm (tlete e1 e2) (vfvar y)) ys) =
  fv_tm (tapp_tm_fvar_spine
    (tlete e1 (tapp_tm e2 (vfvar y))) ys).
Proof.
  rewrite !fv_tm_tapp_tm_fvar_spine.
  rewrite fv_tm_tapp_tm_tlete_assoc. reflexivity.
Qed.

Lemma tm_lvars_tapp_tlete_assoc_spine e1 e2 y ys :
  tm_lvars (tapp_tm_fvar_spine
    (tapp_tm (tlete e1 e2) (vfvar y)) ys) =
  tm_lvars (tapp_tm_fvar_spine
    (tlete e1 (tapp_tm e2 (vfvar y))) ys).
Proof.
  rewrite !tm_lvars_tapp_tm_fvar_spine.
  rewrite tm_lvars_tapp_tm_tlete_assoc_fvar. reflexivity.
Qed.

Lemma lc_tapp_tm_fvar_spine e ys :
  lc_tm e ->
  lc_tm (tapp_tm_fvar_spine e ys).
Proof.
  induction ys as [|y ys IH]; cbn [tapp_tm_fvar_spine]; intros Hlc.
  - exact Hlc.
  - apply lc_tapp_tm; [apply IH; exact Hlc | constructor].
Qed.

Lemma open_tapp_tm_fvar_spine_shift_bvar0_lc e ys y :
  lc_tm (tapp_tm_fvar_spine e ys) ->
  open_tm 0 (vfvar y)
    (tapp_tm (tm_shift 0 (tapp_tm_fvar_spine e ys)) (vbvar 0)) =
  tapp_tm_fvar_spine e (y :: ys).
Proof.
  intros Hlc.
  cbn [tapp_tm_fvar_spine].
  apply open_tapp_tm_shift_bvar0_lc. exact Hlc.
Qed.

Lemma basic_typing_tapp_tlete_assoc_spine Γ e1 e2 y ys T :
  Γ ⊢ₑ tapp_tm_fvar_spine
    (tlete e1 (tapp_tm e2 (vfvar y))) ys ⋮ T ->
  Γ ⊢ₑ tapp_tm_fvar_spine
    (tapp_tm (tlete e1 e2) (vfvar y)) ys ⋮ T.
Proof.
  induction ys as [|z ys IH] in T |- *; cbn [tapp_tm_fvar_spine].
  - apply basic_typing_tapp_tm_tlete_assoc.
  - intros Hty.
    apply basic_typing_tapp_tm_fvar_inv in Hty as [Tx [Hfun Hz]].
    eapply basic_typing_tapp_tm.
    + apply IH. exact Hfun.
    + exact Hz.
Qed.

Lemma basic_tm_has_ltype_tapp_tlete_assoc_spine
    (Σ : lty_env) e1 e2 y ys T :
  lc_tm (tlete e1 e2) ->
  basic_tm_has_ltype Σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) T ->
  basic_tm_has_ltype Σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) T.
Proof.
  intros Hlc [Hsub Hty].
  split.
  - rewrite tm_lvars_tapp_tlete_assoc_spine. exact Hsub.
  - intros η Hfresh Hbv.
    rewrite open_tm_env_lc.
    + assert (Hfresh_src : open_env_fresh_for_lvars η
        (dom Σ ∪ tm_lvars
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys))).
      { rewrite <- tm_lvars_tapp_tlete_assoc_spine. exact Hfresh. }
      assert (Hbv_src :
        lvars_bv (dom Σ ∪ tm_lvars
          (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys)) ⊆
        dom η).
      { rewrite <- tm_lvars_tapp_tlete_assoc_spine. exact Hbv. }
      pose proof (Hty η Hfresh_src Hbv_src) as Htyη.
      rewrite open_tm_env_lc in Htyη by
        (apply lc_tapp_tm_fvar_spine;
         apply lc_tlete_tapp_tm_assoc_source; exact Hlc).
      apply basic_typing_tapp_tlete_assoc_spine.
      exact Htyη.
    + apply lc_tapp_tm_fvar_spine.
      apply lc_tapp_tm; [exact Hlc | constructor].
Qed.

Lemma expr_basic_typing_formula_tapp_tlete_assoc_spine
    (Σ : lty_env) e1 e2 y ys T (m : WfWorldT) :
  lc_tm (tlete e1 e2) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) T) ->
  res_models m (expr_basic_typing_formula Σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) T).
Proof.
  intros Hlc Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [HlcΣ [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split; [exact HlcΣ|].
  split; [exact Hsub|].
  eapply basic_tm_has_ltype_tapp_tlete_assoc_spine; eauto.
Qed.

Lemma expr_eval_in_atom_store_tapp_tlete_assoc_spine σ e1 e2 y ys v :
  store_closed σ ->
  lc_tm (tlete e1 e2) ->
  expr_eval_in_atom_store σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) v <->
  expr_eval_in_atom_store σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) v.
Proof.
  intros Hclosed Hlc.
  induction ys as [|z ys IH] in v |- *; cbn [tapp_tm_fvar_spine].
  - apply expr_eval_in_atom_store_tapp_tm_tlete_assoc;
      [exact Hclosed | exact Hlc | constructor].
  - apply expr_eval_in_atom_store_tapp_tm_fun_equiv.
    + exact Hclosed.
    + apply lc_tapp_tm_fvar_spine.
      apply lc_tlete_tapp_tm_assoc_source. exact Hlc.
    + apply lc_tapp_tm_fvar_spine.
      apply lc_tapp_tm; [exact Hlc | constructor].
    + exact IH.
Qed.

Lemma expr_eval_in_atom_store_tapp_tlete_assoc_spine_closed_on σ e1 e2 y ys v :
  store_closed (store_restrict σ (fv_tm (tapp_tm_fvar_spine
    (tapp_tm (tlete e1 e2) (vfvar y)) ys))) ->
  lc_tm (tlete e1 e2) ->
  expr_eval_in_atom_store σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) v <->
  expr_eval_in_atom_store σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) v.
Proof.
  intros Hclosed Hlc.
  rewrite <- (expr_eval_in_atom_store_restrict_fv_exact σ
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) v).
  rewrite <- (expr_eval_in_atom_store_restrict_fv_exact σ
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) v).
  rewrite <- fv_tm_tapp_tlete_assoc_spine.
  apply expr_eval_in_atom_store_tapp_tlete_assoc_spine; assumption.
Qed.

Lemma expr_total_on_atom_world_tapp_tlete_assoc_spine
    e1 e2 y ys (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm_fvar_spine
      (tapp_tm (tlete e1 e2) (vfvar y)) ys)) m ->
  lc_tm (tlete e1 e2) ->
  expr_total_on_atom_world
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) m ->
  expr_total_on_atom_world
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) m.
Proof.
  intros Hclosed Hlc Htotal.
  unfold expr_total_on_atom_world, expr_total_on in *.
  destruct Htotal as [Hdom Hstores].
  split.
  - rewrite tm_lvars_tapp_tlete_assoc_spine. exact Hdom.
  - intros τ Hτ.
    destruct Hτ as [σ [Hσ ->]].
    destruct (Hstores (lstore_lift_free σ)) as [v Heval].
    { exists σ. split; [exact Hσ | reflexivity]. }
    exists v.
    apply (proj1 (expr_eval_in_atom_store_tapp_tlete_assoc_spine_closed_on
      σ e1 e2 y ys v (Hclosed σ Hσ) Hlc)).
    exact Heval.
Qed.

Lemma expr_total_formula_tapp_tlete_assoc_spine
    e1 e2 y ys (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm_fvar_spine
      (tapp_tm (tlete e1 e2) (vfvar y)) ys)) m ->
  lc_tm (tlete e1 e2) ->
  res_models m (expr_total_formula
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys)) ->
  res_models m (expr_total_formula
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys)).
Proof.
  intros Hclosed Hlc Hmodels.
  apply expr_total_atom_world_to_formula.
  eapply expr_total_on_atom_world_tapp_tlete_assoc_spine; eauto.
  apply expr_total_formula_to_atom_world. exact Hmodels.
Qed.

Lemma expr_result_at_world_tapp_tlete_assoc_spine
    e1 e2 y ys z (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm_fvar_spine
      (tapp_tm (tlete e1 e2) (vfvar y)) ys)) m ->
  lc_tm (tlete e1 e2) ->
  expr_result_at_world
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) z
    (lraw_world (res_lift_free m)) ->
  expr_result_at_world
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) z
    (lraw_world (res_lift_free m)).
Proof.
  intros Hclosed Hlc Hres.
  destruct Hres as [Hzfresh [Hdom Hstores]].
  split.
  - rewrite tm_lvars_tapp_tlete_assoc_spine. exact Hzfresh.
  - split.
    + rewrite tm_lvars_tapp_tlete_assoc_spine. exact Hdom.
    + intros τ Hτ.
      destruct Hτ as [σ [Hσ ->]].
      specialize (Hstores (lstore_lift_free σ)
        ltac:(exists σ; split; [exact Hσ | reflexivity])).
      destruct Hstores as [_ [v [Hlookup Heval]]].
      split.
      * rewrite tm_lvars_tapp_tlete_assoc_spine. exact Hzfresh.
      * exists v. split; [exact Hlookup |].
        apply (proj1 (expr_eval_in_atom_store_tapp_tlete_assoc_spine_closed_on
          σ e1 e2 y ys v (Hclosed σ Hσ) Hlc)).
        exact Heval.
Qed.

Lemma expr_result_formula_tapp_tlete_assoc_spine
    e1 e2 y ys z (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm_fvar_spine
      (tapp_tm (tlete e1 e2) (vfvar y)) ys)) m ->
  lc_tm (tlete e1 e2) ->
  res_models m (expr_result_formula
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) z) ->
  res_models m (expr_result_formula
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) z).
Proof.
  intros Hclosed Hlc Hmodels.
  apply expr_result_atom_world_to_formula.
  eapply expr_result_at_world_tapp_tlete_assoc_spine; eauto.
  apply expr_result_formula_to_atom_world. exact Hmodels.
Qed.

Lemma expr_result_at_world_tapp_tlete_assoc_spine_rev
    e1 e2 y ys z (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm_fvar_spine
      (tapp_tm (tlete e1 e2) (vfvar y)) ys)) m ->
  lc_tm (tlete e1 e2) ->
  expr_result_at_world
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) z
    (lraw_world (res_lift_free m)) ->
  expr_result_at_world
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) z
    (lraw_world (res_lift_free m)).
Proof.
  intros Hclosed Hlc Hres.
  destruct Hres as [Hzfresh [Hdom Hstores]].
  split.
  - rewrite tm_lvars_tapp_tlete_assoc_spine in Hzfresh. exact Hzfresh.
  - split.
    + rewrite tm_lvars_tapp_tlete_assoc_spine in Hdom. exact Hdom.
    + intros τ Hτ.
      destruct Hτ as [σ [Hσ ->]].
      specialize (Hstores (lstore_lift_free σ)
        ltac:(exists σ; split; [exact Hσ | reflexivity])).
      destruct Hstores as [_ [v [Hlookup Heval]]].
      split.
      * rewrite tm_lvars_tapp_tlete_assoc_spine in Hzfresh. exact Hzfresh.
      * exists v. split; [exact Hlookup |].
        apply (proj2 (expr_eval_in_atom_store_tapp_tlete_assoc_spine_closed_on
          σ e1 e2 y ys v (Hclosed σ Hσ) Hlc)).
        exact Heval.
Qed.

Lemma expr_result_formula_tapp_tlete_assoc_spine_rev
    e1 e2 y ys z (m : WfWorldT) :
  wfworld_closed_on
    (fv_tm (tapp_tm_fvar_spine
      (tapp_tm (tlete e1 e2) (vfvar y)) ys)) m ->
  lc_tm (tlete e1 e2) ->
  res_models m (expr_result_formula
    (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) ys) z) ->
  res_models m (expr_result_formula
    (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) ys) z).
Proof.
  intros Hclosed Hlc Hmodels.
  apply expr_result_atom_world_to_formula.
  eapply expr_result_at_world_tapp_tlete_assoc_spine_rev; eauto.
  apply expr_result_formula_to_atom_world. exact Hmodels.
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
	      + apply (proj2 (lc_lvars_no_bv _)).
	        apply lty_env_closed_insert_free. exact HΣ.
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

Lemma res_product_le_r_tlet (n m : WfWorldT)
    (Hc : world_compat n m) :
  m ⊑ res_product n m Hc.
Proof.
  destruct (res_product_comm_eq n m Hc) as [Hc' Heq].
  rewrite Heq.
  apply resA_le_product_l.
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
              rewrite storeA_restrict_dom. set_solver.
           ++ apply basic_typing_lty_env_to_atom_env_denot_relevant_env.
              exact Hlet.
  - cbn [res_models res_models_fuel formula_measure].
    split; [apply formula_scoped_true_iff; exact I | exact I].
Qed.

Definition denot_wand_body_formula
    (gas : nat) (Σg : lty_env) (τx τr : context_ty) (e : tm) : FormulaT :=
  let Σx := typed_lty_env_bind Σg (erase_ty τx) in
  FImpl (basic_world_formula (<[LVBound 0 := erase_ty τx]> ∅))
    (FWand
      (denot_ty_lvar_gas gas Σx
        (cty_shift 0 τx) (tret (vbvar 0)))
      (denot_ty_lvar_gas gas Σx τr
        (tapp_tm (tm_shift 0 e) (vbvar 0)))).


Lemma denot_ty_lvar_guard_wfworld_closed_on_term
    (Σ : lty_env) τ e (m : WfWorldT) :
  m ⊨ FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  wfworld_closed_on (fv_tm e) m.
Proof.
  intros Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [Hbasic _]]].
  eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
  unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
  change (lvars_of_atoms (fv_tm e) ⊆
    dom (storeA_restrict (Σ : gmap logic_var ty)
      (context_ty_lvars τ ∪ tm_lvars e))).
  rewrite storeA_restrict_dom.
  intros v Hv.
  unfold lvars_of_atoms in Hv.
  apply elem_of_map in Hv as [a [-> Ha]].
  apply elem_of_intersection. split.
  - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
      as [Hsub _].
    assert (Ha_lvars : LVFree a ∈ tm_lvars e).
    { apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha. }
    specialize (Hsub _ Ha_lvars).
    unfold denot_relevant_env, denot_relevant_lvars,
      lty_env_restrict_lvars in Hsub.
    change (LVFree a ∈ dom
      (storeA_restrict (Σ : gmap logic_var ty)
        (context_ty_lvars τ ∪ tm_lvars e))) in Hsub.
    rewrite storeA_restrict_dom in Hsub.
    apply elem_of_intersection in Hsub as [HaΣ _].
    exact HaΣ.
  - apply elem_of_union_r.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
Qed.

Lemma denot_ty_lvar_guard_wfworld_closed_on_term_le
    (Σ : lty_env) τ e (m n : WfWorldT) :
  m ⊑ n ->
  m ⊨ FAnd (context_ty_wf_formula (denot_relevant_env Σ τ e) τ)
    (FAnd (basic_world_formula (denot_relevant_env Σ τ e))
      (FAnd
        (expr_basic_typing_formula (denot_relevant_env Σ τ e) e
          (erase_ty τ))
        (expr_total_formula e))) ->
  wfworld_closed_on (fv_tm e) n.
Proof.
  intros Hle Hguard.
  eapply wfworld_closed_on_le.
  - repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [_ [_ [_ Htotal]]].
    pose proof (res_models_fuel_scoped _ _ _ Htotal) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    normalize_denotation_formula_fv_in Hscope.
    exact Hscope.
  - exact Hle.
  - eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    exact Hguard.
Qed.

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
      eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
      unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
      change (lvars_of_atoms (fv_tm (tapp_tm (tlete e1 e2) (vfvar y))) ⊆
        dom (storeA_restrict (Σ : gmap logic_var ty)
          (context_ty_lvars τ ∪ tm_lvars (tlete e1 (tapp_tm e2 (vfvar y)))))).
      rewrite storeA_restrict_dom.
      intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply elem_of_intersection. split.
      - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
          as [Hsub _].
        assert (Ha_src :
          LVFree a ∈ tm_lvars (tlete e1 (tapp_tm e2 (vfvar y)))).
        {
          rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar.
          apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
        }
        specialize (Hsub _ Ha_src).
        change (LVFree a ∈ dom
          (storeA_restrict (Σ : gmap logic_var ty)
            (context_ty_lvars τ ∪
             tm_lvars (tlete e1 (tapp_tm e2 (vfvar y)))))) in Hsub.
        rewrite storeA_restrict_dom in Hsub.
        apply elem_of_intersection in Hsub as [HaΣ _].
        exact HaΣ.
      - apply elem_of_union_r.
        rewrite <- tm_lvars_tapp_tm_tlete_assoc_fvar.
        apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
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
      eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
      unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
      change (lvars_of_atoms (fv_tm (tapp_tm (tlete e1 e2) (vfvar y))) ⊆
        dom (storeA_restrict (Σ : gmap logic_var ty)
          (context_ty_lvars τ ∪ tm_lvars (tapp_tm (tlete e1 e2) (vfvar y))))).
      rewrite storeA_restrict_dom.
      intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply elem_of_intersection. split.
      - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
          as [Hsub _].
        assert (Ha_tgt :
          LVFree a ∈ tm_lvars (tapp_tm (tlete e1 e2) (vfvar y))).
        { apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha. }
        specialize (Hsub _ Ha_tgt).
        change (LVFree a ∈ dom
          (storeA_restrict (Σ : gmap logic_var ty)
            (context_ty_lvars τ ∪
             tm_lvars (tapp_tm (tlete e1 e2) (vfvar y))))) in Hsub.
        rewrite storeA_restrict_dom in Hsub.
        apply elem_of_intersection in Hsub as [HaΣ _].
        exact HaΣ.
      - apply elem_of_union_r.
        apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
    }
    eapply expr_total_formula_tapp_tm_tlete_assoc_rev; eauto.
Qed.

Ltac solve_tapp_tlete_guard_assoc :=
  match goal with
  | Hguard : ?m ⊨ context_ty_wf_formula
        (denot_relevant_env ?Σ ?τ (tlete ?e1 (tapp_tm ?e2 (vfvar ?y)))) ?τ
      ∧ ?m ⊨ basic_world_formula
          (denot_relevant_env ?Σ ?τ (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))))
        ∧ ?m ⊨ expr_basic_typing_formula
            (denot_relevant_env ?Σ ?τ (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))))
            (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (erase_ty ?τ)
          ∧ ?m ⊨ expr_total_formula (tlete ?e1 (tapp_tm ?e2 (vfvar ?y)))
    |- ?m ⊨ context_ty_wf_formula
        (denot_relevant_env ?Σ ?τ (tapp_tm (tlete ?e1 ?e2) (vfvar ?y))) ?τ
      ∧ ?m ⊨ basic_world_formula
          (denot_relevant_env ?Σ ?τ (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)))
        ∧ ?m ⊨ expr_basic_typing_formula
            (denot_relevant_env ?Σ ?τ (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)))
            (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (erase_ty ?τ)
          ∧ ?m ⊨ expr_total_formula (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) =>
      let Hassoc := fresh "Hguard_assoc" in
      pose proof (denot_ty_lvar_guard_tapp_tlete_assoc
        Σ τ e1 e2 y m ltac:(eassumption)
        ltac:(repeat rewrite res_models_and_iff; exact Hguard)) as Hassoc;
      repeat rewrite res_models_and_iff in Hassoc;
      exact Hassoc
  end.

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
      eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld].
      unfold denot_relevant_env, denot_relevant_lvars, lty_env_restrict_lvars.
      change (lvars_of_atoms (fv_tm (tapp_tm_fvar_spine
          (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs))) ⊆
        dom (storeA_restrict (Σ : gmap logic_var ty)
          (context_ty_lvars τ ∪ tm_lvars
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))))).
      rewrite storeA_restrict_dom.
      intros v Hv.
      unfold lvars_of_atoms in Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply elem_of_intersection. split.
      - pose proof (expr_basic_typing_formula_basic_ltype _ _ _ _ Hbasic)
          as [Hsub _].
        assert (Ha_src :
          LVFree a ∈ tm_lvars
            (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))).
        {
          rewrite <- tm_lvars_tapp_tlete_assoc_spine.
          apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
        }
        specialize (Hsub _ Ha_src).
        change (LVFree a ∈ dom
          (storeA_restrict (Σ : gmap logic_var ty)
            (context_ty_lvars τ ∪ tm_lvars
              (tapp_tm_fvar_spine (tlete e1 (tapp_tm e2 (vfvar y))) (z :: zs))))) in Hsub.
        rewrite storeA_restrict_dom in Hsub.
        apply elem_of_intersection in Hsub as [HaΣ _].
        exact HaΣ.
      - apply elem_of_union_r.
        rewrite <- tm_lvars_tapp_tlete_assoc_spine.
        apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
    }
    eapply expr_total_formula_tapp_tlete_assoc_spine; eauto.
Qed.

Ltac solve_tapp_tlete_guard_assoc_spine :=
  match goal with
  | Hguard : ?m ⊨ context_ty_wf_formula
        (denot_relevant_env ?Σ ?τ
          (tapp_tm_fvar_spine (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (?z :: ?zs))) ?τ
      ∧ ?m ⊨ basic_world_formula
          (denot_relevant_env ?Σ ?τ
            (tapp_tm_fvar_spine (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (?z :: ?zs)))
        ∧ ?m ⊨ expr_basic_typing_formula
            (denot_relevant_env ?Σ ?τ
              (tapp_tm_fvar_spine (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (?z :: ?zs)))
            (tapp_tm_fvar_spine (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (?z :: ?zs))
            (erase_ty ?τ)
          ∧ ?m ⊨ expr_total_formula
              (tapp_tm_fvar_spine (tlete ?e1 (tapp_tm ?e2 (vfvar ?y))) (?z :: ?zs))
    |- ?m ⊨ context_ty_wf_formula
        (denot_relevant_env ?Σ ?τ
          (tapp_tm_fvar_spine (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs))) ?τ
      ∧ ?m ⊨ basic_world_formula
          (denot_relevant_env ?Σ ?τ
            (tapp_tm_fvar_spine (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs)))
        ∧ ?m ⊨ expr_basic_typing_formula
            (denot_relevant_env ?Σ ?τ
              (tapp_tm_fvar_spine (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs)))
            (tapp_tm_fvar_spine (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs))
            (erase_ty ?τ)
          ∧ ?m ⊨ expr_total_formula
              (tapp_tm_fvar_spine (tapp_tm (tlete ?e1 ?e2) (vfvar ?y)) (?z :: ?zs)) =>
      let Hassoc := fresh "Hguard_assoc_spine" in
      pose proof (denot_ty_lvar_guard_tapp_tlete_assoc_spine
        Σ τ e1 e2 y z zs m ltac:(eassumption)
        ltac:(repeat rewrite res_models_and_iff; exact Hguard)) as Hassoc;
      repeat rewrite res_models_and_iff in Hassoc;
      exact Hassoc
  end.

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
    + solve_tapp_tlete_guard_assoc_spine.
    + exact Htrue.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τr|τx τr];
      cbn [denot_ty_lvar_gas] in Hm |- *;
      repeat rewrite res_models_and_iff in Hm |- *;
      destruct Hm as [Hguard Hbody];
      split.
    + solve_tapp_tlete_guard_assoc_spine.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_map_same_fv m φsrc)
      end.
      * apply set_eq. intros a.
        normalize_formula_fv.
        rewrite !tm_shift_fv;
        try rewrite <- fv_tm_tapp_tlete_assoc_spine;
        try rewrite <- tm_lvars_tapp_tlete_assoc_spine;
        tauto.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTOver b φ)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full.
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
          normalize_formula_fv.
          try rewrite fv_tm_tapp_tlete_assoc_spine.
          exact Hscope_src.
        }
        eapply res_models_impl_intro; [exact Hscope_tgt_outer|].
        intros Hbasic.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_inner : formula_scoped_in_world my G)
        end.
        { eapply formula_scoped_impl_r. exact Hscope_tgt_outer. }
        eapply res_models_impl_intro; [exact Hscope_tgt_inner|].
        intros Hresult.
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hinner.
        eapply res_models_impl_elim; [exact Hinner|].
        eapply expr_result_formula_tapp_tlete_assoc_spine_rev.
        -- rewrite fv_tm_tapp_tlete_assoc_spine.
           eapply denot_ty_lvar_guard_wfworld_closed_on_term_le.
           ++ eapply res_extend_by_le; exact Hext.
           ++ repeat rewrite res_models_and_iff. exact Hguard.
        -- exact Hlc.
        -- exact Hresult.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc_spine.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_map_same_fv m φsrc)
      end.
      * apply set_eq. intros a.
        normalize_formula_fv.
        rewrite !tm_shift_fv;
        try rewrite <- fv_tm_tapp_tlete_assoc_spine;
        try rewrite <- tm_lvars_tapp_tlete_assoc_spine;
        tauto.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnder b φ)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full.
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
          normalize_formula_fv.
          try rewrite fv_tm_tapp_tlete_assoc_spine.
          exact Hscope_src.
        }
        eapply res_models_impl_intro; [exact Hscope_tgt_outer|].
        intros Hbasic.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_inner : formula_scoped_in_world my G)
        end.
        { eapply formula_scoped_impl_r. exact Hscope_tgt_outer. }
        eapply res_models_impl_intro; [exact Hscope_tgt_inner|].
        intros Hresult.
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hinner.
        eapply res_models_impl_elim; [exact Hinner|].
        eapply expr_result_formula_tapp_tlete_assoc_spine_rev.
        -- rewrite fv_tm_tapp_tlete_assoc_spine.
           eapply denot_ty_lvar_guard_wfworld_closed_on_term_le.
           ++ eapply res_extend_by_le; exact Hext.
           ++ repeat rewrite res_models_and_iff. exact Hguard.
        -- exact Hlc.
        -- exact Hresult.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc_spine.
    + repeat rewrite res_models_and_iff in Hbody |- *.
      destruct Hbody as [H1 H2].
      split; [eapply IH | eapply IH]; eauto.
    + solve_tapp_tlete_guard_assoc_spine.
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
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_or_l.
        eapply formula_scoped_and_r. exact Hscope_full.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTUnion τ1 τ2)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full.
        cbn [denot_ty_lvar_gas] in Hscope_full.
        eapply formula_scoped_or_r.
        eapply formula_scoped_and_r. exact Hscope_full.
      * intros Hτ1. eapply IH; eauto.
      * intros Hτ2. eapply IH; eauto.
      * exact Hbody.
    + solve_tapp_tlete_guard_assoc_spine.
    + pose proof (res_models_fuel_scoped _ _ _ Hbody) as Hscope.
      apply res_models_plus_iff in Hbody as
        [m1 [m2 [Hdef [Hle [H1 H2]]]]].
      * eapply res_models_plus_intro_from_models; [exact Hle| |].
        -- eapply IH; eauto.
        -- eapply IH; eauto.
      * exact Hscope.
    + solve_tapp_tlete_guard_assoc_spine.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_full_world_map m φsrc)
      end.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTArrow τx τr)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full.
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
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full_my.
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
        eapply res_models_impl_intro; [exact Hopened_scope_my|].
        intros Hbasic.
        pose proof (formula_scoped_impl_r _ _ _ Hopened_scope_my)
          as Hscope_tgt_inner.
        eapply res_models_impl_intro; [exact Hscope_tgt_inner|].
        intros Harg.
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
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hinner.
        pose proof (res_models_impl_elim _ _ _ Hinner Harg) as Hres.
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
    + solve_tapp_tlete_guard_assoc_spine.
    + lazymatch type of Hbody with
      | m ⊨ FForall ?φsrc => eapply (res_models_forall_full_world_map m φsrc)
      end.
      * pose proof (denot_ty_lvar_gas_scope_from_relevant_guard
          (S gas) Σ (CTWand τx τr)
          (tapp_tm_fvar_spine (tapp_tm (tlete e1 e2) (vfvar y)) (z :: zs)) m
          ltac:(repeat rewrite res_models_and_iff;
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full.
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
            solve_tapp_tlete_guard_assoc_spine)) as Hscope_full_my.
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
        normalize_formula_fv.
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
          normalize_formula_fv.
          try rewrite fv_tm_tapp_tm_tlete_assoc.
          exact Hscope_src.
        }
        eapply res_models_impl_intro; [exact Hscope_tgt_outer|].
        intros Hbasic.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_inner : formula_scoped_in_world my G)
        end.
        { eapply formula_scoped_impl_r. exact Hscope_tgt_outer. }
        eapply res_models_impl_intro; [exact Hscope_tgt_inner|].
        intros Hresult.
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hinner.
        eapply res_models_impl_elim; [exact Hinner|].
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
        normalize_formula_fv.
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
          normalize_formula_fv.
          try rewrite fv_tm_tapp_tm_tlete_assoc.
          exact Hscope_src.
        }
        eapply res_models_impl_intro; [exact Hscope_tgt_outer|].
        intros Hbasic.
        match goal with
        | |- my ⊨ ?G =>
            assert (Hscope_tgt_inner : formula_scoped_in_world my G)
        end.
        { eapply formula_scoped_impl_r. exact Hscope_tgt_outer. }
        eapply res_models_impl_intro; [exact Hscope_tgt_inner|].
        intros Hresult.
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hinner.
        eapply res_models_impl_elim; [exact Hinner|].
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
        eapply res_models_impl_intro; [exact Hopened_scope_my|].
        intros Hbasic.
        pose proof (formula_scoped_impl_r _ _ _ Hopened_scope_my)
          as Hscope_tgt_inner.
        eapply res_models_impl_intro; [exact Hscope_tgt_inner|].
        intros Harg.
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
        pose proof (res_models_impl_elim _ _ _ Hopen Hbasic) as Hinner.
        pose proof (res_models_impl_elim _ _ _ Hinner Harg) as Hres.
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
Lemma tlet_wand_open_body_transport
    gas (Σ : lty_env) (T1 : ty) (e1 e2 : tm)
    (m mx my myx : WfWorldT) (Fx : FiberExtensionT)
    (x y : atom) τx τr :
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
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    fv_cty τx ∪ fv_cty τr ∪ {[x]} ->
  x <> y ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  LVFree y ∉ dom
    (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2) : lty_env) ->
  LVFree y ∉ dom
    (denot_relevant_env (<[LVFree x := T1]> Σ)
      (CTWand τx τr) (e2 ^^ x) : lty_env) ->
  LVFree y ∉ dom (<[LVFree x := T1]> Σ : lty_env) ->
  lc_tm (e2 ^^ x) ->
  y ∉ fv_tm (tapp_tm (tm_shift 0 (e2 ^^ x)) (vbvar 0)) ->
  basic_context_ty_lvars
    (dom (<[LVFree x := T1]> Σ : lty_env) : gset logic_var)
    (CTWand τx τr) ->
  m ⊑ my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_extend_by my Fx myx ->
  formula_scoped_in_world my
    (formula_open 0 y
      (denot_wand_body_formula gas
        (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
        τx τr (tlete e1 e2))) ->
  myx ⊨ formula_open 0 y
    (denot_wand_body_formula gas
      (denot_relevant_env (<[LVFree x := T1]> Σ)
        (CTWand τx τr) (e2 ^^ x))
      τx τr (e2 ^^ x)) ->
  my ⊨ formula_open 0 y
    (denot_wand_body_formula gas
      (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
      τx τr (tlete e1 e2)).
Proof.
  intros IH HΣ He1 Hlet HFx Htotal Hbase_world Hfresh
    Hy_support Hxy Hyτx Hyτr Hy_target_rel Hy_source_rel Hy_insert
    Hlc_e2x Hy_body_fv Hbasic_src_rel
    Hle Hdom_my HmyFx Hscope_target Hbody.
  unfold denot_wand_body_formula in Hscope_target, Hbody |- *.
  rewrite formula_open_impl in Hbody |- *.
  rewrite formula_open_wand in Hbody |- *.
  rewrite ?formula_open_basic_world_bind0 in Hbody |- * by tlet_support_solver.
  eapply res_models_impl_intro; [exact Hscope_target|].
  intros Hbasic.
  pose proof (res_models_impl_elim _ _ _ Hbody
    ltac:(eapply res_models_extend_mono; [exact HmyFx | exact Hbasic]))
    as Hsource_wand.
  pose proof (formula_scoped_impl_r _ _ _ Hscope_target) as Hscope_target_wand.
  eapply res_models_wand_intro; [exact Hscope_target_wand|].
  intros n Hc Harg.
  assert (Hxτx : LVFree x ∉ context_ty_lvars τx).
  {
    cbn [context_ty_lvars context_ty_lvars_at] in Hfresh.
    fast_set_solver!!.
  }
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
  { apply (proj2 (lc_lvars_no_bv _)). exact HΣ. }
  assert (HyΣ : LVFree y ∉ (dom (Σ : gmap logic_var ty) : gset logic_var)).
  {
    intros HyΣ.
    assert (Hyfv : y ∈ lvars_fv (dom (Σ : gmap logic_var ty) : gset logic_var)).
    { apply lvars_fv_elem. exact HyΣ. }
    apply Hy_support.
    fast_set_solver!!.
  }
  assert (Hclosed_Σy : lty_env_closed (<[LVFree y := erase_ty τx]> Σ)).
  { apply lty_env_closed_insert_free. exact HΣ. }
  assert (He1_Σy :
    lty_env_to_atom_env (<[LVFree y := erase_ty τx]> Σ) ⊢ₑ e1 ⋮ T1).
  {
    eapply basic_typing_env_agree_tm; [exact He1|].
    intros a Ha.
    rewrite !lty_env_to_atom_env_lookup.
    change (((<[LVFree y := erase_ty τx]> (Σ : gmap logic_var ty))
      : gmap logic_var ty) !! LVFree a =
      (Σ : gmap logic_var ty) !! LVFree a).
    rewrite lookup_insert_ne; [reflexivity|].
    intros Hbad. inversion Hbad. subst a.
    apply Hy_support. fast_set_solver!!.
  }
  assert (Hlet_Σy :
    lty_env_to_atom_env (<[LVFree y := erase_ty τx]> Σ) ⊢ₑ
      tlete e1 (tapp_tm e2 (vfvar y)) ⋮ erase_ty (cty_open 0 y τr)).
  {
    rewrite cty_open_preserves_erasure.
    apply basic_typing_tapp_tm_tlete_assoc_rev.
    eapply basic_typing_tapp_tm.
    - eapply basic_typing_env_agree_tm; [exact Hlet|].
      intros a Ha.
      rewrite !lty_env_to_atom_env_lookup.
      change (((<[LVFree y := erase_ty τx]> (Σ : gmap logic_var ty))
        : gmap logic_var ty) !! LVFree a =
        (Σ : gmap logic_var ty) !! LVFree a).
      rewrite lookup_insert_ne; [reflexivity|].
      intros Hbad. inversion Hbad. subst a.
      apply Hy_support. fast_set_solver!!.
    - constructor.
      rewrite lty_env_to_atom_env_lookup.
      change (((<[LVFree y := erase_ty τx]> (Σ : gmap logic_var ty))
        : gmap logic_var ty) !! LVFree y = Some (erase_ty τx)).
      rewrite lookup_insert.
      destruct (decide (LVFree y = LVFree y)); [reflexivity|congruence].
  }
  assert (Htotal_prod :
    res_product n0 my Hc0_my ⊨ expr_total_formula e1).
  {
    eapply res_models_kripke.
    - etransitivity.
      + exact Hle.
      + apply res_product_le_r_tlet.
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
      + apply res_product_le_r_tlet.
      + eapply res_models_kripke; [exact Hle|exact Hbase_world].
    - eapply res_models_kripke.
      + apply res_product_le_r_tlet.
      + rewrite formula_open_basic_world_formula in Hbasic.
        rewrite lty_env_open_one_bound0_singleton in Hbasic.
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
      apply elem_of_union in Hdom as [Hyx|HxΣ].
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
  eapply res_models_kripke.
  - eapply res_product_le_mono.
    + apply res_restrict_le.
    + reflexivity.
  - exact Htarget_body_small.
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
  assert (Hmx_zero : mx ⊨ denot_ty_lvar_gas 0
    (<[LVFree x := T1]> Σ) (CTWand τx τr) (e2 ^^ x)).
  {
    cbn [denot_ty_lvar_gas].
    rewrite res_models_and_iff. split.
    - repeat rewrite res_models_and_iff. exact Hmx_guard.
    - cbn [res_models res_models_fuel formula_measure].
      split; [apply formula_scoped_true_iff; exact I | exact I].
  }
  pose proof (tlet_intro_denotation_gas_zero_support
    Σ T1 e1 e2 m mx Fx x (CTWand τx τr)
    HΣ He1 Hlet HFx Htotal Hbase_world HxΣ Hxτ Hext Hmx_zero)
    as Hm_zero.
  assert (Hguard_m :
    m ⊨ FAnd
      (context_ty_wf_formula
        (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
        (CTWand τx τr))
      (FAnd
        (basic_world_formula
          (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2)))
        (FAnd
          (expr_basic_typing_formula
            (denot_relevant_env Σ (CTWand τx τr) (tlete e1 e2))
            (tlete e1 e2) (erase_ty (CTWand τx τr)))
          (expr_total_formula (tlete e1 e2))))).
  {
    cbn [denot_ty_lvar_gas] in Hm_zero.
    rewrite res_models_and_iff in Hm_zero.
    exact (proj1 Hm_zero).
  }
  assert (Hdenot_scope_m :
    formula_scoped_in_world m
      (denot_ty_lvar_gas (S gas) Σ (CTWand τx τr) (tlete e1 e2))).
  {
    eapply denot_ty_lvar_gas_scope_from_relevant_guard.
    exact Hguard_m.
  }
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
  {
    cbn [denot_ty_lvar_gas] in Hdenot_scope_m.
    eapply formula_scoped_and_r. exact Hdenot_scope_m.
  }
  split.
  - repeat rewrite res_models_and_iff in Hguard_m.
    exact Hguard_m.
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
	    pose proof (formula_scoped_forall_body m _ Hbody_scope_m)
	      as Hforall_body_scope_m.
	    assert (Hy_my : y ∈ world_dom (my : WorldT)).
	    { rewrite Hdom_my. set_solver. }
	    eapply formula_scoped_open_res_le;
	      [exact Hforall_body_scope_m | exact Hle | exact Hy_my].
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
	  eapply tlet_wand_open_body_transport; eauto.
Qed.

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
