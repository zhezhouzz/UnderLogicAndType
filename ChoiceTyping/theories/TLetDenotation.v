(** * ChoiceTyping.TLetDenotation

    Thin denotation-level interface for the [tlet] soundness case. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Export TLetTotal RegularDenotation.
From ChoiceTyping Require Import Naming ResultWorldBridge ResultWorldFreshForall.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

(** Continuation-style expression-result principle for [tlet].

    This is the stabilized version of the earlier fibered statement.  The
    continuation [Q] is kept abstract: the [tlet] reduction should not know
    whether the result type later wraps [Q ν] in fibers, modalities, or other
    type constructors.

    The exact-domain premise [world_dom m = dom Σ] is essential.  [FExprContIn]
    fibers over [dom Σ], while [let_result_world_on] extends the whole input
    world; these line up definitionally only when the input world is already
    minimal for [Σ].  The strong whole-let totality premise is enough to recover
    the body totality needed by the exact-domain bridge; do not reintroduce
    separate may-total assumptions here.  Do not split this lemma by the shape of
    the result type; it is meant to be a type-constructor-independent bridge used
    by the [tlet] case. *)
Lemma FExprCont_tlet_reduction
    (Σ : gmap atom ty) (T1 T2 : ty)
    (m : WfWorld) e1 e2 (x : atom) (Q : atom → FormulaQ)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ fv_tm e2 →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) (tlete e1 e2) m →
  (∀ ν, formula_fv (Q ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) Q →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ FExprContIn (<[x := T1]> Σ) (e2 ^^ x) Q ↔
  m ⊨ FExprContIn Σ (tlete e1 e2) Q.
Proof.
  intros He1 Hlet Hxe2 Hdom Hclosed Htotal_let HQfv HQrename.
  set (m1 := let_result_world_on e1 x m Hfresh Hresult).
  assert (HxΣ : x ∉ dom Σ).
  { rewrite <- Hdom. exact Hfresh. }
  assert (He2 : <[x := T1]> Σ ⊢ₑ e2 ^^ x ⋮ T2).
  { eapply basic_typing_tlete_body_for_fresh; eauto; set_solver. }
  assert (Hdom_m1 : world_dom (m1 : World) = dom (<[x := T1]> Σ)).
  {
    subst m1. rewrite let_result_world_on_dom, Hdom, dom_insert_L.
    set_solver.
  }
  assert (Hfv1 : fv_tm e1 ⊆ dom Σ).
  { apply basic_typing_contains_fv_tm in He1. exact He1. }
  assert (Hlc1 : lc_tm e1).
  { apply typing_tm_lc with (Γ := Σ) (T := T1). exact He1. }
  assert (Hclosed_m1 :
    world_store_closed_on (dom (<[x := T1]> Σ)) m1).
  {
    subst m1. rewrite dom_insert_L.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) by set_solver.
    eapply let_result_world_on_store_closed_on_insert.
    - exact HxΣ.
    - exact Hclosed.
    - intros σ vx Hσ Hsteps.
      assert (Hclosed_fv : world_store_closed_on (fv_tm e1) m).
      { eapply world_store_closed_on_mono; [exact Hfv1 | exact Hclosed]. }
      eapply (steps_closed_result_of_restrict_world
        (fv_tm e1) e1 m (store_restrict σ (fv_tm e1)) vx).
      + rewrite Hdom. exact Hfv1.
      + set_solver.
      + exact Hlc1.
      + exact Hclosed_fv.
      + exists σ. split; [exact Hσ | reflexivity].
      + replace (store_restrict (store_restrict σ (fv_tm e1)) (fv_tm e1))
          with (store_restrict σ (fv_tm e1)).
        * exact Hsteps.
        * store_norm. reflexivity.
  }
  assert (Htotal2 :
    expr_total_on (dom (<[x := T1]> Σ)) (e2 ^^ x) m1).
  {
    subst m1. rewrite dom_insert_L.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) by set_solver.
    eapply (expr_total_on_tlete_elim_body_strong
      (dom Σ) e1 e2 x m Hfresh Hresult).
    - rewrite Hdom. set_solver.
    - exact HxΣ.
    - exact Hxe2.
    - exact Hclosed.
    - eapply typing_tm_lc; eauto.
    - exact Htotal_let.
  }
  assert (HQfv_insert :
    ∀ ν, formula_fv (Q ν) ⊆ dom (<[x := T1]> Σ) ∪ {[ν]}).
  {
    intros ν. specialize (HQfv ν). rewrite dom_insert_L. set_solver.
  }
  assert (HQrename_insert :
    formula_family_rename_stable_on (dom (<[x := T1]> Σ)) Q).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb.
    apply HQrename; rewrite dom_insert_L in *; set_solver.
  }
  assert (Hdecompose_side :
    ∀ ν Hfreshν_body Hresultν_body Hfreshν_tlet Hresultν_tlet,
      ν ∉ dom Σ ∪ {[x]} ∪ fv_tm e2 →
      res_restrict
        (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
        (world_dom (m : World) ∪ {[ν]}) =
      let_result_world_on (tlete e1 e2) ν m Hfreshν_tlet Hresultν_tlet).
  {
    intros ν Hfreshν_body Hresultν_body Hfreshν_tlet Hresultν_tlet Hνfresh.
    unfold m1.
    rewrite (let_result_world_on_tlete_decompose
      (dom Σ) e1 e2 x ν m
      Hfresh Hresult Hfreshν_body Hresultν_body
      Hfreshν_tlet Hresultν_tlet).
    - reflexivity.
    - apply basic_typing_contains_fv_tm in Hlet. exact Hlet.
    - apply basic_typing_contains_fv_tm in Hlet. simpl in Hlet. set_solver.
    - exact Hfreshν_tlet.
    - rewrite Hdom. set_solver.
    - intros σ Hσ. exact (proj1 (Hclosed σ Hσ)).
    - intros σ Hσ. exact (proj2 (Hclosed σ Hσ)).
    - intros σ vx Hσ Hsteps.
      eapply steps_closed_result.
      + eapply (msubst_closed_tm_of_restrict_world (dom Σ) e1 m σ).
        * rewrite Hdom. set_solver.
        * exact Hfv1.
        * exact Hlc1.
        * exact Hclosed.
        * exists σ. split; [exact Hσ |].
          rewrite (store_restrict_idemp σ (dom Σ)).
          -- reflexivity.
          -- pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
             set_solver.
      + exact Hsteps.
    - intros σ Hσ.
      pose proof (typing_tm_lc _ _ _ Hlet) as Hlclet.
      apply lc_lete_iff_body in Hlclet as [_ Hbodye2].
      eapply body_tm_msubst.
      + exact (proj1 (Hclosed σ Hσ)).
      + exact (proj2 (Hclosed σ Hσ)).
      + exact Hbodye2.
  }
  split.
  - intros Hcont.
    pose proof (proj1
      (FExprContIn_iff_let_result_world_on_exact_domain
        (<[x := T1]> Σ) T2 (e2 ^^ x) Q m1
        He2 Hdom_m1 Hclosed_m1 Htotal2 HQfv_insert HQrename_insert)
      Hcont) as [L [HLdom Hbody]].
    apply (proj2
      (FExprContIn_iff_let_result_world_on_exact_domain
        Σ T2 (tlete e1 e2) Q m
        Hlet Hdom Hclosed Htotal_let HQfv HQrename)).
    exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e2).
    split; [set_solver |].
    intros ν Hν Hfreshν_tlet Hresultν_tlet.
    assert (Hfreshν_body : ν ∉ world_dom (m1 : World)).
    {
      subst m1. rewrite let_result_world_on_dom, Hdom. set_solver.
    }
    assert (Hresultν_body :
      ∀ σ, (m1 : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm (e2 ^^ x)))
          (e2 ^^ x) →* tret vx).
    {
      eapply expr_total_on_to_fv_result; eauto.
    }
    pose proof (Hbody ν ltac:(set_solver) Hfreshν_body Hresultν_body)
      as Hnested.
    pose proof (proj1 (res_models_minimal_on
      (dom Σ ∪ {[ν]})
      (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
      (Q ν) (HQfv ν)) Hnested) as Hnested_min.
    replace (dom Σ ∪ {[ν]}) with (world_dom (m : World) ∪ {[ν]})
      in Hnested_min by (rewrite Hdom; reflexivity).
    rewrite (Hdecompose_side ν Hfreshν_body Hresultν_body
      Hfreshν_tlet Hresultν_tlet ltac:(set_solver)) in Hnested_min.
    exact Hnested_min.
  - intros Hcont.
    pose proof (proj1
      (FExprContIn_iff_let_result_world_on_exact_domain
        Σ T2 (tlete e1 e2) Q m
        Hlet Hdom Hclosed Htotal_let HQfv HQrename)
      Hcont) as [L [HLdom Hwhole]].
    apply (proj2
      (FExprContIn_iff_let_result_world_on_exact_domain
        (<[x := T1]> Σ) T2 (e2 ^^ x) Q m1
        He2 Hdom_m1 Hclosed_m1 Htotal2 HQfv_insert HQrename_insert)).
    exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e2).
    split; [rewrite dom_insert_L; set_solver |].
    intros ν Hν Hfreshν_body Hresultν_body.
    assert (Hfreshν_tlet : ν ∉ world_dom (m : World)).
    { rewrite Hdom. set_solver. }
    assert (Hresultν_tlet :
      ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm (tlete e1 e2)))
          (tlete e1 e2) →* tret vx).
    {
      eapply expr_total_on_to_fv_result; eauto.
    }
    pose proof (Hwhole ν ltac:(set_solver) Hfreshν_tlet Hresultν_tlet)
      as Hwholeν.
    assert (Hrestrict :
      res_restrict
        (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
        (dom Σ ∪ {[ν]}) ⊨ Q ν).
    {
      replace (dom Σ ∪ {[ν]}) with (world_dom (m : World) ∪ {[ν]})
        by (rewrite Hdom; reflexivity).
      rewrite (Hdecompose_side ν Hfreshν_body Hresultν_body
        Hfreshν_tlet Hresultν_tlet ltac:(set_solver)).
      exact Hwholeν.
    }
    exact (proj2 (res_models_minimal_on
      (dom Σ ∪ {[ν]})
      (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
      (Q ν) (HQfv ν)) Hrestrict).
Qed.

Lemma denot_ty_fuel_tlet_reduction_formula_on_arrow_case
    gas (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τx τ :
  Δ ⊢ₑ e1 ⋮ T1 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTArrow τx τ) →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  cty_measure (CTArrow τx τ) <= S gas →
  basic_choice_ty (dom Δ) (CTArrow τx τ) →
  let_result_world_on e1 x m Hfresh Hresult ⊨
    fresh_forall (dom (<[x:=T1]> Δ)) (fun y =>
      FImpl
        (denot_ty_fuel gas (<[y:=erase_ty τx]> (<[x:=T1]> Δ)) τx
          (tret (vfvar y)))
        (denot_ty_fuel gas (<[y:=erase_ty τx]> (<[x:=T1]> Δ))
          ({0 ~> y} τ) (tapp_tm (e2 ^^ x) (vfvar y)))) <->
  m ⊨
    fresh_forall (dom Δ) (fun y =>
      FImpl
        (denot_ty_fuel gas (<[y:=erase_ty τx]> Δ) τx
          (tret (vfvar y)))
        (denot_ty_fuel gas (<[y:=erase_ty τx]> Δ)
          ({0 ~> y} τ) (tapp_tm (tlete e1 e2) (vfvar y)))).
Proof.
Admitted.

Lemma denot_ty_fuel_tlet_reduction_formula_on_wand_case
    gas (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τx τ :
  Δ ⊢ₑ e1 ⋮ T1 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTWand τx τ) →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  cty_measure (CTWand τx τ) <= S gas →
  basic_choice_ty (dom Δ) (CTWand τx τ) →
  let_result_world_on e1 x m Hfresh Hresult ⊨
    fresh_forall (dom (<[x:=T1]> Δ)) (fun y =>
      FWand
        (denot_ty_fuel gas (<[y:=erase_ty τx]> (<[x:=T1]> Δ)) τx
          (tret (vfvar y)))
        (denot_ty_fuel gas (<[y:=erase_ty τx]> (<[x:=T1]> Δ))
          ({0 ~> y} τ) (tapp_tm (e2 ^^ x) (vfvar y)))) <->
  m ⊨
    fresh_forall (dom Δ) (fun y =>
      FWand
        (denot_ty_fuel gas (<[y:=erase_ty τx]> Δ) τx
          (tret (vfvar y)))
        (denot_ty_fuel gas (<[y:=erase_ty τx]> Δ)
          ({0 ~> y} τ) (tapp_tm (tlete e1 e2) (vfvar y)))).
Proof.
Admitted.

Lemma denot_ty_fuel_intro gas Σ τ e m :
  basic_choice_ty (dom Σ) τ →
  Σ ⊢ₑ e ⋮ erase_ty τ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  m ⊨ denot_ty_fuel_body gas Σ τ e →
  dom Σ ⊆ world_dom (m : World) →
  m ⊨ denot_ty_fuel gas Σ τ e.
Proof.
  intros Hbasic Htyped Hclosed Htotal Hbody Hdom.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m
    (denot_ty_fuel_body gas Σ τ e) Hbody) as Hbody_scope.
  rewrite denot_ty_fuel_unfold.
  unfold denot_ty_obligations.
  eapply res_models_with_store_and_intro.
  - unfold formula_scoped_in_world.
    simpl.
    unfold formula_scoped_in_world in Hbody_scope. simpl in Hbody_scope.
    set_solver.
  - eapply res_models_with_store_pure_intro.
    + unfold formula_scoped_in_world. simpl. set_solver.
    + split; assumption.
  - eapply res_models_with_store_and_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold stale, stale_logic_qualifier. simpl. set_solver.
    + eapply res_models_with_store_resource_atom_intro.
      * unfold formula_scoped_in_world. simpl.
        unfold stale, stale_logic_qualifier. simpl. set_solver.
      * eapply world_closed_on_le.
        -- apply res_restrict_le.
        -- exact Hclosed.
    + eapply res_models_with_store_and_intro.
      * unfold formula_scoped_in_world. simpl.
        unfold stale, stale_logic_qualifier. simpl.
        unfold formula_scoped_in_world in Hbody_scope. simpl in Hbody_scope.
        set_solver.
      * eapply res_models_with_store_store_resource_atom_intro.
        -- unfold formula_scoped_in_world. simpl.
           unfold stale, stale_logic_qualifier. simpl. set_solver.
        -- change (expr_total_with_store (dom Σ) e
             (store_restrict ∅ (dom Σ)) (res_restrict m (dom Σ))).
           rewrite store_restrict_empty.
           apply expr_total_with_store_empty_restrict.
           exact Htotal.
      * exact Hbody.
Qed.

Lemma denot_ty_fuel_body_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  m ⊨ denot_ty_fuel_body gas Σ τ e.
Proof.
  intros Hm.
  rewrite denot_ty_fuel_unfold in Hm.
  unfold denot_ty_obligations in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  exact Hm.
Qed.

Lemma let_result_world_on_world_closed_on_insert_from_basic
    (Δ : gmap atom ty) T e x (m : WfWorld) Hfresh Hresult :
  Δ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  x ∉ dom Δ →
  world_closed_on (dom (<[x := T]> Δ))
    (let_result_world_on e x m Hfresh Hresult).
Proof.
  intros Htyped Hdom Hclosed Hx.
  eapply world_store_closed_on_world_closed_on.
  rewrite dom_insert_L.
  replace ({[x]} ∪ dom Δ) with (dom Δ ∪ {[x]}) by set_solver.
  eapply let_result_world_on_store_closed_on_insert.
  - exact Hx.
  - exact Hclosed.
  - intros σ vx Hσ Hsteps.
    pose proof (basic_typing_contains_fv_tm Δ e T Htyped) as Hfv.
    pose proof (typing_tm_lc Δ e T Htyped) as Hlc.
    assert (Hclosed_fv : world_store_closed_on (fv_tm e) m).
    { eapply world_store_closed_on_mono; [exact Hfv | exact Hclosed]. }
    eapply (steps_closed_result_of_restrict_world
      (fv_tm e) e m (store_restrict σ (fv_tm e)) vx).
    + rewrite Hdom. exact Hfv.
    + set_solver.
    + exact Hlc.
    + exact Hclosed_fv.
    + exists σ. split; [exact Hσ | reflexivity].
    + replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
        with (store_restrict σ (fv_tm e)).
      * exact Hsteps.
      * store_norm. reflexivity.
Qed.

Lemma denot_ty_fuel_tlet_reduction_full_from_body_on gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τ2 :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) τ2 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  (let_result_world_on e1 x m Hfresh Hresult
      ⊨ denot_ty_fuel_body gas (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_fuel_body gas Δ τ2 (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel gas (<[x:=T1]> Δ) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel gas Δ τ2 (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet Hformula_iff.
  assert (Hbody_basic : basic_choice_ty (dom (<[x:=T1]> Δ)) τ2).
  { eapply basic_choice_ty_mono; [| exact Hbasicτ].
    rewrite dom_insert_L. set_solver. }
  assert (Hbody_typed : <[x:=T1]> Δ ⊢ₑ e2 ^^ x ⋮ erase_ty τ2).
  { eapply basic_typing_tlete_body_for_fresh; eauto. }
  assert (Hbody_closed :
    world_closed_on (dom (<[x:=T1]> Δ))
      (let_result_world_on e1 x m Hfresh Hresult)).
  {
    eapply let_result_world_on_world_closed_on_insert_from_basic; eauto.
    set_solver.
  }
  assert (Hbody_total :
    expr_total_on (dom (<[x:=T1]> Δ)) (e2 ^^ x)
      (let_result_world_on e1 x m Hfresh Hresult)).
  {
    rewrite dom_insert_L.
    replace ({[x]} ∪ dom Δ) with (dom Δ ∪ {[x]}) by set_solver.
    eapply (expr_total_on_tlete_elim_body_strong
      (dom Δ) e1 e2 x m Hfresh Hresult).
    - rewrite Hdom. set_solver.
    - set_solver.
    - set_solver.
    - exact Hclosed.
    - eapply typing_tm_lc; eauto.
    - exact Htotal.
  }
  assert (Htarget_closed : world_closed_on (dom Δ) m).
  { eapply world_store_closed_on_world_closed_on. exact Hclosed. }
  split; intros Hmodel.
  - eapply denot_ty_fuel_intro; eauto.
    apply Hformula_iff.
    eapply denot_ty_fuel_body_of_formula. exact Hmodel.
    rewrite Hdom. set_solver.
  - eapply denot_ty_fuel_intro; eauto.
    apply Hformula_iff.
    eapply denot_ty_fuel_body_of_formula. exact Hmodel.
    rewrite let_result_world_on_dom, Hdom, dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_tlet_reduction_body_from_full_on gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τ2 :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) τ2 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  (let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel gas (<[x:=T1]> Δ) τ2 (e2 ^^ x)
   <->
   m ⊨ denot_ty_fuel gas Δ τ2 (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel_body gas (<[x:=T1]> Δ) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel_body gas Δ τ2 (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet Hresult_iff.
  split; intros Hformula.
  - apply denot_ty_fuel_body_of_formula.
    apply (proj1 Hresult_iff).
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasicτ].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_tlete_body_for_fresh; eauto.
    + eapply let_result_world_on_world_closed_on_insert_from_basic; eauto.
      set_solver.
    + rewrite dom_insert_L.
      replace ({[x]} ∪ dom Δ) with (dom Δ ∪ {[x]}) by set_solver.
      eapply (expr_total_on_tlete_elim_body_strong
        (dom Δ) e1 e2 x m Hfresh Hresult).
      * rewrite Hdom. set_solver.
      * set_solver.
      * set_solver.
      * exact Hclosed.
      * eapply typing_tm_lc; eauto.
      * exact Htotal.
    + exact Hformula.
    + rewrite let_result_world_on_dom, Hdom, dom_insert_L. set_solver.
  - apply denot_ty_fuel_body_of_formula.
    apply (proj2 Hresult_iff).
    eapply denot_ty_fuel_intro.
    + exact Hbasicτ.
    + exact Hlet.
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + exact Hformula.
    + rewrite Hdom. set_solver.
Qed.

Lemma denot_ty_fuel_tlet_reduction_full_on_over_case gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    b φ :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTOver b φ) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTOver b φ) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel (S gas) (<[x:=T1]> Δ) (CTOver b φ) (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel (S gas) Δ (CTOver b φ) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet.
  eapply denot_ty_fuel_tlet_reduction_full_from_body_on; eauto.
  cbn [denot_ty_fuel_body fv_cty erase_ty].
  inversion Hbasicτ as [D b' φ' Hqbody| | | | | |]; subst.
  assert (Hφ : qual_dom φ ⊆ dom Δ).
  { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
  rewrite (FExprContIn_post_eq_at_fresh
    (<[x:=T1]> Δ) (e2 ^^ x)
    (fun ν =>
      let φν := qual_open_atom 0 ν φ in
      FAnd
        (basic_world_formula (<[ν:=TBase b]> (<[x:=T1]> Δ))
          ({[ν]} ∪ qual_dom φν))
        (fib_vars (qual_dom φν)
          (FOver (FTypeQualifier φν))))
    (fun ν =>
      let φν := qual_open_atom 0 ν φ in
      FAnd
        (basic_world_formula (<[ν:=TBase b]> Δ)
          ({[ν]} ∪ qual_dom φν))
        (fib_vars (qual_dom φν)
          (FOver (FTypeQualifier φν))))).
  2:{
    eapply (denot_refinement_over_cont_insert_fresh_eq
      (dom Δ : aset) Δ x T1 b φ); [set_solver | reflexivity].
  }
  eapply (FExprCont_tlet_reduction Δ T1 (TBase b) m e1 e2 x); eauto.
  - set_solver.
  - eapply denot_refinement_over_cont_fv_subset. exact Hφ.
  - eapply denot_refinement_over_cont_rename_stable. exact Hφ.
Qed.

Lemma denot_ty_fuel_tlet_reduction_full_on_under_case gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    b φ :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTUnder b φ) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTUnder b φ) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel (S gas) (<[x:=T1]> Δ) (CTUnder b φ) (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel (S gas) Δ (CTUnder b φ) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet.
  eapply denot_ty_fuel_tlet_reduction_full_from_body_on; eauto.
  cbn [denot_ty_fuel_body fv_cty erase_ty].
  inversion Hbasicτ as [|D b' φ' Hqbody| | | | |]; subst.
  assert (Hφ : qual_dom φ ⊆ dom Δ).
  { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
  rewrite (FExprContIn_post_eq_at_fresh
    (<[x:=T1]> Δ) (e2 ^^ x)
    (fun ν =>
      let φν := qual_open_atom 0 ν φ in
      FAnd
        (basic_world_formula (<[ν:=TBase b]> (<[x:=T1]> Δ))
          ({[ν]} ∪ qual_dom φν))
        (fib_vars (qual_dom φν)
          (FUnder (FTypeQualifier φν))))
    (fun ν =>
      let φν := qual_open_atom 0 ν φ in
      FAnd
        (basic_world_formula (<[ν:=TBase b]> Δ)
          ({[ν]} ∪ qual_dom φν))
        (fib_vars (qual_dom φν)
          (FUnder (FTypeQualifier φν))))).
  2:{
    eapply (denot_refinement_under_cont_insert_fresh_eq
      (dom Δ : aset) Δ x T1 b φ); [set_solver | reflexivity].
  }
  eapply (FExprCont_tlet_reduction Δ T1 (TBase b) m e1 e2 x); eauto.
  - set_solver.
  - eapply denot_refinement_under_cont_fv_subset. exact Hφ.
  - eapply denot_refinement_under_cont_rename_stable. exact Hφ.
Qed.

Lemma denot_ty_fuel_tlet_reduction_full_on_inter_case gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τa τb :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTInter τa τb) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTInter τa τb) →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_fuel gas (<[x:=T1]> Δ) τa (e2 ^^ x) <->
   m ⊨ denot_ty_fuel gas Δ τa (tlete e1 e2)) →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_fuel gas (<[x:=T1]> Δ) τb (e2 ^^ x) <->
   m ⊨ denot_ty_fuel gas Δ τb (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel (S gas) (<[x:=T1]> Δ) (CTInter τa τb) (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel (S gas) Δ (CTInter τa τb) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet HIHa HIHb.
  eapply denot_ty_fuel_tlet_reduction_full_from_body_on; eauto.
  cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty].
  split; intros Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj1 HIHa). eapply res_models_and_elim_l. exact Hmodel.
    + apply (proj1 HIHb). eapply res_models_and_elim_r. exact Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj2 HIHa). eapply res_models_and_elim_l. exact Hmodel.
    + apply (proj2 HIHb). eapply res_models_and_elim_r. exact Hmodel.
Qed.

Lemma res_models_or_transport_between_worlds
    (m n : WfWorld) (φa φb ψa ψb : FormulaQ) :
  formula_fv ψa ⊆ world_dom (n : World) →
  formula_fv ψb ⊆ world_dom (n : World) →
  (m ⊨ φa → n ⊨ ψa) →
  (m ⊨ φb → n ⊨ ψb) →
  m ⊨ FOr φa φb →
  n ⊨ FOr ψa ψb.
Proof.
  intros Hψa Hψb Ha Hb Hor.
  unfold res_models, res_models_with_store in Hor.
  simpl in Hor. destruct Hor as [_ [Hleft | Hright]].
  - eapply res_models_or_intro_l_from_model.
    + apply Ha. unfold res_models, res_models_with_store.
      lazymatch type of Hleft with
      | res_models_with_store_fuel ?g ?ρ ?w ?φ =>
          eapply (res_models_with_store_fuel_irrel g (formula_measure φ) ρ w φ);
          [simpl; lia | lia | exact Hleft]
      end.
    + exact Hψb.
  - eapply res_models_or_intro_r_from_model.
    + exact Hψa.
    + apply Hb. unfold res_models, res_models_with_store.
      lazymatch type of Hright with
      | res_models_with_store_fuel ?g ?ρ ?w ?φ =>
          eapply (res_models_with_store_fuel_irrel g (formula_measure φ) ρ w φ);
          [simpl; lia | lia | exact Hright]
      end.
Qed.

Lemma denot_ty_fuel_tlet_reduction_full_on_union_case gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τa τb :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  cty_measure (CTUnion τa τb) <= S gas →
  basic_choice_ty (dom Δ) (CTUnion τa τb) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTUnion τa τb) →
  basic_choice_ty (dom Δ) τa →
  basic_choice_ty (dom Δ) τb →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_fuel gas (<[x:=T1]> Δ) τa (e2 ^^ x) <->
   m ⊨ denot_ty_fuel gas Δ τa (tlete e1 e2)) →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_fuel gas (<[x:=T1]> Δ) τb (e2 ^^ x) <->
   m ⊨ denot_ty_fuel gas Δ τb (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel (S gas) (<[x:=T1]> Δ) (CTUnion τa τb) (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel (S gas) Δ (CTUnion τa τb) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hgas Hbasicτ Hlet
    HbasicA HbasicB HIHa HIHb.
  assert (HgasA : cty_measure τa <= gas) by (cbn in Hgas; lia).
  assert (HgasB : cty_measure τb <= gas) by (cbn in Hgas; lia).
  eapply denot_ty_fuel_tlet_reduction_full_from_body_on; eauto.
  cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty].
  split; intros Hmodel.
  - eapply res_models_or_transport_between_worlds; [| | apply (proj1 HIHa) | apply (proj1 HIHb) | exact Hmodel].
    + rewrite Hdom.
      eapply denot_ty_fuel_formula_fv_subset_env; [exact HgasA |].
      eapply basic_choice_ty_fv_subset. exact HbasicA.
    + rewrite Hdom.
      eapply denot_ty_fuel_formula_fv_subset_env; [exact HgasB |].
      eapply basic_choice_ty_fv_subset. exact HbasicB.
  - eapply res_models_or_transport_between_worlds; [| | apply (proj2 HIHa) | apply (proj2 HIHb) | exact Hmodel].
    + rewrite let_result_world_on_dom, Hdom.
      pose proof (denot_ty_fuel_formula_fv_subset_env
        gas (<[x:=T1]> Δ) τa (e2 ^^ x) HgasA
        ltac:(rewrite dom_insert_L;
          pose proof (basic_choice_ty_fv_subset (dom Δ) τa HbasicA);
          set_solver)) as Hfv.
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz. set_solver.
    + rewrite let_result_world_on_dom, Hdom.
      pose proof (denot_ty_fuel_formula_fv_subset_env
        gas (<[x:=T1]> Δ) τb (e2 ^^ x) HgasB
        ltac:(rewrite dom_insert_L;
          pose proof (basic_choice_ty_fv_subset (dom Δ) τb HbasicB);
          set_solver)) as Hfv.
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_tlet_reduction_full_on gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  ∀ τ2,
    cty_measure τ2 <= gas →
    basic_choice_ty (dom Δ) τ2 →
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
    let_result_world_on e1 x m Hfresh Hresult
      ⊨ denot_ty_fuel gas (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_fuel gas Δ τ2 (tlete e1 e2).
Proof.
  revert Δ T1 e1 e2 m x Hfresh Hresult.
  induction gas as [|gas IH]; intros Δ T1 e1 e2 m x Hfresh Hresult
    He1 Hdom Hclosed Htotal Hx_base τ2 Hgas Hbasicτ Hlet.
  - pose proof (cty_measure_gt_0 τ2). lia.
  - destruct τ2 as [b φ|b φ|τa τb|τa τb|τa τb|τx τ|τx τ].
    + eapply denot_ty_fuel_tlet_reduction_full_on_over_case; eauto.
    + eapply denot_ty_fuel_tlet_reduction_full_on_under_case; eauto.
    + cbn [cty_measure] in Hgas.
      inversion Hbasicτ as [| |D τ1' τ2' HbasicA HbasicB Herase| | | |]; subst.
      assert (HfullA :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τa (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τa (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult);
          [exact He1 | exact Hdom | exact Hclosed | exact Htotal |
           exact Hx_base | lia | exact HbasicA | exact Hlet].
      }
      assert (HletB : Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τb).
      { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
      assert (HfullB :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τb (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τb (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult);
          [exact He1 | exact Hdom | exact Hclosed | exact Htotal |
           exact Hx_base | lia | exact HbasicB | exact HletB].
      }
      eapply denot_ty_fuel_tlet_reduction_full_on_inter_case;
        [exact He1 | exact Hdom | exact Hclosed | exact Htotal |
         exact Hx_base | exact Hbasicτ | exact Hlet | exact HfullA | exact HfullB].
    + cbn [cty_measure] in Hgas.
      inversion Hbasicτ as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
      assert (HfullA :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τa (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τa (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult);
          [exact He1 | exact Hdom | exact Hclosed | exact Htotal |
           exact Hx_base | lia | exact HbasicA | exact Hlet].
      }
      assert (HletB : Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τb).
      { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
      assert (HfullB :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τb (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τb (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult);
          [exact He1 | exact Hdom | exact Hclosed | exact Htotal |
           exact Hx_base | lia | exact HbasicB | exact HletB].
      }
      eapply denot_ty_fuel_tlet_reduction_full_on_union_case;
        [exact He1 | exact Hdom | exact Hclosed | exact Htotal |
         exact Hx_base | exact Hgas | exact Hbasicτ | exact Hlet |
         exact HbasicA | exact HbasicB | exact HfullA | exact HfullB].
    + (* CTSum: still needs the sum/resource distribution argument. *)
      admit.
    + (* CTArrow: postponed with the function-type reduction proof. *)
      admit.
    + (* CTWand: same shape as Arrow, with separating implication. *)
      admit.
Admitted.

Lemma denot_ty_fuel_tlet_reduction_formula_on gas
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_store_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  ∀ τ2,
    cty_measure τ2 <= gas →
    basic_choice_ty (dom Δ) τ2 →
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
    let_result_world_on e1 x m Hfresh Hresult
      ⊨ denot_ty_fuel gas (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_fuel gas Δ τ2 (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base τ2 Hgas Hbasicτ Hlet.
  eapply denot_ty_fuel_tlet_reduction_full_on; eauto.
Qed.

Lemma denot_ty_fuel_tlet_reduction_formula gas (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx),
  cty_measure τ2 <= gas →
  denot_ty_regular_in_ctx_under Σ Γ τ2 →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) →
  world_store_closed_on (dom (erase_ctx_under Σ Γ)) m →
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2 →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_fuel gas (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)))
        τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_fuel gas (erase_ctx_under Σ Γ) τ2 (tlete e1 e2).
Proof.
  intros Σ Γ τ1 e1 e2 m x Hfresh Hresult
    Hgas [HbasicΓ Hbasicτ] He1 Hlet Hdom Hclosed Htotal Hx.
  assert (HxΔ : x ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1)
    by exact HxΔ.
  eapply (denot_ty_fuel_tlet_reduction_formula_on
    gas (erase_ctx_under Σ Γ) (erase_ty τ1) e1 e2 m x
    Hfresh Hresult); eauto.
  set_solver.
Qed.

Lemma denot_ty_tlet_reduction_formula (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx),
  denot_ty_regular_in_ctx_under Σ Γ τ2 →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2 →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
  intros Σ Γ τ1 e1 e2 m x Hfresh Hresult Hregular He1 Hlet Hdom Hctx Htotal Hx.
  unfold denot_ty_in_ctx_under, denot_ty_on.
  eapply denot_ty_fuel_tlet_reduction_formula; eauto.
  eapply denot_ctx_in_env_world_store_closed_on_erased; eauto.
  exact (proj1 Hregular).
Qed.

Lemma denot_ty_tlet_reduction_formula_any_world (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx),
  denot_ty_regular_in_ctx_under Σ Γ τ2 →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2 →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
Admitted.

Lemma expr_total_tlet_reduction
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_tm e2 →
  expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
    (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult)
  <->
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m.
Proof.
Admitted.

Lemma denot_ty_regular_tlet_context_iff
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) x :
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 →
  denot_ty_regular_in_ctx_under Σ Γ τ1 →
  denot_ty_regular_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 ↔
  denot_ty_regular_in_ctx_under Σ Γ τ2.
Proof.
  intros Hfresh [HctxΓ Hτ1]. split.
  - intros [Hctxcomma Hτ2_body].
    split.
    + inversion Hctxcomma; subst; assumption.
    + eapply basic_choice_ty_drop_fresh.
      * intros Hxτ. apply Hfresh. apply elem_of_union_r. exact Hxτ.
      * replace (dom (erase_ctx_under Σ Γ) ∪ {[x]}) with
          (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)))).
        -- exact Hτ2_body.
        -- rewrite erase_ctx_under_comma_bind_dom_nf. set_solver.
  - intros [HctxΓ' Hτ2].
    split.
    + eapply Basic_CtxComma.
      * exact HctxΓ'.
      * eapply Basic_CtxBind.
        -- rewrite <- (erase_ctx_under_dom_basic Σ Γ HctxΓ').
           set_solver.
        -- replace (dom Σ ∪ ctx_dom Γ) with
             (dom (erase_ctx_under Σ Γ)).
           ++ exact Hτ1.
           ++ rewrite erase_ctx_under_dom_basic by exact HctxΓ'. set_solver.
      * simpl. pose proof (erase_ctx_under_dom_basic Σ Γ HctxΓ') as HdomΓ.
        set_solver.
    + rewrite erase_ctx_under_comma_bind_dom_nf.
      eapply (basic_choice_ty_mono
        (dom (erase_ctx_under Σ Γ))
        (dom (erase_ctx_under Σ Γ) ∪ {[x]})); [set_solver | exact Hτ2].
Qed.

Lemma denot_ty_total_tlet_reduction
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  m ⊨ denot_ctx_in_env Σ Γ →
  denot_ty_total_model_in_ctx_under Σ Γ τ1 e1 m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2 →
  denot_ty_total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2
    (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult)
  <->
  denot_ty_total_model_in_ctx_under Σ Γ τ2 (tlete e1 e2) m.
Proof.
  intros He1 Hlet Hctx Hmodel1 Hfreshx.
  pose proof (denot_ty_regular_tlet_context_iff
    Σ Γ τ1 τ2 x ltac:(set_solver)
    (denot_ty_total_model_regular Σ Γ τ1 e1 m Hmodel1))
    as Hregular_iff.
	  split; intros Hmodel.
	  - destruct Hmodel as [[Hregular_body Hformula_body] Htotal_body].
	    pose proof (proj1 (expr_total_tlet_reduction
	      Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult Hlet Hctx ltac:(set_solver))
	      Htotal_body) as Htotal_target.
	    split.
	    + split.
	      * apply (proj1 Hregular_iff). exact Hregular_body.
		      * apply (proj1 (denot_ty_tlet_reduction_formula_any_world
		          τ2 Σ Γ τ1 e1 e2 m x Hfresh Hresult
		          (proj1 Hregular_iff Hregular_body) He1 Hlet Hctx
		          Htotal_target Hfreshx)).
	        exact Hformula_body.
	    + exact Htotal_target.
	  - destruct Hmodel as [[Hregular_target Hformula_target] Htotal_target].
	    split.
	    + split.
	      * apply (proj2 Hregular_iff). exact Hregular_target.
		      * apply (proj2 (denot_ty_tlet_reduction_formula_any_world
		          τ2 Σ Γ τ1 e1 e2 m x Hfresh Hresult
		          Hregular_target He1 Hlet Hctx Htotal_target Hfreshx)).
	        exact Hformula_target.
    + apply (proj2 (expr_total_tlet_reduction
        Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult Hlet Hctx ltac:(set_solver))).
      exact Htotal_target.
Qed.

(** The total [tlet] rule after splitting the body premise cofinally. *)
Lemma denot_tlet_total_semantic
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset)
    :
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_model_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    total_model_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  entails_total (denot_ctx_in_env Σ Γ)
    (denot_ty_total_model_in_ctx_under Σ Γ τ2 (tlete e1 e2)).
Proof.
  intros Herase Hwflet IH1 Hbody m Hm.
  pose proof (IH1 m Hm) as Hmodel.
  pose proof (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel) as Htotal1.
  pose (Fresh :=
    L ∪ world_dom (m : World) ∪ dom (erase_ctx_under Σ Γ) ∪
    fv_tm e2 ∪ fv_cty τ2).
  pose (x := fresh_for Fresh).
  assert (HxFresh : x ∉ Fresh) by (subst x; apply fresh_for_not_in).
  assert (HxL : x ∉ L) by (subst Fresh; set_solver).
  assert (Hfresh : x ∉ world_dom (m : World)) by (subst Fresh; set_solver).
  assert (Hx_tlet :
    x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2)
    by (subst Fresh; set_solver).
  assert (Hclosed_erased :
    world_store_closed_on (dom (erase_ctx_under Σ Γ)) m).
  {
    pose proof (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel)
      as Hbasic.
    intros σ Hσ.
    assert (Hdom_erase :
      dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ).
    { apply erase_ctx_under_dom_basic. exact Hbasic. }
    rewrite Hdom_erase.
    split.
    - exact (proj1 (denot_ctx_in_env_store_erased_typed
        Σ Γ m σ Hbasic Hm Hσ)).
    - exact (denot_ctx_in_env_store_erased_lc
        Σ Γ m σ Hbasic Hm Hσ).
  }
  assert (Hresult : ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx).
  { eapply expr_total_on_to_fv_result; eauto. }
  set (m' := let_result_world_on e1 x m Hfresh Hresult).
  assert (Hctx :
    m' ⊨ denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1))).
  {
    subst m'. eapply tlet_split_premises_body_ctx_from_result; eauto.
  }
  pose proof (Hbody x HxL m' Hctx) as Hbody_model.
  exact (proj1
    (denot_ty_total_tlet_reduction
      Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult
      Herase Hwflet Hm Hmodel Hx_tlet)
    Hbody_model).
Qed.

Lemma denot_tlet_semantic
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2 (L : aset) :
  choice_typing_wf Σ Γ e1 τ1 →
  choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof.
(** Placeholder: this is the non-total semantic [tlet] statement and should not
    be used as evidence that the [tlet] case is proved.  The current active
    route is the total statement [denot_tlet_total_semantic] above. *)
Admitted.
