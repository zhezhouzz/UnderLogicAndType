(** * ChoiceTyping.TLetReduction

    Fuel-level and model-level reduction lemmas for the [tlet] soundness case.
    The final semantic wrappers stay in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Export TLetTotal RegularDenotation.
From ChoiceTyping Require Import Naming ResultWorldBridge ResultWorldFreshForall.
From ChoiceType Require Import BasicStore LocallyNamelessProps DenotationRefinement.

Import Tactics.

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
  { eauto using basic_typing_contains_fv_tm. }
  assert (Hlc1 : lc_tm e1).
  { eauto using typing_tm_lc. }
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
      + eauto.
      + eauto.
      + exists σ. split; [exact Hσ | reflexivity].
      + replace (store_restrict (store_restrict σ (fv_tm e1)) (fv_tm e1))
          with (store_restrict σ (fv_tm e1)).
        * eauto.
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
    - eauto using basic_typing_contains_fv_tm.
    - apply basic_typing_contains_fv_tm in Hlet. simpl in Hlet. set_solver.
    - eauto.
    - rewrite Hdom. set_solver.
    - intros σ Hσ. exact (proj1 (Hclosed σ Hσ)).
    - intros σ Hσ. exact (proj2 (Hclosed σ Hσ)).
    - intros σ vx Hσ Hsteps.
      eapply steps_closed_result.
      + eapply (msubst_closed_tm_of_restrict_world (dom Σ) e1 m σ).
        * rewrite Hdom. set_solver.
        * exact Hfv1.
        * eauto.
        * eauto.
        * exists σ. split; [exact Hσ |].
          rewrite (store_restrict_idemp σ (dom Σ)).
          -- reflexivity.
          -- pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
             set_solver.
      + eauto.
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

Lemma expr_total_on_restrict_insert_fresh
    (Σ : gmap atom ty) T e x (m : WfWorld) :
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  expr_total_on (dom Σ) e (res_restrict m (dom Σ)).
Proof.
  intros Hx Hdom Hclosed [Hfv Htotal].
  split; [set_solver |].
  intros σ Hσ.
  destruct Hσ as [σm [Hσm Hrestrict]].
  specialize (Htotal σm Hσm).
  replace (subst_map (store_restrict σ (dom Σ)) e)
    with (subst_map (store_restrict σm (dom (<[x := T]> Σ))) e).
  - exact Htotal.
  - symmetry.
    eapply subst_map_eq_on_fv.
    + apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
    + rewrite !store_restrict_restrict.
      rewrite <- Hrestrict.
      rewrite !store_restrict_restrict.
      f_equal. rewrite dom_insert_L. set_solver.
Qed.

Lemma world_store_closed_on_restrict_insert_fresh
    (Σ : gmap atom ty) T x (m : WfWorld) :
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  world_store_closed_on (dom Σ) (res_restrict m (dom Σ)).
Proof.
  intros Hclosed σ Hσ.
  destruct Hσ as [σm [Hσm <-]].
  rewrite store_restrict_restrict.
  replace (dom Σ ∩ dom Σ) with (dom Σ) by set_solver.
  replace (store_restrict σm (dom Σ))
    with (store_restrict (store_restrict σm (dom (<[x := T]> Σ))) (dom Σ)).
  - apply store_closed_restrict.
    exact (Hclosed σm Hσm).
  - rewrite store_restrict_restrict.
    f_equal. rewrite dom_insert_L. set_solver.
Qed.

Lemma FExprContIn_insert_fresh_env_irrel
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := Tx]> Σ) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  res_restrict m (dom Σ) ⊨ FExprContIn Σ e P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P.
Proof.
  intros Hty Hx Hdom Hclosed Htotal HPfv HPrename Hcont.
  assert (Hdom_restrict :
    world_dom (res_restrict m (dom Σ) : World) = dom Σ).
  { simpl. rewrite Hdom, dom_insert_L. set_solver. }
  assert (Hclosed_restrict :
    world_store_closed_on (dom Σ) (res_restrict m (dom Σ))).
  { eapply world_store_closed_on_restrict_insert_fresh; eauto. }
  assert (Htotal_restrict :
    expr_total_on (dom Σ) e (res_restrict m (dom Σ))).
  {
    eapply (expr_total_on_restrict_insert_fresh Σ Tx e x m); eauto.
  }
  assert (Hty_insert : <[x := Tx]> Σ ⊢ₑ e ⋮ T).
  {
    eapply basic_typing_weaken_insert_tm.
    - set_solver.
    - exact Hty.
  }
  assert (HPfv_insert :
    ∀ ν, formula_fv (P ν) ⊆ dom (<[x := Tx]> Σ) ∪ {[ν]}).
  { intros ν. specialize (HPfv ν). rewrite dom_insert_L. set_solver. }
  assert (HPrename_insert :
    formula_family_rename_stable_on (dom (<[x := Tx]> Σ)) P).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb.
    apply HPrename; rewrite dom_insert_L in *; set_solver.
  }
  pose proof (proj1
    (FExprContIn_iff_let_result_world_on_exact_domain
      Σ T e P (res_restrict m (dom Σ))
      Hty Hdom_restrict Hclosed_restrict Htotal_restrict HPfv HPrename)
    Hcont) as [L [HL Hbody]].
  apply (proj2
    (FExprContIn_iff_let_result_world_on_exact_domain
      (<[x := Tx]> Σ) T e P m
      Hty_insert Hdom Hclosed Htotal HPfv_insert HPrename_insert)).
  exists (L ∪ dom (<[x := Tx]> Σ) ∪ fv_tm e).
  split; [set_solver |].
  intros ν Hν Hfresh Hresult.
  assert (Hfresh_restrict :
    ν ∉ world_dom (res_restrict m (dom Σ) : World)).
  { rewrite Hdom_restrict. set_solver. }
  assert (Hresult_restrict :
    ∀ σ, (res_restrict m (dom Σ) : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
  {
    eapply expr_total_on_to_fv_result; eauto.
  }
  pose proof (Hbody ν ltac:(set_solver) Hfresh_restrict Hresult_restrict)
    as Hsmall.
  pose proof (proj2 (res_models_minimal_on
    (dom Σ ∪ {[ν]})
    (let_result_world_on e ν m Hfresh Hresult)
    (P ν) (HPfv ν))) as Hminimal.
  apply Hminimal.
  rewrite (let_result_world_on_restrict_input
    (dom Σ) e ν m Hfresh Hresult Hfresh_restrict Hresult_restrict).
  - exact Hsmall.
  - destruct Htotal as [Hfv _].
    rewrite dom_insert_L in Hfv.
    set_solver.
  - rewrite Hdom, dom_insert_L. set_solver.
  - set_solver.
Qed.

Lemma FExprContIn_restrict_insert_fresh_env_irrel
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := Tx]> Σ) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P →
  res_restrict m (dom Σ) ⊨ FExprContIn Σ e P.
Proof.
  intros Hty Hx Hdom Hclosed Htotal HPfv HPrename Hcont.
  assert (Hdom_restrict :
    world_dom (res_restrict m (dom Σ) : World) = dom Σ).
  { simpl. rewrite Hdom, dom_insert_L. set_solver. }
  assert (Hclosed_restrict :
    world_store_closed_on (dom Σ) (res_restrict m (dom Σ))).
  { eapply world_store_closed_on_restrict_insert_fresh; eauto. }
  assert (Htotal_restrict :
    expr_total_on (dom Σ) e (res_restrict m (dom Σ))).
  {
    eapply (expr_total_on_restrict_insert_fresh Σ Tx e x m); eauto.
  }
  assert (Hty_insert : <[x := Tx]> Σ ⊢ₑ e ⋮ T).
  {
    eapply basic_typing_weaken_insert_tm.
    - set_solver.
    - exact Hty.
  }
  assert (HPfv_insert :
    ∀ ν, formula_fv (P ν) ⊆ dom (<[x := Tx]> Σ) ∪ {[ν]}).
  { intros ν. specialize (HPfv ν). rewrite dom_insert_L. set_solver. }
  assert (HPrename_insert :
    formula_family_rename_stable_on (dom (<[x := Tx]> Σ)) P).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb.
    apply HPrename; rewrite dom_insert_L in *; set_solver.
  }
  pose proof (proj1
    (FExprContIn_iff_let_result_world_on_exact_domain
      (<[x := Tx]> Σ) T e P m
      Hty_insert Hdom Hclosed Htotal HPfv_insert HPrename_insert)
    Hcont) as [L [HL Hbody]].
  apply (proj2
    (FExprContIn_iff_let_result_world_on_exact_domain
      Σ T e P (res_restrict m (dom Σ))
      Hty Hdom_restrict Hclosed_restrict Htotal_restrict HPfv HPrename)).
  exists (L ∪ dom (<[x := Tx]> Σ) ∪ fv_tm e).
  split; [set_solver |].
  intros ν Hν Hfresh_restrict Hresult_restrict.
  assert (Hfresh : ν ∉ world_dom (m : World)).
  { rewrite Hdom, dom_insert_L. set_solver. }
  assert (Hresult :
    ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
  {
    eapply expr_total_on_to_fv_result; eauto.
  }
  pose proof (Hbody ν ltac:(set_solver) Hfresh Hresult) as Hfull.
  pose proof (proj1 (res_models_minimal_on
    (dom Σ ∪ {[ν]})
    (let_result_world_on e ν m Hfresh Hresult)
    (P ν) (HPfv ν))) as Hminimal.
  rewrite <- (let_result_world_on_restrict_input
    (dom Σ) e ν m Hfresh Hresult Hfresh_restrict Hresult_restrict).
  - apply Hminimal. exact Hfull.
  - destruct Htotal as [Hfv _].
    rewrite dom_insert_L in Hfv.
    set_solver.
  - rewrite Hdom, dom_insert_L. set_solver.
  - set_solver.
Qed.

Lemma FExprContIn_insert_fresh_env_irrel_iff
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := Tx]> Σ) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P <->
  res_restrict m (dom Σ) ⊨ FExprContIn Σ e P.
Proof.
  intros Hty Hx Hdom Hclosed Htotal HPfv HPrename.
  split.
  - eapply FExprContIn_restrict_insert_fresh_env_irrel; eauto.
  - eapply FExprContIn_insert_fresh_env_irrel; eauto.
Qed.

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

Lemma denot_ty_fuel_basic_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  basic_choice_ty (dom Σ) τ ∧ Σ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hm.
  rewrite denot_ty_fuel_unfold in Hm.
  unfold denot_ty_obligations, FBasicTypingIn in Hm.
  apply res_models_with_store_and_elim_l in Hm.
  exact (res_models_with_store_pure_elim _ _ _ Hm).
Qed.

Lemma msubst_tapp_tm σ ef vx :
  m{σ} (tapp_tm ef vx) = tapp_tm (m{σ} ef) (m{σ} vx).
Proof.
  induction ef; simpl.
  - rewrite msubst_tapp, msubst_ret. reflexivity.
  - rewrite !msubst_lete. rewrite IHef2. reflexivity.
  - rewrite msubst_lete, msubst_tprim.
    rewrite msubst_tapp.
    rewrite (msubst_fresh σ (vbvar 0)) by set_solver.
    cbn [tapp_tm].
    rewrite msubst_tprim.
    reflexivity.
  - rewrite msubst_lete, msubst_tapp.
    rewrite msubst_tapp.
    rewrite (msubst_fresh σ (vbvar 0)) by set_solver.
    cbn [tapp_tm].
    rewrite msubst_tapp.
    reflexivity.
  - rewrite msubst_lete, msubst_tmatch.
    rewrite msubst_tapp.
    rewrite (msubst_fresh σ (vbvar 0)) by set_solver.
    cbn [tapp_tm].
    rewrite msubst_tmatch.
    reflexivity.
Qed.

Lemma msubst_fvar_store_swap_lookup σ x y v :
  closed_env σ →
  σ !! y = Some v →
  m{store_swap x y σ} (vfvar x) = m{σ} (vfvar y).
Proof.
  intros Hclosed Hlookup.
  rewrite (msubst_fvar_lookup_closed σ y v Hclosed Hlookup).
  rewrite (msubst_fvar_lookup_closed (store_swap x y σ) x v).
  - reflexivity.
  - apply closed_env_store_swap. exact Hclosed.
  - change (store_swap x y σ !! x = Some v).
    rewrite store_swap_lookup_inv.
    replace (atom_swap x y x) with y
      by (unfold atom_swap; repeat destruct decide; congruence).
    exact Hlookup.
Qed.

Lemma msubst_tret_fvar_store_swap_lookup σ x y v :
  closed_env σ →
  σ !! y = Some v →
  m{store_swap x y σ} (tret (vfvar x)) = m{σ} (tret (vfvar y)).
Proof.
  intros Hclosed Hlookup.
  rewrite !msubst_ret.
  rewrite (msubst_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

Lemma msubst_tapp_tm_fvar_store_swap_lookup σ e x y v :
  closed_env σ →
  lc_env σ →
  σ !! y = Some v →
  x ∉ fv_tm e →
  y ∉ fv_tm e →
  m{store_swap x y σ} (tapp_tm e (vfvar x)) =
  m{σ} (tapp_tm e (vfvar y)).
Proof.
  intros Hclosed Hlc Hlookup Hx Hy.
  rewrite !msubst_tapp_tm.
  rewrite (msubst_store_swap_fresh tm x y σ e) by assumption.
  rewrite (msubst_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

(** The two lemmas below are the explicit-name/cofinite rename principles
    needed by the function-type cases.

    They are intentionally stated as semantic [formula_family_rename_stable_on]
    lemmas rather than syntactic equalities.  [denot_ty_fuel] now contains
    [FPure], [FClosedResourceIn], and [FStrongTotalIn] obligations; a syntactic
    [formula_rename_atom] does not rewrite those Rocq propositions.  The proof
    must therefore transport the obligations semantically:

    - [FPure] uses basic typing/formation rename for the fresh parameter;
    - [FClosedResourceIn] uses resource swap/restrict compatibility;
    - [FStrongTotalIn] uses operational totality under swapped stores;
    - the recursive body uses the [gas] induction hypothesis.

    The argument-family lemma covers the antecedent of Arrow/Wand.  The result
    family covers the consequent, where the result type is opened with the same
    fresh parameter and the expression is the ANF application sugar
    [tapp_tm e (vfvar x)]. *)
Lemma denot_ty_fuel_fresh_arg_family_rename_stable
    gas (Σ : gmap atom ty) τx :
  cty_measure τx <= gas →
  basic_choice_ty (dom Σ) τx →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      τx (tret (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_fuel_fresh_result_family_rename_stable
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τ <= gas →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_fuel_insert_fresh_env_irrel gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e.
Proof.
  revert Σ τ e x T m.
  induction gas as [|gas IH]; intros Σ τ e x T m Hgas Hx Hdom Hclosed Htotal Hsrc.
  - pose proof (cty_measure_gt_0 τ). lia.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasic_src].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_weaken_insert_tm; [set_solver | exact Htyped_src].
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      destruct τ as [b φ|b φ|τa τb|τa τb|τa τb|τx τ|τx τ].
      * cbn [denot_ty_fuel_body fv_cty erase_ty] in *.
        inversion Hbasic_src as [D b' φ' Hqbody| | | | | |]; subst.
        assert (Hφ : qual_dom φ ⊆ dom Σ).
        { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
        rewrite (FExprContIn_post_eq_at_fresh
          (<[x:=T]> Σ) e
          (fun ν =>
            let φν := qual_open_atom 0 ν φ in
            FAnd
              (basic_world_formula (<[ν:=TBase b]> (<[x:=T]> Σ))
                ({[ν]} ∪ qual_dom φν))
              (fib_vars (qual_dom φν)
                (FOver (FTypeQualifier φν))))
          (fun ν =>
            let φν := qual_open_atom 0 ν φ in
            FAnd
              (basic_world_formula (<[ν:=TBase b]> Σ)
                ({[ν]} ∪ qual_dom φν))
              (fib_vars (qual_dom φν)
                (FOver (FTypeQualifier φν))))).
        2:{
          eapply (denot_refinement_over_cont_insert_fresh_eq
            (dom Σ : aset) Σ x T b φ); [set_solver | reflexivity].
        }
        eapply FExprContIn_insert_fresh_env_irrel.
        -- exact Htyped_src.
        -- set_solver.
        -- exact Hdom.
        -- exact Hclosed.
        -- exact Htotal.
        -- eapply denot_refinement_over_cont_fv_subset. exact Hφ.
        -- eapply denot_refinement_over_cont_rename_stable. exact Hφ.
        -- exact Hbody.
      * cbn [denot_ty_fuel_body fv_cty erase_ty] in *.
        inversion Hbasic_src as [|D b' φ' Hqbody| | | | |]; subst.
        assert (Hφ : qual_dom φ ⊆ dom Σ).
        { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
        rewrite (FExprContIn_post_eq_at_fresh
          (<[x:=T]> Σ) e
          (fun ν =>
            let φν := qual_open_atom 0 ν φ in
            FAnd
              (basic_world_formula (<[ν:=TBase b]> (<[x:=T]> Σ))
                ({[ν]} ∪ qual_dom φν))
              (fib_vars (qual_dom φν)
                (FUnder (FTypeQualifier φν))))
          (fun ν =>
            let φν := qual_open_atom 0 ν φ in
            FAnd
              (basic_world_formula (<[ν:=TBase b]> Σ)
                ({[ν]} ∪ qual_dom φν))
              (fib_vars (qual_dom φν)
                (FUnder (FTypeQualifier φν))))).
        2:{
          eapply (denot_refinement_under_cont_insert_fresh_eq
            (dom Σ : aset) Σ x T b φ); [set_solver | reflexivity].
        }
        eapply FExprContIn_insert_fresh_env_irrel.
        -- exact Htyped_src.
        -- set_solver.
        -- exact Hdom.
        -- exact Hclosed.
        -- exact Htotal.
        -- eapply denot_refinement_under_cont_fv_subset. exact Hφ.
        -- eapply denot_refinement_under_cont_rename_stable. exact Hφ.
        -- exact Hbody.
      * cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in *.
        inversion Hbasic_src as [| |D τ1' τ2' HbasicA HbasicB Herase| | | |]; subst.
        eapply res_models_and_intro_from_models.
        -- eapply (IH Σ τa e x T m).
           ++ lia.
           ++ set_solver.
           ++ exact Hdom.
           ++ exact Hclosed.
           ++ exact Htotal.
           ++ apply res_models_and_elim_l in Hbody. exact Hbody.
        -- eapply (IH Σ τb e x T m).
           ++ lia.
           ++ set_solver.
           ++ exact Hdom.
           ++ exact Hclosed.
           ++ exact Htotal.
           ++ apply res_models_and_elim_r in Hbody. exact Hbody.
      * cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in *.
        inversion Hbasic_src as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
        eapply res_models_or_transport_between_worlds; [| | | | exact Hbody].
        -- rewrite Hdom.
           eapply (denot_ty_fuel_formula_fv_subset_env
             gas (<[x:=T]> Σ) τa e); [lia |].
           eapply basic_choice_ty_fv_subset.
           eapply basic_choice_ty_mono; [| exact HbasicA].
           set_solver.
        -- rewrite Hdom.
           eapply (denot_ty_fuel_formula_fv_subset_env
             gas (<[x:=T]> Σ) τb e); [lia |].
           eapply basic_choice_ty_fv_subset.
           eapply basic_choice_ty_mono; [| exact HbasicB].
           set_solver.
        -- intros Ha.
           eapply (IH Σ τa e x T m).
           ++ lia.
           ++ set_solver.
           ++ exact Hdom.
           ++ exact Hclosed.
           ++ exact Htotal.
           ++ exact Ha.
        -- intros Hb.
           eapply (IH Σ τb e x T m).
           ++ lia.
           ++ set_solver.
           ++ exact Hdom.
           ++ exact Hclosed.
           ++ exact Htotal.
           ++ exact Hb.
      * cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in *.
        inversion Hbasic_src as [| | | |D τ1' τ2' HbasicA HbasicB Herase| |]; subst.
        unfold res_models, res_models_with_store in Hbody.
        simpl in Hbody.
        destruct Hbody as [_ [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]]].
        assert (Hdom_n1 :
          world_dom (n1 : World) = world_dom (res_restrict m (dom Σ) : World)).
        {
          pose proof (res_models_with_store_fuel_scoped
            _ ∅ n1 (denot_ty_fuel gas Σ τa e) Hn1) as Hscope1.
          unfold formula_scoped_in_world in Hscope1.
          pose proof (denot_ty_fuel_env_fv_subset
            gas Σ τa e ltac:(cbn in Hgas; lia)) as Henvfv.
	          pose proof (raw_le_dom _ _ Hle) as Hdom_le.
	          simpl in Hdom_le.
	          change (world_dom (n1 : World) = world_dom (m : World) ∩ dom Σ).
	          apply set_eq. intros z. split.
	          -- intros Hz. apply Hdom_le. exact Hz.
	          -- intros Hz. apply Hscope1. apply elem_of_union. right.
	             apply Henvfv. apply elem_of_intersection in Hz as [_ HzΣ].
	             exact HzΣ.
	        }
	        destruct (res_sum_lift_along_restrict m n1 n2 (dom Σ) Hdef
	          Hdom_n1 Hle) as
	          [m1 [m2 [Hdef'
	            [Hdom_m1 [Hdom_m2 [Hsub_m1 [Hsub_m2
	              [Hrestr1 [Hrestr2 Hle_full]]]]]]]]].
        eapply res_models_plus_intro.
        -- unfold formula_scoped_in_world. simpl.
           rewrite Hdom.
           pose proof (denot_ty_fuel_formula_fv_subset_env
             gas (<[x:=T]> Σ) τa e ltac:(lia)
             ltac:(eapply basic_choice_ty_fv_subset;
               eapply basic_choice_ty_mono; [| exact HbasicA]; set_solver))
             as HfvA.
           pose proof (denot_ty_fuel_formula_fv_subset_env
             gas (<[x:=T]> Σ) τb e ltac:(lia)
             ltac:(eapply basic_choice_ty_fv_subset;
               eapply basic_choice_ty_mono; [| exact HbasicB]; set_solver))
             as HfvB.
	           intros z Hz.
	           apply elem_of_union in Hz as [Hz | Hz].
	           { rewrite dom_empty_L in Hz. apply not_elem_of_empty in Hz. contradiction. }
	           apply elem_of_union in Hz as [Hz | Hz].
	           { apply HfvA. exact Hz. }
	           { apply HfvB. exact Hz. }
        -- exact Hle_full.
        -- eapply (IH Σ τa e x T m1).
           ++ lia.
           ++ set_solver.
	           ++ rewrite Hdom_m1. exact Hdom.
	           ++ intros σ Hσ.
	              apply Hclosed. exact (proj2 Hsub_m1 σ Hσ).
	           ++ destruct Htotal as [Hfv Hsn]. split; [rewrite dom_insert_L; set_solver |].
	              intros σ Hσ. apply Hsn. exact (proj2 Hsub_m1 σ Hσ).
	           ++ rewrite Hrestr1.
	              eapply res_models_with_store_fuel_irrel.
	              ** apply Nat.le_add_r.
	              ** lia.
	              ** exact Hn1.
        -- eapply (IH Σ τb e x T m2).
           ++ lia.
           ++ set_solver.
	           ++ rewrite Hdom_m2. exact Hdom.
	           ++ intros σ Hσ.
	              apply Hclosed. exact (proj2 Hsub_m2 σ Hσ).
	           ++ destruct Htotal as [Hfv Hsn]. split; [rewrite dom_insert_L; set_solver |].
	              intros σ Hσ. apply Hsn. exact (proj2 Hsub_m2 σ Hσ).
	           ++ rewrite Hrestr2.
	              eapply res_models_with_store_fuel_irrel.
	              ** apply Nat.le_add_l.
	              ** lia.
	              ** exact Hn2.
      * admit.
      * admit.
    + rewrite Hdom, dom_insert_L. set_solver.
Admitted.

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
  - eauto.
  - eauto.
  - intros σ vx Hσ Hsteps.
    pose proof (basic_typing_contains_fv_tm Δ e T Htyped) as Hfv.
    pose proof (typing_tm_lc Δ e T Htyped) as Hlc.
    assert (Hclosed_fv : world_store_closed_on (fv_tm e) m).
    { eapply world_store_closed_on_mono; [exact Hfv | exact Hclosed]. }
    eapply (steps_closed_result_of_restrict_world
      (fv_tm e) e m (store_restrict σ (fv_tm e)) vx).
    + rewrite Hdom. exact Hfv.
    + set_solver.
    + eauto.
    + eauto.
    + exists σ. split; [exact Hσ | reflexivity].
    + replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
        with (store_restrict σ (fv_tm e)).
      * eauto.
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
    eauto using denot_ty_fuel_body_of_formula.
    rewrite Hdom. set_solver.
  - eapply denot_ty_fuel_intro; eauto.
    apply Hformula_iff.
    eauto using denot_ty_fuel_body_of_formula.
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
    + eauto.
    + rewrite let_result_world_on_dom, Hdom, dom_insert_L. set_solver.
  - apply denot_ty_fuel_body_of_formula.
    apply (proj2 Hresult_iff).
    eapply denot_ty_fuel_intro.
    + eauto.
    + eauto.
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + eauto.
    + eauto.
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
    + apply (proj1 HIHa). eauto using res_models_and_elim_l.
    + apply (proj1 HIHb). eauto using res_models_and_elim_r.
  - apply res_models_and_intro_from_models.
    + apply (proj2 HIHa). eauto using res_models_and_elim_l.
    + apply (proj2 HIHb). eauto using res_models_and_elim_r.
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
          epose proof (basic_choice_ty_fv_subset (dom Δ) τa HbasicA);
          set_solver)) as Hfv.
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz. set_solver.
    + rewrite let_result_world_on_dom, Hdom.
      pose proof (denot_ty_fuel_formula_fv_subset_env
        gas (<[x:=T1]> Δ) τb (e2 ^^ x) HgasB
        ltac:(rewrite dom_insert_L;
          epose proof (basic_choice_ty_fv_subset (dom Δ) τb HbasicB);
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
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult); eauto; lia.
      }
      assert (HletB : Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τb).
      { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
      assert (HfullB :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τb (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τb (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult); eauto; lia.
      }
      eapply denot_ty_fuel_tlet_reduction_full_on_inter_case; eauto.
    + cbn [cty_measure] in Hgas.
      inversion Hbasicτ as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
      assert (HfullA :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τa (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τa (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult); eauto; lia.
      }
      assert (HletB : Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τb).
      { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
      assert (HfullB :
        let_result_world_on e1 x m Hfresh Hresult ⊨
          denot_ty_fuel gas (<[x:=T1]> Δ) τb (e2 ^^ x) <->
        m ⊨ denot_ty_fuel gas Δ τb (tlete e1 e2)).
      {
        eapply (IH Δ T1 e1 e2 m x Hfresh Hresult); eauto; lia.
      }
      eapply denot_ty_fuel_tlet_reduction_full_on_union_case; eauto.
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
