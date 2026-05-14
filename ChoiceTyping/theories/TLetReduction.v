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
  destruct (Htotal σm Hσm) as [vx Hsteps].
  exists vx.
  replace (subst_map (store_restrict σ (dom Σ)) e)
    with (subst_map (store_restrict σm (dom (<[x := T]> Σ))) e).
  - exact Hsteps.
  - symmetry.
    eapply subst_map_eq_on_fv.
    + apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
    + rewrite !store_restrict_restrict.
      rewrite <- Hrestrict.
      rewrite !store_restrict_restrict.
      f_equal. rewrite dom_insert_L. set_solver.
Qed.

Lemma expr_total_on_restrict_self X e (m : WfWorld) :
  expr_total_on X e m →
  expr_total_on X e (res_restrict m X).
Proof.
  intros [Hfv Htotal]. split; [exact Hfv |].
  intros σ Hσ.
  destruct Hσ as [σm [Hσm <-]].
  rewrite store_restrict_restrict.
  replace (X ∩ X) with X by set_solver.
  apply Htotal. exact Hσm.
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
  rewrite denot_ty_fuel_unfold.
  unfold denot_ty_obligations.
  apply res_models_and_intro_from_models.
  - unfold FBasicTypingIn, res_models.
    eapply res_models_with_store_store_resource_atom_vars_intro.
    + unfold formula_scoped_in_world.
	      rewrite formula_fv_FStoreResourceAtomVars.
	      rewrite !atom_env_to_lty_env_dom.
	      rewrite lvars_fv_union, !lvars_fv_of_atoms.
      rewrite dom_empty_L. set_solver.
    + rewrite lty_env_open_atom_env_empty, open_cty_env_empty, open_tm_env_empty.
      split; assumption.
  - apply res_models_and_intro_from_models.
    + unfold FClosedResourceIn, res_models.
      eapply res_models_with_store_resource_atom_vars_intro.
      * unfold formula_scoped_in_world.
        rewrite formula_fv_FResourceAtomVars.
        rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
        rewrite dom_empty_L. set_solver.
      * rewrite atom_env_to_lty_env_atom_dom.
        eapply world_closed_on_le.
        -- apply res_restrict_le.
        -- exact Hclosed.
    + apply res_models_and_intro_from_models.
      * unfold FStrongTotalIn, res_models.
        eapply res_models_with_store_store_resource_atom_vars_intro.
        -- unfold formula_scoped_in_world.
           rewrite formula_fv_FStoreResourceAtomVars.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite dom_empty_L. set_solver.
        -- rewrite atom_env_to_lty_env_atom_dom.
           rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms.
           rewrite store_restrict_empty, open_tm_env_empty.
           eapply expr_total_with_store_empty_restrict; eauto.
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
  destruct (res_models_with_store_store_resource_atom_vars_elim _ _ _ _ Hm)
    as [_ [_ [Hbasic _]]].
  rewrite lty_env_open_atom_env_empty, open_cty_env_empty, open_tm_env_empty in Hbasic.
  exact Hbasic.
Qed.

Lemma world_closed_on_extend X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_closed_on X m →
  world_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - store_norm. reflexivity.
Qed.

Lemma denot_ty_fuel_world_closed_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  world_closed_on (dom Σ) m.
Proof.
  intros Hm.
  rewrite denot_ty_fuel_unfold in Hm.
  unfold denot_ty_obligations, FClosedResourceIn in Hm.
  apply res_models_with_store_and_elim_r in Hm.
  apply res_models_with_store_and_elim_l in Hm.
	  destruct (res_models_with_store_resource_atom_vars_elim ∅ m
	    (dom (atom_env_to_lty_env Σ))
	    (world_closed_on (lty_env_atom_dom (atom_env_to_lty_env Σ))) Hm)
	    as [m0 [Hscope [Hclosed Hle]]].
	  rewrite atom_env_to_lty_env_atom_dom in Hclosed.
	  rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Hclosed.
  eapply (world_closed_on_extend (dom Σ)
    (res_restrict m0 (dom Σ)) m).
  - simpl. intros z Hz. apply elem_of_intersection. split; [| exact Hz].
    unfold formula_scoped_in_world in Hscope.
    rewrite dom_empty_L in Hscope.
    apply Hscope. apply elem_of_union. right.
    rewrite formula_fv_FResourceAtomVars.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz.
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma denot_ty_fuel_expr_total_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  expr_total_on (dom Σ) e m.
Proof.
  intros Hm.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hm)
    as [_ Htyped].
  split.
  - eauto using basic_typing_contains_fv_tm.
  - rewrite denot_ty_fuel_unfold in Hm.
    unfold denot_ty_obligations, FStrongTotalIn in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_l in Hm.
    destruct (res_models_with_store_store_resource_atom_vars_elim ∅ m
      (dom (atom_env_to_lty_env Σ))
      (fun η ρ m =>
        expr_total_with_store (lty_env_atom_dom (atom_env_to_lty_env Σ))
          (open_tm_env η e) ρ m) Hm)
      as [m0 [Hscope [Htotal Hle]]].
    rewrite atom_env_to_lty_env_atom_dom in Htotal.
    rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms in Htotal.
    rewrite store_restrict_empty, open_tm_env_empty in Htotal.
    destruct Htotal as [_ Htotal].
    intros σ Hσ.
    pose proof (res_restrict_eq_of_le m0 m Hle) as Hrestrict.
    assert (Hσm0 :
      (m0 : World) (store_restrict σ (world_dom (m0 : World)))).
    { assert ((res_restrict m (world_dom (m0 : World)) : World)
        (store_restrict σ (world_dom (m0 : World)))) as Hraw.
      { exists σ. split; [exact Hσ | reflexivity]. }
      rewrite Hrestrict in Hraw. exact Hraw. }
    assert (HdomΣ : dom Σ ⊆ world_dom (m0 : World)).
    { unfold formula_scoped_in_world in Hscope.
      rewrite dom_empty_L in Hscope.
      intros z Hz. apply Hscope. apply elem_of_union. right.
      rewrite formula_fv_FStoreResourceAtomVars.
      rewrite atom_env_to_lty_env_dom, lvars_fv_of_atoms. exact Hz. }
    assert (HσD :
      (res_restrict m0 (dom Σ) : World) (store_restrict σ (dom Σ))).
    { exists (store_restrict σ (world_dom (m0 : World))).
      split; [exact Hσm0 |].
      rewrite store_restrict_restrict.
      replace (world_dom (m0 : World) ∩ dom Σ) with (dom Σ)
        by set_solver.
      reflexivity. }
    specialize (Htotal _ HσD) as [vx Hsteps].
    exists vx.
    rewrite map_empty_union in Hsteps.
    rewrite store_restrict_restrict in Hsteps.
    replace (dom Σ ∩ dom Σ) with (dom Σ) in Hsteps by set_solver.
    exact Hsteps.
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
  σ !! y = Some v →
  x ∉ fv_tm e →
  y ∉ fv_tm e →
  m{store_swap x y σ} (tapp_tm e (vfvar x)) =
  m{σ} (tapp_tm e (vfvar y)).
Proof.
  intros Hclosed Hlookup Hx Hy.
  rewrite !msubst_tapp_tm.
  rewrite (msubst_store_swap_fresh tm x y σ e) by assumption.
  rewrite (msubst_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

Lemma aset_swap_fresh_union_singleton x y D :
  x ∉ D →
  y ∉ D →
  aset_swap x y (D ∪ {[y]}) = D ∪ {[x]}.
Proof.
  intros Hx Hy. apply set_eq. intros z.
  rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
  unfold atom_swap.
  repeat destruct decide; set_solver.
Qed.

Lemma store_restrict_swap_fresh_union_singleton (σ : Store) x y D :
  x ∉ D →
  y ∉ D →
  store_restrict (store_swap x y σ) (D ∪ {[x]}) =
  store_swap x y (store_restrict σ (D ∪ {[y]})).
Proof.
  intros Hx Hy.
  rewrite <- (aset_swap_fresh_union_singleton x y D Hx Hy).
  apply store_restrict_swap.
Qed.

Lemma store_swap_insert_fresh (σ : gmap atom value) x y z v :
  z ≠ x →
  z ≠ y →
  store_swap (V:=value) x y (<[z := v]> σ : gmap atom value) =
  (<[z := v]> (store_swap (V:=value) x y σ) : gmap atom value).
Proof.
  intros Hzx Hzy.
  unfold store_swap.
  rewrite kmap_insert.
  - rewrite atom_swap_fresh by congruence. reflexivity.
  - apply atom_swap_inj.
Qed.

Lemma let_result_world_on_tret_fvar_swap
    D x y ν (m : WfWorld)
    Hfresh_src Hresult_src Hfresh_tgt Hresult_tgt :
  x ∉ D →
  y ∉ D →
  ν ∉ D ∪ {[x]} ∪ {[y]} →
  world_dom (m : World) = D ∪ {[y]} →
  world_closed_on (D ∪ {[y]}) m →
  let_result_world_on (tret (vfvar x)) ν (res_swap x y m)
    Hfresh_src Hresult_src =
  res_swap x y
    (let_result_world_on (tret (vfvar y)) ν m
      Hfresh_tgt Hresult_tgt).
Proof.
  intros Hx Hy Hν Hdom Hclosed.
  assert (Hνx : ν ≠ x) by set_solver.
  assert (Hνy : ν ≠ y) by set_solver.
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite Hdom, !aset_swap_union, !aset_swap_singleton.
    replace (atom_swap x y y) with x
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by set_solver.
    rewrite atom_swap_fresh by set_solver.
    set_solver.
  - intros σ. simpl. split.
    + intros [σ0 [vx [Hσ0 [Hsteps ->]]]].
      destruct Hσ0 as [σm [Hσm Hswap]]. subst σ0.
      assert (Hy_dom : y ∈ dom σm).
      { rewrite (wfworld_store_dom m σm Hσm), Hdom. set_solver. }
      apply elem_of_dom in Hy_dom as [vy Hlookup_y].
      assert (Hclosed_y : closed_env (store_restrict σm {[y]})).
      {
        replace (store_restrict σm {[y]}) with
          (store_restrict (store_restrict σm (D ∪ {[y]})) {[y]}).
        - apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
        - store_norm. replace ((D ∪ {[y]}) ∩ {[y]}) with ({[y]} : aset) by set_solver.
          reflexivity.
      }
      assert (Hlookup_y_restrict :
        store_restrict σm {[y]} !! y = Some vy).
      { rewrite store_restrict_lookup, decide_True by set_solver. exact Hlookup_y. }
      assert (Hclosed_x : closed_env
        (store_restrict (store_swap x y σm) {[x]})).
      {
        replace ({[x]} : aset) with ((∅ : aset) ∪ {[x]}) by set_solver.
        rewrite store_restrict_swap_fresh_union_singleton with (D := ∅)
          by (try apply not_elem_of_empty).
        replace ((∅ : aset) ∪ {[y]}) with ({[y]} : aset) by set_solver.
        apply closed_env_store_swap. exact Hclosed_y.
      }
      assert (Hlookup_x_restrict :
        store_restrict (store_swap x y σm) {[x]} !! x = Some vy).
      {
        rewrite store_restrict_lookup, decide_True by set_solver.
        rewrite store_swap_lookup_inv.
        replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        exact Hlookup_y.
      }
      change (m{store_restrict (store_swap x y σm) {[x]}} (tret (vfvar x)) →*
        tret vx) in Hsteps.
      rewrite (msubst_ret_fvar_lookup_closed _ x vy Hclosed_x Hlookup_x_restrict) in Hsteps.
      pose proof (value_steps_self vy (tret vx) Hsteps) as Heq.
      inversion Heq. subst vx.
      exists (<[ν := vy]> σm). split.
      * exists σm, vy. repeat split; eauto.
        change (m{store_restrict σm {[y]}} (tret (vfvar y)) →* tret vy).
        rewrite (msubst_ret_fvar_lookup_closed _ y vy Hclosed_y Hlookup_y_restrict).
        exact Hsteps.
      * rewrite store_swap_insert_fresh by congruence.
        reflexivity.
    + intros [σtgt [[σm [vx [Hσm [Hsteps ->]]]] Hswap]].
      subst σ.
      assert (Hy_dom : y ∈ dom σm).
      { rewrite (wfworld_store_dom m σm Hσm), Hdom. set_solver. }
      apply elem_of_dom in Hy_dom as [vy Hlookup_y].
      assert (Hclosed_y : closed_env (store_restrict σm {[y]})).
      {
        replace (store_restrict σm {[y]}) with
          (store_restrict (store_restrict σm (D ∪ {[y]})) {[y]}).
        - apply closed_env_restrict. exact (proj1 (Hclosed σm Hσm)).
        - store_norm. replace ((D ∪ {[y]}) ∩ {[y]}) with ({[y]} : aset) by set_solver.
          reflexivity.
      }
      assert (Hlookup_y_restrict :
        store_restrict σm {[y]} !! y = Some vy).
      { rewrite store_restrict_lookup, decide_True by set_solver. exact Hlookup_y. }
      change (m{store_restrict σm {[y]}} (tret (vfvar y)) →*
        tret vx) in Hsteps.
      rewrite (msubst_ret_fvar_lookup_closed _ y vy Hclosed_y Hlookup_y_restrict) in Hsteps.
      pose proof (value_steps_self vy (tret vx) Hsteps) as Heq.
      inversion Heq. subst vx.
      assert (Hclosed_x : closed_env
        (store_restrict (store_swap x y σm) {[x]})).
      {
        replace ({[x]} : aset) with ((∅ : aset) ∪ {[x]}) by set_solver.
        rewrite store_restrict_swap_fresh_union_singleton with (D := ∅)
          by (try apply not_elem_of_empty).
        replace ((∅ : aset) ∪ {[y]}) with ({[y]} : aset) by set_solver.
        apply closed_env_store_swap. exact Hclosed_y.
      }
      assert (Hlookup_x_restrict :
        store_restrict (store_swap x y σm) {[x]} !! x = Some vy).
      {
        rewrite store_restrict_lookup, decide_True by set_solver.
        rewrite store_swap_lookup_inv.
        replace (atom_swap x y x) with y
          by (unfold atom_swap; repeat destruct decide; congruence).
        exact Hlookup_y.
      }
      exists (store_swap x y σm), vy.
      repeat split.
      * exists σm. split; [exact Hσm | reflexivity].
      * change (m{store_restrict (store_swap x y σm) {[x]}} (tret (vfvar x)) →*
          tret vy).
        rewrite (msubst_ret_fvar_lookup_closed _ x vy Hclosed_x Hlookup_x_restrict).
        exact Hsteps.
      * rewrite store_swap_insert_fresh by congruence.
        reflexivity.
Qed.

Lemma world_closed_on_swap_fresh_union_singleton_iff D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_closed_on (D ∪ {[x]}) (res_swap x y m) ↔
  world_closed_on (D ∪ {[y]}) m.
Proof.
  intros Hx Hy. split; intros Hclosed.
  - pose proof (world_closed_on_swap x y (D ∪ {[x]}) (res_swap x y m)
      Hclosed) as Hswap.
    rewrite res_swap_involutive in Hswap.
    replace (aset_swap x y (D ∪ {[x]})) with (D ∪ {[y]}) in Hswap;
      [exact Hswap |].
    apply set_eq. intros z.
    rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
    unfold atom_swap.
    repeat destruct decide; set_solver.
  - pose proof (world_closed_on_swap x y (D ∪ {[y]}) m Hclosed) as Hswap.
    replace (aset_swap x y (D ∪ {[y]})) with (D ∪ {[x]}) in Hswap;
      [exact Hswap |].
    symmetry. apply aset_swap_fresh_union_singleton; assumption.
Qed.

Lemma world_store_closed_on_swap_fresh_union_singleton_iff D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_store_closed_on (D ∪ {[x]}) (res_swap x y m) ↔
  world_store_closed_on (D ∪ {[y]}) m.
Proof.
  intros Hx Hy. split; intros Hclosed.
  - pose proof (world_store_closed_on_swap x y (D ∪ {[x]}) (res_swap x y m)
      Hclosed) as Hswap.
    rewrite res_swap_involutive in Hswap.
    replace (aset_swap x y (D ∪ {[x]})) with (D ∪ {[y]}) in Hswap;
      [exact Hswap |].
    apply set_eq. intros z.
    rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
    unfold atom_swap.
    repeat destruct decide; set_solver.
  - pose proof (world_store_closed_on_swap x y (D ∪ {[y]}) m Hclosed) as Hswap.
    replace (aset_swap x y (D ∪ {[y]})) with (D ∪ {[x]}) in Hswap;
      [exact Hswap |].
    symmetry. apply aset_swap_fresh_union_singleton; assumption.
Qed.

Lemma expr_total_with_store_empty_tret_fvar_swap_exact
    D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_dom (m : World) = D ∪ {[y]} →
  world_store_closed_on (D ∪ {[y]}) m →
  expr_total_with_store (D ∪ {[y]}) (tret (vfvar y)) ∅ m →
  expr_total_with_store (D ∪ {[x]}) (tret (vfvar x)) ∅ (res_swap x y m).
Proof.
  intros Hx Hy Hdom Hclosed [_ Htotal].
  split.
  - intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite map_empty_union.
    rewrite store_restrict_swap_fresh_union_singleton by assumption.
    apply store_closed_store_swap.
    apply Hclosed. exact Hσy.
  - intros σx Hσx.
  simpl in Hσx.
  destruct Hσx as [σy [Hσy Hσx]]. subst σx.
  rewrite map_empty_union.
  rewrite store_restrict_swap_fresh_union_singleton by assumption.
  pose proof (Hclosed σy Hσy) as [Hclosed_y _].
  assert (Hy_dom : y ∈ dom σy).
  { rewrite (wfworld_store_dom m σy Hσy), Hdom. set_solver. }
  apply elem_of_dom in Hy_dom as [vy Hlookup].
  assert (Hlookup_restrict :
    store_restrict σy (D ∪ {[y]}) !! y = Some vy).
  { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
  destruct (Htotal σy Hσy) as [vout Hsteps].
  exists vout.
  change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
    (tret (vfvar x)) →* tret vout).
  rewrite (msubst_tret_fvar_store_swap_lookup
    (store_restrict σy (D ∪ {[y]})) x y vy
    Hclosed_y Hlookup_restrict).
  replace (store_restrict σy (D ∪ {[y]}))
    with (store_restrict (∅ ∪ σy) (D ∪ {[y]}))
    by (rewrite map_empty_union; reflexivity).
  exact Hsteps.
Qed.

Lemma expr_total_with_store_empty_tapp_tm_fvar_swap_exact
    D e x y (m : WfWorld) :
  x ∉ D ∪ fv_tm e →
  y ∉ D ∪ fv_tm e →
  world_dom (m : World) = D ∪ {[y]} →
  world_store_closed_on (D ∪ {[y]}) m →
  expr_total_with_store (D ∪ {[y]}) (tapp_tm e (vfvar y)) ∅ m →
  expr_total_with_store (D ∪ {[x]}) (tapp_tm e (vfvar x)) ∅ (res_swap x y m).
Proof.
  intros Hx Hy Hdom Hclosed [_ Htotal].
  split.
  - intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite map_empty_union.
    rewrite store_restrict_swap_fresh_union_singleton by set_solver.
    apply store_closed_store_swap.
    apply Hclosed. exact Hσy.
  - intros σx Hσx.
  simpl in Hσx.
  destruct Hσx as [σy [Hσy Hσx]]. subst σx.
  rewrite map_empty_union.
  rewrite store_restrict_swap_fresh_union_singleton by set_solver.
  pose proof (Hclosed σy Hσy) as [Hclosed_y _].
  assert (Hy_dom : y ∈ dom σy).
  { rewrite (wfworld_store_dom m σy Hσy), Hdom. set_solver. }
  apply elem_of_dom in Hy_dom as [vy Hlookup].
  assert (Hlookup_restrict :
    store_restrict σy (D ∪ {[y]}) !! y = Some vy).
  { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
  destruct (Htotal σy Hσy) as [vout Hsteps].
  exists vout.
  change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
    (tapp_tm e (vfvar x)) →* tret vout).
  rewrite (msubst_tapp_tm_fvar_store_swap_lookup
    (store_restrict σy (D ∪ {[y]})) e x y vy
    Hclosed_y Hlookup_restrict ltac:(set_solver) ltac:(set_solver)).
  replace (store_restrict σy (D ∪ {[y]}))
    with (store_restrict (∅ ∪ σy) (D ∪ {[y]}))
    by (rewrite map_empty_union; reflexivity).
  exact Hsteps.
Qed.

Lemma expr_total_on_tret_fvar_swap_iff D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  D ∪ {[y]} ⊆ world_dom (m : World) →
  world_closed_on (D ∪ {[y]}) m →
  expr_total_on (D ∪ {[x]}) (tret (vfvar x)) (res_swap x y m) ↔
  expr_total_on (D ∪ {[y]}) (tret (vfvar y)) m.
Proof.
  intros Hx Hy Hdom Hclosed. split.
  - intros [_ Htotal]. split; [set_solver |].
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σ).
    { rewrite (wfworld_store_dom m σ Hσ). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σ (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    pose proof (Htotal (store_swap x y σ)) as Hsteps_total.
    assert ((res_swap x y m : World) (store_swap x y σ)) as Hσswap.
    { simpl. exists σ. split; [exact Hσ | reflexivity]. }
    specialize (Hsteps_total Hσswap) as [vout Hsteps].
    exists vout.
    rewrite store_restrict_swap_fresh_union_singleton in Hsteps by assumption.
    change (m{store_restrict σ (D ∪ {[y]})} (tret (vfvar y)) →* tret vout).
    rewrite <- (msubst_tret_fvar_store_swap_lookup
      (store_restrict σ (D ∪ {[y]})) x y vy
      (proj1 Hclosedσ) Hlookup_restrict).
    exact Hsteps.
  - intros [_ Htotal]. split; [set_solver |].
    intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite store_restrict_swap_fresh_union_singleton by assumption.
    pose proof (Hclosed σy Hσy) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σy).
    { rewrite (wfworld_store_dom m σy Hσy). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σy (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    destruct (Htotal σy Hσy) as [vout Hsteps].
    exists vout.
    change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
      (tret (vfvar x)) →* tret vout).
    rewrite (msubst_tret_fvar_store_swap_lookup
      (store_restrict σy (D ∪ {[y]})) x y vy
      (proj1 Hclosedσ) Hlookup_restrict).
    exact Hsteps.
Qed.

Lemma expr_total_on_tapp_tm_fvar_swap_iff D e x y (m : WfWorld) :
  x ∉ D ∪ fv_tm e →
  y ∉ D ∪ fv_tm e →
  fv_tm e ⊆ D →
  D ∪ {[y]} ⊆ world_dom (m : World) →
  world_closed_on (D ∪ {[y]}) m →
  expr_total_on (D ∪ {[x]}) (tapp_tm e (vfvar x)) (res_swap x y m) ↔
  expr_total_on (D ∪ {[y]}) (tapp_tm e (vfvar y)) m.
Proof.
  intros Hx Hy Hfve Hdom Hclosed. split.
  - intros [_ Htotal]. split.
    { rewrite fv_tapp_tm. simpl. set_solver. }
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σ).
    { rewrite (wfworld_store_dom m σ Hσ). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σ (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    pose proof (Htotal (store_swap x y σ)) as Hsteps_total.
    assert ((res_swap x y m : World) (store_swap x y σ)) as Hσswap.
    { simpl. exists σ. split; [exact Hσ | reflexivity]. }
    specialize (Hsteps_total Hσswap) as [vout Hsteps].
    exists vout.
    rewrite store_restrict_swap_fresh_union_singleton in Hsteps by set_solver.
    change (m{store_restrict σ (D ∪ {[y]})} (tapp_tm e (vfvar y)) →* tret vout).
    rewrite <- (msubst_tapp_tm_fvar_store_swap_lookup
      (store_restrict σ (D ∪ {[y]})) e x y vy
      (proj1 Hclosedσ) Hlookup_restrict ltac:(set_solver) ltac:(set_solver)).
    exact Hsteps.
  - intros [_ Htotal]. split.
    { rewrite fv_tapp_tm. simpl. set_solver. }
    intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite store_restrict_swap_fresh_union_singleton by set_solver.
    pose proof (Hclosed σy Hσy) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σy).
    { rewrite (wfworld_store_dom m σy Hσy). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σy (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    destruct (Htotal σy Hσy) as [vout Hsteps].
    exists vout.
    change (m{store_swap x y (store_restrict σy (D ∪ {[y]}))}
      (tapp_tm e (vfvar x)) →* tret vout).
    rewrite (msubst_tapp_tm_fvar_store_swap_lookup
      (store_restrict σy (D ∪ {[y]})) e x y vy
      (proj1 Hclosedσ) Hlookup_restrict ltac:(set_solver) ltac:(set_solver)).
    exact Hsteps.
Qed.

Lemma swap_scoped_insert_dom x y D (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  D ∪ {[x]} ⊆ world_dom (res_swap x y m : World) →
  D ∪ {[y]} ⊆ world_dom (m : World).
Proof.
  intros Hx Hy Hscope z Hz.
  assert (Hzswap : atom_swap x y z ∈ D ∪ {[x]}).
  {
    rewrite !elem_of_union, !elem_of_singleton in Hz |- *.
    unfold atom_swap in *.
    repeat destruct decide; set_solver.
  }
  specialize (Hscope (atom_swap x y z) Hzswap).
  simpl in Hscope.
  rewrite elem_of_aset_swap in Hscope.
  rewrite atom_swap_involutive in Hscope.
  exact Hscope.
Qed.

Lemma denot_ty_fuel_rebuild_fresh_tret_from_body gas
    (Σ : gmap atom ty) τx x y (m : WfWorld) :
  cty_measure τx <= gas →
  x ∉ dom Σ →
  y ∉ dom Σ →
  basic_choice_ty (dom Σ) τx →
  res_swap x y m ⊨ denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
    τx (tret (vfvar x)) →
  m ⊨ denot_ty_fuel_body gas (<[y := erase_ty τx]> Σ)
    τx (tret (vfvar y)) →
  m ⊨ denot_ty_fuel gas (<[y := erase_ty τx]> Σ)
    τx (tret (vfvar y)).
Proof.
  intros Hgas Hx Hy Hbasic Hsrc Hbody.
  pose proof (res_models_with_store_fuel_scoped _ ∅ (res_swap x y m)
    (denot_ty_fuel gas (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
    Hsrc) as Hscope_src.
  assert (Hscope_y :
    dom (<[y := erase_ty τx]> Σ) ⊆ world_dom (m : World)).
  {
    replace (dom (<[y:=erase_ty τx]> Σ)) with (dom Σ ∪ {[y]})
      by (rewrite dom_insert_L; set_solver).
    eapply swap_scoped_insert_dom; [exact Hx | exact Hy |].
    replace (dom Σ ∪ {[x]}) with (dom (<[x:=erase_ty τx]> Σ))
      by (rewrite dom_insert_L; set_solver).
    etransitivity.
    - eapply (denot_ty_fuel_env_fv_subset
        gas (<[x:=erase_ty τx]> Σ) τx (tret (vfvar x))).
      exact Hgas.
    - unfold formula_scoped_in_world in Hscope_src.
      rewrite dom_empty_L in Hscope_src.
      intros z Hz. apply Hscope_src. apply elem_of_union. right. exact Hz.
  }
  eapply denot_ty_fuel_intro.
  - eapply basic_choice_ty_mono; [| exact Hbasic].
    rewrite dom_insert_L. set_solver.
  - apply basic_typing_tret_fvar_insert.
	  - pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
	      as Hclosed_src.
	    rewrite dom_insert_L in Hclosed_src.
	    rewrite dom_insert_L.
	    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
	    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
	    apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
	      (dom Σ) x y m Hx Hy)).
	    exact Hclosed_src.
  - pose proof (denot_ty_fuel_expr_total_on_of_formula _ _ _ _ _ Hsrc)
      as Htotal_src.
	    rewrite dom_insert_L in Htotal_src.
	    rewrite dom_insert_L.
	    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
	    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Htotal_src by set_solver.
	    assert (Hclosed_y : world_closed_on (dom Σ ∪ {[y]}) m).
	    {
	      pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
	        as Hclosed_src.
	      rewrite dom_insert_L in Hclosed_src.
	      replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
	      apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
	        (dom Σ) x y m Hx Hy)).
	      exact Hclosed_src.
	    }
	    apply (proj1 (expr_total_on_tret_fvar_swap_iff
	      (dom Σ) x y m Hx Hy
	      ltac:(rewrite dom_insert_L in Hscope_y;
	            intros z Hz; apply Hscope_y; set_solver)
	      Hclosed_y)).
	    exact Htotal_src.
  - exact Hbody.
  - exact Hscope_y.
Qed.

Lemma denot_ty_fuel_rebuild_fresh_tapp_from_body gas
    (Σ : gmap atom ty) τx τ e x y (m : WfWorld) :
  cty_measure ({0 ~> y} τ) <= gas →
  x ∉ dom Σ ∪ fv_tm e →
  y ∉ dom Σ ∪ fv_tm e →
  fv_tm e ⊆ dom Σ →
  basic_choice_ty (dom Σ ∪ {[y]}) ({0 ~> y} τ) →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  res_swap x y m ⊨ denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
    ({0 ~> x} τ) (tapp_tm e (vfvar x)) →
  m ⊨ denot_ty_fuel_body gas (<[y := erase_ty τx]> Σ)
    ({0 ~> y} τ) (tapp_tm e (vfvar y)) →
  m ⊨ denot_ty_fuel gas (<[y := erase_ty τx]> Σ)
    ({0 ~> y} τ) (tapp_tm e (vfvar y)).
Proof.
  intros Hgas Hx Hy Hfve Hbasic Htye Hsrc Hbody.
  pose proof (res_models_with_store_fuel_scoped _ ∅ (res_swap x y m)
    (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))) Hsrc) as Hscope_src.
  assert (Hscope_y :
    dom (<[y := erase_ty τx]> Σ) ⊆ world_dom (m : World)).
  {
    replace (dom (<[y:=erase_ty τx]> Σ)) with (dom Σ ∪ {[y]})
      by (rewrite dom_insert_L; set_solver).
    eapply swap_scoped_insert_dom;
      [intro H; apply Hx; set_solver
      |intro H; apply Hy; set_solver
      |].
    replace (dom Σ ∪ {[x]}) with (dom (<[x:=erase_ty τx]> Σ))
      by (rewrite dom_insert_L; set_solver).
    etransitivity.
    - eapply (denot_ty_fuel_env_fv_subset
        gas (<[x:=erase_ty τx]> Σ) ({0 ~> x} τ)
        (tapp_tm e (vfvar x))).
      rewrite !cty_open_preserves_measure in *. exact Hgas.
    - unfold formula_scoped_in_world in Hscope_src.
      rewrite dom_empty_L in Hscope_src.
      intros z Hz. apply Hscope_src. apply elem_of_union. right. exact Hz.
  }
  eapply denot_ty_fuel_intro.
  - eapply basic_choice_ty_mono; [| exact Hbasic].
    rewrite dom_insert_L. set_solver.
  - eapply basic_typing_tapp_tm_fvar_insert.
    + set_solver.
    + rewrite cty_open_preserves_erasure. exact Htye.
  - pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
      as Hclosed_src.
    rewrite dom_insert_L in Hclosed_src.
    rewrite dom_insert_L.
    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
    apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
      (dom Σ) x y m ltac:(set_solver) ltac:(set_solver))).
    exact Hclosed_src.
  - pose proof (denot_ty_fuel_expr_total_on_of_formula _ _ _ _ _ Hsrc)
      as Htotal_src.
    rewrite dom_insert_L in Htotal_src.
    rewrite dom_insert_L.
    replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Htotal_src by set_solver.
    assert (Hclosed_y : world_closed_on (dom Σ ∪ {[y]}) m).
    {
      pose proof (denot_ty_fuel_world_closed_on_of_formula _ _ _ _ _ Hsrc)
        as Hclosed_src.
      rewrite dom_insert_L in Hclosed_src.
      replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hclosed_src by set_solver.
      apply (proj1 (world_closed_on_swap_fresh_union_singleton_iff
        (dom Σ) x y m ltac:(set_solver) ltac:(set_solver))).
      exact Hclosed_src.
    }
    apply (proj1 (expr_total_on_tapp_tm_fvar_swap_iff
      (dom Σ) e x y m Hx Hy Hfve
      ltac:(rewrite dom_insert_L in Hscope_y;
            intros z Hz; apply Hscope_y; set_solver)
      Hclosed_y)).
    exact Htotal_src.
  - exact Hbody.
  - exact Hscope_y.
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

Lemma formula_family_rename_stable_and D P Q :
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FAnd (P x) (Q x)).
Proof.
  intros HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl.
  split; intros Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj1 (HP x y n Hx Hy)).
      apply res_models_and_elim_l in Hmodel. exact Hmodel.
    + apply (proj1 (HQ x y n Hx Hy)).
      apply res_models_and_elim_r in Hmodel. exact Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj2 (HP x y n Hx Hy)).
      apply res_models_and_elim_l in Hmodel. exact Hmodel.
    + apply (proj2 (HQ x y n Hx Hy)).
      apply res_models_and_elim_r in Hmodel. exact Hmodel.
Qed.

Lemma formula_family_rename_stable_const D φ :
  formula_fv φ ⊆ D →
  formula_family_rename_stable_on D (fun _ => φ).
Proof.
  intros Hfv.
  unfold formula_family_rename_stable_on.
  intros x y n Hx Hy.
  apply res_models_rename_atom_fresh; set_solver.
Qed.

Definition formula_family_support_exact_on (D : aset) (P : atom → FormulaQ) : Prop :=
  ∀ x, x ∉ D → formula_fv (P x) = D ∪ {[x]}.

Lemma formula_family_support_exact_and D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FAnd (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_or D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FOr (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_plus D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FPlus (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_impl D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FImpl (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma formula_family_support_exact_wand D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_support_exact_on D (fun x => FWand (P x) (Q x)).
Proof.
  intros HP HQ x Hx. simpl. rewrite HP, HQ by exact Hx. set_solver.
Qed.

Lemma atom_swap_left_eq x y : atom_swap x y x = y.
Proof. unfold atom_swap. repeat destruct decide; congruence. Qed.

Lemma atom_swap_right_eq x y : atom_swap x y y = x.
Proof. unfold atom_swap. repeat destruct decide; congruence. Qed.

Lemma denot_ty_fuel_fresh_arg_family_support_exact
    gas (Σ : gmap atom ty) τx :
  cty_measure τx <= gas →
  basic_choice_ty (dom Σ) τx →
  formula_family_support_exact_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      τx (tret (vfvar x))).
Proof.
  intros Hgas Hbasic x Hx.
  apply set_eq. intros z. split.
  - intros Hz.
    eapply denot_ty_fuel_formula_fv_subset_env in Hz.
    + rewrite dom_insert_L in Hz. set_solver.
    + exact Hgas.
    + eapply basic_choice_ty_fv_subset.
      eapply basic_choice_ty_mono; [| exact Hbasic].
      rewrite dom_insert_L. set_solver.
  - intros Hz.
    eapply denot_ty_fuel_env_fv_subset; [exact Hgas |].
    rewrite dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_fresh_result_family_support_exact
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τ <= gas →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_support_exact_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))).
Proof.
  intros Hgas Hbasic_body x Hx.
  apply set_eq. intros z. split.
  - intros Hz.
    eapply denot_ty_fuel_formula_fv_subset_env in Hz.
    + rewrite dom_insert_L in Hz. set_solver.
    + rewrite cty_open_preserves_measure. exact Hgas.
    + eapply basic_choice_ty_fv_subset.
      replace (dom (<[x:=erase_ty τx]> Σ)) with (dom Σ ∪ {[x]})
        by (rewrite dom_insert_L; set_solver).
      apply Hbasic_body. exact Hx.
  - intros Hz.
    eapply denot_ty_fuel_env_fv_subset.
    + rewrite cty_open_preserves_measure. exact Hgas.
    + rewrite dom_insert_L. set_solver.
Qed.

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
  fv_tm e ⊆ dom Σ →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
      ({0 ~> x} τ) (tapp_tm e (vfvar x))).
Proof.
Admitted.

Lemma denot_ty_fuel_arrow_body_family_support_exact
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_support_exact_on (dom Σ) (fun x =>
    FImpl
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hbasic_body.
  apply formula_family_support_exact_impl.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
Qed.

Lemma denot_ty_fuel_wand_body_family_support_exact
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_support_exact_on (dom Σ) (fun x =>
    FWand
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hbasic_body.
  apply formula_family_support_exact_wand.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
Qed.

Lemma support_exact_rename_to_target_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  n ⊨ formula_rename_atom x y (P x) →
  formula_fv (P y) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hmodel.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (formula_rename_atom x y (P x))) ∅ n
    (formula_rename_atom x y (P x)) Hmodel) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite dom_empty_L in Hscope.
  rewrite Hsupp by exact Hy.
  intros z Hz.
  apply Hscope.
  apply elem_of_union_r.
  rewrite formula_fv_rename_atom.
  rewrite Hsupp by exact Hx.
  rewrite elem_of_aset_swap.
  apply elem_of_union in Hz as [HzD | Hzy].
  - apply elem_of_union_l.
    rewrite atom_swap_fresh; [exact HzD | set_solver | set_solver].
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzy. subst z.
    rewrite atom_swap_right_eq. apply elem_of_singleton. reflexivity.
Qed.

Lemma support_exact_target_to_rename_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  n ⊨ P y →
  formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hmodel.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (P y)) ∅ n (P y) Hmodel) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  rewrite dom_empty_L in Hscope.
  rewrite formula_fv_rename_atom.
  rewrite Hsupp by exact Hx.
  intros z Hz.
  rewrite elem_of_aset_swap in Hz.
  apply Hscope.
  apply elem_of_union_r.
  rewrite Hsupp by exact Hy.
  apply elem_of_union in Hz as [HzD | Hzx].
  - apply elem_of_union_l.
    assert (Hzx : z ≠ x).
    { intros ->. rewrite atom_swap_left_eq in HzD. exact (Hy HzD). }
    assert (Hzy : z ≠ y).
    { intros ->. rewrite atom_swap_right_eq in HzD. exact (Hx HzD). }
    rewrite atom_swap_fresh in HzD by assumption. exact HzD.
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzx.
    apply elem_of_singleton.
    unfold atom_swap in Hzx. repeat destruct decide; congruence.
Qed.

Lemma support_exact_renamed_family_covers_target D P x y :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  D ∪ {[y]} ⊆ formula_fv (formula_rename_atom x y (P x)).
Proof.
  intros Hsupp Hx Hy z Hz.
  rewrite formula_fv_rename_atom.
  rewrite Hsupp by exact Hx.
  rewrite elem_of_aset_swap.
  apply elem_of_union in Hz as [HzD | Hzy].
  - apply elem_of_union_l.
    rewrite atom_swap_fresh; [exact HzD | set_solver | set_solver].
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzy. subst z.
    rewrite atom_swap_right_eq. apply elem_of_singleton. reflexivity.
Qed.

Lemma support_exact_renamed_scope_to_target_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World) →
  formula_fv (P y) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hscope.
  rewrite Hsupp by exact Hy.
  intros z Hz.
  apply Hscope.
  eapply support_exact_renamed_family_covers_target; eauto.
Qed.

Lemma support_exact_target_scope_to_renamed_scope D P x y n :
  formula_family_support_exact_on D P →
  x ∉ D →
  y ∉ D →
  formula_fv (P y) ⊆ world_dom (n : World) →
  formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World).
Proof.
  intros Hsupp Hx Hy Hscope z Hz.
  rewrite formula_fv_rename_atom in Hz.
  pose proof (Hsupp x Hx) as Hsuppx.
  rewrite Hsuppx in Hz.
  rewrite elem_of_aset_swap in Hz.
  apply Hscope.
  rewrite Hsupp by exact Hy.
  apply elem_of_union in Hz as [HzD | Hzx].
  - apply elem_of_union_l.
    assert (Hz_ne_x : z ≠ x).
    { intros ->. rewrite atom_swap_left_eq in HzD. exact (Hy HzD). }
    assert (Hz_ne_y : z ≠ y).
    { intros ->. rewrite atom_swap_right_eq in HzD. exact (Hx HzD). }
    rewrite atom_swap_fresh in HzD by assumption. exact HzD.
  - apply elem_of_union_r.
    apply elem_of_singleton in Hzx.
    apply elem_of_singleton.
    unfold atom_swap in Hzx. repeat destruct decide; congruence.
Qed.

Lemma formula_family_rename_stable_or_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FOr (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FOr (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FOr (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_or_transport_between_worlds; [| | | | exact Hmodel].
    + eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + apply (proj1 (HP x y n Hx Hy)).
    + apply (proj1 (HQ x y n Hx Hy)).
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FOr (P y) (Q y))) ∅ n
      (FOr (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_or_transport_between_worlds; [| | | | exact Hmodel].
    + eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
      simpl in Hscope. set_solver.
    + apply (proj2 (HP x y n Hx Hy)).
    + apply (proj2 (HQ x y n Hx Hy)).
Qed.

Lemma formula_family_rename_stable_plus_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FPlus (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FPlus (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FPlus (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_plus_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (P y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (Q y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' Hm'. apply (proj1 (HP x y m' Hx Hy)). exact Hm'.
    + intros m' Hm'. apply (proj1 (HQ x y m' Hx Hy)). exact Hm'.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FPlus (P y) (Q y))) ∅ n
      (FPlus (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_plus_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (formula_rename_atom x y (Q x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' Hm'. apply (proj2 (HP x y m' Hx Hy)). exact Hm'.
    + intros m' Hm'. apply (proj2 (HQ x y m' Hx Hy)). exact Hm'.
Qed.

Lemma formula_family_rename_stable_impl_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FImpl (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FImpl (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FImpl (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_impl_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (P y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (Q y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPy. apply (proj2 (HP x y m' Hx Hy)). exact HPy.
    + intros m' _ HQx. apply (proj1 (HQ x y m' Hx Hy)). exact HQx.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FImpl (P y) (Q y))) ∅ n
      (FImpl (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_impl_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (formula_rename_atom x y (Q x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPx. apply (proj1 (HP x y m' Hx Hy)). exact HPx.
    + intros m' _ HQy. apply (proj2 (HQ x y m' Hx Hy)). exact HQy.
Qed.

Lemma formula_family_rename_stable_wand_exact D P Q :
  formula_family_support_exact_on D P →
  formula_family_support_exact_on D Q →
  formula_family_rename_stable_on D P →
  formula_family_rename_stable_on D Q →
  formula_family_rename_stable_on D (fun x => FWand (P x) (Q x)).
Proof.
  intros HPsupp HQsupp HP HQ.
  unfold formula_family_rename_stable_on in *.
  intros x y n Hx Hy. simpl. split; intros Hmodel.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FWand (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x)))) ∅ n
      (FWand (formula_rename_atom x y (P x))
         (formula_rename_atom x y (Q x))) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_wand_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (P y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (Q y) ⊆ world_dom (n : World)).
      { eapply support_exact_renamed_scope_to_target_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPy. apply (proj2 (HP x y m' Hx Hy)). exact HPy.
    + intros m' Hc HQx.
      apply (proj1 (HQ x y (res_product m' n Hc) Hx Hy)). exact HQx.
  - pose proof (res_models_with_store_fuel_scoped
      (formula_measure (FWand (P y) (Q y))) ∅ n
      (FWand (P y) (Q y)) Hmodel) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    eapply res_models_wand_map; [| | | exact Hmodel].
    + unfold formula_scoped_in_world. simpl.
      assert (HPscope : formula_fv (formula_rename_atom x y (P x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HPsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      assert (HQscope : formula_fv (formula_rename_atom x y (Q x)) ⊆ world_dom (n : World)).
      { eapply support_exact_target_scope_to_renamed_scope; [exact HQsupp | exact Hx | exact Hy |].
        simpl in Hscope. set_solver. }
      set_solver.
    + intros m' _ HPx. apply (proj1 (HP x y m' Hx Hy)). exact HPx.
    + intros m' Hc HQy.
      apply (proj2 (HQ x y (res_product m' n Hc) Hx Hy)). exact HQy.
Qed.

Lemma denot_ty_fuel_arrow_body_family_rename_stable
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  fv_tm e ⊆ dom Σ →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    FImpl
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hfve Htye Hbasic_body.
  apply formula_family_rename_stable_impl_exact.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_arg_family_rename_stable; eauto.
  - eapply denot_ty_fuel_fresh_result_family_rename_stable; eauto.
Qed.

Lemma denot_ty_fuel_wand_body_family_rename_stable
    gas (Σ : gmap atom ty) τx τ e :
  cty_measure τx <= gas →
  cty_measure τ <= gas →
  basic_choice_ty (dom Σ) τx →
  fv_tm e ⊆ dom Σ →
  Σ ⊢ₑ e ⋮ (erase_ty τx →ₜ erase_ty τ) →
  (∀ x, x ∉ dom Σ → basic_choice_ty (dom Σ ∪ {[x]}) ({0 ~> x} τ)) →
  formula_family_rename_stable_on (dom Σ) (fun x =>
    FWand
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)))
      (denot_ty_fuel gas (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp_tm e (vfvar x)))).
Proof.
  intros Hgasx Hgas Hbasicx Hfve Htye Hbasic_body.
  apply formula_family_rename_stable_wand_exact.
  - eapply denot_ty_fuel_fresh_arg_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_result_family_support_exact; eauto.
  - eapply denot_ty_fuel_fresh_arg_family_rename_stable; eauto.
  - eapply denot_ty_fuel_fresh_result_family_rename_stable; eauto.
Qed.

Lemma denot_ty_fuel_drop_fresh_env_irrel gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e.
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
Admitted.

Lemma denot_ty_fuel_insert_fresh_env_irrel_iff gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e <->
  res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e.
Proof.
  intros Hgas Hx Hdom Hclosed Htotal. split.
  - eapply denot_ty_fuel_drop_fresh_env_irrel; eauto.
  - eapply denot_ty_fuel_insert_fresh_env_irrel; eauto.
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

Lemma FExprContIn_FResultBasicWorld_insert_fresh_type_env_irrel
    (Σ : gmap atom ty) x T b D e R (m : WfWorld) :
  x ∉ dom Σ ∪ lvars_fv D →
  m ⊨ FExprContIn (<[x := T]> Σ) e
      (FAnd (FResultBasicWorld (atom_env_to_lty_env (<[x := T]> Σ)) b D) R) <->
  m ⊨ FExprContIn (<[x := T]> Σ) e
      (FAnd (FResultBasicWorld (atom_env_to_lty_env Σ) b D) R).
Proof.
  intros Hx.
  apply res_models_of_formula_store_equiv.
  eapply FExprContIn_post_open_store_equiv.
  - cbn [formula_fv].
    rewrite !formula_fv_FResultBasicWorld_atom_env.
    reflexivity.
  - intros ν Hν.
    cbn [formula_open formula_fv].
    rewrite !formula_fv_FResultBasicWorld_atom_env_insert_fresh_open by exact Hx.
    reflexivity.
  - intros ν Hν.
    apply formula_store_equiv_and.
    + apply formula_fv_FResultBasicWorld_atom_env_insert_fresh_open.
      exact Hx.
    + reflexivity.
    + apply formula_store_equiv_FResultBasicWorld_atom_env_insert_fresh_open.
      exact Hx.
    + apply formula_store_equiv_refl.
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
  cbn [denot_ty_fuel_body denot_ty_fuel_body_lvar cty_measure].
  rewrite !FExprContIn_atom_env_to_lty_env.
  pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hfvτ.
  simpl in Hfvτ.
  destruct φ as [Dφ Pφ]; simpl in *.
  etransitivity.
  - eapply FExprContIn_FResultBasicWorld_insert_fresh_type_env_irrel.
    set_solver.
  - change (let_result_world_on e1 x m Hfresh Hresult
      ⊨ FExprContIn (<[x:=T1]> Δ) (e2 ^^ x)
          (fun _ : atom =>
            FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
              (FFibVars (Dφ) (FOver (FTypeQualifier (qual Dφ Pφ))))) <->
      m ⊨ FExprContIn Δ (tlete e1 e2)
          (fun _ : atom =>
            FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
              (FFibVars (Dφ) (FOver (FTypeQualifier (qual Dφ Pφ)))))).
    eapply FExprCont_tlet_reduction; eauto; try set_solver.
    + intros ν. cbn [formula_fv].
    eapply union_least.
      * pose proof (formula_fv_FResultBasicWorld_atom_env_subset Δ b Dφ Hfvτ).
        set_solver.
      * set_solver.
    + apply formula_family_rename_stable_const.
      intros ν. cbn [formula_fv].
      eapply union_least.
      * pose proof (formula_fv_FResultBasicWorld_atom_env_subset Δ b Dφ Hfvτ).
        set_solver.
      * set_solver.
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
  cbn [denot_ty_fuel_body denot_ty_fuel_body_lvar cty_measure].
  rewrite !FExprContIn_atom_env_to_lty_env.
  pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hfvτ.
  simpl in Hfvτ.
  destruct φ as [Dφ Pφ]; simpl in *.
  etransitivity.
  - eapply FExprContIn_FResultBasicWorld_insert_fresh_type_env_irrel.
    set_solver.
  - change (let_result_world_on e1 x m Hfresh Hresult
      ⊨ FExprContIn (<[x:=T1]> Δ) (e2 ^^ x)
          (fun _ : atom =>
            FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
              (FFibVars (Dφ) (FUnder (FTypeQualifier (qual Dφ Pφ))))) <->
      m ⊨ FExprContIn Δ (tlete e1 e2)
          (fun _ : atom =>
            FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
              (FFibVars (Dφ) (FUnder (FTypeQualifier (qual Dφ Pφ)))))).
    eapply FExprCont_tlet_reduction; eauto; try set_solver.
    + intros ν. cbn [formula_fv].
    eapply union_least.
      * pose proof (formula_fv_FResultBasicWorld_atom_env_subset Δ b Dφ Hfvτ).
        set_solver.
      * set_solver.
    + apply formula_family_rename_stable_const.
      intros ν. cbn [formula_fv].
      eapply union_least.
      * pose proof (formula_fv_FResultBasicWorld_atom_env_subset Δ b Dφ Hfvτ).
        set_solver.
      * set_solver.
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
  intros Σ Γ τ1 e1 e2 m x Hfresh Hresult Hregular He1 Hlet Hctx Htotal Hx.
  set (Δ := erase_ctx_under Σ Γ).
  assert (HbasicΓ : basic_ctx (dom Σ) Γ) by exact (proj1 Hregular).
  assert (Hbasicτ : basic_choice_ty (dom Δ) τ2) by exact (proj2 Hregular).
  assert (Hcover : dom Δ ⊆ world_dom (m : World)).
  { subst Δ. eapply denot_ctx_in_env_world_covers_erased; eauto. }
  assert (HxΔ : x ∉ dom Δ) by (subst Δ; set_solver).
  assert (Hfresh0 : x ∉ world_dom (res_restrict m (dom Δ) : World)).
  { simpl. set_solver. }
  assert (Hfv1 : fv_tm e1 ⊆ dom Δ).
  { subst Δ. eapply basic_typing_contains_fv_tm. exact He1. }
  assert (Hclosed_m : world_store_closed_on (dom Δ) m).
  { subst Δ. eapply denot_ctx_in_env_world_store_closed_on_erased; eauto. }
  assert (Hresult0 : ∀ σ, (res_restrict m (dom Δ) : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx).
  {
    intros σ Hσ.
    destruct Hσ as [σm [Hσm Hrestrict]].
    destruct (Hresult σm Hσm) as [vx Hsteps].
    exists vx.
    replace (store_restrict σ (fv_tm e1))
      with (store_restrict σm (fv_tm e1)).
    - exact Hsteps.
    - rewrite <- Hrestrict.
      store_norm.
      replace (dom Δ ∩ fv_tm e1) with (fv_tm e1) by set_solver.
      reflexivity.
  }
  assert (Hclosed0 : world_store_closed_on (dom Δ) (res_restrict m (dom Δ))).
  { eapply world_store_closed_on_restrict; [reflexivity | exact Hclosed_m]. }
  assert (Htotal0 :
      expr_total_on (dom Δ) (tlete e1 e2) (res_restrict m (dom Δ))).
  { apply expr_total_on_restrict_self. exact Htotal. }
  assert (Hctx_fv : formula_fv (denot_ctx_in_env Σ Γ) ⊆ dom Δ).
  {
    subst Δ.
    unfold denot_ctx_in_env.
    cbn [formula_fv].
    rewrite !basic_world_formula_fv.
    pose proof (denot_ctx_under_formula_fv_subset Σ Γ) as Hctx_fv.
    pose proof (basic_ctx_fv_subset (dom Σ) Γ HbasicΓ) as HΓfv.
    rewrite erase_ctx_under_dom_basic by exact HbasicΓ.
    rewrite ctx_stale_eq_fv_dom in Hctx_fv.
    set_solver.
  }
  assert (Hctx0 : res_restrict m (dom Δ) ⊨ denot_ctx_in_env Σ Γ).
  { exact (proj1 (res_models_minimal_on (dom Δ) m
      (denot_ctx_in_env Σ Γ) Hctx_fv) Hctx). }
  assert (Hbody_env :
      erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) =
      <[x := erase_ty τ1]> Δ).
  { subst Δ. apply erase_ctx_under_comma_bind_env_fresh. exact HxΔ. }
  assert (Hbody_fv :
      formula_fv
        (denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))
      ⊆ dom Δ ∪ {[x]}).
  {
    unfold denot_ty_in_ctx_under, denot_ty_on.
    rewrite Hbody_env.
    pose proof (denot_ty_fuel_formula_fv_subset_env
      (cty_measure τ2) (<[x:=erase_ty τ1]> Δ) τ2 (e2 ^^ x)
      ltac:(lia)
      ltac:(eapply basic_choice_ty_fv_subset;
        eapply basic_choice_ty_mono; [| exact Hbasicτ];
        rewrite dom_insert_L; set_solver)) as Hfv.
    rewrite dom_insert_L in Hfv.
    set_solver.
  }
  assert (Htarget_fv :
      formula_fv (denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2)) ⊆ dom Δ).
  {
    subst Δ.
    unfold denot_ty_in_ctx_under, denot_ty_on.
    eapply denot_ty_fuel_formula_fv_subset_env; [lia |].
    eapply basic_choice_ty_fv_subset. exact Hbasicτ.
  }
  assert (Hresult_world_restrict :
      res_restrict (let_result_world_on e1 x m Hfresh Hresult)
        (dom Δ ∪ {[x]}) =
      let_result_world_on e1 x (res_restrict m (dom Δ)) Hfresh0 Hresult0).
  {
    eapply let_result_world_on_restrict_input.
    - exact Hfv1.
    - exact Hcover.
    - exact HxΔ.
  }
  pose proof (denot_ty_tlet_reduction_formula
    τ2 Σ Γ τ1 e1 e2 (res_restrict m (dom Δ)) x
    Hfresh0 Hresult0 Hregular He1 Hlet
    ltac:(simpl; set_solver) Hctx0 Htotal0 Hx) as Hexact.
  split; intros Hmodel.
  - apply (proj2 (res_models_minimal_on (dom Δ) m
      (denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2)) Htarget_fv)).
    apply (proj1 Hexact).
    rewrite <- Hresult_world_restrict.
    apply (proj1 (res_models_minimal_on (dom Δ ∪ {[x]})
      (let_result_world_on e1 x m Hfresh Hresult)
      (denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))
      Hbody_fv)).
    exact Hmodel.
  - apply (proj2 (res_models_minimal_on (dom Δ ∪ {[x]})
      (let_result_world_on e1 x m Hfresh Hresult)
      (denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x))
      Hbody_fv)).
    rewrite Hresult_world_restrict.
    apply (proj2 Hexact).
    apply (proj1 (res_models_minimal_on (dom Δ) m
      (denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2)) Htarget_fv)).
    exact Hmodel.
Qed.

Lemma expr_total_tlet_reduction
    (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e1 m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_tm e2 →
  expr_total_on (dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1))))
    (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult)
  <->
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m.
Proof.
  intros Hlet HbasicΓ Hctx Htotal1 Hx.
  rewrite erase_ctx_under_comma_bind_dom_nf.
  split.
  - intros Hbody.
    eapply expr_total_on_tlete_intro_strong.
    + eapply denot_ctx_in_env_world_covers_erased; eauto.
    + intros Hbad. apply Hx. apply elem_of_union_l. exact Hbad.
    + intros Hbad. apply Hx. apply elem_of_union_r. exact Hbad.
    + eapply denot_ctx_in_env_world_store_closed_on_erased; eauto.
    + eapply typing_tm_lc; eauto.
    + exact Htotal1.
    + exact Hbody.
  - intros Hlet_total.
    eapply expr_total_on_tlete_elim_body_strong.
    + eapply denot_ctx_in_env_world_covers_erased; eauto.
    + intros Hbad. apply Hx. apply elem_of_union_l. exact Hbad.
    + intros Hbad. apply Hx. apply elem_of_union_r. exact Hbad.
    + eapply denot_ctx_in_env_world_store_closed_on_erased; eauto.
    + eapply typing_tm_lc; eauto.
    + exact Hlet_total.
Qed.

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
	      Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult Hlet
        (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel1) Hctx
        (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel1)
        ltac:(set_solver))
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
        Σ Γ τ1 τ2 e1 e2 m x Hfresh Hresult Hlet
        (denot_ty_total_model_basic_ctx Σ Γ τ1 e1 m Hmodel1) Hctx
        (denot_ty_total_model_total Σ Γ τ1 e1 m Hmodel1)
        ltac:(set_solver))).
      exact Htotal_target.
Qed.

(** The total [tlet] rule after splitting the body premise cofinally. *)
