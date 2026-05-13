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
  intros Hx Hdom Hclosed [Hfv [n Htotal]].
  split; [set_solver |].
  exists n.
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

Lemma expr_total_on_drop_insert_fresh_same
    (Σ : gmap atom ty) T e x (m : WfWorld) :
  x ∉ dom Σ ∪ fv_tm e →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  expr_total_on (dom Σ) e m.
Proof.
  intros Hx Hclosed [Hfv [n Htotal]].
  split; [set_solver |].
  exists n.
  intros σ Hσ.
  specialize (Htotal σ Hσ).
  replace (subst_map (store_restrict σ (dom Σ)) e)
    with (subst_map (store_restrict σ (dom (<[x := T]> Σ))) e).
  - exact Htotal.
  - symmetry.
    eapply subst_map_eq_on_fv.
    + apply closed_env_restrict. exact (proj1 (Hclosed σ Hσ)).
    + rewrite !store_restrict_restrict.
      f_equal. rewrite dom_insert_L. set_solver.
Qed.

Lemma expr_total_on_restrict_self X e (m : WfWorld) :
  expr_total_on X e m →
  expr_total_on X e (res_restrict m X).
Proof.
  intros [Hfv [n Htotal]]. split; [exact Hfv |].
  exists n.
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

Lemma FExprContIn_insert_fresh_env_irrel_iff_at_world
    (Σ : gmap atom ty) T Tx e x (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  x ∉ dom Σ ∪ fv_tm e →
  dom (<[x := Tx]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := Tx]> Σ)) m →
  expr_total_on (dom (<[x := Tx]> Σ)) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn (<[x := Tx]> Σ) e P <->
  m ⊨ FExprContIn Σ e P.
Proof.
  intros Hty Hx Hdom_sub Hclosed Htotal HPfv HPrename.
  assert (Hdom_ins :
    world_dom (res_restrict m (dom (<[x:=Tx]> Σ)) : World) =
    dom (<[x:=Tx]> Σ)).
  { simpl. set_solver. }
  assert (Hclosed_ins :
    world_store_closed_on (dom (<[x:=Tx]> Σ))
      (res_restrict m (dom (<[x:=Tx]> Σ)))).
  {
    eapply world_store_closed_on_restrict.
    - reflexivity.
    - exact Hclosed.
  }
  assert (Htotal_ins :
    expr_total_on (dom (<[x:=Tx]> Σ)) e
      (res_restrict m (dom (<[x:=Tx]> Σ)))).
  { apply expr_total_on_restrict_self. exact Htotal. }
  assert (Hfv_ins :
    formula_fv (FExprContIn (<[x:=Tx]> Σ) e P) ⊆ dom (<[x:=Tx]> Σ)).
  {
    apply FExprContIn_formula_fv_subset.
    - reflexivity.
    - intros ν _. specialize (HPfv ν).
      rewrite dom_insert_L. set_solver.
  }
  assert (Hfv_base :
    formula_fv (FExprContIn Σ e P) ⊆ dom (<[x:=Tx]> Σ)).
  {
    apply FExprContIn_formula_fv_subset.
    - rewrite dom_insert_L. set_solver.
    - intros ν _. specialize (HPfv ν).
      rewrite dom_insert_L. set_solver.
  }
  assert (Hfv_base_small :
    formula_fv (FExprContIn Σ e P) ⊆ dom Σ).
  {
    apply FExprContIn_formula_fv_subset.
    - reflexivity.
    - intros ν _. apply HPfv.
  }
  split.
  - intros Hm.
    pose proof (proj1 (res_models_minimal_on
      (dom (<[x:=Tx]> Σ)) m (FExprContIn (<[x:=Tx]> Σ) e P)
      Hfv_ins) Hm) as Hm_min.
    pose proof (proj1 (FExprContIn_insert_fresh_env_irrel_iff
      Σ T Tx e x P (res_restrict m (dom (<[x:=Tx]> Σ))
      ) Hty Hx Hdom_ins Hclosed_ins Htotal_ins HPfv HPrename) Hm_min)
      as Hbase_min.
    rewrite res_restrict_restrict_eq in Hbase_min.
    replace (dom (<[x:=Tx]> Σ) ∩ dom Σ) with (dom Σ) in Hbase_min
      by (rewrite dom_insert_L; set_solver).
    eapply res_models_kripke; [apply res_restrict_le | exact Hbase_min].
  - intros Hm.
    pose proof (proj1 (res_models_minimal_on
      (dom (<[x:=Tx]> Σ)) m (FExprContIn Σ e P)
      Hfv_base) Hm) as Hbase_big_min.
    pose proof (proj1 (res_models_minimal_on
      (dom Σ) (res_restrict m (dom (<[x:=Tx]> Σ))
      ) (FExprContIn Σ e P) Hfv_base_small) Hbase_big_min)
      as Hbase_big_min'.
    assert (Hbase_nested :
      res_restrict (res_restrict m (dom (<[x:=Tx]> Σ))) (dom Σ)
        ⊨ FExprContIn Σ e P).
    { exact Hbase_big_min'. }
    pose proof (proj2 (FExprContIn_insert_fresh_env_irrel_iff
      Σ T Tx e x P (res_restrict m (dom (<[x:=Tx]> Σ))
      ) Hty Hx Hdom_ins Hclosed_ins Htotal_ins HPfv HPrename) Hbase_nested)
      as Hins_min.
    eapply res_models_kripke; [apply res_restrict_le | exact Hins_min].
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
           ++ exact Hclosed.
           ++ exact Htotal.
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

Lemma world_store_closed_on_extend X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_store_closed_on X m →
  world_store_closed_on X n.
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

Lemma world_store_closed_on_sum_le_l X (m n1 n2 : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  X ⊆ world_dom (n1 : World) →
  world_store_closed_on X m →
  res_sum n1 n2 Hdef ⊑ m →
  world_store_closed_on X n1.
Proof.
  intros HX Hclosed Hle σ Hσ.
  pose proof (res_restrict_eq_of_le (res_sum n1 n2 Hdef) m Hle) as Hrestrict.
  assert ((res_restrict m (world_dom (res_sum n1 n2 Hdef : World)) : World) σ)
    as HσR.
  { rewrite Hrestrict. simpl. left. exact Hσ. }
  destruct HσR as [σm [Hσm Hstore]].
  replace (store_restrict σ X) with (store_restrict σm X).
  - exact (Hclosed σm Hσm).
  - rewrite <- Hstore.
    rewrite store_restrict_restrict.
    replace (world_dom (res_sum n1 n2 Hdef : World) ∩ X) with X by set_solver.
    reflexivity.
Qed.

Lemma world_store_closed_on_sum_le_r X (m n1 n2 : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  X ⊆ world_dom (n2 : World) →
  world_store_closed_on X m →
  res_sum n1 n2 Hdef ⊑ m →
  world_store_closed_on X n2.
Proof.
  intros HX Hclosed Hle σ Hσ.
  pose proof (res_restrict_eq_of_le (res_sum n1 n2 Hdef) m Hle) as Hrestrict.
  assert ((res_restrict m (world_dom (res_sum n1 n2 Hdef : World)) : World) σ)
    as HσR.
  { rewrite Hrestrict. simpl. right. exact Hσ. }
  destruct HσR as [σm [Hσm Hstore]].
  replace (store_restrict σ X) with (store_restrict σm X).
  - exact (Hclosed σm Hσm).
  - rewrite <- Hstore.
    rewrite store_restrict_restrict.
    replace (world_dom (res_sum n1 n2 Hdef : World) ∩ X) with X.
    + reflexivity.
    + simpl.
      apply set_eq. intros z. split.
      * intros Hz. apply elem_of_intersection. split; [| exact Hz].
        unfold raw_sum_defined in Hdef. rewrite Hdef. apply HX. exact Hz.
      * intros Hz. apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
Qed.

Lemma expr_total_on_sum_le_l X e (m n1 n2 : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  X ⊆ world_dom (n1 : World) →
  expr_total_on X e m →
  res_sum n1 n2 Hdef ⊑ m →
  expr_total_on X e n1.
Proof.
  intros HX [Hfv [n Htotal]] Hle. split; [exact Hfv |].
  exists n.
  intros σ Hσ.
  pose proof (res_restrict_eq_of_le (res_sum n1 n2 Hdef) m Hle) as Hrestrict.
  assert ((res_restrict m (world_dom (res_sum n1 n2 Hdef : World)) : World) σ)
    as HσR.
  { rewrite Hrestrict. simpl. left. exact Hσ. }
  destruct HσR as [σm [Hσm Hstore]].
  replace (store_restrict σ X) with (store_restrict σm X).
  - exact (Htotal σm Hσm).
  - rewrite <- Hstore.
    rewrite store_restrict_restrict.
    replace (world_dom (res_sum n1 n2 Hdef : World) ∩ X) with X by set_solver.
    reflexivity.
Qed.

Lemma expr_total_on_sum_le_r X e (m n1 n2 : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  X ⊆ world_dom (n2 : World) →
  expr_total_on X e m →
  res_sum n1 n2 Hdef ⊑ m →
  expr_total_on X e n2.
Proof.
  intros HX [Hfv [n Htotal]] Hle. split; [exact Hfv |].
  exists n.
  intros σ Hσ.
  pose proof (res_restrict_eq_of_le (res_sum n1 n2 Hdef) m Hle) as Hrestrict.
  assert ((res_restrict m (world_dom (res_sum n1 n2 Hdef : World)) : World) σ)
    as HσR.
  { rewrite Hrestrict. simpl. right. exact Hσ. }
  destruct HσR as [σm [Hσm Hstore]].
  replace (store_restrict σ X) with (store_restrict σm X).
  - exact (Htotal σm Hσm).
  - rewrite <- Hstore.
    rewrite store_restrict_restrict.
    replace (world_dom (res_sum n1 n2 Hdef : World) ∩ X) with X.
    + reflexivity.
    + simpl.
      apply set_eq. intros z. split.
      * intros Hz. apply elem_of_intersection. split; [| exact Hz].
        unfold raw_sum_defined in Hdef. rewrite Hdef. apply HX. exact Hz.
      * intros Hz. apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
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
  destruct (res_models_with_store_resource_atom_elim ∅ m (dom Σ)
    (world_closed_on (dom Σ)) Hm) as [m0 [Hscope [Hclosed Hle]]].
  eapply (world_closed_on_extend (dom Σ) (res_restrict m0 (dom Σ)) m).
  - simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
    unfold stale, stale_logic_qualifier in Hscope. simpl in Hscope.
    rewrite dom_empty_L in Hscope.
    intros z Hz. simpl. apply elem_of_intersection. split.
    + apply Hscope. set_solver.
    + exact Hz.
  - etrans; [apply res_restrict_le | exact Hle].
  - exact Hclosed.
Qed.

Lemma denot_ty_fuel_world_store_closed_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  world_store_closed_on (dom Σ) m.
Proof.
  apply denot_ty_fuel_world_closed_on_of_formula.
Qed.

Lemma denot_ty_fuel_expr_total_on_of_formula gas Σ τ e m :
  m ⊨ denot_ty_fuel gas Σ τ e →
  expr_total_on (dom Σ) e m.
Proof.
  intros Hm.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hm)
    as [_ Htyped].
  split.
  - eapply basic_typing_contains_fv_tm. exact Htyped.
  - rewrite denot_ty_fuel_unfold in Hm.
    unfold denot_ty_obligations, FStrongTotalIn in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_r in Hm.
    apply res_models_with_store_and_elim_l in Hm.
    destruct (res_models_with_store_store_resource_atom_elim ∅ m (dom Σ)
      (fun ρ m => expr_total_with_store (dom Σ) e ρ m) Hm)
      as [m0 [Hscope [Htotal Hle]]].
    destruct Htotal as [_ [n Htotal]].
    exists n.
    intros σ Hσ.
    pose proof (res_restrict_eq_of_le m0 m Hle) as Hrestrict.
    assert ((res_restrict m (world_dom (m0 : World)) : World)
      (store_restrict σ (world_dom (m0 : World)))) as Hσm0.
    { exists σ. split; [exact Hσ | reflexivity]. }
    rewrite Hrestrict in Hσm0.
	    replace (store_restrict σ (dom Σ)) with
	      (store_restrict (store_restrict σ (world_dom (m0 : World))) (dom Σ)).
	    2:{
	      rewrite store_restrict_restrict.
	      replace (world_dom (m0 : World) ∩ dom Σ) with (dom Σ).
	      - reflexivity.
	      - apply set_eq. intros z. split; intros Hz.
	        + apply elem_of_intersection. split; [| exact Hz].
	          unfold formula_scoped_in_world in Hscope. simpl in Hscope.
	          unfold stale, stale_logic_qualifier in Hscope. simpl in Hscope.
	          rewrite dom_empty_L in Hscope.
	          apply Hscope. set_solver.
	        + apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
    }
    rewrite store_restrict_empty in Htotal.
    assert ((res_restrict m0 (dom Σ) : World)
      (store_restrict (store_restrict σ (world_dom (m0 : World))) (dom Σ))) as HσD.
    { exists (store_restrict σ (world_dom (m0 : World))).
      split; [exact Hσm0 | reflexivity]. }
    specialize (Htotal _ HσD).
    rewrite map_empty_union in Htotal.
    rewrite store_restrict_restrict in Htotal.
    replace (dom Σ ∩ dom Σ) with (dom Σ) in Htotal by set_solver.
    exact Htotal.
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

Lemma strongly_normalizing_tret_fvar_store_swap_lookup σ x y v :
  closed_env σ →
  σ !! y = Some v →
  strongly_normalizing (m{store_swap x y σ} (tret (vfvar x))) ↔
  strongly_normalizing (m{σ} (tret (vfvar y))).
Proof.
  intros Hclosed Hlookup.
  rewrite (msubst_tret_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

Lemma strongly_normalizing_fuel_tret_fvar_store_swap_lookup n σ x y v :
  closed_env σ →
  σ !! y = Some v →
  strongly_normalizing_fuel n (m{store_swap x y σ} (tret (vfvar x))) ↔
  strongly_normalizing_fuel n (m{σ} (tret (vfvar y))).
Proof.
  intros Hclosed Hlookup.
  rewrite (msubst_tret_fvar_store_swap_lookup σ x y v Hclosed Hlookup).
  reflexivity.
Qed.

Lemma strongly_normalizing_tapp_tm_fvar_store_swap_lookup σ e x y v :
  closed_env σ →
  σ !! y = Some v →
  x ∉ fv_tm e →
  y ∉ fv_tm e →
  strongly_normalizing (m{store_swap x y σ} (tapp_tm e (vfvar x))) ↔
  strongly_normalizing (m{σ} (tapp_tm e (vfvar y))).
Proof.
  intros Hclosed Hlookup Hx Hy.
  rewrite (msubst_tapp_tm_fvar_store_swap_lookup σ e x y v
    Hclosed Hlookup Hx Hy).
  reflexivity.
Qed.

Lemma strongly_normalizing_fuel_tapp_tm_fvar_store_swap_lookup n σ e x y v :
  closed_env σ →
  σ !! y = Some v →
  x ∉ fv_tm e →
  y ∉ fv_tm e →
  strongly_normalizing_fuel n (m{store_swap x y σ} (tapp_tm e (vfvar x))) ↔
  strongly_normalizing_fuel n (m{σ} (tapp_tm e (vfvar y))).
Proof.
  intros Hclosed Hlookup Hx Hy.
  rewrite (msubst_tapp_tm_fvar_store_swap_lookup σ e x y v
    Hclosed Hlookup Hx Hy).
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

Lemma FExprContIn_tret_fvar_swap_iff
    (Σ : gmap atom ty) T (P : atom → FormulaQ)
    x y (m : WfWorld) :
  x ∉ dom Σ →
  y ∉ dom Σ →
  world_dom (m : World) = dom Σ ∪ {[y]} →
  world_store_closed_on (dom Σ ∪ {[y]}) m →
  expr_total_on (dom Σ ∪ {[x]}) (tret (vfvar x)) (res_swap x y m) →
  expr_total_on (dom Σ ∪ {[y]}) (tret (vfvar y)) m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  res_swap x y m ⊨ FExprContIn (<[x := T]> Σ) (tret (vfvar x)) P ↔
  m ⊨ FExprContIn (<[y := T]> Σ) (tret (vfvar y)) P.
Proof.
  intros Hx Hy Hdom Hclosed Htotal_src_base Htotal HPfv HPrename.
  assert (Hdom_src :
    world_dom (res_swap x y m : World) = dom (<[x := T]> Σ)).
  {
    simpl. rewrite Hdom, aset_swap_union, aset_swap_singleton.
    replace (atom_swap x y y) with x
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by set_solver.
    rewrite dom_insert_L. set_solver.
  }
  assert (Hclosed_src :
    world_store_closed_on (dom (<[x := T]> Σ)) (res_swap x y m)).
  {
    rewrite dom_insert_L.
    replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) by set_solver.
    pose proof (world_store_closed_on_swap x y (dom Σ ∪ {[y]}) m Hclosed)
      as Hswap_closed.
    replace (aset_swap x y (dom Σ ∪ {[y]})) with (dom Σ ∪ {[x]})
      in Hswap_closed.
    - exact Hswap_closed.
    - symmetry. apply aset_swap_fresh_union_singleton; assumption.
  }
  assert (Htotal_src :
    expr_total_on (dom (<[x := T]> Σ)) (tret (vfvar x)) (res_swap x y m)).
  { rewrite dom_insert_L. replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) by set_solver. exact Htotal_src_base. }
  assert (Hdom_tgt : world_dom (m : World) = dom (<[y := T]> Σ)).
  { rewrite dom_insert_L, Hdom. set_solver. }
  assert (Hclosed_tgt :
    world_store_closed_on (dom (<[y := T]> Σ)) m).
  { rewrite dom_insert_L. replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver. exact Hclosed. }
  assert (Htotal_tgt :
    expr_total_on (dom (<[y := T]> Σ)) (tret (vfvar y)) m).
  { rewrite dom_insert_L. replace ({[y]} ∪ dom Σ) with (dom Σ ∪ {[y]}) by set_solver. exact Htotal. }
  assert (HPfv_src :
    ∀ ν, formula_fv (P ν) ⊆ dom (<[x := T]> Σ) ∪ {[ν]}).
  { intros ν. rewrite dom_insert_L. pose proof (HPfv ν). set_solver. }
  assert (HPfv_tgt :
    ∀ ν, formula_fv (P ν) ⊆ dom (<[y := T]> Σ) ∪ {[ν]}).
  { intros ν. rewrite dom_insert_L. pose proof (HPfv ν). set_solver. }
  assert (HPrename_src :
    formula_family_rename_stable_on (dom (<[x := T]> Σ)) P).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb. apply HPrename; rewrite dom_insert_L in *; set_solver.
  }
  assert (HPrename_tgt :
    formula_family_rename_stable_on (dom (<[y := T]> Σ)) P).
  {
    unfold formula_family_rename_stable_on in *.
    intros a b n Ha Hb. apply HPrename; rewrite dom_insert_L in *; set_solver.
  }
  split; intros Hcont.
  - pose proof (proj1 (FExprContIn_iff_let_result_world_on_exact_domain
      (<[x := T]> Σ) T (tret (vfvar x)) P (res_swap x y m)
      (basic_typing_tret_fvar_insert Σ x T) Hdom_src Hclosed_src Htotal_src
      HPfv_src HPrename_src) Hcont) as [L [HL Huse]].
    apply (proj2 (FExprContIn_iff_let_result_world_on_exact_domain
      (<[y := T]> Σ) T (tret (vfvar y)) P m
      (basic_typing_tret_fvar_insert Σ y T) Hdom_tgt Hclosed_tgt Htotal_tgt
      HPfv_tgt HPrename_tgt)).
    exists (L ∪ dom Σ ∪ {[x]} ∪ {[y]}). split.
    { rewrite dom_insert_L. set_solver. }
    intros ν Hν Hfreshν Hresultν.
    assert (Hfreshν_src : ν ∉ world_dom (res_swap x y m : World)).
    {
      rewrite Hdom_src, dom_insert_L. set_solver.
    }
    assert (Hresultν_src : ∀ σ, (res_swap x y m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm (tret (vfvar x))))
        (tret (vfvar x)) →* tret vx).
    {
      eapply expr_total_on_to_fv_result.
      - exact Hclosed_src.
      - exact Htotal_src.
    }
    pose proof (Huse ν ltac:(set_solver) Hfreshν_src Hresultν_src) as Hsrcν.
    rewrite (let_result_world_on_tret_fvar_swap
      (dom Σ) x y ν m Hfreshν_src Hresultν_src Hfreshν Hresultν
      Hx Hy ltac:(set_solver) Hdom
      ltac:(eapply world_store_closed_on_world_closed_on; exact Hclosed)) in Hsrcν.
    rewrite <- res_models_swap in Hsrcν.
    apply (proj1 (res_models_rename_atom_fresh x y (P ν)
      (let_result_world_on (tret (vfvar y)) ν m Hfreshν Hresultν)
      ltac:(pose proof (HPfv ν); set_solver)
      ltac:(pose proof (HPfv ν); set_solver))).
    exact Hsrcν.
  - pose proof (proj1 (FExprContIn_iff_let_result_world_on_exact_domain
      (<[y := T]> Σ) T (tret (vfvar y)) P m
      (basic_typing_tret_fvar_insert Σ y T) Hdom_tgt Hclosed_tgt Htotal_tgt
      HPfv_tgt HPrename_tgt) Hcont) as [L [HL Huse]].
    apply (proj2 (FExprContIn_iff_let_result_world_on_exact_domain
      (<[x := T]> Σ) T (tret (vfvar x)) P (res_swap x y m)
      (basic_typing_tret_fvar_insert Σ x T) Hdom_src Hclosed_src Htotal_src
      HPfv_src HPrename_src)).
    exists (L ∪ dom Σ ∪ {[x]} ∪ {[y]}). split.
    { rewrite dom_insert_L. set_solver. }
    intros ν Hν Hfreshν_src Hresultν_src.
    assert (Hfreshν : ν ∉ world_dom (m : World)).
    { rewrite Hdom. set_solver. }
    assert (Hresultν : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm (tret (vfvar y))))
        (tret (vfvar y)) →* tret vx).
    {
      eapply expr_total_on_to_fv_result.
      - exact Hclosed_tgt.
      - exact Htotal_tgt.
    }
    pose proof (Huse ν ltac:(set_solver) Hfreshν Hresultν) as Htgtν.
    apply (proj2 (res_models_rename_atom_fresh x y (P ν)
      (let_result_world_on (tret (vfvar y)) ν m Hfreshν Hresultν)
      ltac:(pose proof (HPfv ν); set_solver)
      ltac:(pose proof (HPfv ν); set_solver))) in Htgtν.
    rewrite res_models_swap in Htgtν.
    rewrite (let_result_world_on_tret_fvar_swap
      (dom Σ) x y ν m Hfreshν_src Hresultν_src Hfreshν Hresultν
      Hx Hy ltac:(set_solver) Hdom
      ltac:(eapply world_store_closed_on_world_closed_on; exact Hclosed)).
    exact Htgtν.
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
  intros Hx Hy Hdom Hclosed [_ [n Htotal]].
  split.
  - intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite map_empty_union.
    rewrite store_restrict_swap_fresh_union_singleton by assumption.
    apply store_closed_store_swap.
    apply Hclosed. exact Hσy.
  - exists n. intros σx Hσx.
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
  apply (proj2 (strongly_normalizing_fuel_tret_fvar_store_swap_lookup n
    (store_restrict σy (D ∪ {[y]})) x y vy
    Hclosed_y Hlookup_restrict)).
  replace (store_restrict σy (D ∪ {[y]}))
    with (store_restrict (∅ ∪ σy) (D ∪ {[y]}))
    by (rewrite map_empty_union; reflexivity).
  apply Htotal. exact Hσy.
Qed.

Lemma expr_total_with_store_empty_tret_fvar_swap_exact_iff
    D x y (m : WfWorld) :
  x ∉ D →
  y ∉ D →
  world_dom (m : World) = D ∪ {[y]} →
  world_store_closed_on (D ∪ {[y]}) m →
  expr_total_with_store (D ∪ {[x]}) (tret (vfvar x)) ∅ (res_swap x y m) ↔
  expr_total_with_store (D ∪ {[y]}) (tret (vfvar y)) ∅ m.
Proof.
  intros Hx Hy Hdom Hclosed. split.
  - intros Htotal.
    replace m with (res_swap y x (res_swap x y m)).
    2:{ rewrite res_swap_sym, res_swap_involutive. reflexivity. }
    eapply (expr_total_with_store_empty_tret_fvar_swap_exact
      D y x (res_swap x y m) Hy Hx).
    + simpl. rewrite Hdom.
      apply set_eq. intros z.
      rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
      unfold atom_swap. repeat destruct decide; set_solver.
    + apply (proj2 (world_store_closed_on_swap_fresh_union_singleton_iff
        D x y m ltac:(set_solver) ltac:(set_solver))).
      exact Hclosed.
    + exact Htotal.
  - apply expr_total_with_store_empty_tret_fvar_swap_exact; assumption.
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
  intros Hx Hy Hdom Hclosed [_ [n Htotal]].
  split.
  - intros σx Hσx.
    simpl in Hσx.
    destruct Hσx as [σy [Hσy Hσx]]. subst σx.
    rewrite map_empty_union.
    rewrite store_restrict_swap_fresh_union_singleton by set_solver.
    apply store_closed_store_swap.
    apply Hclosed. exact Hσy.
  - exists n. intros σx Hσx.
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
  apply (proj2 (strongly_normalizing_fuel_tapp_tm_fvar_store_swap_lookup n
    (store_restrict σy (D ∪ {[y]})) e x y vy
    Hclosed_y Hlookup_restrict ltac:(set_solver) ltac:(set_solver))).
  replace (store_restrict σy (D ∪ {[y]}))
    with (store_restrict (∅ ∪ σy) (D ∪ {[y]}))
    by (rewrite map_empty_union; reflexivity).
  apply Htotal. exact Hσy.
Qed.

Lemma expr_total_with_store_empty_tapp_tm_fvar_swap_exact_iff
    D e x y (m : WfWorld) :
  x ∉ D ∪ fv_tm e →
  y ∉ D ∪ fv_tm e →
  world_dom (m : World) = D ∪ {[y]} →
  world_store_closed_on (D ∪ {[y]}) m →
  expr_total_with_store (D ∪ {[x]}) (tapp_tm e (vfvar x)) ∅
    (res_swap x y m) ↔
  expr_total_with_store (D ∪ {[y]}) (tapp_tm e (vfvar y)) ∅ m.
Proof.
  intros Hx Hy Hdom Hclosed. split.
  - intros Htotal.
    replace m with (res_swap y x (res_swap x y m)).
    2:{ rewrite res_swap_sym, res_swap_involutive. reflexivity. }
    eapply (expr_total_with_store_empty_tapp_tm_fvar_swap_exact
      D e y x (res_swap x y m) Hy Hx).
    + simpl. rewrite Hdom.
      apply set_eq. intros z.
      rewrite elem_of_aset_swap, !elem_of_union, !elem_of_singleton.
      unfold atom_swap. repeat destruct decide; set_solver.
    + apply (proj2 (world_store_closed_on_swap_fresh_union_singleton_iff
        D x y m ltac:(set_solver) ltac:(set_solver))).
      exact Hclosed.
    + exact Htotal.
  - apply expr_total_with_store_empty_tapp_tm_fvar_swap_exact; assumption.
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
  - intros [_ [n Htotal]]. split; [set_solver |].
    exists n.
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σ).
    { rewrite (wfworld_store_dom m σ Hσ). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σ (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    pose proof (Htotal (store_swap x y σ)) as Hsn.
    assert ((res_swap x y m : World) (store_swap x y σ)) as Hσswap.
    { simpl. exists σ. split; [exact Hσ | reflexivity]. }
    specialize (Hsn Hσswap).
    rewrite store_restrict_swap_fresh_union_singleton in Hsn by assumption.
    apply (proj1 (strongly_normalizing_fuel_tret_fvar_store_swap_lookup n
      (store_restrict σ (D ∪ {[y]})) x y vy
      (proj1 Hclosedσ) Hlookup_restrict)).
    exact Hsn.
  - intros [_ [n Htotal]]. split; [set_solver |].
    exists n.
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
    apply (proj2 (strongly_normalizing_fuel_tret_fvar_store_swap_lookup n
      (store_restrict σy (D ∪ {[y]})) x y vy
      (proj1 Hclosedσ) Hlookup_restrict)).
    apply Htotal. exact Hσy.
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
  - intros [_ [n Htotal]]. split.
    { rewrite fv_tapp_tm. simpl. set_solver. }
    exists n.
    intros σ Hσ.
    pose proof (Hclosed σ Hσ) as Hclosedσ.
    assert (Hy_dom : y ∈ dom σ).
    { rewrite (wfworld_store_dom m σ Hσ). apply Hdom. set_solver. }
    apply elem_of_dom in Hy_dom as [vy Hlookup].
    assert (Hlookup_restrict :
      store_restrict σ (D ∪ {[y]}) !! y = Some vy).
    { apply store_restrict_lookup_some_2; [exact Hlookup | set_solver]. }
    pose proof (Htotal (store_swap x y σ)) as Hsn.
    assert ((res_swap x y m : World) (store_swap x y σ)) as Hσswap.
    { simpl. exists σ. split; [exact Hσ | reflexivity]. }
    specialize (Hsn Hσswap).
    rewrite store_restrict_swap_fresh_union_singleton in Hsn by set_solver.
    apply (proj1 (strongly_normalizing_fuel_tapp_tm_fvar_store_swap_lookup n
      (store_restrict σ (D ∪ {[y]})) e x y vy
      (proj1 Hclosedσ) Hlookup_restrict ltac:(set_solver) ltac:(set_solver))).
    exact Hsn.
  - intros [_ [n Htotal]]. split.
    { rewrite fv_tapp_tm. simpl. set_solver. }
    exists n.
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
    apply (proj2 (strongly_normalizing_fuel_tapp_tm_fvar_store_swap_lookup n
      (store_restrict σy (D ∪ {[y]})) e x y vy
      (proj1 Hclosedσ) Hlookup_restrict ltac:(set_solver) ltac:(set_solver))).
    apply Htotal. exact Hσy.
Qed.

Lemma dom_insert_fresh_union (Σ : gmap atom ty) x T :
  x ∉ dom Σ →
  dom (<[x := T]> Σ) = dom Σ ∪ {[x]}.
Proof.
  intros _. rewrite dom_insert_L. set_solver.
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

Lemma FBasicTypingIn_insert_swap_iff
    (Σ : gmap atom ty) x y T τ e (m : WfWorld) :
  x ∉ dom Σ →
  y ∉ dom Σ →
  m ⊨ formula_rename_atom x y (FBasicTypingIn (<[x := T]> Σ) τ e) ↔
  m ⊨ FBasicTypingIn (<[y := T]> Σ)
    (cty_swap_atom x y τ) (tm_swap_atom x y e).
Proof.
  intros Hx Hy.
  unfold FBasicTypingIn.
  rewrite formula_rename_FPure.
  split; intros Hm.
  - destruct (res_models_with_store_pure_elim _ _ _ Hm) as [Hbasic Htyped].
    eapply res_models_with_store_pure_intro.
    + unfold formula_scoped_in_world. simpl. set_solver.
    + split.
      * replace (dom (<[y:=T]> Σ))
          with (aset_swap x y (dom (<[x:=T]> Σ))).
        -- apply basic_choice_ty_swap. exact Hbasic.
        -- rewrite !dom_insert_L, aset_swap_union, aset_swap_singleton.
           rewrite atom_swap_left_eq, aset_swap_fresh by assumption.
           set_solver.
      * rewrite (cty_swap_preserves_erasure x y τ).
        replace (<[y:=T]> Σ)
          with (store_swap x y (<[x:=T]> Σ)).
        -- apply basic_typing_swap_tm. exact Htyped.
        -- rewrite store_swap_insert, atom_swap_left_eq.
           rewrite store_swap_fresh by assumption. reflexivity.
  - destruct (res_models_with_store_pure_elim _ _ _ Hm) as [Hbasic Htyped].
    eapply res_models_with_store_pure_intro.
    + unfold formula_scoped_in_world. simpl. set_solver.
    + split.
      * pose proof (basic_choice_ty_swap x y _ _ Hbasic) as Hback.
        rewrite cty_swap_atom_involutive in Hback.
        replace (aset_swap x y (dom (<[y:=T]> Σ)))
          with (dom (<[x:=T]> Σ)) in Hback.
        -- exact Hback.
        -- rewrite !dom_insert_L, aset_swap_union, aset_swap_singleton.
           rewrite atom_swap_right_eq, aset_swap_fresh by assumption.
           set_solver.
      * pose proof (basic_typing_swap_tm _ _ _ x y Htyped) as Htyped_swap.
        rewrite tm_swap_atom_involutive in Htyped_swap.
        rewrite (cty_swap_preserves_erasure x y τ) in Htyped_swap.
        replace (store_swap x y (<[y:=T]> Σ))
          with (<[x:=T]> Σ) in Htyped_swap.
        -- exact Htyped_swap.
        -- rewrite store_swap_insert, atom_swap_right_eq.
           rewrite store_swap_fresh by assumption. reflexivity.
Qed.

Lemma FClosedResourceIn_insert_swap_iff
    (Σ : gmap atom ty) x y T (m : WfWorld) :
  x ∉ dom Σ →
  y ∉ dom Σ →
  m ⊨ formula_rename_atom x y (FClosedResourceIn (<[x := T]> Σ)) ↔
  m ⊨ FClosedResourceIn (<[y := T]> Σ).
Proof.
  intros Hx Hy.
  unfold FClosedResourceIn.
  rewrite formula_rename_FResourceAtom.
  replace (aset_swap x y (dom (<[x:=T]> Σ)))
    with (dom (<[y:=T]> Σ)).
  2:{
    rewrite !dom_insert_L, aset_swap_union, aset_swap_singleton.
    rewrite atom_swap_left_eq, aset_swap_fresh by assumption.
    set_solver.
  }
  split; intros Hm.
  - destruct (res_models_with_store_resource_atom_elim ∅ m
      (dom (<[y:=T]> Σ))
      (fun m0 : WfWorld => world_closed_on (dom (<[x:=T]> Σ)) (res_swap x y m0))
      Hm) as [m0 [Hscope [Hclosed Hle]]].
    assert (Hclosed_m0 :
      world_closed_on (dom (<[y:=T]> Σ)) (res_restrict m0 (dom (<[y:=T]> Σ)))).
    {
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) in Hclosed by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[x:=T]> Σ)) with (dom Σ ∪ {[x]}) in Hclosed by
        (rewrite dom_insert_L; set_solver).
      exact (proj1 (world_closed_on_swap_fresh_union_singleton_iff
        (dom Σ) x y (res_restrict m0 (dom Σ ∪ {[y]})) Hx Hy) Hclosed).
    }
    eapply res_models_with_store_resource_atom_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
      set_solver.
    + eapply (world_closed_on_extend (dom (<[y:=T]> Σ))
        (res_restrict m0 (dom (<[y:=T]> Σ))) (res_restrict m (dom (<[y:=T]> Σ)))).
      * simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
        set_solver.
      * apply res_restrict_le_mono. exact Hle.
      * exact Hclosed_m0.
  - destruct (res_models_with_store_resource_atom_elim ∅ m
      (dom (<[y:=T]> Σ)) (world_closed_on (dom (<[y:=T]> Σ)) ) Hm)
      as [m0 [Hscope [Hclosed Hle]]].
    assert (Hclosed_m :
      world_closed_on (dom (<[y:=T]> Σ)) (res_restrict m (dom (<[y:=T]> Σ)))).
    {
      eapply (world_closed_on_extend (dom (<[y:=T]> Σ))
        (res_restrict m0 (dom (<[y:=T]> Σ))) (res_restrict m (dom (<[y:=T]> Σ)))).
      - simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
        set_solver.
      - apply res_restrict_le_mono. exact Hle.
      - exact Hclosed.
    }
    eapply res_models_with_store_resource_atom_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
      set_solver.
    + replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[x:=T]> Σ)) with (dom Σ ∪ {[x]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) in Hclosed_m by
        (rewrite dom_insert_L; set_solver).
      exact (proj2 (world_closed_on_swap_fresh_union_singleton_iff
        (dom Σ) x y (res_restrict m (dom Σ ∪ {[y]})) Hx Hy) Hclosed_m).
Qed.

Lemma expr_total_with_store_empty_extend X e (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  expr_total_with_store X e ∅ m →
  expr_total_with_store X e ∅ (res_restrict n X).
Proof.
  intros HXm Hle [Hclosed [k Htotal]].
  split.
  - intros σ Hσ.
    destruct Hσ as [σn [Hσn Hrestrict]].
    assert ((res_restrict n (world_dom (m : World)) : World)
      (store_restrict σn (world_dom (m : World)))) as Hσm.
    { exists σn. split; [exact Hσn | reflexivity]. }
    rewrite (res_restrict_eq_of_le m n Hle) in Hσm.
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X =
      store_restrict ((∅ : Store) ∪ store_restrict σn (world_dom (m : World))) X).
    { rewrite !map_empty_union.
      rewrite <- Hrestrict.
      rewrite !store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      replace (world_dom (m : World) ∩ X) with X by set_solver.
      reflexivity. }
    rewrite Heq. apply Hclosed. exact Hσm.
  - exists k. intros σ Hσ.
    destruct Hσ as [σn [Hσn Hrestrict]].
    assert ((res_restrict n (world_dom (m : World)) : World)
      (store_restrict σn (world_dom (m : World)))) as Hσm.
    { exists σn. split; [exact Hσn | reflexivity]. }
    rewrite (res_restrict_eq_of_le m n Hle) in Hσm.
    assert (Heq : store_restrict ((∅ : Store) ∪ σ) X =
      store_restrict ((∅ : Store) ∪ store_restrict σn (world_dom (m : World))) X).
    { rewrite !map_empty_union.
      rewrite <- Hrestrict.
      rewrite !store_restrict_restrict.
      replace (X ∩ X) with X by set_solver.
      replace (world_dom (m : World) ∩ X) with X by set_solver.
      reflexivity. }
    rewrite Heq. apply Htotal. exact Hσm.
Qed.

Lemma expr_total_with_store_empty_closed_on X e (m : WfWorld) :
  expr_total_with_store X e ∅ m →
  world_store_closed_on X m.
Proof.
  intros [Hclosed _] σ Hσ.
  specialize (Hclosed σ Hσ).
  rewrite map_empty_union in Hclosed.
  exact Hclosed.
Qed.

Lemma FStrongTotalIn_insert_tret_fvar_swap_iff
    (Σ : gmap atom ty) x y T (m : WfWorld) :
  x ∉ dom Σ →
  y ∉ dom Σ →
  m ⊨ formula_rename_atom x y
    (FStrongTotalIn (<[x := T]> Σ) (tret (vfvar x))) ↔
  m ⊨ FStrongTotalIn (<[y := T]> Σ) (tret (vfvar y)).
Proof.
  intros Hx Hy.
  unfold FStrongTotalIn.
  rewrite formula_rename_FStoreResourceAtom.
  replace (aset_swap x y (dom (<[x:=T]> Σ)))
    with (dom (<[y:=T]> Σ)).
  2:{
    rewrite !dom_insert_L, aset_swap_union, aset_swap_singleton.
    rewrite atom_swap_left_eq, aset_swap_fresh by assumption.
    set_solver.
  }
  split; intros Hm.
  - destruct (res_models_with_store_store_resource_atom_elim ∅ m
      (dom (<[y:=T]> Σ))
      (fun ρ m0 => expr_total_with_store (dom (<[x:=T]> Σ))
        (tret (vfvar x)) (store_swap x y ρ) (res_swap x y m0))
      Hm) as [m0 [Hscope [Htotal Hle]]].
    rewrite store_restrict_empty, store_swap_empty in Htotal.
    assert (Htotal_m0 :
      expr_total_with_store (dom (<[y:=T]> Σ)) (tret (vfvar y)) ∅
        (res_restrict m0 (dom (<[y:=T]> Σ)))).
    {
      replace (dom (<[x:=T]> Σ)) with (dom Σ ∪ {[x]}) in Htotal by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) in Htotal by
        (rewrite dom_insert_L; set_solver).
      pose proof (expr_total_with_store_empty_closed_on _ _ _ Htotal) as Hclosed_swap.
      pose proof (proj1 (world_store_closed_on_swap_fresh_union_singleton_iff
        (dom Σ) x y (res_restrict m0 (dom Σ ∪ {[y]})) Hx Hy)
        Hclosed_swap) as Hclosed_y.
      exact (proj1 (expr_total_with_store_empty_tret_fvar_swap_exact_iff
        (dom Σ) x y (res_restrict m0 (dom Σ ∪ {[y]})) Hx Hy
        ltac:(simpl; unfold formula_scoped_in_world in Hscope; simpl in Hscope;
              apply set_eq; intros z; split; intros Hz;
              [apply elem_of_intersection in Hz as [_ Hz]; exact Hz
              |apply elem_of_intersection; split; [apply Hscope; set_solver | exact Hz]])
        Hclosed_y) Htotal).
    }
    eapply res_models_with_store_store_resource_atom_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
      set_solver.
    + eapply (expr_total_with_store_empty_extend
        (dom (<[y:=T]> Σ)) (tret (vfvar y))
        (res_restrict m0 (dom (<[y:=T]> Σ))) m).
      * simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
        unfold stale, stale_logic_qualifier in Hscope. simpl in Hscope.
        set_solver.
      * etrans; [apply res_restrict_le | exact Hle].
      * exact Htotal_m0.
  - destruct (res_models_with_store_store_resource_atom_elim ∅ m
      (dom (<[y:=T]> Σ))
      (fun ρ m0 => expr_total_with_store (dom (<[y:=T]> Σ))
        (tret (vfvar y)) ρ m0)
      Hm) as [m0 [Hscope [Htotal Hle]]].
    rewrite store_restrict_empty in Htotal.
    assert (Htotal_m :
      expr_total_with_store (dom (<[y:=T]> Σ)) (tret (vfvar y)) ∅
        (res_restrict m (dom (<[y:=T]> Σ)))).
    {
      eapply (expr_total_with_store_empty_extend
        (dom (<[y:=T]> Σ)) (tret (vfvar y))
        (res_restrict m0 (dom (<[y:=T]> Σ))) m).
      - simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
        unfold stale, stale_logic_qualifier in Hscope. simpl in Hscope.
        set_solver.
      - etrans; [apply res_restrict_le | exact Hle].
      - exact Htotal.
    }
    eapply res_models_with_store_store_resource_atom_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
      set_solver.
    + rewrite store_restrict_empty, store_swap_empty.
      replace (dom (<[x:=T]> Σ)) with (dom Σ ∪ {[x]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) in Htotal_m by
        (rewrite dom_insert_L; set_solver).
      pose proof (expr_total_with_store_empty_closed_on _ _ _ Htotal_m) as Hclosed_y.
      assert (Hdom_y_m : world_dom (res_restrict m (dom Σ ∪ {[y]}) : World) =
        dom Σ ∪ {[y]}).
      {
        assert (Hscope0 : dom (<[y:=T]> Σ) ⊆ world_dom (m0 : World)).
        { intros z Hz. apply Hscope.
          unfold stale, stale_logic_qualifier. simpl. set_solver. }
        pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
        apply set_eq. intros z. split; intros Hz.
        - simpl in Hz. apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
        - simpl. apply elem_of_intersection. split; [| exact Hz].
          apply Hdomle. apply Hscope0. rewrite dom_insert_L. set_solver.
      }
      exact (proj2 (expr_total_with_store_empty_tret_fvar_swap_exact_iff
        (dom Σ) x y (res_restrict m (dom Σ ∪ {[y]})) Hx Hy
        Hdom_y_m Hclosed_y) Htotal_m).
Qed.

Lemma FStrongTotalIn_insert_tapp_fvar_swap_iff
    (Σ : gmap atom ty) x y T e (m : WfWorld) :
  x ∉ dom Σ ∪ fv_tm e →
  y ∉ dom Σ ∪ fv_tm e →
  fv_tm e ⊆ dom Σ →
  m ⊨ formula_rename_atom x y
    (FStrongTotalIn (<[x := T]> Σ) (tapp_tm e (vfvar x))) ↔
  m ⊨ FStrongTotalIn (<[y := T]> Σ) (tapp_tm e (vfvar y)).
Proof.
  intros Hx Hy Hfve.
  unfold FStrongTotalIn.
  rewrite formula_rename_FStoreResourceAtom.
  replace (aset_swap x y (dom (<[x:=T]> Σ)))
    with (dom (<[y:=T]> Σ)).
  2:{
    rewrite !dom_insert_L, aset_swap_union, aset_swap_singleton.
    rewrite atom_swap_left_eq, aset_swap_fresh by set_solver.
    set_solver.
  }
  split; intros Hm.
  - destruct (res_models_with_store_store_resource_atom_elim ∅ m
      (dom (<[y:=T]> Σ))
      (fun ρ m0 => expr_total_with_store (dom (<[x:=T]> Σ))
        (tapp_tm e (vfvar x)) (store_swap x y ρ) (res_swap x y m0))
      Hm) as [m0 [Hscope [Htotal Hle]]].
    rewrite store_restrict_empty, store_swap_empty in Htotal.
    assert (Htotal_m0 :
      expr_total_with_store (dom (<[y:=T]> Σ)) (tapp_tm e (vfvar y)) ∅
        (res_restrict m0 (dom (<[y:=T]> Σ)))).
    {
      replace (dom (<[x:=T]> Σ)) with (dom Σ ∪ {[x]}) in Htotal by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) in Htotal by
        (rewrite dom_insert_L; set_solver).
      pose proof (expr_total_with_store_empty_closed_on _ _ _ Htotal) as Hclosed_swap.
      pose proof (proj1 (world_store_closed_on_swap_fresh_union_singleton_iff
        (dom Σ) x y (res_restrict m0 (dom Σ ∪ {[y]}))
        ltac:(set_solver) ltac:(set_solver)) Hclosed_swap) as Hclosed_y.
      exact (proj1 (expr_total_with_store_empty_tapp_tm_fvar_swap_exact_iff
        (dom Σ) e x y (res_restrict m0 (dom Σ ∪ {[y]}))
        Hx Hy
        ltac:(simpl; unfold formula_scoped_in_world in Hscope; simpl in Hscope;
              apply set_eq; intros z; split; intros Hz;
              [apply elem_of_intersection in Hz as [_ Hz]; exact Hz
              |apply elem_of_intersection; split; [apply Hscope; set_solver | exact Hz]])
        Hclosed_y) Htotal).
    }
    eapply res_models_with_store_store_resource_atom_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
      set_solver.
    + eapply (expr_total_with_store_empty_extend
        (dom (<[y:=T]> Σ)) (tapp_tm e (vfvar y))
        (res_restrict m0 (dom (<[y:=T]> Σ))) m).
      * simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
        unfold stale, stale_logic_qualifier in Hscope. simpl in Hscope.
        set_solver.
      * etrans; [apply res_restrict_le | exact Hle].
      * exact Htotal_m0.
  - destruct (res_models_with_store_store_resource_atom_elim ∅ m
      (dom (<[y:=T]> Σ))
      (fun ρ m0 => expr_total_with_store (dom (<[y:=T]> Σ))
        (tapp_tm e (vfvar y)) ρ m0)
      Hm) as [m0 [Hscope [Htotal Hle]]].
    rewrite store_restrict_empty in Htotal.
    assert (Htotal_m :
      expr_total_with_store (dom (<[y:=T]> Σ)) (tapp_tm e (vfvar y)) ∅
        (res_restrict m (dom (<[y:=T]> Σ)))).
    {
      eapply (expr_total_with_store_empty_extend
        (dom (<[y:=T]> Σ)) (tapp_tm e (vfvar y))
        (res_restrict m0 (dom (<[y:=T]> Σ))) m).
      - simpl. unfold formula_scoped_in_world in Hscope. simpl in Hscope.
        unfold stale, stale_logic_qualifier in Hscope. simpl in Hscope.
        set_solver.
      - etrans; [apply res_restrict_le | exact Hle].
      - exact Htotal.
    }
    eapply res_models_with_store_store_resource_atom_intro.
    + unfold formula_scoped_in_world. simpl.
      unfold formula_scoped_in_world in Hscope. simpl in Hscope.
      pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
      set_solver.
    + rewrite store_restrict_empty, store_swap_empty.
      replace (dom (<[x:=T]> Σ)) with (dom Σ ∪ {[x]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) by
        (rewrite dom_insert_L; set_solver).
      replace (dom (<[y:=T]> Σ)) with (dom Σ ∪ {[y]}) in Htotal_m by
        (rewrite dom_insert_L; set_solver).
      pose proof (expr_total_with_store_empty_closed_on _ _ _ Htotal_m) as Hclosed_y.
      assert (Hdom_y_m : world_dom (res_restrict m (dom Σ ∪ {[y]}) : World) =
        dom Σ ∪ {[y]}).
      {
        assert (Hscope0 : dom (<[y:=T]> Σ) ⊆ world_dom (m0 : World)).
        { intros z Hz. apply Hscope.
          unfold stale, stale_logic_qualifier. simpl. set_solver. }
        pose proof (raw_le_dom (m0 : World) (m : World) Hle) as Hdomle.
        apply set_eq. intros z. split; intros Hz.
        - simpl in Hz. apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
        - simpl. apply elem_of_intersection. split; [| exact Hz].
          apply Hdomle. apply Hscope0. rewrite dom_insert_L. set_solver.
      }
      exact (proj2 (expr_total_with_store_empty_tapp_tm_fvar_swap_exact_iff
        (dom Σ) e x y (res_restrict m (dom Σ ∪ {[y]}))
        Hx Hy Hdom_y_m Hclosed_y) Htotal_m).
Qed.

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

Lemma res_models_fresh_forall_family_equiv
    (m : WfWorld) (D1 D2 : aset) (P Q : atom → FormulaQ) :
  formula_scoped_in_world ∅ m (fresh_forall D2 Q) →
  formula_family_rename_stable_on D1 P →
  formula_family_rename_stable_on D2 Q →
  (∀ y m',
    y ∉ D1 →
    y ∉ D2 →
    m' ⊨ P y →
    m' ⊨ Q y) →
  m ⊨ fresh_forall D1 P →
  m ⊨ fresh_forall D2 Q.
Proof.
  intros Hscope2 HPren HQren Hpoint Hsrc.
  unfold fresh_forall in *.
  apply res_models_forall_intro; [exact Hscope2 |].
  unfold res_models, res_models_with_store in Hsrc.
  simpl in Hsrc.
  destruct Hsrc as [_ [L [HL Hforall]]].
  exists (L ∪ D1 ∪ D2). split; [set_solver |].
  intros y Hy m' Hdom Hrestr.
  assert (HyL : y ∉ L) by set_solver.
  assert (HyD1 : y ∉ D1) by set_solver.
  assert (HyD2 : y ∉ D2) by set_solver.
  pose proof (Hforall y HyL m' Hdom Hrestr) as HPfuel.
  assert (HPmodel : m' ⊨ formula_rename_atom (fresh_for D1) y (P (fresh_for D1))).
  {
    unfold res_models, res_models_with_store.
    models_fuel_irrel HPfuel.
  }
  pose proof (proj1 (HPren (fresh_for D1) y m'
    (fresh_for_not_in D1) HyD1) HPmodel) as HPy.
  pose proof (Hpoint y m' HyD1 HyD2 HPy) as HQy.
  exact (proj2 (HQren (fresh_for D2) y m'
    (fresh_for_not_in D2) HyD2) HQy).
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

Lemma denot_ty_fuel_insert_fresh_env_irrel_same_world_over_case gas
    (Σ : gmap atom ty) b φ e x T (m : WfWorld) :
  x ∉ dom Σ ∪ qual_dom φ ∪ fv_tm e →
  dom (<[x := T]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTOver b φ) e <->
  m ⊨ denot_ty_fuel (S gas) Σ (CTOver b φ) e.
Proof.
  intros Hx Hdom_sub Hclosed Htotal. split.
  - intros Hsrc.
    pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    assert (Htyped_base : Σ ⊢ₑ e ⋮ b).
    {
      eapply basic_typing_drop_insert_fresh_tm.
      - intros Hxe. apply Hx. set_solver.
      - exact Htyped_src.
    }
    assert (Hbasic_base : basic_choice_ty (dom Σ) (CTOver b φ)).
    {
      eapply basic_choice_ty_drop_fresh.
      - intros Hxτ. apply Hx. set_solver.
      - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
        + exact Hbasic_src.
        + rewrite dom_insert_L. set_solver.
    }
    inversion Hbasic_base as [D b' φ' Hqbody| | | | | |]; subst.
    assert (Hφ : qual_dom φ ⊆ dom Σ).
    { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
    eapply denot_ty_fuel_intro.
    + exact Hbasic_base.
    + exact Htyped_base.
    + eapply world_store_closed_on_world_closed_on.
      eapply world_store_closed_on_mono; [| exact Hclosed].
      rewrite dom_insert_L. set_solver.
    + eapply expr_total_on_drop_insert_fresh_same.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hclosed.
      * exact Htotal.
    + cbn [denot_ty_fuel_body fv_cty erase_ty].
      pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body fv_cty erase_ty] in Hbody.
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
              (FOver (FTypeQualifier φν))))) in Hbody.
      2:{
        eapply (denot_refinement_over_cont_insert_fresh_eq
          (dom Σ : aset) Σ x T b φ); [set_solver | reflexivity].
      }
      pose proof (FExprContIn_insert_fresh_env_irrel_iff_at_world
        Σ b T e x
        (fun ν =>
          let φν := qual_open_atom 0 ν φ in
          FAnd
            (basic_world_formula (<[ν:=TBase b]> Σ)
              ({[ν]} ∪ qual_dom φν))
            (fib_vars (qual_dom φν)
              (FOver (FTypeQualifier φν)))) m) as Hcont_iff.
      assert (Hx_e : x ∉ dom Σ ∪ fv_tm e).
      {
        intros Hxe. apply Hx.
        apply elem_of_union in Hxe as [Hxe | Hxe].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hxe.
        -- apply elem_of_union_r. exact Hxe.
      }
      pose proof (Hcont_iff Htyped_base Hx_e Hdom_sub Hclosed Htotal
        ltac:(eapply denot_refinement_over_cont_fv_subset; exact Hφ)
        ltac:(eapply denot_refinement_over_cont_rename_stable; exact Hφ))
        as Hcont_iff'.
      exact (proj1 Hcont_iff' Hbody).
    + etrans; [| exact Hdom_sub].
      rewrite dom_insert_L. set_solver.
  - intros Hsrc.
    pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    inversion Hbasic_src as [D b' φ' Hqbody| | | | | |]; subst.
    assert (Hφ : qual_dom φ ⊆ dom Σ).
    { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasic_src].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_weaken_insert_tm; [set_solver | exact Htyped_src].
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + cbn [denot_ty_fuel_body fv_cty erase_ty].
      pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body fv_cty erase_ty] in Hbody.
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
      pose proof (FExprContIn_insert_fresh_env_irrel_iff_at_world
        Σ b T e x
        (fun ν =>
          let φν := qual_open_atom 0 ν φ in
          FAnd
            (basic_world_formula (<[ν:=TBase b]> Σ)
              ({[ν]} ∪ qual_dom φν))
            (fib_vars (qual_dom φν)
              (FOver (FTypeQualifier φν)))) m) as Hcont_iff.
      assert (Hx_e : x ∉ dom Σ ∪ fv_tm e).
      {
        intros Hxe. apply Hx.
        apply elem_of_union in Hxe as [Hxe | Hxe].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hxe.
        -- apply elem_of_union_r. exact Hxe.
      }
      pose proof (Hcont_iff Htyped_src Hx_e Hdom_sub Hclosed Htotal
        ltac:(eapply denot_refinement_over_cont_fv_subset; exact Hφ)
        ltac:(eapply denot_refinement_over_cont_rename_stable; exact Hφ))
        as Hcont_iff'.
      exact (proj2 Hcont_iff' Hbody).
    + exact Hdom_sub.
Qed.

Lemma denot_ty_fuel_insert_fresh_env_irrel_same_world_under_case gas
    (Σ : gmap atom ty) b φ e x T (m : WfWorld) :
  x ∉ dom Σ ∪ qual_dom φ ∪ fv_tm e →
  dom (<[x := T]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTUnder b φ) e <->
  m ⊨ denot_ty_fuel (S gas) Σ (CTUnder b φ) e.
Proof.
  intros Hx Hdom_sub Hclosed Htotal. split.
  - intros Hsrc.
    pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    assert (Htyped_base : Σ ⊢ₑ e ⋮ b).
    {
      eapply basic_typing_drop_insert_fresh_tm.
      - intros Hxe. apply Hx. set_solver.
      - exact Htyped_src.
    }
    assert (Hbasic_base : basic_choice_ty (dom Σ) (CTUnder b φ)).
    {
      eapply basic_choice_ty_drop_fresh.
      - intros Hxτ. apply Hx. set_solver.
      - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
        + exact Hbasic_src.
        + rewrite dom_insert_L. set_solver.
    }
    inversion Hbasic_base as [|D b' φ' Hqbody| | | | |]; subst.
    assert (Hφ : qual_dom φ ⊆ dom Σ).
    { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
    eapply denot_ty_fuel_intro.
    + exact Hbasic_base.
    + exact Htyped_base.
    + eapply world_store_closed_on_world_closed_on.
      eapply world_store_closed_on_mono; [| exact Hclosed].
      rewrite dom_insert_L. set_solver.
    + eapply expr_total_on_drop_insert_fresh_same.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hclosed.
      * exact Htotal.
    + cbn [denot_ty_fuel_body fv_cty erase_ty].
      pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body fv_cty erase_ty] in Hbody.
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
              (FUnder (FTypeQualifier φν))))) in Hbody.
      2:{
        eapply (denot_refinement_under_cont_insert_fresh_eq
          (dom Σ : aset) Σ x T b φ); [set_solver | reflexivity].
      }
      pose proof (FExprContIn_insert_fresh_env_irrel_iff_at_world
        Σ b T e x
        (fun ν =>
          let φν := qual_open_atom 0 ν φ in
          FAnd
            (basic_world_formula (<[ν:=TBase b]> Σ)
              ({[ν]} ∪ qual_dom φν))
            (fib_vars (qual_dom φν)
              (FUnder (FTypeQualifier φν)))) m) as Hcont_iff.
      assert (Hx_e : x ∉ dom Σ ∪ fv_tm e).
      {
        intros Hxe. apply Hx.
        apply elem_of_union in Hxe as [Hxe | Hxe].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hxe.
        -- apply elem_of_union_r. exact Hxe.
      }
      pose proof (Hcont_iff Htyped_base Hx_e Hdom_sub Hclosed Htotal
        ltac:(eapply denot_refinement_under_cont_fv_subset; exact Hφ)
        ltac:(eapply denot_refinement_under_cont_rename_stable; exact Hφ))
        as Hcont_iff'.
      exact (proj1 Hcont_iff' Hbody).
    + etrans; [| exact Hdom_sub].
      rewrite dom_insert_L. set_solver.
  - intros Hsrc.
    pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    inversion Hbasic_src as [|D b' φ' Hqbody| | | | |]; subst.
    assert (Hφ : qual_dom φ ⊆ dom Σ).
    { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasic_src].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_weaken_insert_tm; [set_solver | exact Htyped_src].
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + cbn [denot_ty_fuel_body fv_cty erase_ty].
      pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body fv_cty erase_ty] in Hbody.
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
      pose proof (FExprContIn_insert_fresh_env_irrel_iff_at_world
        Σ b T e x
        (fun ν =>
          let φν := qual_open_atom 0 ν φ in
          FAnd
            (basic_world_formula (<[ν:=TBase b]> Σ)
              ({[ν]} ∪ qual_dom φν))
            (fib_vars (qual_dom φν)
              (FUnder (FTypeQualifier φν)))) m) as Hcont_iff.
      assert (Hx_e : x ∉ dom Σ ∪ fv_tm e).
      {
        intros Hxe. apply Hx.
        apply elem_of_union in Hxe as [Hxe | Hxe].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hxe.
        -- apply elem_of_union_r. exact Hxe.
      }
      pose proof (Hcont_iff Htyped_src Hx_e Hdom_sub Hclosed Htotal
        ltac:(eapply denot_refinement_under_cont_fv_subset; exact Hφ)
        ltac:(eapply denot_refinement_under_cont_rename_stable; exact Hφ))
        as Hcont_iff'.
      exact (proj2 Hcont_iff' Hbody).
    + exact Hdom_sub.
Qed.

Lemma denot_ty_fuel_insert_fresh_env_irrel_same_world_inter_case gas
    (Σ : gmap atom ty) τa τb e x T (m : WfWorld) :
  (∀ τ (m' : WfWorld),
    cty_measure τ <= gas →
    x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
    dom (<[x := T]> Σ) ⊆ world_dom (m' : World) →
    world_store_closed_on (dom (<[x := T]> Σ)) m' →
    expr_total_on (dom (<[x := T]> Σ)) e m' →
    m' ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e <->
    m' ⊨ denot_ty_fuel gas Σ τ e) →
  cty_measure (CTInter τa τb) <= S gas →
  x ∉ dom Σ ∪ fv_cty (CTInter τa τb) ∪ fv_tm e →
  dom (<[x := T]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTInter τa τb) e <->
  m ⊨ denot_ty_fuel (S gas) Σ (CTInter τa τb) e.
Proof.
  intros IH Hgas Hx Hdom_sub Hclosed Htotal. split; intros Hsrc.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    assert (Hbasic_base : basic_choice_ty (dom Σ) (CTInter τa τb)).
    {
      eapply basic_choice_ty_drop_fresh.
      - intros Hxτ. apply Hx.
        apply elem_of_union_l. apply elem_of_union_r. exact Hxτ.
      - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
        + exact Hbasic_src.
        + rewrite dom_insert_L. set_solver.
    }
    assert (Htyped_base : Σ ⊢ₑ e ⋮ erase_ty (CTInter τa τb)).
    {
      eapply basic_typing_drop_insert_fresh_tm.
      - intros Hxe. apply Hx. apply elem_of_union_r. exact Hxe.
      - exact Htyped_src.
    }
    eapply denot_ty_fuel_intro.
    + exact Hbasic_base.
    + exact Htyped_base.
    + eapply world_store_closed_on_world_closed_on.
      eapply world_store_closed_on_mono; [| exact Hclosed].
      rewrite dom_insert_L. set_solver.
    + eapply expr_total_on_drop_insert_fresh_same.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hclosed.
      * exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody |- *.
      apply res_models_and_intro_from_models.
      * apply res_models_and_elim_l in Hbody.
        destruct (IH τa m) as [IHto _].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. left. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHto Hbody).
      * apply res_models_and_elim_r in Hbody.
        destruct (IH τb m) as [IHto _].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. right. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHto Hbody).
    + etrans; [| exact Hdom_sub].
      rewrite dom_insert_L. set_solver.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasic_src].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_weaken_insert_tm; [set_solver | exact Htyped_src].
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody |- *.
      apply res_models_and_intro_from_models.
      * apply res_models_and_elim_l in Hbody.
        destruct (IH τa m) as [_ IHfrom].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. left. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHfrom Hbody).
      * apply res_models_and_elim_r in Hbody.
        destruct (IH τb m) as [_ IHfrom].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. right. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHfrom Hbody).
    + exact Hdom_sub.
Qed.

Lemma denot_ty_fuel_insert_fresh_env_irrel_same_world_union_case gas
    (Σ : gmap atom ty) τa τb e x T (m : WfWorld) :
  (∀ τ (m' : WfWorld),
    cty_measure τ <= gas →
    x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
    dom (<[x := T]> Σ) ⊆ world_dom (m' : World) →
    world_store_closed_on (dom (<[x := T]> Σ)) m' →
    expr_total_on (dom (<[x := T]> Σ)) e m' →
    m' ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e <->
    m' ⊨ denot_ty_fuel gas Σ τ e) →
  cty_measure (CTUnion τa τb) <= S gas →
  x ∉ dom Σ ∪ fv_cty (CTUnion τa τb) ∪ fv_tm e →
  dom (<[x := T]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTUnion τa τb) e <->
  m ⊨ denot_ty_fuel (S gas) Σ (CTUnion τa τb) e.
Proof.
  intros IH Hgas Hx Hdom_sub Hclosed Htotal. split; intros Hsrc.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    assert (Hbasic_base : basic_choice_ty (dom Σ) (CTUnion τa τb)).
    {
      eapply basic_choice_ty_drop_fresh.
      - intros Hxτ. apply Hx.
        apply elem_of_union_l. apply elem_of_union_r. exact Hxτ.
      - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
        + exact Hbasic_src.
        + rewrite dom_insert_L. set_solver.
    }
    assert (Htyped_base : Σ ⊢ₑ e ⋮ erase_ty (CTUnion τa τb)).
    {
      eapply basic_typing_drop_insert_fresh_tm.
      - intros Hxe. apply Hx. apply elem_of_union_r. exact Hxe.
      - exact Htyped_src.
    }
    inversion Hbasic_base as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
    eapply denot_ty_fuel_intro.
    + exact Hbasic_base.
    + exact Htyped_base.
    + eapply world_store_closed_on_world_closed_on.
      eapply world_store_closed_on_mono; [| exact Hclosed].
      rewrite dom_insert_L. set_solver.
    + eapply expr_total_on_drop_insert_fresh_same.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hclosed.
      * exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody |- *.
      eapply res_models_or_transport_between_worlds; [| | | | exact Hbody].
      * etrans; [| etrans; [| exact Hdom_sub]].
        -- eapply (denot_ty_fuel_formula_fv_subset_env gas Σ τa e).
           ++ cbn [cty_measure] in Hgas. lia.
           ++ eapply basic_choice_ty_fv_subset. exact HbasicA.
        -- rewrite dom_insert_L. set_solver.
      * etrans; [| etrans; [| exact Hdom_sub]].
        -- eapply (denot_ty_fuel_formula_fv_subset_env gas Σ τb e).
           ++ cbn [cty_measure] in Hgas. lia.
           ++ eapply basic_choice_ty_fv_subset. exact HbasicB.
        -- rewrite dom_insert_L. set_solver.
      * intros Ha.
        destruct (IH τa m) as [IHto _].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. left. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHto Ha).
      * intros Hb.
        destruct (IH τb m) as [IHto _].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. right. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHto Hb).
    + etrans; [| exact Hdom_sub].
      rewrite dom_insert_L. set_solver.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    inversion Hbasic_src as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasic_src].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_weaken_insert_tm; [set_solver | exact Htyped_src].
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody |- *.
      eapply res_models_or_transport_between_worlds; [| | | | exact Hbody].
      * etrans; [| exact Hdom_sub].
        eapply (denot_ty_fuel_formula_fv_subset_env gas (<[x:=T]> Σ) τa e);
          [cbn [cty_measure] in Hgas; lia |].
        eapply basic_choice_ty_fv_subset.
        eapply basic_choice_ty_mono; [| exact HbasicA].
        rewrite dom_insert_L. set_solver.
      * etrans; [| exact Hdom_sub].
        eapply (denot_ty_fuel_formula_fv_subset_env gas (<[x:=T]> Σ) τb e);
          [cbn [cty_measure] in Hgas; lia |].
        eapply basic_choice_ty_fv_subset.
        eapply basic_choice_ty_mono; [| exact HbasicB].
        rewrite dom_insert_L. set_solver.
      * intros Ha.
        destruct (IH τa m) as [_ IHfrom].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. left. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHfrom Ha).
      * intros Hb.
        destruct (IH τb m) as [_ IHfrom].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. right. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_sub.
        -- exact Hclosed.
        -- exact Htotal.
        -- exact (IHfrom Hb).
    + exact Hdom_sub.
Qed.

Lemma denot_ty_fuel_insert_fresh_env_irrel_same_world_sum_case gas
    (Σ : gmap atom ty) τa τb e x T (m : WfWorld) :
  (∀ τ (m' : WfWorld),
    cty_measure τ <= gas →
    x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
    dom (<[x := T]> Σ) ⊆ world_dom (m' : World) →
    world_store_closed_on (dom (<[x := T]> Σ)) m' →
    expr_total_on (dom (<[x := T]> Σ)) e m' →
    m' ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e <->
    m' ⊨ denot_ty_fuel gas Σ τ e) →
  cty_measure (CTSum τa τb) <= S gas →
  x ∉ dom Σ ∪ fv_cty (CTSum τa τb) ∪ fv_tm e →
  dom (<[x := T]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTSum τa τb) e <->
  m ⊨ denot_ty_fuel (S gas) Σ (CTSum τa τb) e.
Proof.
  intros IH Hgas Hx Hdom_sub Hclosed Htotal. split; intros Hsrc.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    assert (Hbasic_base : basic_choice_ty (dom Σ) (CTSum τa τb)).
    {
      eapply basic_choice_ty_drop_fresh.
      - intros Hxτ. apply Hx.
        apply elem_of_union_l. apply elem_of_union_r. exact Hxτ.
      - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
        + exact Hbasic_src.
        + rewrite dom_insert_L. set_solver.
    }
    assert (Htyped_base : Σ ⊢ₑ e ⋮ erase_ty (CTSum τa τb)).
    {
      eapply basic_typing_drop_insert_fresh_tm.
      - intros Hxe. apply Hx. apply elem_of_union_r. exact Hxe.
      - exact Htyped_src.
    }
    inversion Hbasic_base as [| | | |D τ1' τ2' HbasicA HbasicB Herase| |]; subst.
    eapply denot_ty_fuel_intro.
    + exact Hbasic_base.
    + exact Htyped_base.
    + eapply world_store_closed_on_world_closed_on.
      eapply world_store_closed_on_mono; [| exact Hclosed].
      rewrite dom_insert_L. set_solver.
    + eapply expr_total_on_drop_insert_fresh_same.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hclosed.
      * exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody |- *.
      unfold res_models, res_models_with_store in Hbody.
      simpl in Hbody.
      destruct Hbody as [_ [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]]].
      assert (Hdom_n1 : dom (<[x:=T]> Σ) ⊆ world_dom (n1 : World)).
      {
        pose proof (res_models_with_store_fuel_scoped
          _ ∅ n1 (denot_ty_fuel gas (<[x:=T]> Σ) τa e) Hn1)
          as Hscope.
        unfold formula_scoped_in_world in Hscope.
        intros z Hz. apply Hscope. apply elem_of_union. right.
        eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
        exact Hz.
      }
      assert (Hdom_n2 : dom (<[x:=T]> Σ) ⊆ world_dom (n2 : World)).
      {
        pose proof (res_models_with_store_fuel_scoped
          _ ∅ n2 (denot_ty_fuel gas (<[x:=T]> Σ) τb e) Hn2)
          as Hscope.
        unfold formula_scoped_in_world in Hscope.
        intros z Hz. apply Hscope. apply elem_of_union. right.
        eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
        exact Hz.
      }
      eapply res_models_plus_intro with (m1 := n1) (m2 := n2) (Hdef := Hdef).
      * unfold formula_scoped_in_world. simpl.
        intros z Hz.
        apply elem_of_union in Hz as [Hz | Hz].
        -- rewrite dom_empty_L in Hz. apply not_elem_of_empty in Hz. contradiction.
        -- apply elem_of_union in Hz as [Hz | Hz].
           ++ assert (HzΣ : z ∈ dom Σ).
              {
                eapply (denot_ty_fuel_formula_fv_subset_env gas Σ τa e).
                - cbn [cty_measure] in Hgas. lia.
                - eapply basic_choice_ty_fv_subset. exact HbasicA.
                - exact Hz.
              }
              exact (Hdom_sub z ltac:(rewrite dom_insert_L; set_solver)).
           ++ assert (HzΣ : z ∈ dom Σ).
              {
                eapply (denot_ty_fuel_formula_fv_subset_env gas Σ τb e).
                - cbn [cty_measure] in Hgas. lia.
                - eapply basic_choice_ty_fv_subset. exact HbasicB.
                - exact Hz.
              }
              exact (Hdom_sub z ltac:(rewrite dom_insert_L; set_solver)).
      * exact Hle.
      * assert (Hn1_model : n1 ⊨ denot_ty_fuel gas (<[x:=T]> Σ) τa e).
        { unfold res_models, res_models_with_store. models_fuel_irrel Hn1. }
        destruct (IH τa n1) as [IHto _].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. left. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_n1.
        -- eapply world_store_closed_on_sum_le_l; eauto.
        -- eapply expr_total_on_sum_le_l; eauto.
        -- exact (IHto Hn1_model).
      * assert (Hn2_model : n2 ⊨ denot_ty_fuel gas (<[x:=T]> Σ) τb e).
        { unfold res_models, res_models_with_store. models_fuel_irrel Hn2. }
        destruct (IH τb n2) as [IHto _].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. right. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- exact Hdom_n2.
        -- eapply world_store_closed_on_sum_le_r; eauto.
        -- eapply expr_total_on_sum_le_r; eauto.
        -- exact (IHto Hn2_model).
    + etrans; [| exact Hdom_sub].
      rewrite dom_insert_L. set_solver.
  - pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
      as [Hbasic_src Htyped_src].
    inversion Hbasic_src as [| | | |D τ1' τ2' HbasicA HbasicB Herase| |]; subst.
    eapply denot_ty_fuel_intro.
    + eapply basic_choice_ty_mono; [| exact Hbasic_src].
      rewrite dom_insert_L. set_solver.
    + eapply basic_typing_weaken_insert_tm; [set_solver | exact Htyped_src].
    + eapply world_store_closed_on_world_closed_on. exact Hclosed.
    + exact Htotal.
    + pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
      cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody |- *.
      pose proof (denot_ty_fuel_formula_fv_subset_env
        gas Σ τa e ltac:(cbn [cty_measure] in Hgas; lia)
        ltac:(eapply basic_choice_ty_fv_subset; exact HbasicA)) as HfvA.
      pose proof (denot_ty_fuel_formula_fv_subset_env
        gas Σ τb e ltac:(cbn [cty_measure] in Hgas; lia)
        ltac:(eapply basic_choice_ty_fv_subset; exact HbasicB)) as HfvB.
      pose proof (proj1 (res_models_minimal_on (dom Σ) m
        (FPlus (denot_ty_fuel gas Σ τa e) (denot_ty_fuel gas Σ τb e))
        ltac:(simpl; set_solver)) Hbody) as Hbody_min.
      unfold res_models, res_models_with_store in Hbody_min.
      simpl in Hbody_min.
      destruct Hbody_min as [_ [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]]].
      assert (Hdom_n1 :
        world_dom (n1 : World) = world_dom (res_restrict m (dom Σ) : World)).
      {
        pose proof (res_models_with_store_fuel_scoped
          _ ∅ n1 (denot_ty_fuel gas Σ τa e) Hn1) as Hscope1.
        unfold formula_scoped_in_world in Hscope1.
        pose proof (raw_le_dom _ _ Hle) as Hdom_le.
        change (world_dom (n1 : World) = world_dom (m : World) ∩ dom Σ).
        apply set_eq. intros z. split.
        - intros Hz. apply Hdom_le. exact Hz.
        - intros Hz. apply Hscope1. apply elem_of_union. right.
          eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
          apply elem_of_intersection in Hz as [_ HzΣ]. exact HzΣ.
      }
      destruct (res_sum_lift_along_restrict m n1 n2 (dom Σ) Hdef
        Hdom_n1 Hle) as
        [m1 [m2 [Hdef'
          [Hdom_m1 [Hdom_m2 [Hsub_m1 [Hsub_m2
            [Hrestr1 [Hrestr2 Hle_full]]]]]]]]].
      eapply res_models_plus_intro with (m1 := m1) (m2 := m2) (Hdef := Hdef').
      * unfold formula_scoped_in_world. simpl.
        intros z Hz.
        apply elem_of_union in Hz as [Hz | Hz].
        -- rewrite dom_empty_L in Hz. apply not_elem_of_empty in Hz. contradiction.
        -- apply elem_of_union in Hz as [Hz | Hz].
           ++ eapply denot_ty_fuel_formula_fv_subset_env in Hz.
              3:{ eapply basic_choice_ty_fv_subset.
                  eapply basic_choice_ty_mono; [| exact HbasicA].
                  rewrite dom_insert_L. set_solver. }
              2:{ cbn [cty_measure] in Hgas. lia. }
              exact (Hdom_sub z Hz).
           ++ eapply denot_ty_fuel_formula_fv_subset_env in Hz.
              3:{ eapply basic_choice_ty_fv_subset.
                  eapply basic_choice_ty_mono; [| exact HbasicB].
                  rewrite dom_insert_L. set_solver. }
              2:{ cbn [cty_measure] in Hgas. lia. }
              exact (Hdom_sub z Hz).
      * exact Hle_full.
      * assert (Hn1_model : n1 ⊨ denot_ty_fuel gas Σ τa e).
        { unfold res_models, res_models_with_store. models_fuel_irrel Hn1. }
        assert (Hm1_base : m1 ⊨ denot_ty_fuel gas Σ τa e).
        {
          apply (proj2 (res_models_minimal_on (dom Σ) m1
            (denot_ty_fuel gas Σ τa e) HfvA)).
          rewrite Hrestr1. exact Hn1_model.
        }
        destruct (IH τa m1) as [_ IHfrom].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. left. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- rewrite Hdom_m1. exact Hdom_sub.
        -- intros σ Hσ. apply Hclosed. exact (proj2 Hsub_m1 σ Hσ).
        -- destruct Htotal as [Hfv [n Hsn]]. split; [exact Hfv |].
           exists n.
           intros σ Hσ. apply Hsn. exact (proj2 Hsub_m1 σ Hσ).
        -- exact (IHfrom Hm1_base).
      * assert (Hn2_model : n2 ⊨ denot_ty_fuel gas Σ τb e).
        { unfold res_models, res_models_with_store. models_fuel_irrel Hn2. }
        assert (Hm2_base : m2 ⊨ denot_ty_fuel gas Σ τb e).
        {
          apply (proj2 (res_models_minimal_on (dom Σ) m2
            (denot_ty_fuel gas Σ τb e) HfvB)).
          rewrite Hrestr2. exact Hn2_model.
        }
        destruct (IH τb m2) as [_ IHfrom].
        -- cbn [cty_measure] in Hgas. lia.
        -- intros Hbad. apply Hx.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l. exact Hbad.
              ** apply elem_of_union_r. simpl. apply elem_of_union. right. exact Hbad.
           ++ apply elem_of_union_r. exact Hbad.
        -- rewrite Hdom_m2. exact Hdom_sub.
        -- intros σ Hσ. apply Hclosed. exact (proj2 Hsub_m2 σ Hσ).
        -- destruct Htotal as [Hfv [n Hsn]]. split; [exact Hfv |].
           exists n.
           intros σ Hσ. apply Hsn. exact (proj2 Hsub_m2 σ Hσ).
        -- exact (IHfrom Hm2_base).
    + exact Hdom_sub.
Qed.

Lemma denot_ty_fuel_drop_fresh_env_irrel_over_case gas
    (Σ : gmap atom ty) b φ e x T (m : WfWorld) :
  x ∉ dom Σ ∪ qual_dom φ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTOver b φ) e →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel (S gas) Σ (CTOver b φ) e.
Proof.
  intros Hx Hdom Hclosed Htotal Hsrc.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
    as [Hbasic_src Htyped_src].
  assert (Htyped_base : Σ ⊢ₑ e ⋮ b).
  {
    eapply basic_typing_drop_insert_fresh_tm.
    - intros Hxe. apply Hx. set_solver.
    - exact Htyped_src.
  }
  assert (Hbasic_base : basic_choice_ty (dom Σ) (CTOver b φ)).
  {
    eapply basic_choice_ty_drop_fresh.
    - intros Hxτ. apply Hx. set_solver.
    - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
      + exact Hbasic_src.
      + rewrite dom_insert_L. set_solver.
  }
  inversion Hbasic_base as [D b' φ' Hqbody| | | | | |]; subst.
  assert (Hφ : qual_dom φ ⊆ dom Σ).
  { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
  eapply denot_ty_fuel_intro.
  - exact Hbasic_base.
  - exact Htyped_base.
  - eapply world_store_closed_on_world_closed_on.
    eapply world_store_closed_on_restrict_insert_fresh. exact Hclosed.
  - eapply expr_total_on_restrict_insert_fresh; eauto.
    intros Hxe. apply Hx. set_solver.
  - cbn [denot_ty_fuel_body fv_cty erase_ty].
    pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
    cbn [denot_ty_fuel_body fv_cty erase_ty] in Hbody.
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
            (FOver (FTypeQualifier φν))))) in Hbody.
    2:{
      eapply (denot_refinement_over_cont_insert_fresh_eq
        (dom Σ : aset) Σ x T b φ); [set_solver | reflexivity].
    }
    eapply FExprContIn_restrict_insert_fresh_env_irrel.
    + exact Htyped_base.
    + intros Hxe. apply Hx.
      apply elem_of_union in Hxe as [Hxdom | Hxfv].
      * apply elem_of_union_l. apply elem_of_union_l. exact Hxdom.
      * apply elem_of_union_r. exact Hxfv.
    + exact Hdom.
    + exact Hclosed.
    + exact Htotal.
    + eapply denot_refinement_over_cont_fv_subset. exact Hφ.
    + eapply denot_refinement_over_cont_rename_stable. exact Hφ.
    + exact Hbody.
  - simpl. rewrite Hdom, dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_drop_fresh_env_irrel_under_case gas
    (Σ : gmap atom ty) b φ e x T (m : WfWorld) :
  x ∉ dom Σ ∪ qual_dom φ ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTUnder b φ) e →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel (S gas) Σ (CTUnder b φ) e.
Proof.
  intros Hx Hdom Hclosed Htotal Hsrc.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
    as [Hbasic_src Htyped_src].
  assert (Htyped_base : Σ ⊢ₑ e ⋮ b).
  {
    eapply basic_typing_drop_insert_fresh_tm.
    - intros Hxe. apply Hx. set_solver.
    - exact Htyped_src.
  }
  assert (Hbasic_base : basic_choice_ty (dom Σ) (CTUnder b φ)).
  {
    eapply basic_choice_ty_drop_fresh.
    - intros Hxτ. apply Hx. set_solver.
    - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
      + exact Hbasic_src.
      + rewrite dom_insert_L. set_solver.
  }
  inversion Hbasic_base as [|D b' φ' Hqbody| | | | |]; subst.
  assert (Hφ : qual_dom φ ⊆ dom Σ).
  { eapply basic_qualifier_body_fv_subset. exact Hqbody. }
  eapply denot_ty_fuel_intro.
  - exact Hbasic_base.
  - exact Htyped_base.
  - eapply world_store_closed_on_world_closed_on.
    eapply world_store_closed_on_restrict_insert_fresh. exact Hclosed.
  - eapply expr_total_on_restrict_insert_fresh; eauto.
    intros Hxe. apply Hx. set_solver.
  - cbn [denot_ty_fuel_body fv_cty erase_ty].
    pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
    cbn [denot_ty_fuel_body fv_cty erase_ty] in Hbody.
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
            (FUnder (FTypeQualifier φν))))) in Hbody.
    2:{
      eapply (denot_refinement_under_cont_insert_fresh_eq
        (dom Σ : aset) Σ x T b φ); [set_solver | reflexivity].
    }
    eapply FExprContIn_restrict_insert_fresh_env_irrel.
    + exact Htyped_base.
    + intros Hxe. apply Hx.
      apply elem_of_union in Hxe as [Hxdom | Hxfv].
      * apply elem_of_union_l. apply elem_of_union_l. exact Hxdom.
      * apply elem_of_union_r. exact Hxfv.
    + exact Hdom.
    + exact Hclosed.
    + exact Htotal.
    + eapply denot_refinement_under_cont_fv_subset. exact Hφ.
    + eapply denot_refinement_under_cont_rename_stable. exact Hφ.
    + exact Hbody.
  - simpl. rewrite Hdom, dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_drop_fresh_env_irrel_inter_case gas
    (Σ : gmap atom ty) τa τb e x T (m : WfWorld) :
  (∀ τ,
    cty_measure τ <= gas →
    x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
    world_dom (m : World) = dom (<[x := T]> Σ) →
    world_store_closed_on (dom (<[x := T]> Σ)) m →
    expr_total_on (dom (<[x := T]> Σ)) e m →
    m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e →
    res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e) →
  cty_measure (CTInter τa τb) <= S gas →
  x ∉ dom Σ ∪ fv_cty (CTInter τa τb) ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTInter τa τb) e →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel (S gas) Σ (CTInter τa τb) e.
Proof.
  intros IH Hgas Hx Hdom Hclosed Htotal Hsrc.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
    as [Hbasic_src Htyped_src].
  assert (Hbasic_base : basic_choice_ty (dom Σ) (CTInter τa τb)).
  {
    eapply basic_choice_ty_drop_fresh.
    - intros Hxτ. apply Hx.
      apply elem_of_union_l. apply elem_of_union_r.
      exact Hxτ.
    - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
      + exact Hbasic_src.
      + rewrite dom_insert_L. set_solver.
  }
  assert (Htyped_base : Σ ⊢ₑ e ⋮ erase_ty (CTInter τa τb)).
  {
    eapply basic_typing_drop_insert_fresh_tm.
    - intros Hxe. apply Hx.
      apply elem_of_union_r. exact Hxe.
    - exact Htyped_src.
  }
  inversion Hbasic_base as [| |D τ1' τ2' HbasicA HbasicB Herase| | | |]; subst.
  eapply denot_ty_fuel_intro.
  - exact Hbasic_base.
  - exact Htyped_base.
  - eapply world_store_closed_on_world_closed_on.
    eapply world_store_closed_on_restrict_insert_fresh. exact Hclosed.
  - eapply expr_total_on_restrict_insert_fresh; eauto.
    intros Hxe. apply Hx.
    apply elem_of_union in Hxe as [Hxdom | Hxfv].
    + apply elem_of_union_l. apply elem_of_union_l. exact Hxdom.
    + apply elem_of_union_r. exact Hxfv.
  - pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
    cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody.
    cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty].
    apply res_models_and_intro_from_models.
    + eapply IH.
      * cbn in Hgas. lia.
	      * intros Hbad. apply Hx.
	        apply elem_of_union in Hbad as [Hbad | Hbad].
	        -- apply elem_of_union_l.
             apply elem_of_union in Hbad as [Hbad | Hbad].
             ++ apply elem_of_union_l. exact Hbad.
             ++ apply elem_of_union_r. simpl.
                apply elem_of_union. left. exact Hbad.
	        -- apply elem_of_union_r. exact Hbad.
      * exact Hdom.
      * exact Hclosed.
      * exact Htotal.
      * apply res_models_and_elim_l in Hbody. exact Hbody.
    + eapply IH.
      * cbn in Hgas. lia.
	      * intros Hbad. apply Hx.
	        apply elem_of_union in Hbad as [Hbad | Hbad].
	        -- apply elem_of_union_l.
             apply elem_of_union in Hbad as [Hbad | Hbad].
             ++ apply elem_of_union_l. exact Hbad.
             ++ apply elem_of_union_r. simpl.
                apply elem_of_union. right. exact Hbad.
	        -- apply elem_of_union_r. exact Hbad.
      * exact Hdom.
      * exact Hclosed.
      * exact Htotal.
      * apply res_models_and_elim_r in Hbody. exact Hbody.
  - simpl. rewrite Hdom, dom_insert_L. set_solver.
Qed.

Lemma denot_ty_fuel_drop_fresh_env_irrel_union_case gas
    (Σ : gmap atom ty) τa τb e x T (m : WfWorld) :
  (∀ τ,
    cty_measure τ <= gas →
    x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
    world_dom (m : World) = dom (<[x := T]> Σ) →
    world_store_closed_on (dom (<[x := T]> Σ)) m →
    expr_total_on (dom (<[x := T]> Σ)) e m →
    m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e →
    res_restrict m (dom Σ) ⊨ denot_ty_fuel gas Σ τ e) →
  cty_measure (CTUnion τa τb) <= S gas →
  x ∉ dom Σ ∪ fv_cty (CTUnion τa τb) ∪ fv_tm e →
  world_dom (m : World) = dom (<[x := T]> Σ) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel (S gas) (<[x := T]> Σ) (CTUnion τa τb) e →
  res_restrict m (dom Σ) ⊨ denot_ty_fuel (S gas) Σ (CTUnion τa τb) e.
Proof.
  intros IH Hgas Hx Hdom Hclosed Htotal Hsrc.
  pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
    as [Hbasic_src Htyped_src].
  assert (Hbasic_base : basic_choice_ty (dom Σ) (CTUnion τa τb)).
  {
    eapply basic_choice_ty_drop_fresh.
    - intros Hxτ. apply Hx.
      apply elem_of_union_l. apply elem_of_union_r. exact Hxτ.
    - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
      + exact Hbasic_src.
      + rewrite dom_insert_L. set_solver.
  }
  assert (Htyped_base : Σ ⊢ₑ e ⋮ erase_ty (CTUnion τa τb)).
  {
    eapply basic_typing_drop_insert_fresh_tm.
    - intros Hxe. apply Hx. apply elem_of_union_r. exact Hxe.
    - exact Htyped_src.
  }
  inversion Hbasic_base as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
  eapply denot_ty_fuel_intro.
  - exact Hbasic_base.
  - exact Htyped_base.
  - eapply world_store_closed_on_world_closed_on.
    eapply world_store_closed_on_restrict_insert_fresh. exact Hclosed.
  - eapply expr_total_on_restrict_insert_fresh; eauto.
    intros Hxe. apply Hx.
    apply elem_of_union in Hxe as [Hxdom | Hxfv].
    + apply elem_of_union_l. apply elem_of_union_l. exact Hxdom.
    + apply elem_of_union_r. exact Hxfv.
  - pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
    cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody.
    cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty].
    eapply res_models_or_transport_between_worlds; [| | | | exact Hbody].
    + simpl. intros z Hz.
      assert (HzΣ : z ∈ dom Σ).
      {
        eapply (denot_ty_fuel_formula_fv_subset_env gas Σ τa e).
        - cbn [cty_measure] in Hgas. lia.
        - eapply basic_choice_ty_fv_subset. exact HbasicA.
        - exact Hz.
      }
      apply elem_of_intersection. split.
      * rewrite Hdom, dom_insert_L. apply elem_of_union_r. exact HzΣ.
      * exact HzΣ.
    + simpl. intros z Hz.
      assert (HzΣ : z ∈ dom Σ).
      {
        eapply (denot_ty_fuel_formula_fv_subset_env gas Σ τb e).
        - cbn [cty_measure] in Hgas. lia.
        - eapply basic_choice_ty_fv_subset. exact HbasicB.
        - exact Hz.
      }
      apply elem_of_intersection. split.
      * rewrite Hdom, dom_insert_L. apply elem_of_union_r. exact HzΣ.
      * exact HzΣ.
    + intros Ha. eapply IH.
      * cbn [cty_measure] in Hgas. lia.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l. exact Hbad.
           ++ apply elem_of_union_r. simpl.
              apply elem_of_union. left. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hdom.
      * exact Hclosed.
      * exact Htotal.
      * exact Ha.
    + intros Hb. eapply IH.
      * cbn [cty_measure] in Hgas. lia.
      * intros Hbad. apply Hx.
        apply elem_of_union in Hbad as [Hbad | Hbad].
        -- apply elem_of_union_l.
           apply elem_of_union in Hbad as [Hbad | Hbad].
           ++ apply elem_of_union_l. exact Hbad.
           ++ apply elem_of_union_r. simpl.
              apply elem_of_union. right. exact Hbad.
        -- apply elem_of_union_r. exact Hbad.
      * exact Hdom.
      * exact Hclosed.
      * exact Htotal.
      * exact Hb.
  - simpl. rewrite Hdom, dom_insert_L. set_solver.
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
  revert Σ τ e x T m.
  induction gas as [|gas IH]; intros Σ τ e x T m Hgas Hx Hdom Hclosed Htotal Hsrc.
  - pose proof (cty_measure_gt_0 τ). lia.
  - destruct τ as [b φ|b φ|τa τb|τa τb|τa τb|τx τ|τx τ].
    + eapply denot_ty_fuel_drop_fresh_env_irrel_over_case; eauto.
    + eapply denot_ty_fuel_drop_fresh_env_irrel_under_case; eauto.
    + eapply denot_ty_fuel_drop_fresh_env_irrel_inter_case; eauto.
    + eapply denot_ty_fuel_drop_fresh_env_irrel_union_case; eauto.
    + cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in *.
      pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hsrc)
        as [Hbasic_src Htyped_src].
      assert (Hbasic_base : basic_choice_ty (dom Σ) (CTSum τa τb)).
      {
        eapply basic_choice_ty_drop_fresh.
        - intros Hxτ. apply Hx.
          apply elem_of_union_l. apply elem_of_union_r. exact Hxτ.
        - replace (dom Σ ∪ {[x]}) with (dom (<[x:=T]> Σ)).
          + exact Hbasic_src.
          + rewrite dom_insert_L. set_solver.
      }
      assert (Htyped_base : Σ ⊢ₑ e ⋮ erase_ty (CTSum τa τb)).
      {
        eapply basic_typing_drop_insert_fresh_tm.
        - intros Hxe. apply Hx. apply elem_of_union_r. exact Hxe.
        - exact Htyped_src.
      }
      inversion Hbasic_base as [| | | |D τ1' τ2' HbasicA HbasicB Herase| |]; subst.
      eapply denot_ty_fuel_intro.
      * exact Hbasic_base.
      * exact Htyped_base.
      * eapply world_store_closed_on_world_closed_on.
        eapply world_store_closed_on_restrict_insert_fresh. exact Hclosed.
      * eapply expr_total_on_restrict_insert_fresh; eauto.
        intros Hxe. apply Hx.
        apply elem_of_union in Hxe as [Hxdom | Hxfv].
        -- apply elem_of_union_l. apply elem_of_union_l. exact Hxdom.
        -- apply elem_of_union_r. exact Hxfv.
      * pose proof (denot_ty_fuel_body_of_formula _ _ _ _ _ Hsrc) as Hbody.
        cbn [denot_ty_fuel_body cty_measure fv_cty erase_ty] in Hbody.
        unfold res_models, res_models_with_store in Hbody.
        simpl in Hbody.
        destruct Hbody as [_ [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]]].
        set (r1 := res_restrict n1 (dom Σ)).
        set (r2 := res_restrict n2 (dom Σ)).
        assert (HdefR : raw_sum_defined r1 r2).
        {
          subst r1 r2. unfold raw_sum_defined. simpl.
          rewrite Hdef. reflexivity.
        }
        eapply res_models_plus_intro with (m1 := r1) (m2 := r2) (Hdef := HdefR).
        -- unfold formula_scoped_in_world. simpl.
           pose proof (denot_ty_fuel_formula_fv_subset_env
             gas Σ τa e ltac:(cbn [cty_measure] in Hgas; lia)
             ltac:(eapply basic_choice_ty_fv_subset; exact HbasicA)) as HfvA.
           pose proof (denot_ty_fuel_formula_fv_subset_env
             gas Σ τb e ltac:(cbn [cty_measure] in Hgas; lia)
             ltac:(eapply basic_choice_ty_fv_subset; exact HbasicB)) as HfvB.
           simpl. intros z Hz.
           apply elem_of_union in Hz as [Hz | Hz].
           { rewrite dom_empty_L in Hz. apply not_elem_of_empty in Hz. contradiction. }
           apply elem_of_union in Hz as [Hz | Hz].
           ++ apply HfvA in Hz. simpl. set_solver.
           ++ apply HfvB in Hz. simpl. set_solver.
        -- subst r1 r2.
           eapply res_le_restrict.
           ++ etrans.
              ** eapply (res_sum_le_mono
                   (res_restrict n1 (dom Σ)) (res_restrict n2 (dom Σ))
                   n1 n2 HdefR Hdef);
                   apply res_restrict_le.
              ** exact Hle.
           ++ simpl. set_solver.
        -- unfold r1.
           eapply (IH Σ τa e x T n1).
           ++ cbn [cty_measure] in Hgas. lia.
           ++ intros Hbad. apply Hx.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l.
                 apply elem_of_union in Hbad as [Hbad | Hbad].
                 --- apply elem_of_union_l. exact Hbad.
                 --- apply elem_of_union_r. simpl.
                     apply elem_of_union. left. exact Hbad.
              ** apply elem_of_union_r. exact Hbad.
           ++ assert (Hdom_n1 : world_dom (n1 : World) = dom (<[x:=T]> Σ)).
              {
                apply set_eq. intros z. split.
                - intros Hz.
                  pose proof (raw_le_dom (res_sum n1 n2 Hdef : World) (m : World) Hle)
                    as Hdom_le.
                  rewrite Hdom in Hdom_le.
                  apply Hdom_le. simpl. exact Hz.
                - intros Hz.
                  pose proof (res_models_with_store_fuel_scoped
                    _ ∅ n1 (denot_ty_fuel gas (<[x:=T]> Σ) τa e) Hn1)
                    as Hscope1.
                  unfold formula_scoped_in_world in Hscope1.
                  apply Hscope1. apply elem_of_union. right.
                  eapply denot_ty_fuel_env_fv_subset.
                  + cbn [cty_measure] in Hgas. lia.
                  + exact Hz.
              }
              exact Hdom_n1.
           ++ intros σ Hσ.
              assert (Hσsum : (res_sum n1 n2 Hdef : World) σ).
              { simpl. left. exact Hσ. }
              unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
              rewrite Hle in Hσsum. simpl in Hσsum.
              destruct Hσsum as [σm [Hσm Hrestrict]].
              assert (Hinsert_sum :
                dom (<[x:=T]> Σ) ⊆ world_dom (res_sum n1 n2 Hdef : World)).
              {
                intros z Hz. simpl.
                pose proof (res_models_with_store_fuel_scoped
                  _ ∅ n1 (denot_ty_fuel gas (<[x:=T]> Σ) τa e) Hn1)
                  as Hscope1.
                unfold formula_scoped_in_world in Hscope1.
                apply Hscope1. apply elem_of_union. right.
                eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
                exact Hz.
              }
              rewrite <- Hrestrict.
              rewrite store_restrict_restrict.
              replace (world_dom (res_sum n1 n2 Hdef : World) ∩ dom (<[x:=T]> Σ))
                with (dom (<[x:=T]> Σ)) by set_solver.
              apply Hclosed. exact Hσm.
           ++ destruct Htotal as [Hfv_total [ntotal Hsn]]. split.
              ** simpl. rewrite dom_insert_L. set_solver.
              ** exists ntotal. intros σ Hσ.
                 assert (Hσsum : (res_sum n1 n2 Hdef : World) σ).
                 { simpl. left. exact Hσ. }
                 unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
                 rewrite Hle in Hσsum. simpl in Hσsum.
                 destruct Hσsum as [σm [Hσm Hrestrict]].
                 assert (Hinsert_sum :
                   dom (<[x:=T]> Σ) ⊆ world_dom (res_sum n1 n2 Hdef : World)).
                 {
                   intros z Hz. simpl.
                   pose proof (res_models_with_store_fuel_scoped
                     _ ∅ n1 (denot_ty_fuel gas (<[x:=T]> Σ) τa e) Hn1)
                     as Hscope1.
                   unfold formula_scoped_in_world in Hscope1.
                   apply Hscope1. apply elem_of_union. right.
                   eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
                   exact Hz.
                 }
                 replace (store_restrict σ (dom (<[x:=T]> Σ)))
                   with (store_restrict σm (dom (<[x:=T]> Σ))).
                 { apply Hsn. exact Hσm. }
                 rewrite <- Hrestrict.
                 rewrite store_restrict_restrict.
                 replace (world_dom (res_sum n1 n2 Hdef : World) ∩ dom (<[x:=T]> Σ))
                   with (dom (<[x:=T]> Σ)) by set_solver.
                 reflexivity.
           ++ unfold res_models, res_models_with_store.
              models_fuel_irrel Hn1.
        -- unfold r2.
           eapply (IH Σ τb e x T n2).
           ++ cbn [cty_measure] in Hgas. lia.
           ++ intros Hbad. apply Hx.
              apply elem_of_union in Hbad as [Hbad | Hbad].
              ** apply elem_of_union_l.
                 apply elem_of_union in Hbad as [Hbad | Hbad].
                 --- apply elem_of_union_l. exact Hbad.
                 --- apply elem_of_union_r. simpl.
                     apply elem_of_union. right. exact Hbad.
              ** apply elem_of_union_r. exact Hbad.
           ++ assert (Hdom_n2 : world_dom (n2 : World) = dom (<[x:=T]> Σ)).
              {
                apply set_eq. intros z. split.
                - intros Hz.
                  pose proof (raw_le_dom (res_sum n1 n2 Hdef : World) (m : World) Hle)
                    as Hdom_le.
                  rewrite Hdom in Hdom_le.
                  apply Hdom_le. simpl. rewrite Hdef. exact Hz.
                - intros Hz.
                  pose proof (res_models_with_store_fuel_scoped
                    _ ∅ n2 (denot_ty_fuel gas (<[x:=T]> Σ) τb e) Hn2)
                    as Hscope2.
                  unfold formula_scoped_in_world in Hscope2.
                  apply Hscope2. apply elem_of_union. right.
                  eapply denot_ty_fuel_env_fv_subset.
                  + cbn [cty_measure] in Hgas. lia.
                  + exact Hz.
              }
              exact Hdom_n2.
           ++ intros σ Hσ.
              assert (Hσsum : (res_sum n1 n2 Hdef : World) σ).
              { simpl. right. exact Hσ. }
              unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
              rewrite Hle in Hσsum. simpl in Hσsum.
              destruct Hσsum as [σm [Hσm Hrestrict]].
              assert (Hinsert_sum :
                dom (<[x:=T]> Σ) ⊆ world_dom (res_sum n1 n2 Hdef : World)).
              {
                intros z Hz. simpl. rewrite Hdef.
                pose proof (res_models_with_store_fuel_scoped
                  _ ∅ n2 (denot_ty_fuel gas (<[x:=T]> Σ) τb e) Hn2)
                  as Hscope2.
                unfold formula_scoped_in_world in Hscope2.
                apply Hscope2. apply elem_of_union. right.
                eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
                exact Hz.
              }
              rewrite <- Hrestrict.
              rewrite store_restrict_restrict.
              replace (world_dom (res_sum n1 n2 Hdef : World) ∩ dom (<[x:=T]> Σ))
                with (dom (<[x:=T]> Σ)) by set_solver.
              apply Hclosed. exact Hσm.
           ++ destruct Htotal as [Hfv_total [ntotal Hsn]]. split.
              ** simpl. rewrite dom_insert_L. set_solver.
              ** exists ntotal. intros σ Hσ.
                 assert (Hσsum : (res_sum n1 n2 Hdef : World) σ).
                 { simpl. right. exact Hσ. }
                 unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
                 rewrite Hle in Hσsum. simpl in Hσsum.
                 destruct Hσsum as [σm [Hσm Hrestrict]].
                 assert (Hinsert_sum :
                   dom (<[x:=T]> Σ) ⊆ world_dom (res_sum n1 n2 Hdef : World)).
                 {
                   intros z Hz. simpl. rewrite Hdef.
                   pose proof (res_models_with_store_fuel_scoped
                     _ ∅ n2 (denot_ty_fuel gas (<[x:=T]> Σ) τb e) Hn2)
                     as Hscope2.
                   unfold formula_scoped_in_world in Hscope2.
                   apply Hscope2. apply elem_of_union. right.
                   eapply denot_ty_fuel_env_fv_subset; [cbn [cty_measure] in Hgas; lia |].
                   exact Hz.
                 }
                 replace (store_restrict σ (dom (<[x:=T]> Σ)))
                   with (store_restrict σm (dom (<[x:=T]> Σ))).
                 { apply Hsn. exact Hσm. }
                 rewrite <- Hrestrict.
                 rewrite store_restrict_restrict.
                 replace (world_dom (res_sum n1 n2 Hdef : World) ∩ dom (<[x:=T]> Σ))
                   with (dom (<[x:=T]> Σ)) by set_solver.
                 reflexivity.
           ++ unfold res_models, res_models_with_store.
              models_fuel_irrel Hn2.
      * simpl. rewrite Hdom, dom_insert_L. set_solver.
    + (* CTArrow: needs fresh-forall transport with the iff irrelevance lemma. *)
      admit.
    + (* CTWand: same fresh-forall issue as Arrow. *)
      admit.
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
	           ++ destruct Htotal as [Hfv [ntotal Hsn]]. split; [rewrite dom_insert_L; set_solver |].
	              exists ntotal.
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
	           ++ destruct Htotal as [Hfv [ntotal Hsn]]. split; [rewrite dom_insert_L; set_solver |].
	              exists ntotal.
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

Lemma denot_ty_fuel_insert_fresh_env_irrel_iff_at_world gas
    (Σ : gmap atom ty) (τ : choice_ty) e x T (m : WfWorld) :
  cty_measure τ <= gas →
  x ∉ dom Σ ∪ fv_cty τ ∪ fv_tm e →
  dom (<[x := T]> Σ) ⊆ world_dom (m : World) →
  world_store_closed_on (dom (<[x := T]> Σ)) m →
  expr_total_on (dom (<[x := T]> Σ)) e m →
  m ⊨ denot_ty_fuel gas (<[x := T]> Σ) τ e <->
  m ⊨ denot_ty_fuel gas Σ τ e.
Proof.
  intros Hgas Hx Hdom_sub Hclosed Htotal. split.
  - intros Hins.
    pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hins)
      as [Hbasic_ins _].
    pose proof (denot_ty_fuel_formula_fv_subset_env
      gas (<[x:=T]> Σ) τ e Hgas
      ltac:(eapply basic_choice_ty_fv_subset; exact Hbasic_ins)) as Hfv_ins.
    pose proof (proj1 (res_models_minimal_on
      (dom (<[x:=T]> Σ)) m
      (denot_ty_fuel gas (<[x:=T]> Σ) τ e)
      Hfv_ins) Hins) as Hins_min.
    assert (Hdom_min :
      world_dom (res_restrict m (dom (<[x:=T]> Σ)) : World) =
      dom (<[x:=T]> Σ)).
    { simpl. set_solver. }
    assert (Hclosed_min :
      world_store_closed_on (dom (<[x:=T]> Σ))
        (res_restrict m (dom (<[x:=T]> Σ)))).
    {
      eapply world_store_closed_on_restrict.
      - reflexivity.
      - exact Hclosed.
    }
    assert (Htotal_min :
      expr_total_on (dom (<[x:=T]> Σ)) e
        (res_restrict m (dom (<[x:=T]> Σ)))).
    { apply expr_total_on_restrict_self. exact Htotal. }
    pose proof (proj1 (denot_ty_fuel_insert_fresh_env_irrel_iff
      gas Σ τ e x T (res_restrict m (dom (<[x:=T]> Σ)))
      Hgas Hx Hdom_min Hclosed_min Htotal_min) Hins_min) as Hbase_min.
    rewrite res_restrict_restrict_eq in Hbase_min.
    replace (dom (<[x:=T]> Σ) ∩ dom Σ) with (dom Σ) in Hbase_min
      by (rewrite dom_insert_L; set_solver).
    eapply res_models_kripke; [apply res_restrict_le | exact Hbase_min].
  - intros Hbase.
    pose proof (denot_ty_fuel_basic_of_formula _ _ _ _ _ Hbase)
      as [Hbasic_base _].
    pose proof (denot_ty_fuel_formula_fv_subset_env
      gas Σ τ e Hgas
      ltac:(eapply basic_choice_ty_fv_subset; exact Hbasic_base)) as Hfv_base.
    pose proof (proj1 (res_models_minimal_on
      (dom Σ) m (denot_ty_fuel gas Σ τ e) Hfv_base) Hbase)
      as Hbase_min.
    assert (Hdom_min :
      world_dom (res_restrict m (dom (<[x:=T]> Σ)) : World) =
      dom (<[x:=T]> Σ)).
    { simpl. set_solver. }
    assert (Hclosed_min :
      world_store_closed_on (dom (<[x:=T]> Σ))
        (res_restrict m (dom (<[x:=T]> Σ)))).
    {
      eapply world_store_closed_on_restrict.
      - reflexivity.
      - exact Hclosed.
    }
    assert (Htotal_min :
      expr_total_on (dom (<[x:=T]> Σ)) e
        (res_restrict m (dom (<[x:=T]> Σ)))).
    { apply expr_total_on_restrict_self. exact Htotal. }
    assert (Hbase_min' :
      res_restrict (res_restrict m (dom (<[x:=T]> Σ))) (dom Σ)
        ⊨ denot_ty_fuel gas Σ τ e).
    {
      rewrite res_restrict_restrict_eq.
      replace (dom (<[x:=T]> Σ) ∩ dom Σ) with (dom Σ)
        by (rewrite dom_insert_L; set_solver).
      exact Hbase_min.
    }
    pose proof (proj2 (denot_ty_fuel_insert_fresh_env_irrel_iff
      gas Σ τ e x T (res_restrict m (dom (<[x:=T]> Σ)))
      Hgas Hx Hdom_min Hclosed_min Htotal_min) Hbase_min') as Hins_min.
    eapply res_models_kripke; [apply res_restrict_le | exact Hins_min].
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
