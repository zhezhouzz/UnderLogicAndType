(** * ChoiceTyping.TLetReduction

    Type-denotation reduction lemmas for the [tlet] soundness case.
    The final semantic bridge stays in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceTyping Require Export TLetTotal RegularDenotation.
From ChoiceTyping Require Import Naming ResultWorldBridge ResultWorldExprCont
  TLetReductionSupport.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Import Tactics.

Local Lemma singleton_union_comm_dom (Σ : gmap atom ty) T x :
  {[x]} ∪ dom Σ = dom (<[x := T]> Σ).
Proof.
  rewrite dom_insert_L. reflexivity.
Qed.

Local Ltac tlet_regular :=
  eauto 6 using basic_typing_contains_fv_tm, typing_tm_lc.

Local Lemma FExprContIn_atom_env Σ e (Q : FormulaQ) :
  FExprContIn (atom_env_to_lty_env Σ) e Q = FExprContIn Σ e Q.
Proof.
  unfold FExprContIn, FExprResultOn, into_lvars, into_lvars_lvset,
    into_lvars_aset.
  rewrite atom_env_to_lty_env_dom.
  reflexivity.
Qed.

Lemma FExprCont_tlet_reduction
    (Σ : gmap atom ty) (T1 T2 : ty)
    (m : WfWorld) e1 e2 (x : atom) (Q : FormulaQ)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ fv_tm e2 →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) (tlete e1 e2) m →
  formula_fv Q ⊆ dom Σ →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ FExprContIn (<[x := T1]> Σ) (e2 ^^ x) Q ↔
  m ⊨ FExprContIn Σ (tlete e1 e2) Q.
Proof.
  intros He1 Hlet Hxe2 Hdom Hclosed Htotal_let HQfv.
  set (m1 := let_result_world_on e1 x m Hfresh Hresult).
  assert (HxΣ : x ∉ dom Σ).
  { rewrite <- Hdom. exact Hfresh. }
  assert (He2 : <[x := T1]> Σ ⊢ₑ e2 ^^ x ⋮ T2).
  { eapply basic_typing_tlete_body_for_fresh; eauto; set_solver. }
  assert (Hdom_m1 : world_dom (m1 : World) = dom (<[x := T1]> Σ)).
  {
    subst m1. rewrite let_result_world_on_dom, Hdom, dom_insert_L.
    rewrite union_comm_L. reflexivity.
  }
  assert (Hfv1 : fv_tm e1 ⊆ dom Σ).
  { tlet_regular. }
  assert (Hclosed_m1 :
    world_closed_on (dom (<[x := T1]> Σ)) m1).
  {
    subst m1. rewrite dom_insert_L.
    rewrite union_comm_L.
    eapply let_result_world_on_store_closed_on_insert.
    - set_solver.
    - exact Hclosed.
    - intros σ vx Hσ Hsteps.
      assert (Hclosed_fv : world_closed_on (fv_tm e1) m).
      { eapply world_closed_on_mono; [exact Hfv1 | exact Hclosed]. }
      eapply (steps_closed_result_of_restrict_world
        (fv_tm e1) e1 m (store_restrict σ (fv_tm e1)) vx).
      + rewrite Hdom. exact Hfv1.
      + set_solver.
      + tlet_regular.
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
    - set_solver.
    - exact Hxe2.
    - exact Hclosed.
    - tlet_regular.
    - exact Htotal_let.
  }
  assert (HQfv_insert : formula_fv Q ⊆ dom (<[x := T1]> Σ)).
  { rewrite dom_insert_L. set_solver. }
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
    - tlet_regular.
    - apply basic_typing_contains_fv_tm in Hlet. simpl in Hlet. set_solver.
    - set_solver.
    - rewrite Hdom. set_solver.
    - intros σ Hσ. exact (proj1 (Hclosed σ Hσ)).
    - intros σ Hσ. exact (proj2 (Hclosed σ Hσ)).
    - intros σ vx Hσ Hsteps.
      eapply steps_closed_result.
      + eapply (msubst_closed_tm_of_restrict_world (dom Σ) e1 m σ).
        * rewrite Hdom. set_solver.
        * exact Hfv1.
        * tlet_regular.
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
  assert (HQopen_fv :
    ∀ ν, formula_fv (formula_open 0 ν Q) ⊆ dom Σ ∪ {[ν]}).
  {
    intros ν z Hz.
    pose proof (formula_open_fv_subset 0 ν Q z Hz) as HzQ.
    set_solver.
  }
  split.
  - intros Hcont.
    pose proof (proj1
      (FExprContIn_iff_let_result_world
        (<[x := T1]> Σ) T2 (e2 ^^ x) Q m1
        He2 Hdom_m1 Hclosed_m1 Htotal2 HQfv_insert)
      Hcont) as [L [HLdom Hbody]].
    apply (proj2
      (FExprContIn_iff_let_result_world
        Σ T2 (tlete e1 e2) Q m
        Hlet Hdom Hclosed Htotal_let HQfv)).
    exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e2).
    split; [set_solver |].
    intros ν Hν Hfreshν_tlet Hresultν_tlet.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[[HνL HνΣ] Hνx] Hνe2].
    assert (Hfreshν_body : ν ∉ world_dom (m1 : World)).
    {
      subst m1. rewrite let_result_world_on_dom, Hdom, not_elem_of_union.
      split; eauto 6.
    }
    assert (Hresultν_body :
      ∀ σ, (m1 : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm (e2 ^^ x)))
          (e2 ^^ x) →* tret vx).
    {
      eapply expr_total_on_to_fv_result; eauto.
    }
    pose proof (Hbody ν HνL Hfreshν_body Hresultν_body)
      as Hnested.
    pose proof (proj1 (res_models_minimal_on
      (dom Σ ∪ {[ν]})
      (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
      (formula_open 0 ν Q) (HQopen_fv ν)) Hnested) as Hnested_min.
    replace (dom Σ ∪ {[ν]}) with (world_dom (m : World) ∪ {[ν]})
      in Hnested_min by (rewrite Hdom; reflexivity).
    rewrite (Hdecompose_side ν Hfreshν_body Hresultν_body
      Hfreshν_tlet Hresultν_tlet ltac:(
        rewrite !not_elem_of_union; repeat split; eauto 6)) in Hnested_min.
    exact Hnested_min.
  - intros Hcont.
    pose proof (proj1
      (FExprContIn_iff_let_result_world
        Σ T2 (tlete e1 e2) Q m
        Hlet Hdom Hclosed Htotal_let HQfv)
      Hcont) as [L [HLdom Hwhole]].
    apply (proj2
      (FExprContIn_iff_let_result_world
        (<[x := T1]> Σ) T2 (e2 ^^ x) Q m1
        He2 Hdom_m1 Hclosed_m1 Htotal2 HQfv_insert)).
    exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e2).
    split; [rewrite dom_insert_L; set_solver |].
    intros ν Hν Hfreshν_body Hresultν_body.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[[HνL HνΣ] Hνx] Hνe2].
    assert (Hfreshν_tlet : ν ∉ world_dom (m : World)).
    { rewrite Hdom. exact HνΣ. }
    assert (Hresultν_tlet :
      ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm (tlete e1 e2)))
          (tlete e1 e2) →* tret vx).
    {
      eapply expr_total_on_to_fv_result; eauto.
    }
    pose proof (Hwhole ν HνL Hfreshν_tlet Hresultν_tlet)
      as Hwholeν.
    assert (Hrestrict :
      res_restrict
        (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
        (dom Σ ∪ {[ν]}) ⊨ formula_open 0 ν Q).
    {
      replace (dom Σ ∪ {[ν]}) with (world_dom (m : World) ∪ {[ν]})
        by (rewrite Hdom; reflexivity).
      rewrite (Hdecompose_side ν Hfreshν_body Hresultν_body
        Hfreshν_tlet Hresultν_tlet ltac:(
          rewrite !not_elem_of_union; repeat split; eauto 6)).
      exact Hwholeν.
    }
    exact (proj2 (res_models_minimal_on
      (dom Σ ∪ {[ν]})
      (let_result_world_on (e2 ^^ x) ν m1 Hfreshν_body Hresultν_body)
      (formula_open 0 ν Q) (HQopen_fv ν)) Hrestrict).
Qed.


Lemma let_result_world_on_closed_insert_from_basic
    (Δ : gmap atom ty) T e x (m : WfWorld) Hfresh Hresult :
  Δ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  x ∉ dom Δ →
  world_closed_on (dom (<[x := T]> Δ))
    (let_result_world_on e x m Hfresh Hresult).
Proof.
  intros Htyped Hdom Hclosed Hx.
  rewrite dom_insert_L.
  replace ({[x]} ∪ dom Δ) with (dom Δ ∪ {[x]}) by set_solver.
  eapply let_result_world_on_store_closed_on_insert.
  - eauto.
  - eauto.
  - intros σ vx Hσ Hsteps.
    pose proof (basic_typing_contains_fv_tm Δ e T Htyped) as Hfv.
    pose proof (typing_tm_lc Δ e T Htyped) as Hlc.
    assert (Hclosed_fv : world_closed_on (fv_tm e) m).
    { eapply world_closed_on_mono; [exact Hfv | exact Hclosed]. }
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

Lemma denot_ty_tlet_reduction_add_obligations
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τ2 :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) τ2 →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  (let_result_world_on e1 x m Hfresh Hresult
      ⊨ denot_ty_body (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_body Δ τ2 (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
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
    eapply let_result_world_on_closed_insert_from_basic; eauto.
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
    - tlet_regular.
    - exact Htotal.
  }
  assert (Htarget_closed : world_closed_on (dom Δ) m).
  { tlet_regular. }
  split; intros Hmodel.
  - eapply denot_ty_intro; eauto.
    apply Hformula_iff.
    eauto using denot_ty_body_of_formula.
    rewrite Hdom. set_solver.
  - eapply denot_ty_intro; eauto.
    apply Hformula_iff.
    eauto using denot_ty_body_of_formula.
    rewrite let_result_world_on_dom, Hdom, dom_insert_L. set_solver.
Qed.

Lemma FExprContIn_result_basic_env_irrel
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
    rewrite !FResultBasicWorld_fv_atom_env.
    reflexivity.
  - intros ν Hν.
    cbn [formula_open formula_fv].
    rewrite !FResultBasicWorld_insert_fresh_open_fv by exact Hx.
    reflexivity.
  - intros ν Hν.
    apply formula_store_equiv_and.
    + apply FResultBasicWorld_insert_fresh_open_fv.
      exact Hx.
    + reflexivity.
    + apply FResultBasicWorld_insert_fresh_open_equiv.
      exact Hx.
    + apply formula_store_equiv_refl.
Qed.

Lemma denot_ty_tlet_reduction_over_case
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    b φ :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTOver b φ) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTOver b φ) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_on (<[x:=T1]> Δ) (CTOver b φ) (e2 ^^ x)
  <->
    m ⊨ denot_ty_on Δ (CTOver b φ) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet.
  eapply denot_ty_tlet_reduction_add_obligations; eauto.
  cbn [denot_ty_body denot_ty_body_lvar].
  rewrite !FExprContIn_atom_env.
  pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hfvτ.
  simpl in Hfvτ.
  destruct φ as [Dφ Pφ]; simpl in *.
  etransitivity.
  - eapply FExprContIn_result_basic_env_irrel.
    set_solver.
  - change (let_result_world_on e1 x m Hfresh Hresult
      ⊨ FExprContIn (<[x:=T1]> Δ) (e2 ^^ x)
          (FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
            (FFibVars (Dφ) (FOver (FTypeQualifier (qual Dφ Pφ))))) <->
      m ⊨ FExprContIn Δ (tlete e1 e2)
          (FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
            (FFibVars (Dφ) (FOver (FTypeQualifier (qual Dφ Pφ)))))).
    eapply (FExprCont_tlet_reduction
      Δ T1 (TBase b) m e1 e2 x
      (FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b Dφ)
        (FFibVars Dφ (FOver (FTypeQualifier (qual Dφ Pφ)))))
      Hfresh Hresult).
    + exact He1.
    + exact Hlet.
    + set_solver.
    + exact Hdom.
    + exact Hclosed.
    + exact Htotal.
    + cbn [formula_fv].
    eapply union_least.
      * pose proof (FResultBasicWorld_fv_atom_env_subset Δ b Dφ Hfvτ).
        set_solver.
      * set_solver.
Qed.

Lemma denot_ty_tlet_reduction_under_case
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    b φ :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTUnder b φ) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTUnder b φ) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_on (<[x:=T1]> Δ) (CTUnder b φ) (e2 ^^ x)
  <->
    m ⊨ denot_ty_on Δ (CTUnder b φ) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet.
  eapply denot_ty_tlet_reduction_add_obligations; eauto.
  cbn [denot_ty_body denot_ty_body_lvar].
  rewrite !FExprContIn_atom_env.
  pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hfvτ.
  simpl in Hfvτ.
  destruct φ as [Dφ Pφ]; simpl in *.
  etransitivity.
  - eapply FExprContIn_result_basic_env_irrel.
    set_solver.
  - change (let_result_world_on e1 x m Hfresh Hresult
      ⊨ FExprContIn (<[x:=T1]> Δ) (e2 ^^ x)
          (FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
            (FFibVars (Dφ) (FUnder (FTypeQualifier (qual Dφ Pφ))))) <->
      m ⊨ FExprContIn Δ (tlete e1 e2)
          (FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b (Dφ))
            (FFibVars (Dφ) (FUnder (FTypeQualifier (qual Dφ Pφ)))))).
    eapply (FExprCont_tlet_reduction
      Δ T1 (TBase b) m e1 e2 x
      (FAnd (FResultBasicWorld (atom_env_to_lty_env Δ) b Dφ)
        (FFibVars Dφ (FUnder (FTypeQualifier (qual Dφ Pφ)))))
      Hfresh Hresult).
    + exact He1.
    + exact Hlet.
    + set_solver.
    + exact Hdom.
    + exact Hclosed.
    + exact Htotal.
    + cbn [formula_fv].
    eapply union_least.
      * pose proof (FResultBasicWorld_fv_atom_env_subset Δ b Dφ Hfvτ).
        set_solver.
      * set_solver.
Qed.

Lemma denot_ty_tlet_reduction_inter_case
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τa τb :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTInter τa τb) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTInter τa τb) →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_on (<[x:=T1]> Δ) τa (e2 ^^ x) <->
   m ⊨ denot_ty_on Δ τa (tlete e1 e2)) →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_on (<[x:=T1]> Δ) τb (e2 ^^ x) <->
   m ⊨ denot_ty_on Δ τb (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_on (<[x:=T1]> Δ) (CTInter τa τb) (e2 ^^ x)
  <->
  m ⊨ denot_ty_on Δ (CTInter τa τb) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet HIHa HIHb.
  eapply denot_ty_tlet_reduction_add_obligations; eauto.
  cbn [denot_ty_body denot_ty_body_lvar fv_cty erase_ty].
  split; intros Hmodel.
  - apply res_models_and_intro_from_models.
    + apply (proj1 HIHa). eauto using res_models_and_elim_l.
    + apply (proj1 HIHb). eauto using res_models_and_elim_r.
  - apply res_models_and_intro_from_models.
    + apply (proj2 HIHa). eauto using res_models_and_elim_l.
    + apply (proj2 HIHb). eauto using res_models_and_elim_r.
Qed.

Lemma denot_ty_tlet_reduction_union_case
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τa τb :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) (CTUnion τa τb) →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty (CTUnion τa τb) →
  basic_choice_ty (dom Δ) τa →
  basic_choice_ty (dom Δ) τb →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_on (<[x:=T1]> Δ) τa (e2 ^^ x) <->
   m ⊨ denot_ty_on Δ τa (tlete e1 e2)) →
  (let_result_world_on e1 x m Hfresh Hresult ⊨
      denot_ty_on (<[x:=T1]> Δ) τb (e2 ^^ x) <->
   m ⊨ denot_ty_on Δ τb (tlete e1 e2)) →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_on (<[x:=T1]> Δ) (CTUnion τa τb) (e2 ^^ x)
  <->
  m ⊨ denot_ty_on Δ (CTUnion τa τb) (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet
    HbasicA HbasicB HIHa HIHb.
  assert (HfvA : fv_cty τa ⊆ dom Δ)
    by (eapply basic_choice_ty_fv_subset; exact HbasicA).
  assert (HfvB : fv_cty τb ⊆ dom Δ)
    by (eapply basic_choice_ty_fv_subset; exact HbasicB).
  assert (HfvA_insert : fv_cty τa ⊆ dom (<[x:=T1]> Δ)).
  { rewrite dom_insert_L. set_solver. }
  assert (HfvB_insert : fv_cty τb ⊆ dom (<[x:=T1]> Δ)).
  { rewrite dom_insert_L. set_solver. }
  eapply denot_ty_tlet_reduction_add_obligations; eauto.
  cbn [denot_ty_body denot_ty_body_lvar fv_cty erase_ty].
  split; intros Hmodel.
  - eapply res_models_or_transport_between_worlds; [| | apply (proj1 HIHa) | apply (proj1 HIHb) | exact Hmodel].
    + rewrite Hdom.
      eapply denot_ty_on_fv_subset_env.
      eapply basic_choice_ty_fv_subset. exact HbasicA.
    + rewrite Hdom.
      eapply denot_ty_on_fv_subset_env.
      eapply basic_choice_ty_fv_subset. exact HbasicB.
  - eapply res_models_or_transport_between_worlds; [| | apply (proj2 HIHa) | apply (proj2 HIHb) | exact Hmodel].
    + rewrite let_result_world_on_dom, Hdom.
      pose proof (denot_ty_on_fv_subset_env
        (<[x:=T1]> Δ) τa (e2 ^^ x) HfvA_insert) as Hfv.
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz. set_solver.
    + rewrite let_result_world_on_dom, Hdom.
      pose proof (denot_ty_on_fv_subset_env
        (<[x:=T1]> Δ) τb (e2 ^^ x) HfvB_insert) as Hfv.
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz. set_solver.
Qed.

Lemma denot_ty_tlet_reduction_on
    (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
    (m : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx) :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  expr_total_on (dom Δ) (tlete e1 e2) m →
  x ∉ dom Δ ∪ fv_tm e2 →
  ∀ τ2,
    basic_choice_ty (dom Δ) τ2 →
    Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
    let_result_world_on e1 x m Hfresh Hresult
      ⊨ denot_ty_on (<[x:=T1]> Δ) τ2 (e2 ^^ x)
    <->
    m ⊨ denot_ty_on Δ τ2 (tlete e1 e2).
Proof.
  intros He1 Hdom Hclosed Htotal Hx_base τ2.
  induction τ2 as [b φ|b φ|τa IHa τb IHb|τa IHa τb IHb
    |τa IHa τb IHb|τx IHx τ IH|τx IHx τ IH];
    intros Hbasicτ Hlet.
  - eapply denot_ty_tlet_reduction_over_case; eauto.
  - eapply denot_ty_tlet_reduction_under_case; eauto.
  - inversion Hbasicτ as [| |D τ1' τ2' HbasicA HbasicB Herase| | | |]; subst.
    assert (HfullA :
      let_result_world_on e1 x m Hfresh Hresult ⊨
        denot_ty_on (<[x:=T1]> Δ) τa (e2 ^^ x) <->
      m ⊨ denot_ty_on Δ τa (tlete e1 e2)).
    { eapply IHa; eauto. }
    assert (HletB : Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τb).
    { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
    assert (HfullB :
      let_result_world_on e1 x m Hfresh Hresult ⊨
        denot_ty_on (<[x:=T1]> Δ) τb (e2 ^^ x) <->
      m ⊨ denot_ty_on Δ τb (tlete e1 e2)).
    { eapply IHb; eauto. }
    eapply denot_ty_tlet_reduction_inter_case; eauto.
  - inversion Hbasicτ as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
    assert (HfullA :
      let_result_world_on e1 x m Hfresh Hresult ⊨
        denot_ty_on (<[x:=T1]> Δ) τa (e2 ^^ x) <->
      m ⊨ denot_ty_on Δ τa (tlete e1 e2)).
    { eapply IHa; eauto. }
    assert (HletB : Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τb).
    { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
    assert (HfullB :
      let_result_world_on e1 x m Hfresh Hresult ⊨
        denot_ty_on (<[x:=T1]> Δ) τb (e2 ^^ x) <->
      m ⊨ denot_ty_on Δ τb (tlete e1 e2)).
    { eapply IHb; eauto. }
    eapply denot_ty_tlet_reduction_union_case; eauto.
  - (* CTSum: still needs the sum/resource distribution argument. *)
    admit.
  - (* CTArrow: postponed with the function-type reduction proof. *)
    admit.
  - (* CTWand: same shape as Arrow, with separating implication. *)
    admit.
Admitted.

Lemma denot_ty_tlet_reduction_ctx_on (τ2 : choice_ty): forall
    (Σ : gmap atom ty) (Γ : ctx) (τ1: choice_ty) e1 e2
    (m : WfWorld) x
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx),
  denot_ty_regular_in_ctx_under Σ Γ τ2 →
  erase_ctx_under Σ Γ ⊢ₑ e1 ⋮ erase_ty τ1 →
  erase_ctx_under Σ Γ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ2 →
  world_dom (m : World) = dom (erase_ctx_under Σ Γ) →
  world_closed_on (dom (erase_ctx_under Σ Γ)) m →
  expr_total_on (dom (erase_ctx_under Σ Γ)) (tlete e1 e2) m →
  x ∉ dom (erase_ctx_under Σ Γ) ∪ fv_cty τ2 ∪ fv_tm e2 →
  let_result_world_on e1 x m Hfresh Hresult
    ⊨ denot_ty_on (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ1)))
        τ2 (e2 ^^ x)
  <->
  m ⊨ denot_ty_on (erase_ctx_under Σ Γ) τ2 (tlete e1 e2).
Proof.
  intros Σ Γ τ1 e1 e2 m x Hfresh Hresult
    [HbasicΓ Hbasicτ] He1 Hlet Hdom Hclosed Htotal Hx.
  assert (HxΔ : x ∉ dom (erase_ctx_under Σ Γ)) by set_solver.
  rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ1)
    by exact HxΔ.
  eapply (denot_ty_tlet_reduction_on
    (erase_ctx_under Σ Γ) (erase_ty τ1) e1 e2 m x
    Hfresh Hresult); eauto.
  set_solver.
Qed.

Lemma denot_ty_tlet_reduction_in_ctx (τ2 : choice_ty): forall
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
  unfold denot_ty_in_ctx_under.
  eapply denot_ty_tlet_reduction_ctx_on; eauto.
  eapply denot_ctx_in_env_world_closed_on_erased; eauto.
  exact (proj1 Hregular).
Qed.

Lemma denot_ty_tlet_reduction_any_world (τ2 : choice_ty): forall
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
  assert (Hclosed_m : world_closed_on (dom Δ) m).
  { subst Δ. eapply denot_ctx_in_env_world_closed_on_erased; eauto. }
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
  assert (Hclosed0 : world_closed_on (dom Δ) (res_restrict m (dom Δ))).
  { eapply world_closed_on_restrict; [reflexivity | exact Hclosed_m]. }
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
    unfold denot_ty_in_ctx_under.
    rewrite Hbody_env.
    pose proof (denot_ty_on_fv_subset
      (<[x:=erase_ty τ1]> Δ) τ2 (e2 ^^ x)) as Hfv.
    assert (Hτ2 : fv_cty τ2 ⊆ dom (<[x:=erase_ty τ1]> Δ)).
    { eapply basic_choice_ty_fv_subset;
        eapply basic_choice_ty_mono; [| exact Hbasicτ];
        rewrite dom_insert_L; set_solver. }
    intros z Hz.
    pose proof (Hfv z Hz) as Hz'.
    apply elem_of_union in Hz' as [Hz'|Hz'].
    - rewrite dom_insert_L in Hz'. set_solver.
    - pose proof (Hτ2 z Hz') as Hzdom.
      rewrite dom_insert_L in Hzdom. set_solver.
  }
  assert (Htarget_fv :
      formula_fv (denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2)) ⊆ dom Δ).
  {
    subst Δ.
    unfold denot_ty_in_ctx_under.
    pose proof (denot_ty_on_fv_subset
      (erase_ctx_under Σ Γ) τ2 (tlete e1 e2)) as Hfv.
    pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hτ.
    intros z Hz.
    pose proof (Hfv z Hz) as Hz'.
    apply elem_of_union in Hz' as [Hz'|Hz']; [exact Hz'|].
    exact (Hτ z Hz').
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
  pose proof (denot_ty_tlet_reduction_in_ctx
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
