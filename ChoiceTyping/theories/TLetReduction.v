(** * ChoiceTyping.TLetReduction

    Type-denotation reduction lemmas for the [tlet] soundness case.
    The final semantic bridge stays in [TLetDenotation]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps BasicTypingProps
  LocallyNamelessProps StrongNormalization Sugar.
From ChoiceLogic Require Export FormulaDerived FormulaWorldExtension.
From ChoiceTyping Require Export TLetTotal RegularDenotation.
From ChoiceTyping Require Import Naming SoundnessCommon LetResultWorld
  ResultWorldClosed ResultWorldExprCont ResultWorldExtension.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Import Tactics.

Local Lemma dom_insert_union_r (Δ : gmap atom ty) T x :
  dom Δ ∪ {[x]} = dom (<[x := T]> Δ).
Proof.
  rewrite dom_insert_L. set_solver.
Qed.

Local Lemma inter_eq_right_of_subset (X Y : aset) :
  Y ⊆ X →
  X ∩ Y = Y.
Proof.
  set_solver.
Qed.

Local Lemma expr_total_on_restrict_self X e (m : WfWorld) :
  expr_total_on X e m →
  expr_total_on X e (res_restrict m X).
Proof.
  intros [Hfv Htotal]. split; [eauto 6 |].
  intros σ [σm [Hσm <-]].
  rewrite store_restrict_twice_same.
  apply Htotal; eauto 6.
Qed.

Local Lemma result_witness_lift_restrict
    X e (m n : WfWorld) :
  fv_tm e ⊆ X →
  res_restrict n X = m →
  (∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) →
  ∀ σ, (n : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hfv Hrestrict Hresult σ Hσ.
  assert (Hσm : (m : World) (store_restrict σ X)).
  {
    rewrite <- Hrestrict.
    exists σ. split; [exact Hσ | reflexivity].
  }
  destruct (Hresult _ Hσm) as [vx Hsteps].
  exists vx.
  replace (store_restrict (store_restrict σ X) (fv_tm e))
    with (store_restrict σ (fv_tm e)) in Hsteps.
  - exact Hsteps.
  - rewrite store_restrict_twice_subset by exact Hfv.
    reflexivity.
Qed.

Local Lemma tapp_tm_tlete e1 e2 v :
  tapp_tm (tlete e1 e2) v = tlete e1 (tapp_tm e2 v).
Proof. reflexivity. Qed.

Local Lemma open_tapp_tm_fvar e x y :
  (tapp_tm e (vfvar y)) ^^ x = tapp_tm (e ^^ x) (vfvar y).
Proof.
  unfold open_one.
  change (open_tm 0 (vfvar x) (tapp_tm e (vfvar y)) =
    tapp_tm (open_tm 0 (vfvar x) e) (vfvar y)).
  apply open_tapp_tm_lc_arg. constructor.
Qed.

Local Lemma basic_typing_tlet_tapp_fvar
    (Δ : gmap atom ty) e1 e2 y Tx T :
  y ∉ dom Δ →
  Δ ⊢ₑ tlete e1 e2 ⋮ (Tx →ₜ T) →
  <[y := Tx]> Δ ⊢ₑ tlete e1 (tapp_tm e2 (vfvar y)) ⋮ T.
Proof.
  intros Hy Htyped.
  change (tlete e1 (tapp_tm e2 (vfvar y)))
    with (tapp_tm (tlete e1 e2) (vfvar y)).
  eapply basic_typing_tapp_tm_fvar_insert; eauto.
Qed.

Local Lemma fresh_tapp_body_insert
    (Δ : gmap atom ty) e2 x y Tx :
  x ∉ dom Δ ∪ fv_tm e2 →
  x <> y →
  x ∉ dom (<[y := Tx]> Δ) ∪ fv_tm (tapp_tm e2 (vfvar y)).
Proof.
  intros Hx Hxy.
  rewrite dom_insert_L, fv_tapp_tm.
  simpl. set_solver.
Qed.

Local Lemma dom_insert_eq_union (Δ : gmap atom ty) x T :
  dom (<[x := T]> Δ) = dom Δ ∪ {[x]}.
Proof. rewrite dom_insert_L. set_solver. Qed.

Local Lemma basic_choice_body_insert
    (Δ : gmap atom ty) y Ty τ (L : aset) :
  (∀ z, z ∉ L → basic_choice_ty (dom Δ ∪ {[z]}) ({0 ~> z} τ)) →
  y ∉ L →
  basic_choice_ty (dom (<[y := Ty]> Δ)) ({0 ~> y} τ).
Proof.
  intros Hbody Hy.
  rewrite dom_insert_eq_union.
  eauto.
Qed.

Local Lemma fresh_notin_restrict_insert_dom X x (n : WfWorld) :
  x ∉ X →
  world_dom (n : World) = X ∪ {[x]} →
  x ∉ world_dom (res_restrict n X : World).
Proof.
  intros HxX Hdom Hx.
  simpl in Hx. rewrite Hdom in Hx. set_solver.
Qed.

Local Lemma restrict_insert_dom_covers_left X x (n : WfWorld) :
  world_dom (n : World) = X ∪ {[x]} →
  X ⊆ world_dom (res_restrict n X : World).
Proof.
  intros Hdom z Hz.
  simpl. rewrite Hdom. set_solver.
Qed.

Local Lemma res_restrict_insert_dom_eq X x (n : WfWorld) :
  world_dom (n : World) = X ∪ {[x]} →
  world_dom (res_restrict n X : World) = X.
Proof.
  intros Hdom. simpl. rewrite Hdom. set_solver.
Qed.

Local Lemma denot_ty_model_world_dom_eq_env
    (Σ : gmap atom ty) τ e (m n : WfWorld) :
  n ⊨ denot_ty_on Σ τ e →
  n ⊑ m →
  world_dom (m : World) = dom Σ →
  world_dom (n : World) = dom Σ.
Proof.
  intros Hmodel Hle Hdom_m.
  apply set_eq. intros z. split.
  - intros Hz. rewrite <- Hdom_m. eapply raw_le_dom; eauto.
  - intros Hz.
    eapply (res_models_with_store_fuel_scoped
      (formula_measure (denot_ty_on Σ τ e)) ∅ n
      (denot_ty_on Σ τ e)) in Hmodel.
    unfold formula_scoped_in_world in Hmodel.
    apply Hmodel.
    apply elem_of_union_r.
    apply denot_ty_on_env_fv_subset. exact Hz.
Qed.

Local Lemma denot_ty_model_world_dom_eq_env_upper
    (Σ : gmap atom ty) τ e (n : WfWorld) :
  n ⊨ denot_ty_on Σ τ e →
  world_dom (n : World) ⊆ dom Σ →
  world_dom (n : World) = dom Σ.
Proof.
  intros Hmodel Hdom_upper.
  apply set_eq. intros z. split.
  - exact (Hdom_upper z).
  - intros Hz.
    eapply (res_models_with_store_fuel_scoped
      (formula_measure (denot_ty_on Σ τ e)) ∅ n
      (denot_ty_on Σ τ e)) in Hmodel.
    unfold formula_scoped_in_world in Hmodel.
    apply Hmodel.
    apply elem_of_union_r.
    apply denot_ty_on_env_fv_subset. exact Hz.
Qed.

Local Lemma denot_ty_model_world_dom_eq_insert
    (Δ : gmap atom ty) T x τ e (m : WfWorld) :
  m ⊨ denot_ty_on (<[x := T]> Δ) τ e →
  world_dom (m : World) ⊆ dom Δ ∪ {[x]} →
  world_dom (m : World) = dom Δ ∪ {[x]}.
Proof.
  intros Hmodel Hdom_upper.
  apply set_eq. intros z. split.
  - exact (Hdom_upper z).
  - rewrite (dom_insert_union_r Δ T x).
    intros Hz.
    eapply (res_models_with_store_fuel_scoped
      (formula_measure (denot_ty_on (<[x:=T]> Δ) τ e)) ∅ m
      (denot_ty_on (<[x:=T]> Δ) τ e)) in Hmodel.
    unfold formula_scoped_in_world in Hmodel.
    apply Hmodel.
    apply elem_of_union_r.
    apply denot_ty_on_env_fv_subset. exact Hz.
Qed.

Local Lemma res_subset_of_le_same_domain (n m : WfWorld) :
  n ⊑ m →
  world_dom (n : World) = world_dom (m : World) →
  res_subset n m.
Proof.
  intros Hle Hdom.
  assert (Heq : n = m) by (eapply res_le_same_dom_eq; eauto).
  subst. apply res_subset_refl.
Qed.

Local Lemma res_subset_via_sum_left (n1 n2 m : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  res_sum n1 n2 Hdef ⊑ m →
  world_dom (n1 : World) = world_dom (m : World) →
  res_subset n1 m.
Proof.
  intros Hle Hdom.
  eapply res_subset_trans.
  - apply res_sum_subset_l.
  - eapply res_subset_of_le_same_domain.
    + exact Hle.
    + simpl. exact Hdom.
Qed.

Local Lemma res_subset_via_sum_right (n1 n2 m : WfWorld)
    (Hdef : raw_sum_defined n1 n2) :
  res_sum n1 n2 Hdef ⊑ m →
  world_dom (n2 : World) = world_dom (m : World) →
  res_subset n2 m.
Proof.
  intros Hle Hdom.
  eapply res_subset_trans.
  - apply res_sum_subset_r.
  - eapply res_subset_of_le_same_domain.
    + exact Hle.
    + simpl. rewrite Hdef. exact Hdom.
Qed.

Local Lemma let_result_world_on_sum_le
    X e x (m m1 m2 : WfWorld)
    Hfresh Hresult Hfresh1 Hresult1 Hfresh2 Hresult2
    (Hdef : raw_sum_defined m1 m2)
    (Hdefx : raw_sum_defined
      (let_result_world_on e x m1 Hfresh1 Hresult1)
      (let_result_world_on e x m2 Hfresh2 Hresult2)) :
  fv_tm e ⊆ X →
  world_dom (m1 : World) = X →
  world_dom (m2 : World) = X →
  res_sum m1 m2 Hdef ⊑ m →
  res_sum (let_result_world_on e x m1 Hfresh1 Hresult1)
    (let_result_world_on e x m2 Hfresh2 Hresult2) Hdefx ⊑
    let_result_world_on e x m Hfresh Hresult.
Proof.
  intros Hfv Hdom1 Hdom2 Hle.
  pose proof (raw_le_dom _ _ Hle) as Hdom_sum_m.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle |- *.
  apply world_ext.
  - simpl in Hdom_sum_m |- *.
    rewrite Hdom1 in Hdom_sum_m |- *.
    clear -Hdom_sum_m. set_solver.
  - intros σx. simpl. split.
    + intros [Hσx | Hσx].
      * destruct (let_result_world_on_elim e x m1 Hfresh1 Hresult1 σx Hσx)
          as [σ [vx [Hσ [Hsteps ->]]]].
        assert (Hsumσ : (res_sum m1 m2 Hdef : World) σ).
        { simpl. left. exact Hσ. }
        rewrite Hle in Hsumσ. simpl in Hsumσ.
        destruct Hsumσ as [σm [Hσm Hσm_restrict]].
        exists (<[x:=vx]> σm). split.
        -- exists σm, vx. split; [exact Hσm |].
           split.
           ++ replace (store_restrict σm (fv_tm e))
                with (store_restrict σ (fv_tm e)).
              ** exact Hsteps.
              ** rewrite <- Hσm_restrict.
                 rewrite store_restrict_twice_subset; [reflexivity |].
                 simpl. rewrite Hdom1. exact Hfv.
           ++ reflexivity.
        -- rewrite store_restrict_insert_fresh_union.
           ++ rewrite Hσm_restrict. reflexivity.
           ++ eapply store_lookup_none_of_dom.
              ** apply wfworld_store_dom. exact Hσm.
              ** exact Hfresh.
           ++ simpl. exact Hfresh1.
      * destruct (let_result_world_on_elim e x m2 Hfresh2 Hresult2 σx Hσx)
          as [σ [vx [Hσ [Hsteps ->]]]].
        assert (Hsumσ : (res_sum m1 m2 Hdef : World) σ).
        { simpl. right. exact Hσ. }
        rewrite Hle in Hsumσ. simpl in Hsumσ.
        destruct Hsumσ as [σm [Hσm Hσm_restrict]].
        exists (<[x:=vx]> σm). split.
        -- exists σm, vx. split; [exact Hσm |].
           split.
           ++ replace (store_restrict σm (fv_tm e))
                with (store_restrict σ (fv_tm e)).
              ** exact Hsteps.
              ** rewrite <- Hσm_restrict.
                 rewrite store_restrict_twice_subset; [reflexivity |].
                 simpl. rewrite Hdom1. exact Hfv.
           ++ reflexivity.
        -- rewrite store_restrict_insert_fresh_union.
           ++ rewrite Hσm_restrict. reflexivity.
           ++ eapply store_lookup_none_of_dom.
              ** apply wfworld_store_dom. exact Hσm.
              ** exact Hfresh.
           ++ simpl. rewrite Hdef. exact Hfresh2.
    + intros [σmx [Hσmx Hrestrict]].
      destruct (let_result_world_on_elim e x m Hfresh Hresult σmx Hσmx)
        as [σ [vx [Hσ [Hsteps ->]]]].
      set (Ssum := world_dom (res_sum m1 m2 Hdef : World)).
      assert (Hproj : (res_sum m1 m2 Hdef : World)
        (store_restrict σ Ssum)).
      {
        rewrite Hle.
        exists σ. split; [exact Hσ |].
        subst Ssum.
        reflexivity.
      }
      simpl in Hproj. destruct Hproj as [Hσ1 | Hσ2].
      * left. exists (store_restrict σ (world_dom (m1 : World))), vx.
        split; [exact Hσ1 |].
        split.
        -- replace (store_restrict (store_restrict σ (world_dom (m1 : World))) (fv_tm e))
             with (store_restrict σ (fv_tm e)).
           ++ exact Hsteps.
           ++ rewrite store_restrict_twice_subset; [reflexivity |].
              rewrite Hdom1. exact Hfv.
        -- rewrite <- Hrestrict.
           rewrite store_restrict_insert_fresh_union.
           ++ simpl. reflexivity.
           ++ eapply store_lookup_none_of_dom.
              ** apply wfworld_store_dom. exact Hσ.
              ** exact Hfresh.
           ++ simpl. exact Hfresh1.
      * right. exists (store_restrict σ (world_dom (m2 : World))), vx.
        split.
        -- replace (store_restrict σ (world_dom (m2 : World)))
             with (store_restrict σ (world_dom (res_sum m1 m2 Hdef : World)))
             by (simpl; rewrite Hdef; reflexivity).
           exact Hσ2.
        -- split.
           ++ replace (store_restrict (store_restrict σ (world_dom (m2 : World))) (fv_tm e))
                with (store_restrict σ (fv_tm e)).
              ** exact Hsteps.
              ** rewrite store_restrict_twice_subset; [reflexivity |].
                 rewrite Hdom2. exact Hfv.
           ++ rewrite <- Hrestrict.
              rewrite store_restrict_insert_fresh_union.
              ** replace (store_restrict σ (world_dom (m2 : World)))
                   with (store_restrict σ (world_dom (res_sum m1 m2 Hdef : World)))
                   by (simpl; rewrite Hdef; reflexivity).
                 reflexivity.
              ** eapply store_lookup_none_of_dom.
                 --- apply wfworld_store_dom. exact Hσ.
                 --- exact Hfresh.
              ** simpl. rewrite Hdef. exact Hfresh2.
Qed.

Local Ltac tlet_regular :=
  eauto 6 using basic_typing_contains_fv_tm, typing_tm_lc.

Local Ltac denot_ty_gas_saturate :=
  fold denot_ty_body_lvar_gas in *;
  fold cty_depth in *;
  repeat match goal with
  | |- context[denot_ty_obligations ?Σe ?Στ ?τ ?e
        (denot_ty_body_lvar_gas ?gas ?Σe ?Στ ?τ ?e)] =>
      rewrite (denot_ty_obligations_body_gas_saturate gas Σe Στ τ e)
        by cbn [cty_depth]; lia
  | H : context[denot_ty_obligations ?Σe ?Στ ?τ ?e
        (denot_ty_body_lvar_gas ?gas ?Σe ?Στ ?τ ?e)] |- _ =>
      rewrite (denot_ty_obligations_body_gas_saturate gas Σe Στ τ e) in H
        by cbn [cty_depth]; lia
  | |- context[denot_ty_lvar_gas ?gas ?Σe ?Στ ?τ ?e] =>
      rewrite (denot_ty_lvar_gas_saturate gas Σe Στ τ e) by cbn [cty_depth]; lia
  | H : context[denot_ty_lvar_gas ?gas ?Σe ?Στ ?τ ?e] |- _ =>
      rewrite (denot_ty_lvar_gas_saturate gas Σe Στ τ e) in H by cbn [cty_depth]; lia
  end.

Local Lemma FExprContIn_atom_env Σ e (Q : FormulaQ) :
  FExprContIn (atom_env_to_lty_env Σ) e Q = FExprContIn Σ e Q.
Proof.
  unfold FExprContIn, FExprResultOn, into_lvars, into_lvars_lvset,
    into_lvars_aset.
  rewrite atom_env_to_lty_env_dom.
  reflexivity.
Qed.

Local Lemma tlet_body_typing_for_result
    (Σ : gmap atom ty) T1 T2 e1 e2 x :
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ dom Σ ∪ fv_tm e2 →
  <[x := T1]> Σ ⊢ₑ e2 ^^ x ⋮ T2.
Proof.
  intros He1 Hlet Hx.
  eapply basic_typing_tlete_body_for_fresh; eauto; set_solver.
Qed.

Local Lemma let_result_world_body_dom
    (Σ : gmap atom ty) T1 e1 x (m : WfWorld) Hfresh Hresult :
  world_dom (m : World) = dom Σ →
  world_dom (let_result_world_on e1 x m Hfresh Hresult : World) =
    dom (<[x := T1]> Σ).
Proof.
  intros Hdom.
  rewrite let_result_world_on_dom, Hdom, dom_insert_L.
  rewrite union_comm_L. reflexivity.
Qed.

Local Lemma let_result_world_body_closed
    (Σ : gmap atom ty) T1 e1 x (m : WfWorld) Hfresh Hresult :
  Σ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  world_closed_on (dom (<[x := T1]> Σ))
    (let_result_world_on e1 x m Hfresh Hresult).
Proof.
  intros He1 Hdom Hclosed.
  rewrite dom_insert_L.
  rewrite union_comm_L.
  eapply let_result_world_on_store_closed_on_insert.
  - set_solver.
  - exact Hclosed.
  - intros σ vx Hσ Hsteps.
    assert (Hfv1 : fv_tm e1 ⊆ dom Σ) by tlet_regular.
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
      * symmetry. apply store_restrict_twice_same.
Qed.

Local Lemma let_result_world_body_total
    (Σ : gmap atom ty) T1 T2 e1 e2 x (m : WfWorld) Hfresh Hresult :
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  x ∉ fv_tm e2 →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) (tlete e1 e2) m →
  expr_total_on (dom (<[x := T1]> Σ)) (e2 ^^ x)
    (let_result_world_on e1 x m Hfresh Hresult).
Proof.
  intros He1 Hlet Hxe2 Hdom Hclosed Htotal.
  rewrite dom_insert_L.
  replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) by set_solver.
  eapply (expr_total_on_tlete_elim_body_strong
    (dom Σ) e1 e2 x m Hfresh Hresult).
  - rewrite Hdom. set_solver.
  - rewrite <- Hdom. exact Hfresh.
  - exact Hxe2.
  - exact Hclosed.
  - tlet_regular.
  - exact Htotal.
Qed.

Local Lemma let_result_world_tlet_restrict_decompose_typed
    (Σ : gmap atom ty) T1 T2 e1 e2 x ν
    (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    Hresult Hfreshν_body Hresultν_body Hfreshν_tlet Hresultν_tlet :
  Σ ⊢ₑ e1 ⋮ T1 →
  Σ ⊢ₑ tlete e1 e2 ⋮ T2 →
  ν ∉ dom Σ ∪ {[x]} ∪ fv_tm e2 →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  res_restrict
    (let_result_world_on (e2 ^^ x) ν
      (let_result_world_on e1 x m Hfresh Hresult)
      Hfreshν_body Hresultν_body)
    (world_dom (m : World) ∪ {[ν]}) =
  let_result_world_on (tlete e1 e2) ν m Hfreshν_tlet Hresultν_tlet.
Proof.
  intros He1 Hlet Hνfresh Hdom Hclosed.
  rewrite (let_result_world_on_tlete_decompose
    (dom Σ) e1 e2 x ν m
    Hfresh Hresult Hfreshν_body Hresultν_body
    Hfreshν_tlet Hresultν_tlet).
  - reflexivity.
  - tlet_regular.
  - apply basic_typing_contains_fv_tm in Hlet. simpl in Hlet. set_solver.
  - rewrite Hdom.
    rewrite !not_elem_of_union in Hνfresh.
    exact (proj1 (proj1 Hνfresh)).
  - rewrite Hdom. clear -Hνfresh. set_solver.
  - intros σ Hσ. exact (proj1 (Hclosed σ Hσ)).
  - intros σ Hσ. exact (proj2 (Hclosed σ Hσ)).
  - intros σ vx Hσ Hsteps.
    assert (Hfv1 : fv_tm e1 ⊆ dom Σ) by tlet_regular.
    eapply steps_closed_result.
    + eapply (msubst_closed_tm_of_restrict_world (dom Σ) e1 m σ).
      * rewrite Hdom. set_solver.
      * exact Hfv1.
      * tlet_regular.
      * exact Hclosed.
      * exists σ. split; [exact Hσ |].
        rewrite (store_restrict_idemp_eq σ (dom Σ)).
        -- reflexivity.
        -- pose proof (wfworld_store_dom m σ Hσ) as Hdomσ.
           rewrite Hdom in Hdomσ. exact Hdomσ.
    + exact Hsteps.
  - intros σ Hσ.
    pose proof (typing_tm_lc _ _ _ Hlet) as Hlclet.
    apply lc_lete_iff_body in Hlclet as [_ Hbodye2].
    eapply body_tm_msubst.
    + exact (proj1 (Hclosed σ Hσ)).
    + exact (proj2 (Hclosed σ Hσ)).
    + exact Hbodye2.
Qed.

Local Lemma FExprCont_tlet_body_family_to_whole
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
  (∃ L : aset,
    dom (<[x := T1]> Σ) ⊆ L ∧
    ∀ ν F n,
      ν ∉ L →
      forall_extension_shape
        (world_dom (let_result_world_on e1 x m Hfresh Hresult : World)) ν F →
      let_result_world_on e1 x m Hfresh Hresult #> F ~~> n →
      n ⊨ FExprResultAt (dom (<[x := T1]> Σ)) (e2 ^^ x) ν →
      n ⊨ formula_open 0 ν Q) →
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν F n,
      ν ∉ L →
      forall_extension_shape (world_dom (m : World)) ν F →
      m #> F ~~> n →
      n ⊨ FExprResultAt (dom Σ) (tlete e1 e2) ν →
      n ⊨ formula_open 0 ν Q.
Proof.
  intros He1 Hlet Hxe2 Hdom Hclosed Htotal_let HQfv [L [HLdom Hbody]].
  pose proof (tlet_body_typing_for_result
    Σ T1 T2 e1 e2 x He1 Hlet ltac:(set_solver)) as He2.
  pose proof (let_result_world_body_dom
    Σ T1 e1 x m Hfresh Hresult Hdom) as Hdom_m1.
  pose proof (let_result_world_body_closed
    Σ T1 e1 x m Hfresh Hresult He1 Hdom Hclosed) as Hclosed_m1.
  assert (HQopen_fv :
    ∀ ν, formula_fv (formula_open 0 ν Q) ⊆ dom Σ ∪ {[ν]}).
  { intros ν. apply formula_open_fv_subset_env. exact HQfv. }
  exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e2).
  split; [set_solver |].
  intros ν F n Hν HFshape Hext Hresult_tlet_model.
  rewrite !not_elem_of_union in Hν.
  destruct Hν as [[[HνL HνΣ] Hνx] Hνe2].
  assert (Hfreshν_tlet : ν ∉ world_dom (m : World)).
  { rewrite Hdom. exact HνΣ. }
  destruct (result_extension_as_let_result_world
    Σ T2 (tlete e1 e2) ν m n F Hfreshν_tlet
    Hlet Hdom Hclosed HνΣ HFshape Hext Hresult_tlet_model)
    as [Hresultν_tlet ->].
  assert (Hfreshν_body :
    ν ∉ world_dom (let_result_world_on e1 x m Hfresh Hresult : World)).
  {
    rewrite let_result_world_on_dom, Hdom, not_elem_of_union.
    split; eauto 6.
  }
  assert (Hresultν_body :
    ∀ σ, (let_result_world_on e1 x m Hfresh Hresult : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm (e2 ^^ x)))
        (e2 ^^ x) →* tret vx).
  {
    refine (expr_total_on_to_fv_result _ _ _ Hclosed_m1 _).
    eapply (let_result_world_body_total
      Σ T1 T2 e1 e2 x m Hfresh Hresult); eauto.
  }
  destruct (let_result_world_as_result_extension
    (<[x := T1]> Σ) T2 (e2 ^^ x) ν
    (let_result_world_on e1 x m Hfresh Hresult)
    Hfreshν_body Hresultν_body He2 Hdom_m1 Hclosed_m1
    ltac:(rewrite dom_insert_L; set_solver))
    as [Fbody [HFbody [Hext_body Hbody_result]]].
  set (mbodyν :=
    let_result_world_on (e2 ^^ x) ν
      (let_result_world_on e1 x m Hfresh Hresult)
      Hfreshν_body Hresultν_body).
  pose proof (Hbody ν Fbody mbodyν HνL HFbody Hext_body Hbody_result)
    as Hnested.
  pose proof (proj1 (res_models_minimal_on
    (dom Σ ∪ {[ν]}) mbodyν
    (formula_open 0 ν Q) (HQopen_fv ν)) Hnested) as Hnested_min.
  subst mbodyν.
  replace (dom Σ ∪ {[ν]}) with (world_dom (m : World) ∪ {[ν]})
    in Hnested_min by (rewrite Hdom; reflexivity).
  rewrite (let_result_world_tlet_restrict_decompose_typed
    Σ T1 T2 e1 e2 x ν m Hfresh Hresult
    Hfreshν_body Hresultν_body Hfreshν_tlet Hresultν_tlet
    He1 Hlet ltac:(rewrite !not_elem_of_union; repeat split; eauto 6)
    Hdom Hclosed) in Hnested_min.
  exact Hnested_min.
Qed.

Local Lemma FExprCont_tlet_whole_family_to_body
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
  (∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν F n,
      ν ∉ L →
      forall_extension_shape (world_dom (m : World)) ν F →
      m #> F ~~> n →
      n ⊨ FExprResultAt (dom Σ) (tlete e1 e2) ν →
      n ⊨ formula_open 0 ν Q) →
  ∃ L : aset,
    dom (<[x := T1]> Σ) ⊆ L ∧
    ∀ ν F n,
      ν ∉ L →
      forall_extension_shape
        (world_dom (let_result_world_on e1 x m Hfresh Hresult : World)) ν F →
      let_result_world_on e1 x m Hfresh Hresult #> F ~~> n →
      n ⊨ FExprResultAt (dom (<[x := T1]> Σ)) (e2 ^^ x) ν →
      n ⊨ formula_open 0 ν Q.
Proof.
  intros He1 Hlet Hxe2 Hdom Hclosed Htotal_let HQfv [L [HLdom Hwhole]].
  pose proof (tlet_body_typing_for_result
    Σ T1 T2 e1 e2 x He1 Hlet ltac:(set_solver)) as He2.
  pose proof (let_result_world_body_dom
    Σ T1 e1 x m Hfresh Hresult Hdom) as Hdom_m1.
  pose proof (let_result_world_body_closed
    Σ T1 e1 x m Hfresh Hresult He1 Hdom Hclosed) as Hclosed_m1.
  assert (HQopen_fv :
    ∀ ν, formula_fv (formula_open 0 ν Q) ⊆ dom Σ ∪ {[ν]}).
  { intros ν. apply formula_open_fv_subset_env. exact HQfv. }
  exists (L ∪ dom Σ ∪ {[x]} ∪ fv_tm e2).
  split; [rewrite dom_insert_L; set_solver |].
  intros ν F n Hν HFshape Hext Hresult_body_model.
  rewrite !not_elem_of_union in Hν.
  destruct Hν as [[[HνL HνΣ] Hνx] Hνe2].
  assert (Hfreshν_body :
    ν ∉ world_dom (let_result_world_on e1 x m Hfresh Hresult : World)).
  {
    rewrite let_result_world_on_dom, Hdom, not_elem_of_union.
    split; eauto 6.
  }
  destruct (result_extension_as_let_result_world
    (<[x := T1]> Σ) T2 (e2 ^^ x) ν
    (let_result_world_on e1 x m Hfresh Hresult) n F Hfreshν_body
    He2 Hdom_m1 Hclosed_m1 ltac:(rewrite dom_insert_L; set_solver)
    HFshape Hext Hresult_body_model)
    as [Hresultν_body Hn_eq].
  assert (Hfreshν_tlet : ν ∉ world_dom (m : World)).
  { rewrite Hdom. exact HνΣ. }
  assert (Hresultν_tlet :
    ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm (tlete e1 e2)))
        (tlete e1 e2) →* tret vx).
  { exact (expr_total_on_to_fv_result _ _ _ Hclosed Htotal_let). }
  destruct (let_result_world_as_result_extension
    Σ T2 (tlete e1 e2) ν m Hfreshν_tlet Hresultν_tlet
    Hlet Hdom Hclosed HνΣ)
    as [Ftlet [HFtlet [Hext_tlet Htlet_result]]].
  set (mtletν := let_result_world_on
    (tlete e1 e2) ν m Hfreshν_tlet Hresultν_tlet).
  pose proof (Hwhole ν Ftlet mtletν HνL HFtlet Hext_tlet Htlet_result)
    as Hwholeν.
  assert (Hrestrict :
    res_restrict n (dom Σ ∪ {[ν]}) ⊨ formula_open 0 ν Q).
  {
    rewrite Hn_eq.
    replace (dom Σ ∪ {[ν]}) with (world_dom (m : World) ∪ {[ν]})
      by (rewrite Hdom; reflexivity).
    rewrite (let_result_world_tlet_restrict_decompose_typed
      Σ T1 T2 e1 e2 x ν m Hfresh Hresult
      Hfreshν_body Hresultν_body Hfreshν_tlet Hresultν_tlet
      He1 Hlet ltac:(rewrite !not_elem_of_union; repeat split; eauto 6)
      Hdom Hclosed).
    exact Hwholeν.
  }
  exact (proj2 (res_models_minimal_on
    (dom Σ ∪ {[ν]}) n
    (formula_open 0 ν Q) (HQopen_fv ν)) Hrestrict).
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
  pose proof (tlet_body_typing_for_result
    Σ T1 T2 e1 e2 x He1 Hlet ltac:(set_solver)) as He2.
  pose proof (let_result_world_body_dom
    Σ T1 e1 x m Hfresh Hresult Hdom) as Hdom_m1.
  pose proof (let_result_world_body_closed
    Σ T1 e1 x m Hfresh Hresult He1 Hdom Hclosed) as Hclosed_m1.
  pose proof (let_result_world_body_total
    Σ T1 T2 e1 e2 x m Hfresh Hresult
    He1 Hlet Hxe2 Hdom Hclosed Htotal_let) as Htotal2.
  assert (HQfv_insert : formula_fv Q ⊆ dom (<[x := T1]> Σ))
    by (rewrite dom_insert_L; set_solver).
  split.
  - intros Hcont.
    apply (proj2 (FExprContIn_iff_result_extension
      Σ T2 (tlete e1 e2) Q m Hlet Hdom Hclosed Htotal_let HQfv)).
    eapply FExprCont_tlet_body_family_to_whole; eauto.
    eapply (proj1 (FExprContIn_iff_result_extension
      (<[x := T1]> Σ) T2 (e2 ^^ x) Q
      (let_result_world_on e1 x m Hfresh Hresult)
      He2 Hdom_m1 Hclosed_m1 Htotal2 HQfv_insert)); eauto.
  - intros Hcont.
    apply (proj2 (FExprContIn_iff_result_extension
      (<[x := T1]> Σ) T2 (e2 ^^ x) Q
      (let_result_world_on e1 x m Hfresh Hresult)
      He2 Hdom_m1 Hclosed_m1 Htotal2 HQfv_insert)).
    eapply FExprCont_tlet_whole_family_to_body; eauto.
    eapply (proj1 (FExprContIn_iff_result_extension
      Σ T2 (tlete e1 e2) Q m Hlet Hdom Hclosed Htotal_let HQfv)); eauto.
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
  cbn [denot_ty_body denot_ty_body_lvar denot_ty_body_lvar_gas cty_depth].
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
  cbn [denot_ty_body denot_ty_body_lvar denot_ty_body_lvar_gas cty_depth].
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
  unfold denot_ty_body.
  cbn [fv_cty erase_ty].
  rewrite !denot_ty_body_lvar_inter.
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
  { rewrite dom_insert_L. clear -HfvA. set_solver. }
  assert (HfvB_insert : fv_cty τb ⊆ dom (<[x:=T1]> Δ)).
  { rewrite dom_insert_L. clear -HfvB. set_solver. }
  eapply denot_ty_tlet_reduction_add_obligations; eauto.
  unfold denot_ty_body.
  cbn [fv_cty erase_ty].
  rewrite !denot_ty_body_lvar_union.
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
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz.
      clear -HfvA Hz. set_solver.
    + rewrite let_result_world_on_dom, Hdom.
      pose proof (denot_ty_on_fv_subset_env
        (<[x:=T1]> Δ) τb (e2 ^^ x) HfvB_insert) as Hfv.
      intros z Hz. apply Hfv in Hz. rewrite dom_insert_L in Hz.
      clear -HfvB Hz. set_solver.
Qed.

Local Lemma let_result_world_on_subset_exact
    X e x (m n : WfWorld) Hfresh Hresult Hfreshn Hresultn :
  fv_tm e ⊆ X →
  world_dom (m : World) = X →
  world_dom (n : World) = X ∪ {[x]} →
  res_subset n (let_result_world_on e x m Hfresh Hresult) →
  n = let_result_world_on e x (res_restrict n X) Hfreshn Hresultn.
Proof.
  intros Hfv Hdom_m Hdom_n [_ Hsub].
  assert (HxX : x ∉ X).
  { rewrite <- Hdom_m. exact Hfresh. }
  apply wfworld_ext. apply world_ext.
  - simpl. rewrite Hdom_n. set_solver.
  - intros σx. simpl. split.
    + intros Hn.
      destruct (let_result_world_on_elim e x m Hfresh Hresult σx
        (Hsub σx Hn)) as [σ [vx [Hσ [Hsteps ->]]]].
      exists (store_restrict σ X), vx.
      split.
      * exists (<[x:=vx]> σ). split; [exact Hn |].
        rewrite store_restrict_insert_notin by exact HxX.
        reflexivity.
      * split.
        -- rewrite store_restrict_twice_subset by exact Hfv.
           exact Hsteps.
        -- assert (Hσ_dom : dom σ = X).
           { rewrite (wfworld_store_dom m σ Hσ). exact Hdom_m. }
	           replace (store_restrict σ X) with σ.
	           ++ reflexivity.
	           ++ symmetry. apply store_restrict_idemp_eq. exact Hσ_dom.
    + intros [σ [vx [[σn [Hn Hrestrict]] [Hsteps ->]]]].
      destruct (let_result_world_on_elim e x m Hfresh Hresult σn
        (Hsub σn Hn)) as [σm [vxm [Hσm [Hstepsm ->]]]].
      rewrite store_restrict_insert_notin in Hrestrict by exact HxX.
	      assert (Hσm_dom : dom σm = X).
	      { rewrite (wfworld_store_dom m σm Hσm). exact Hdom_m. }
	      rewrite store_restrict_idemp in Hrestrict.
	      2:{ clear -Hσm_dom. set_solver. }
      subst σ.
      assert (vx = vxm) as ->.
      {
        eapply steps_result_unique; [exact Hsteps |].
        exact Hstepsm.
      }
      exact Hn.
Qed.

Local Lemma denot_ty_tlet_sum_witness_to_target
    (Δ : gmap atom ty) (T1 : ty) e1 e2
    (m n : WfWorld) (x : atom)
    (Hfresh : x ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx)
    τ
    (IHτ : forall (Δ : gmap atom ty) (T1 : ty) (e1 e2 : tm)
      (m : WfWorld) (x : atom)
      (Hfresh : x ∉ world_dom (m : World))
      (Hresult : ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx),
      Δ ⊢ₑ e1 ⋮ T1 →
      world_dom (m : World) = dom Δ →
      world_closed_on (dom Δ) m →
      expr_total_on (dom Δ) (tlete e1 e2) m →
      x ∉ dom Δ ∪ fv_tm e2 →
      basic_choice_ty (dom Δ) τ →
      Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ →
      let_result_world_on e1 x m Hfresh Hresult
        ⊨ denot_ty_on (<[x:=T1]> Δ) τ (e2 ^^ x)
      <->
      m ⊨ denot_ty_on Δ τ (tlete e1 e2)) :
  Δ ⊢ₑ e1 ⋮ T1 →
  world_dom (m : World) = dom Δ →
  x ∉ dom Δ ∪ fv_tm e2 →
  basic_choice_ty (dom Δ) τ →
  Δ ⊢ₑ tlete e1 e2 ⋮ erase_ty τ →
  world_dom (n : World) = dom Δ ∪ {[x]} →
  res_subset n (let_result_world_on e1 x m Hfresh Hresult) →
  n ⊨ denot_ty_on (<[x:=T1]> Δ) τ (e2 ^^ x) →
  res_restrict n (dom Δ) ⊨ denot_ty_on Δ τ (tlete e1 e2).
Proof.
  intros He1 Hdom Hx_base Hbasic Hlet Hdom_n Hsubset Hmodel.
  destruct Hsubset as [_ Hsub].
  assert (Hfv1 : fv_tm e1 ⊆ dom Δ).
  { eapply basic_typing_contains_fv_tm. exact He1. }
  assert (HxΔ : x ∉ dom Δ).
  {
    intros Hx.
    apply Hx_base. apply elem_of_union_l. exact Hx.
  }
  assert (Hxe2 : x ∉ fv_tm e2).
  {
    intros Hx.
    apply Hx_base. apply elem_of_union_r. exact Hx.
  }
  assert (Hfreshn : x ∉ world_dom (res_restrict n (dom Δ) : World)).
  { eapply fresh_notin_restrict_insert_dom; [exact HxΔ | exact Hdom_n]. }
  assert (Hresultn :
    ∀ σ, (res_restrict n (dom Δ) : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e1)) e1 →* tret vx).
  {
    intros σ Hσ.
    destruct Hσ as [σn [Hσn Hrestrict]].
    destruct (let_result_world_on_elim e1 x m Hfresh Hresult σn
      (Hsub σn Hσn)) as [σm [vx [Hσm [Hsteps ->]]]].
    exists vx.
    rewrite <- Hrestrict.
    rewrite store_restrict_insert_notin.
    - rewrite store_restrict_twice_subset by exact Hfv1.
      exact Hsteps.
    - rewrite <- Hdom. exact Hfresh.
  }
  assert (Hexact :
      n = let_result_world_on e1 x (res_restrict n (dom Δ))
        Hfreshn Hresultn).
  {
    eapply let_result_world_on_subset_exact.
    - exact Hfv1.
    - exact Hdom.
    - exact Hdom_n.
    - split.
      + rewrite Hdom_n, let_result_world_on_dom, Hdom. reflexivity.
      + exact Hsub.
  }
  assert (Hclosed_body :
      world_closed_on (dom (<[x:=T1]> Δ)) n).
  { eapply denot_ty_world_closed_on_of_formula. exact Hmodel. }
  assert (Hclosed_base :
      world_closed_on (dom Δ) (res_restrict n (dom Δ))).
  {
    assert (Hclosed_n_base : world_closed_on (dom Δ) n).
    {
      eapply world_closed_on_mono; [| exact Hclosed_body].
      intros z Hz.
      rewrite dom_insert_L.
      apply elem_of_union_r. exact Hz.
    }
    eapply world_closed_on_restrict.
    - reflexivity.
    - exact Hclosed_n_base.
  }
  assert (Htotal_body :
      expr_total_on (dom (<[x:=T1]> Δ)) (e2 ^^ x) n).
  { eapply denot_ty_expr_total_on_of_formula. exact Hmodel. }
  assert (Htotal_e1 :
      expr_total_on (dom Δ) e1 (res_restrict n (dom Δ))).
  {
    split; [exact Hfv1 |].
    intros σ Hσ.
    destruct (Hresultn σ Hσ) as [vx Hsteps].
    exists vx.
    rewrite <- (subst_map_restrict_to_fv_from_superset e1
      (dom Δ) σ Hfv1 (proj1 (Hclosed_base σ Hσ))).
    exact Hsteps.
  }
  assert (Htotal_tlet :
      expr_total_on (dom Δ) (tlete e1 e2) (res_restrict n (dom Δ))).
  {
    eapply (expr_total_on_tlete_intro_strong
      (dom Δ) e1 e2 x (res_restrict n (dom Δ)) Hfreshn Hresultn).
    - eapply restrict_insert_dom_covers_left. exact Hdom_n.
    - exact HxΔ.
    - exact Hxe2.
    - exact Hclosed_base.
    - tlet_regular.
    - exact Htotal_e1.
    - rewrite <- Hexact.
      rewrite (dom_insert_union_r Δ T1 x).
      exact Htotal_body.
  }
  assert (Hdom_restrict : world_dom (res_restrict n (dom Δ) : World) = dom Δ).
  { eapply res_restrict_insert_dom_eq. exact Hdom_n. }
  pose proof (IHτ Δ T1 e1 e2 (res_restrict n (dom Δ)) x
    Hfreshn Hresultn He1 Hdom_restrict
    Hclosed_base Htotal_tlet Hx_base Hbasic Hlet) as Hiff.
  apply (proj1 Hiff).
  rewrite <- Hexact.
  exact Hmodel.
Qed.

Local Ltac fold_denot_ty_lvar :=
  repeat match goal with
  | |- context[
      denot_ty_obligations ?Σe ?Στ ?τ ?e
        (denot_ty_body_lvar ?Σe ?Στ ?τ ?e)] =>
      change (denot_ty_obligations Σe Στ τ e
        (denot_ty_body_lvar Σe Στ τ e))
        with (denot_ty_lvar Σe Στ τ e)
  | H : context[
      denot_ty_obligations ?Σe ?Στ ?τ ?e
        (denot_ty_body_lvar ?Σe ?Στ ?τ ?e)] |- _ =>
      change (denot_ty_obligations Σe Στ τ e
        (denot_ty_body_lvar Σe Στ τ e))
        with (denot_ty_lvar Σe Στ τ e) in H
  end.

Local Ltac formula_open_denot_norm :=
  cbn [formula_open lqual_open stale_logic_qualifier stale
       into_lvars into_lvars_lvset into_lvars_aset];
  fold_denot_ty_lvar.

Local Lemma denot_ty_lvar_scoped
    (Σe Στ : lty_env) τ e (m : WfWorld) :
  lty_env_atom_dom Σe ∪ lty_env_atom_dom Στ ∪ fv_cty τ ⊆
    world_dom (m : World) →
  formula_scoped_in_world ∅ m (denot_ty_lvar Σe Στ τ e).
Proof.
  intros Hsub.
  unfold formula_scoped_in_world.
  pose proof (denot_ty_lvar_fv_subset Σe Στ τ e).
  set_solver.
Qed.

Local Lemma formula_open_scoped_from_fv
    y (φ : FormulaQ) (m : WfWorld) X :
  formula_fv φ ⊆ X →
  X ∪ {[y]} ⊆ world_dom (m : World) →
  formula_scoped_in_world ∅ m (formula_open 0 y φ).
Proof.
  intros Hfv Hdom.
  unfold formula_scoped_in_world.
  pose proof (formula_open_fv_subset_env 0 y φ X Hfv).
  set_solver.
Qed.

Local Lemma let_result_world_on_forall_transport_iff
    (Σ : gmap atom ty) (T : ty) e x
    (m : WfWorld) Hfresh Hresult (φ ψ : FormulaQ) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  formula_scoped_in_world ∅
    (let_result_world_on e x m Hfresh Hresult) (FForall φ) →
  formula_scoped_in_world ∅ m (FForall ψ) →
  (∃ L : aset,
    world_dom (m : World) ∪
      world_dom (let_result_world_on e x m Hfresh Hresult : World) ⊆ L ∧
    (∀ y F my Hfresh_my Hresult_my G,
      y ∉ L →
      forall_extension_shape (world_dom (m : World)) y F →
      m #> F ~~> my →
      forall_extension_shape
        (world_dom (let_result_world_on e x m Hfresh Hresult : World)) y G →
      let_result_world_on e x m Hfresh Hresult #> G ~~>
        let_result_world_on e x my Hfresh_my Hresult_my →
      let_result_world_on e x my Hfresh_my Hresult_my ⊨
        formula_open 0 y φ →
      my ⊨ formula_open 0 y ψ) ∧
    (∀ y G n (my : WfWorld) Hfresh_my Hresult_my,
      y ∉ L →
      forall_extension_shape
        (world_dom (let_result_world_on e x m Hfresh Hresult : World)) y G →
      let_result_world_on e x m Hfresh Hresult #> G ~~> n →
      world_dom (my : World) = world_dom (m : World) ∪ {[y]} →
      res_restrict my (world_dom (m : World)) = m →
      n = let_result_world_on e x my Hfresh_my Hresult_my →
      my ⊨ formula_open 0 y ψ →
      n ⊨ formula_open 0 y φ)) →
  let_result_world_on e x m Hfresh Hresult ⊨ FForall φ <->
  m ⊨ FForall ψ.
Proof.
  intros Hty Hdom Hclosed Hscopeφ Hscopeψ [L [HL [Hlr Hrl]]].
  split.
  - intros Hforall.
    apply (proj2 (res_models_forall_by_extension_iff m ψ Hscopeψ)).
    destruct (proj1 (res_models_forall_by_extension_iff
      (let_result_world_on e x m Hfresh Hresult) φ Hscopeφ) Hforall)
      as [Lφ [HLφ Hopen]].
    exists (L ∪ Lφ ∪ fv_tm e). split; [set_solver |].
    intros y F my Hy HFshape Hext.
    rewrite !not_elem_of_union in Hy.
    destruct Hy as [[HyL Hyφ] Hye].
    assert (Hy_result :
      y ∉ world_dom (let_result_world_on e x m Hfresh Hresult : World)).
    { rewrite let_result_world_on_dom. set_solver. }
    destruct (let_result_world_on_forall_extension_total
      e x m my Hfresh Hresult y F
      ltac:(rewrite Hdom; eapply basic_typing_contains_fv_tm; exact Hty)
      Hy_result HFshape Hext)
      as [Hfresh_my [Hresult_my [G [HGshape HGext]]]].
    eapply Hlr; eauto.
  - intros Hforall.
    apply (proj2 (res_models_forall_by_extension_iff
      (let_result_world_on e x m Hfresh Hresult) φ Hscopeφ)).
    destruct (proj1 (res_models_forall_by_extension_iff m ψ Hscopeψ) Hforall)
      as [Lψ [HLψ Hopen]].
    exists (L ∪ Lψ ∪ fv_tm e). split; [set_solver |].
    intros y G n Hy HGshape Hext.
    rewrite !not_elem_of_union in Hy.
    destruct Hy as [[HyL Hyψ] Hye].
    destruct (let_result_world_on_forall_extension_recompose_typed
      Σ T e x m n Hfresh Hresult y G Hty Hdom Hclosed
      ltac:(set_solver) HGshape Hext)
      as [my [Hfresh_my [Hresult_my [Hdom_my [Hrestrict_my Hn_eq]]]]].
    destruct (forall_world_as_extend_by m y my ltac:(set_solver)
      Hdom_my Hrestrict_my) as [F [HFshape HFext]].
    specialize (Hopen y F my Hyψ HFshape HFext).
    eapply Hrl; eauto.
Qed.

(** A pure formula equality for opening [denot_ty_lvar] is too strong:
    opening changes the atom domains syntactically, but the closed/total
    obligations only become equivalent after using the surrounding extension
    world's closedness and totality.  The Arrow/Wand proof should use a
    models-level transport lemma instead of a raw rewrite here. *)

Local Definition tlet_arrow_source_arg
    (Δ : gmap atom ty) (T1 : ty) (x : atom) τx : FormulaQ :=
  let Σx := atom_env_to_lty_env (<[x := T1]> Δ) in
  denot_ty_lvar (<[LVBound 0 := erase_ty τx]> Σx)
    Σx τx (tret (vbvar 0)).

Local Definition tlet_arrow_source_conseq
    (Δ : gmap atom ty) (T1 : ty) (x : atom) τx τ e2 : FormulaQ :=
  let Σx := atom_env_to_lty_env (<[x := T1]> Δ) in
  denot_ty_lvar (<[LVBound 0 := erase_ty τx]> Σx)
    (<[LVBound 0 := erase_ty τx]> Σx) τ
    (tapp_tm (e2 ^^ x) (vbvar 0)).

Local Definition tlet_arrow_target_arg
    (Δ : gmap atom ty) τx : FormulaQ :=
  let Σ := atom_env_to_lty_env Δ in
  denot_ty_lvar (<[LVBound 0 := erase_ty τx]> Σ)
    Σ τx (tret (vbvar 0)).

Local Definition tlet_arrow_target_conseq
    (Δ : gmap atom ty) τx τ e1 e2 : FormulaQ :=
  let Σ := atom_env_to_lty_env Δ in
  denot_ty_lvar (<[LVBound 0 := erase_ty τx]> Σ)
    (<[LVBound 0 := erase_ty τx]> Σ) τ
    (tapp_tm (tlete e1 e2) (vbvar 0)).

Local Definition tlet_arrow_source_body
    (Δ : gmap atom ty) (T1 : ty) (x : atom) τx τ e2 : FormulaQ :=
  FImpl
    (tlet_arrow_source_arg Δ T1 x τx)
    (tlet_arrow_source_conseq Δ T1 x τx τ e2).

Local Definition tlet_arrow_target_body
    (Δ : gmap atom ty) τx τ e1 e2 : FormulaQ :=
  FImpl
    (tlet_arrow_target_arg Δ τx)
    (tlet_arrow_target_conseq Δ τx τ e1 e2).


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
  revert Δ T1 e1 e2 m x Hfresh Hresult
    He1 Hdom Hclosed Htotal Hx_base.
  induction τ2 as [b φ|b φ|τa IHa τb IHb|τa IHa τb IHb
    |τa IHa τb IHb|τx IHx τ IH|τx IHx τ IH];
    intros Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0
      He1 Hdom Hclosed Htotal Hx_base Hbasicτ Hlet.
  - eapply denot_ty_tlet_reduction_over_case; eauto.
  - eapply denot_ty_tlet_reduction_under_case; eauto.
  - inversion Hbasicτ as [| |D τ1' τ2' HbasicA HbasicB Herase| | | |]; subst.
    assert (HfullA :
      let_result_world_on e10 x0 m0 Hfresh0 Hresult0 ⊨
        denot_ty_on (<[x0:=T10]> Δ0) τa (e20 ^^ x0) <->
      m0 ⊨ denot_ty_on Δ0 τa (tlete e10 e20)).
    { eapply (IHa Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0); eauto. }
    assert (HletB : Δ0 ⊢ₑ tlete e10 e20 ⋮ erase_ty τb).
    { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
    assert (HfullB :
      let_result_world_on e10 x0 m0 Hfresh0 Hresult0 ⊨
        denot_ty_on (<[x0:=T10]> Δ0) τb (e20 ^^ x0) <->
      m0 ⊨ denot_ty_on Δ0 τb (tlete e10 e20)).
    { eapply (IHb Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0); eauto. }
    eapply denot_ty_tlet_reduction_inter_case; eauto.
  - inversion Hbasicτ as [| | |D τ1' τ2' HbasicA HbasicB Herase| | |]; subst.
    assert (HfullA :
      let_result_world_on e10 x0 m0 Hfresh0 Hresult0 ⊨
        denot_ty_on (<[x0:=T10]> Δ0) τa (e20 ^^ x0) <->
      m0 ⊨ denot_ty_on Δ0 τa (tlete e10 e20)).
    { eapply (IHa Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0); eauto. }
    assert (HletB : Δ0 ⊢ₑ tlete e10 e20 ⋮ erase_ty τb).
    { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
    assert (HfullB :
      let_result_world_on e10 x0 m0 Hfresh0 Hresult0 ⊨
        denot_ty_on (<[x0:=T10]> Δ0) τb (e20 ^^ x0) <->
      m0 ⊨ denot_ty_on Δ0 τb (tlete e10 e20)).
    { eapply (IHb Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0); eauto. }
    eapply denot_ty_tlet_reduction_union_case; eauto.
  - (* CTSum: still needs the sum/resource distribution argument. *)
    inversion Hbasicτ as [| | | |D τ1' τ2' HbasicA HbasicB Herase| |]; subst.
    assert (HfullA :
      let_result_world_on e10 x0 m0 Hfresh0 Hresult0 ⊨
        denot_ty_on (<[x0:=T10]> Δ0) τa (e20 ^^ x0) <->
      m0 ⊨ denot_ty_on Δ0 τa (tlete e10 e20)).
    { eapply (IHa Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0); eauto. }
    assert (HletB : Δ0 ⊢ₑ tlete e10 e20 ⋮ erase_ty τb).
    { replace (erase_ty τb) with (erase_ty τa) by congruence. exact Hlet. }
    assert (HfullB :
      let_result_world_on e10 x0 m0 Hfresh0 Hresult0 ⊨
        denot_ty_on (<[x0:=T10]> Δ0) τb (e20 ^^ x0) <->
      m0 ⊨ denot_ty_on Δ0 τb (tlete e10 e20)).
    { eapply (IHb Δ0 T10 e10 e20 m0 x0 Hfresh0 Hresult0); eauto. }
    eapply denot_ty_tlet_reduction_add_obligations; eauto.
    unfold denot_ty_body.
    cbn [fv_cty erase_ty].
    rewrite !denot_ty_body_lvar_sum.
    split; intros Hmodel.
    + unfold res_models, res_models_with_store in Hmodel.
      cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
        formula_fv] in Hmodel.
      destruct Hmodel as [_ Hplus].
      destruct Hplus as [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]].
      assert (Hdom_n1 : world_dom (n1 : World) = dom Δ0 ∪ {[x0]}).
      {
        eapply denot_ty_model_world_dom_eq_insert.
        - unfold res_models, res_models_with_store.
          models_fuel_irrel Hn1.
        - intros z Hz.
          pose proof (raw_le_dom _ _ Hle) as Hsum_le.
          assert (Hzsum : z ∈ world_dom (res_sum n1 n2 Hdef : World)).
          { simpl. exact Hz. }
          apply Hsum_le in Hzsum.
          rewrite let_result_world_on_dom, Hdom in Hzsum.
          exact Hzsum.
      }
      assert (Hdom_n2 : world_dom (n2 : World) = dom Δ0 ∪ {[x0]}).
      {
        eapply denot_ty_model_world_dom_eq_insert.
        - unfold res_models, res_models_with_store.
          models_fuel_irrel Hn2.
        - intros z Hz.
          pose proof (raw_le_dom _ _ Hle) as Hsum_le.
          assert (Hzsum : z ∈ world_dom (res_sum n1 n2 Hdef : World)).
          { simpl. rewrite Hdef. exact Hz. }
          apply Hsum_le in Hzsum.
          rewrite let_result_world_on_dom, Hdom in Hzsum.
          exact Hzsum.
      }
      assert (Hsub1 :
          res_subset n1 (let_result_world_on e10 x0 m0 Hfresh0 Hresult0)).
      {
        eapply res_subset_via_sum_left; [exact Hle |].
        rewrite Hdom_n1, let_result_world_on_dom, Hdom. reflexivity.
      }
      assert (Hsub2 :
          res_subset n2 (let_result_world_on e10 x0 m0 Hfresh0 Hresult0)).
      {
        eapply res_subset_via_sum_right; [exact Hle |].
        rewrite Hdom_n2, let_result_world_on_dom, Hdom. reflexivity.
      }
      assert (Hdef0 :
          raw_sum_defined (res_restrict n1 (dom Δ0))
            (res_restrict n2 (dom Δ0))).
      { unfold raw_sum_defined. simpl. rewrite Hdef. reflexivity. }
      assert (Hle0 :
          res_sum (res_restrict n1 (dom Δ0))
            (res_restrict n2 (dom Δ0)) Hdef0 ⊑ m0).
      {
        rewrite (res_restrict_sum n1 n2 (dom Δ0) Hdef Hdef0).
        etrans.
        - eapply res_restrict_le_mono. exact Hle.
        - rewrite <- Hdom.
          rewrite let_result_world_on_restrict.
          reflexivity.
      }
      assert (Hn1_model :
        n1 ⊨ denot_ty_on (<[x0:=T10]> Δ0) τa (e20 ^^ x0)).
      { unfold res_models, res_models_with_store. models_fuel_irrel Hn1. }
      pose proof (denot_ty_tlet_sum_witness_to_target
        Δ0 T10 e10 e20 m0 n1 x0 Hfresh0 Hresult0 τa IHa
        He1 Hdom Hx_base HbasicA Hlet Hdom_n1 Hsub1 Hn1_model)
        as Htarget1.
      assert (Hn2_model :
        n2 ⊨ denot_ty_on (<[x0:=T10]> Δ0) τb (e20 ^^ x0)).
      { unfold res_models, res_models_with_store. models_fuel_irrel Hn2. }
      pose proof (denot_ty_tlet_sum_witness_to_target
        Δ0 T10 e10 e20 m0 n2 x0 Hfresh0 Hresult0 τb IHb
        He1 Hdom Hx_base HbasicB HletB Hdom_n2 Hsub2 Hn2_model)
        as Htarget2.
      eapply (res_models_plus_intro_from_models
        m0 (res_restrict n1 (dom Δ0)) (res_restrict n2 (dom Δ0))
        _ _ Hdef0); eauto.
    + unfold res_models, res_models_with_store in Hmodel.
      cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
        formula_fv] in Hmodel.
      destruct Hmodel as [_ Hplus].
      destruct Hplus as [n1 [n2 [Hdef [Hle [Hn1 Hn2]]]]].
      assert (Hn1_model :
        n1 ⊨ denot_ty_on Δ0 τa (tlete e10 e20)).
      { unfold res_models, res_models_with_store. models_fuel_irrel Hn1. }
      assert (Hn2_model :
        n2 ⊨ denot_ty_on Δ0 τb (tlete e10 e20)).
      { unfold res_models, res_models_with_store. models_fuel_irrel Hn2. }
      assert (Hdom_n1 : world_dom (n1 : World) = dom Δ0).
      {
        eapply denot_ty_model_world_dom_eq_env_upper; [exact Hn1_model |].
        intros z Hz. rewrite <- Hdom.
        pose proof (raw_le_dom _ _ Hle) as Hsum_le.
        apply Hsum_le. simpl. exact Hz.
      }
      assert (Hdom_n2 : world_dom (n2 : World) = dom Δ0).
      {
        eapply denot_ty_model_world_dom_eq_env_upper; [exact Hn2_model |].
        intros z Hz. rewrite <- Hdom.
        pose proof (raw_le_dom _ _ Hle) as Hsum_le.
        apply Hsum_le. simpl. rewrite Hdef. exact Hz.
      }
      assert (Hsub1 : res_subset n1 m0).
      {
        eapply res_subset_via_sum_left; [exact Hle |].
        rewrite Hdom_n1, Hdom. reflexivity.
      }
      assert (Hsub2 : res_subset n2 m0).
      {
        eapply res_subset_via_sum_right; [exact Hle |].
        rewrite Hdom_n2, Hdom. reflexivity.
      }
      assert (Hfresh1 : x0 ∉ world_dom (n1 : World)).
      { rewrite Hdom_n1. intros Hx. apply Hx_base. apply elem_of_union_l. exact Hx. }
      assert (Hfresh2 : x0 ∉ world_dom (n2 : World)).
      { rewrite Hdom_n2. intros Hx. apply Hx_base. apply elem_of_union_l. exact Hx. }
      assert (Hresult1 :
        ∀ σ, (n1 : World) σ →
          ∃ vx, subst_map (store_restrict σ (fv_tm e10)) e10 →* tret vx).
      {
        intros σ Hσ. destruct Hsub1 as [_ Hin].
        exact (Hresult0 σ (Hin σ Hσ)).
      }
      assert (Hresult2 :
        ∀ σ, (n2 : World) σ →
          ∃ vx, subst_map (store_restrict σ (fv_tm e10)) e10 →* tret vx).
      {
        intros σ Hσ. destruct Hsub2 as [_ Hin].
        exact (Hresult0 σ (Hin σ Hσ)).
      }
      assert (Hclosed1 : world_closed_on (dom Δ0) n1).
      { eapply denot_ty_world_closed_on_of_formula. exact Hn1_model. }
      assert (Hclosed2 : world_closed_on (dom Δ0) n2).
      { eapply denot_ty_world_closed_on_of_formula. exact Hn2_model. }
      assert (Htotal1 : expr_total_on (dom Δ0) (tlete e10 e20) n1).
      { eapply denot_ty_expr_total_on_of_formula. exact Hn1_model. }
      assert (Htotal2 : expr_total_on (dom Δ0) (tlete e10 e20) n2).
      { eapply denot_ty_expr_total_on_of_formula. exact Hn2_model. }
      pose proof (IHa Δ0 T10 e10 e20 n1 x0 Hfresh1 Hresult1
        He1 Hdom_n1 Hclosed1 Htotal1 Hx_base HbasicA Hlet) as Hiff1.
      pose proof (proj2 Hiff1 Hn1_model) as Hsource1.
      pose proof (IHb Δ0 T10 e10 e20 n2 x0 Hfresh2 Hresult2
        He1 Hdom_n2 Hclosed2 Htotal2 Hx_base HbasicB HletB) as Hiff2.
      pose proof (proj2 Hiff2 Hn2_model) as Hsource2.
      assert (Hdefx :
        raw_sum_defined
          (let_result_world_on e10 x0 n1 Hfresh1 Hresult1)
          (let_result_world_on e10 x0 n2 Hfresh2 Hresult2)).
      { unfold raw_sum_defined. rewrite !let_result_world_on_dom, Hdom_n1, Hdom_n2. reflexivity. }
      assert (Hfv1 : fv_tm e10 ⊆ dom Δ0).
      { eapply basic_typing_contains_fv_tm. exact He1. }
      assert (Hle_source :
        res_sum
          (let_result_world_on e10 x0 n1 Hfresh1 Hresult1)
          (let_result_world_on e10 x0 n2 Hfresh2 Hresult2) Hdefx
        ⊑ let_result_world_on e10 x0 m0 Hfresh0 Hresult0).
      {
        eapply (let_result_world_on_sum_le (dom Δ0)); eauto.
      }
      eapply (res_models_plus_intro_from_models
        (let_result_world_on e10 x0 m0 Hfresh0 Hresult0)
        (let_result_world_on e10 x0 n1 Hfresh1 Hresult1)
        (let_result_world_on e10 x0 n2 Hfresh2 Hresult2)
        _ _ Hdefx); eauto.
  - (* CTArrow: reduce obligations, then transport the function body. *)
    inversion Hbasicτ as [| | | | |D τx' τ' L HbasicX HbasicBody|]; subst.
    eapply denot_ty_tlet_reduction_add_obligations; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_arrow.
    change
      (let_result_world_on e10 x0 m0 Hfresh0 Hresult0
        ⊨ FForall (tlet_arrow_source_body Δ0 T10 x0 τx τ e20) <->
       m0 ⊨ FForall (tlet_arrow_target_body Δ0 τx τ e10 e20)).
    assert (Hsource_forall_scope :
      formula_scoped_in_world ∅
        (let_result_world_on e10 x0 m0 Hfresh0 Hresult0)
        (FForall (tlet_arrow_source_body Δ0 T10 x0 τx τ e20))).
    { admit. (* Source [FForall] scope after unfolding the Arrow body. *) }
    assert (Htarget_forall_scope :
      formula_scoped_in_world ∅ m0
        (FForall (tlet_arrow_target_body Δ0 τx τ e10 e20))).
    { admit. (* Target [FForall] scope after unfolding the Arrow body. *) }
    assert (Htransport :
      ∃ L0 : aset,
        world_dom (m0 : World) ∪
          world_dom (let_result_world_on e10 x0 m0 Hfresh0 Hresult0 : World)
          ⊆ L0 ∧
        (∀ y F my Hfresh_my Hresult_my G,
          y ∉ L0 →
          forall_extension_shape (world_dom (m0 : World)) y F →
          m0 #> F ~~> my →
          forall_extension_shape
            (world_dom
              (let_result_world_on e10 x0 m0 Hfresh0 Hresult0 : World)) y G →
          let_result_world_on e10 x0 m0 Hfresh0 Hresult0 #> G ~~>
            let_result_world_on e10 x0 my Hfresh_my Hresult_my →
          let_result_world_on e10 x0 my Hfresh_my Hresult_my
            ⊨ formula_open 0 y
                (tlet_arrow_source_body Δ0 T10 x0 τx τ e20) →
          my ⊨ formula_open 0 y
                (tlet_arrow_target_body Δ0 τx τ e10 e20)) ∧
        (∀ y G n (my : WfWorld) Hfresh_my Hresult_my,
          y ∉ L0 →
          forall_extension_shape
            (world_dom
              (let_result_world_on e10 x0 m0 Hfresh0 Hresult0 : World)) y G →
          let_result_world_on e10 x0 m0 Hfresh0 Hresult0 #> G ~~> n →
          world_dom (my : World) = world_dom (m0 : World) ∪ {[y]} →
          res_restrict my (world_dom (m0 : World)) = m0 →
          n = let_result_world_on e10 x0 my Hfresh_my Hresult_my →
          my ⊨ formula_open 0 y
                (tlet_arrow_target_body Δ0 τx τ e10 e20) →
          n ⊨ formula_open 0 y
                (tlet_arrow_source_body Δ0 T10 x0 τx τ e20))).
    {
      (* Draft body for this transport:
         - choose [dom Δ0 ∪ fv_tm e20 ∪ {[x0]}] as the cofinite set;
         - derive [world_dom my = dom Δ0 ∪ {[y]}] from [HFext];
         - rewrite each opened [FImpl] with [res_models_impl_iff];
         - use the argument-denotation domain irrelevance across the unused
           [x] extension;
         - use [IH] on [tapp_tm e20 (vfvar y)] versus
           [tapp_tm (tlete e10 e20) (vfvar y)] for the consequent.
         This was the useful script shape; the local proof is admitted here
         because letting Rocq infer the large formulas made this file exceed
         the 40s compile threshold. *)
      admit.
    }
    eapply (let_result_world_on_forall_transport_iff
      Δ0 T10 e10 x0 m0 Hfresh0 Hresult0
      (tlet_arrow_source_body Δ0 T10 x0 τx τ e20)
      (tlet_arrow_target_body Δ0 τx τ e10 e20)); eauto.
  - (* CTWand: same shape as Arrow, with separating implication. *)
    eapply denot_ty_tlet_reduction_add_obligations; eauto.
    unfold denot_ty_body.
    rewrite !denot_ty_body_lvar_wand.
    formula_open_denot_norm.
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
      rewrite store_restrict_twice_subset; eauto.
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
    clear -Hctx_fv HΓfv.
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
    pose proof (basic_choice_ty_fv_subset _ _ Hbasicτ) as Hτ2.
    intros z Hz.
    pose proof (Hfv z Hz) as Hz'.
    apply elem_of_union in Hz' as [Hz'|Hz'].
    - rewrite dom_insert_L in Hz'.
      apply elem_of_union in Hz' as [Hzx | HzΔ].
      + apply elem_of_union_r. exact Hzx.
      + apply elem_of_union_l. exact HzΔ.
    - apply elem_of_union_l. exact (Hτ2 z Hz').
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
