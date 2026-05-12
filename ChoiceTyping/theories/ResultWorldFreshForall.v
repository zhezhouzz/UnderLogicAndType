(** * ChoiceTyping.ResultWorldFreshForall

    Bridges from cofinite [fresh_forall] expression-result formulas to the
    concrete result world used by the tlet proof.

    The representative chosen by [fresh_forall] is explicit-name/cofinite, so
    the primitive lemma returns the renamed body.  Callers that know the body is
    equivariant can use the wrapper lemma to transport it back to [body y]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  BasicTypingProps LocallyNamelessProps.
From ChoiceTyping Require Import ResultWorldBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** Renaming the cofinite representative of an expression-result continuation
    only changes the result coordinate. *)
Lemma FExprResultOn_dom_rename_from_current_exact_domain
    (Σ : gmap atom ty) (T : ty) e ν (n : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  ν ∉ dom Σ →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  n ⊨ FExprResultOn (dom Σ) e ν →
  n ⊨ formula_rename_atom (fresh_for (dom Σ)) ν
        (FExprResultOn (dom Σ) e (fresh_for (dom Σ))).
Proof.
  intros _ Hν _ Hmodel.
  cbn [dom].
  rewrite FExprResultOn_rename_result_fresh.
  - exact Hmodel.
  - apply fresh_for_not_in.
  - exact Hν.
Qed.

Lemma FExprResultOn_dom_exact_domain_eq_let_result_world_on
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  res_restrict n (dom Σ) = m →
  n ⊨ FExprResultOn (dom Σ) e ν →
  n = let_result_world_on e ν m Hfresh Hresult.
Proof.
  intros Hty Hdom Hclosed Hdomn Hrestr Hmodel.
  set (X := dom Σ).
  assert (HνX : ν ∉ X) by (subst X; rewrite <- Hdom; exact Hfresh).
  assert (Hfv : fv_tm e ⊆ X).
  { subst X. apply basic_typing_contains_fv_tm in Hty. exact Hty. }
  assert (Hlc : lc_tm e).
  { eapply typing_tm_lc; eauto. }
  set (E := (∅ : Store)).
  assert (Hmodel_fold :
    res_models_with_store E n
      (foldr FFib (FAtom (expr_logic_qual_on X e ν)) (elements X))).
  {
    subst E. unfold res_models, FExprResultOn in Hmodel.
    subst X.
    unfold fib_vars, fib_vars_acc, set_fold in Hmodel.
    cbn [compose] in Hmodel.
    rewrite foldr_fib_vars_acc_fst_bridge in Hmodel.
    exact Hmodel.
  }
  apply wfworld_ext. apply world_ext.
  - rewrite Hdomn, let_result_world_on_dom, Hdom. subst X. reflexivity.
  - intros σν. split.
    + intros Hσν.
      assert (Hσm : (m : World) (store_restrict σν X)).
      {
        rewrite <- Hrestr.
        exists σν. split; [exact Hσν | reflexivity].
      }
      pose proof (foldr_fib_expr_result_sound
        (elements X) X e ν E n σν (store_restrict σν {[ν]})
        (NoDup_elements X)
        ltac:(subst E; rewrite dom_empty_L; set_solver)
        Hmodel_fold Hσν ltac:(reflexivity)) as Hstore.
      match type of Hstore with
      | expr_result_store _ (subst_map (store_restrict ?R _) _) _ =>
          replace (store_restrict R X) with (store_restrict σν X) in Hstore
      end.
      2:{ subst E. symmetry. apply store_restrict_empty_union_elements. }
      destruct Hstore as [vx [Hνpart [Hstale [Hlc_vx Hsteps]]]].
      exists (store_restrict σν X), vx. split; [exact Hσm |].
      split.
      {
        set (σX := store_restrict σν X).
        set (ρfv := store_restrict σX (fv_tm e)).
        assert (Hclosed_fv : closed_env (store_restrict σX (fv_tm e))).
        {
          subst σX X.
          apply closed_env_restrict.
          destruct (Hclosed _ Hσm) as [Hcl _].
          replace (store_restrict (store_restrict σν (dom Σ)) (dom Σ))
            with (store_restrict σν (dom Σ)) in Hcl.
          - exact Hcl.
          - store_norm. reflexivity.
        }
        pose proof (subst_map_eq_on_fv e σX ρfv Hclosed_fv) as Heq.
        assert (Hagree :
          store_restrict ρfv (fv_tm e) = store_restrict σX (fv_tm e)).
        { subst ρfv. store_norm. reflexivity. }
        specialize (Heq Hagree).
        change (subst_map ρfv e = subst_map σX e) in Heq.
        change (subst_map ρfv e →* tret vx).
        rewrite Heq. exact Hsteps.
      }
      assert (Hid : store_restrict σν (X ∪ {[ν]}) = σν).
      {
        apply store_restrict_idemp.
        pose proof (wfworld_store_dom n σν Hσν) as Hdomσν.
        change (dom σν ⊆ X ∪ {[ν]}).
        rewrite Hdomσν, Hdomn. subst X. set_solver.
      }
      pose proof (store_restrict_union_singleton_insert_from_projection
        σν X ν vx HνX Hνpart) as Hunion.
      rewrite Hid in Hunion. exact Hunion.
    + intros [σ [vx [Hσm [Hsteps ->]]]].
      assert (HprojX : (res_restrict n X : World) σ).
      {
        subst X. rewrite Hrestr. exact Hσm.
      }
      destruct HprojX as [τ [Hτn HτX]].
      assert (Hclosed_vx : stale vx = ∅ ∧ is_lc vx).
      {
        eapply (steps_closed_result_of_restrict_world X e m σ vx).
        - subst X. rewrite <- Hdom. set_solver.
        - exact Hfv.
        - exact Hlc.
        - subst X. exact Hclosed.
        - subst X. simpl.
          exists σ. split; [exact Hσm |].
          apply store_restrict_idemp.
          pose proof (wfworld_store_dom m σ Hσm) as Hdomσ.
          change (dom σ ⊆ dom Σ).
          rewrite Hdomσ, Hdom. set_solver.
        - pose proof (subst_map_eq_on_fv e
            (store_restrict σ X) (store_restrict σ (fv_tm e))) as Heq.
          assert (Hclosed_fv : closed_env
            (store_restrict (store_restrict σ X) (fv_tm e))).
          {
            subst X.
            apply closed_env_restrict.
            destruct (Hclosed _ Hσm) as [Hcl _].
            exact Hcl.
          }
          specialize (Heq Hclosed_fv).
          assert (Hagree :
            store_restrict (store_restrict σ (fv_tm e)) (fv_tm e) =
            store_restrict (store_restrict σ X) (fv_tm e)).
          { store_norm. replace (X ∩ fv_tm e) with (fv_tm e) by set_solver.
            reflexivity. }
          specialize (Heq Hagree).
          change (subst_map (store_restrict σ (fv_tm e)) e =
                  subst_map (store_restrict σ X) e) in Heq.
          rewrite <- Heq. exact Hsteps.
      }
      assert (Henv_eq :
        store_restrict
          (store_restrict (E ∪ store_restrict τ (list_to_set (elements X) : aset)) X)
          (fv_tm e) =
        store_restrict σ (fv_tm e)).
      {
        subst E.
        eapply store_restrict_empty_union_elements_subset; eauto.
      }
      assert (Hclosed_env :
        closed_env
          (store_restrict
            (store_restrict (E ∪ store_restrict τ (list_to_set (elements X) : aset)) X)
            (fv_tm e))).
      {
        rewrite Henv_eq.
        subst X.
        replace (store_restrict σ (fv_tm e))
          with (store_restrict (store_restrict σ (dom Σ)) (fv_tm e)).
        - apply closed_env_restrict.
          exact (proj1 (Hclosed σ Hσm)).
        - store_norm. replace (dom Σ ∩ fv_tm e) with (fv_tm e) by set_solver.
          reflexivity.
      }
      assert (Hexpr_store :
        expr_result_store ν
          (subst_map
            (store_restrict
              (E ∪ store_restrict τ (list_to_set (elements X) : aset)) X)
            e)
          {[ν := vx]}).
      {
        exists vx. split; [reflexivity |]. repeat split.
        - exact (proj1 Hclosed_vx).
        - exact (proj2 Hclosed_vx).
          - pose proof (subst_map_eq_on_fv e
            (store_restrict σ (fv_tm e))
            (store_restrict
              (E ∪ store_restrict τ (list_to_set (elements X) : aset)) X))
            as Heq.
          assert (Hclosed_sigma_fv :
            closed_env (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))).
          {
            replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
              with (store_restrict σ (fv_tm e)).
            - rewrite <- Henv_eq. exact Hclosed_env.
            - store_norm. reflexivity.
          }
          specialize (Heq Hclosed_sigma_fv).
          assert (Hagree :
            store_restrict
              (store_restrict (E ∪ store_restrict τ (list_to_set (elements X) : aset)) X)
              (fv_tm e) =
            store_restrict (store_restrict σ (fv_tm e)) (fv_tm e)).
          {
            rewrite Henv_eq. store_norm. reflexivity.
          }
          specialize (Heq Hagree).
          change (subst_map
            (store_restrict (E ∪ store_restrict τ (list_to_set (elements X) : aset)) X)
            e =
            subst_map (store_restrict σ (fv_tm e)) e) in Heq.
          rewrite Heq. exact Hsteps.
      }
      destruct (foldr_fib_expr_result_complete_paired
        (elements X) X e ν E n τ {[ν := vx]}
        (NoDup_elements X)
        ltac:(subst E; rewrite dom_empty_L; set_solver)
        Hmodel_fold Hτn Hexpr_store)
        as [τ' [Hτ'n [Hτ'X Hτ'ν]]].
      assert (Hτ'_eq : τ' = <[ν := vx]> σ).
      {
        assert (Hid : store_restrict τ' (X ∪ {[ν]}) = τ').
        {
          apply store_restrict_idemp.
          pose proof (wfworld_store_dom n τ' Hτ'n) as Hdomτ'.
          change (dom τ' ⊆ X ∪ {[ν]}).
          rewrite Hdomτ', Hdomn. subst X. set_solver.
        }
        pose proof (store_restrict_union_singleton_insert_from_projection
          τ' X ν vx HνX Hτ'ν) as Hunion.
        assert (Hτ'X_dom : store_restrict τ' X = store_restrict τ X).
        {
          replace X with (list_to_set (elements X) : aset).
          - exact Hτ'X.
          - apply set_eq. intros z.
            rewrite elem_of_list_to_set, elem_of_elements. reflexivity.
        }
        rewrite Hτ'X_dom, HτX in Hunion.
        rewrite Hid in Hunion. exact Hunion.
      }
      rewrite <- Hτ'_eq. exact Hτ'n.
Qed.

Lemma set_difference_pull_singleton (X Y : aset) x :
  x ∈ X →
  x ∉ Y →
  X ∖ Y = (X ∖ ({[x]} ∪ Y)) ∪ {[x]}.
Proof.
  intros HxX HxY.
  apply set_eq. intros z.
  rewrite elem_of_difference, elem_of_union, elem_of_difference,
    elem_of_union, !elem_of_singleton.
  split.
  - intros [HzX HzY].
    destruct (decide (z = x)) as [->|Hzx].
    + right. reflexivity.
    + left. split; [exact HzX |].
      intros [Hzx'|HzY']; [congruence | contradiction].
  - intros [[HzX Hnot] | Hzx].
    + split; [exact HzX |].
      intros HzY. apply Hnot. right. exact HzY.
    + subst z. split; [exact HxX | exact HxY].
Qed.

Lemma let_result_world_on_models_FExprResult :
  ∀ X e ν (n : WfWorld) Hfresh Hresult,
    fv_tm e ⊆ X →
    lc_tm e →
    ν ∉ X →
    X ⊆ world_dom (n : World) →
    world_store_closed_on X n →
    let_result_world_on e ν n Hfresh Hresult ⊨ FExprResultOn X e ν.
Proof.
  intros X e ν n Hfresh Hresult Hfv Hlc HνX HXn Hclosed.
  unfold res_models, FExprResultOn.
  apply fib_vars_models_intro.
  - unfold formula_scoped_in_world.
    rewrite fib_vars_formula_fv. simpl.
    unfold stale, stale_logic_qualifier. simpl.
    rewrite dom_empty_L.
    set_solver.
  - set (nX := res_restrict n X).
    assert (HfreshX : ν ∉ world_dom (nX : World)).
    { subst nX. simpl. set_solver. }
    assert (HresultX : ∀ σ, (nX : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
    {
      subst nX. intros σ [σ0 [Hσ0 Hrestrict]].
      destruct (Hresult σ0 Hσ0) as [vx Hsteps].
      exists vx.
      rewrite <- Hrestrict.
      rewrite store_restrict_restrict.
      replace (X ∩ fv_tm e) with (fv_tm e) by set_solver.
      exact Hsteps.
    }
    set (result := res_restrict
      (let_result_world_on e ν n Hfresh Hresult) (X ∪ {[ν]})).
    assert (Hresult_eq :
      result = let_result_world_on e ν nX HfreshX HresultX).
    {
      subst result nX.
      apply let_result_world_on_restrict_input; eauto.
    }
    eapply fib_vars_obligation_intro
      with (I := fun Fixed ρ w =>
        result_world_slice_inv X ν result Fixed ρ w).
    + eapply result_world_slice_inv_initial.
      * subst result. simpl. set_solver.
      * reflexivity.
    + intros x Y ρ w HxX HxY Hinv.
      eapply (result_world_slice_inv_disjoint
        X ν result (X ∖ ({[x]} ∪ Y)) ρ w x); eauto.
      set_solver.
    + intros x Y ρ w HxX HxY Hinv Hdisj σx Hproj.
      rewrite (set_difference_pull_singleton X Y x HxX HxY).
      eapply (result_world_slice_inv_step
        X ν result (X ∖ ({[x]} ∪ Y)) ρ w x σx Hproj); eauto.
      set_solver.
    + intros ρ w Hinv.
      rewrite Hresult_eq in Hinv.
      assert (HclosedX : world_store_closed_on X nX).
      {
        subst nX.
        eapply world_store_closed_on_restrict.
        - intros z Hz. exact Hz.
        - exact Hclosed.
      }
      assert (HdomnX : world_dom (nX : World) = X).
      {
        subst nX. simpl.
        apply set_eq. intros z. rewrite elem_of_intersection.
        split.
        - intros [_ HzX]. exact HzX.
        - intros HzX. split; [apply HXn; exact HzX | exact HzX].
      }
      eapply (result_world_slice_inv_base X e ν nX HdomnX HfreshX HresultX
        Hfv Hlc HclosedX); eauto.
Qed.

Lemma fresh_forall_expr_result_to_let_result_world_renamed
    X e D (body : atom → FormulaQ) (m : WfWorld) :
  fv_tm e ⊆ X →
  lc_tm e →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  m ⊨ fresh_forall D (fun x => FImpl (FExprResultOn X e x) (body x)) →
  ∃ L : aset,
    world_dom (m : World) ∪ D ∪ X ∪ fv_tm e ⊆ L ∧
    ∀ y,
      y ∉ L →
      ∀ Hfresh Hresult,
        (∀ (n : WfWorld),
          world_dom (n : World) = world_dom (m : World) ∪ {[y]} →
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        let_result_world_on e y m Hfresh Hresult ⊨
          formula_rename_atom (fresh_for D) y (body (fresh_for D)).
Proof.
  intros Hfv Hlc HX Hclosed.
  unfold fresh_forall, res_models, res_models_with_store.
  simpl. intros [_ [L [HL Hforall]]].
  exists (L ∪ D ∪ X ∪ fv_tm e).
  split; [set_solver |].
  intros y Hy Hfresh Hresult Hante.
  assert (HyL : y ∉ L) by set_solver.
  set (w := let_result_world_on e y m Hfresh Hresult).
  pose proof (Hforall y HyL w) as Himpl_fuel.
  specialize (Himpl_fuel ltac:(subst w; reflexivity)).
  specialize (Himpl_fuel (let_result_world_on_restrict e y m Hfresh Hresult)).
  assert (Himpl :
    w ⊨ FImpl
      (formula_rename_atom (fresh_for D) y (FExprResultOn X e (fresh_for D)))
      (formula_rename_atom (fresh_for D) y (body (fresh_for D)))).
  {
    unfold res_models, res_models_with_store.
    simpl.
    destruct Himpl_fuel as [Hscope Himpl_cont].
    split; [exact Hscope |].
    intros m' Hle Hant.
    eapply res_models_with_store_fuel_irrel.
    3: {
      apply Himpl_cont; [exact Hle |].
      models_fuel_irrel Hant.
    }
    all: rewrite ?formula_rename_preserves_measure; lia.
  }
  eapply res_models_impl_elim.
  - exact Himpl.
  - apply Hante.
    + subst w. rewrite let_result_world_on_dom. reflexivity.
    + subst w.
      apply (let_result_world_on_models_FExprResult X).
      * exact Hfv.
      * exact Hlc.
      * set_solver.
      * simpl. set_solver.
      * exact Hclosed.
Qed.

Lemma fresh_forall_expr_result_to_let_result_world
    X e D (body : atom → FormulaQ) (m : WfWorld) :
  fv_tm e ⊆ X →
  lc_tm e →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  m ⊨ fresh_forall D (fun x => FImpl (FExprResultOn X e x) (body x)) →
  ∃ L : aset,
    world_dom (m : World) ∪ D ∪ X ∪ fv_tm e ⊆ L ∧
    ∀ y,
      y ∉ L →
      ∀ Hfresh Hresult,
        (∀ (n : WfWorld),
          world_dom (n : World) = world_dom (m : World) ∪ {[y]} →
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        (∀ n,
          n ⊨ formula_rename_atom (fresh_for D) y (body (fresh_for D)) →
          n ⊨ body y) →
        let_result_world_on e y m Hfresh Hresult ⊨ body y.
Proof.
  intros Hfv Hlc HX Hclosed Hforall.
  destruct (fresh_forall_expr_result_to_let_result_world_renamed
    X e D body m Hfv Hlc HX Hclosed Hforall) as [L [HL Huse]].
  exists L. split; [exact HL |].
  intros y Hy Hfresh Hresult Hante Hbody.
  apply Hbody.
  eapply Huse; eauto.
Qed.

Lemma FExprContIn_to_let_result_world_on_exact_domain
    (Σ : gmap atom ty) (T : ty) e
    (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn Σ e P →
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ P ν.
Proof.
  intros Hty Hdom Hclosed Htotal HPfv HPrename Hcont.
  pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
  pose proof (typing_tm_lc _ _ _ Hty) as Hlc.
  unfold FExprContIn in Hcont.
  destruct (fresh_forall_expr_result_to_let_result_world
    (dom Σ) e (dom Σ) P m Hfv Hlc
    ltac:(rewrite <- Hdom; set_solver) Hclosed Hcont)
    as [L [HL Huse]].
  exists (L ∪ dom Σ). split; [set_solver |].
  intros ν Hν Hfresh Hresult.
  eapply Huse.
  - set_solver.
  - intros n Hdomn Hn.
    cbn [dom].
    eapply FExprResultOn_dom_rename_from_current_exact_domain; eauto.
    + set_solver.
    + rewrite <- Hdom. exact Hdomn.
  - intros n Hn.
    apply (proj1 (HPrename (fresh_for (dom Σ)) ν n
      ltac:(apply fresh_for_not_in) ltac:(set_solver))).
    exact Hn.
Qed.

Lemma let_result_world_on_to_FExprContIn_exact_domain
    (Σ : gmap atom ty) (T : ty) e
    (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  (∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ P ν) →
  m ⊨ FExprContIn Σ e P.
Proof.
  intros Hty Hdom Hclosed Htotal HPfv HPrename Hcont.
  pose proof (basic_typing_contains_fv_tm _ _ _ Hty) as Hfv.
  destruct Hcont as [L [HL Huse]].
  unfold FExprContIn, fresh_forall, res_models, res_models_with_store.
  simpl.
  split.
  - unfold formula_scoped_in_world.
    simpl.
    rewrite FExprResultOn_fv.
    pose proof (fresh_for_not_in (dom Σ)) as Ha.
    pose proof (HPfv (fresh_for (dom Σ))) as HP.
    rewrite Hdom.
    set_solver.
  - exists (L ∪ dom Σ). split; [rewrite Hdom; set_solver |].
    intros ν Hν m' Hdom' Hrestr.
    assert (HνΣ : ν ∉ dom Σ) by set_solver.
    assert (Hfreshν : ν ∉ world_dom (m : World)) by (rewrite Hdom; exact HνΣ).
    assert (Hresultν : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
    { eapply expr_total_on_to_fv_result; eauto. }
    assert (Hbody :
      let_result_world_on e ν m Hfreshν Hresultν ⊨ P ν).
    { eapply Huse; eauto. set_solver. }
    assert (Hscope_impl :
      formula_scoped_in_world ∅ m'
        (formula_rename_atom (fresh_for (dom Σ)) ν
          (FImpl (FExprResultOn (dom Σ) e (fresh_for (dom Σ)))
                 (P (fresh_for (dom Σ)))))).
    {
      replace (formula_rename_atom (fresh_for (dom Σ)) ν
        (FImpl (FExprResultOn (dom Σ) e (fresh_for (dom Σ)))
               (P (fresh_for (dom Σ)))))
        with (FImpl (FExprResultOn (dom Σ) e ν)
              (formula_rename_atom (fresh_for (dom Σ)) ν
                (P (fresh_for (dom Σ))))).
      2:{
        simpl. cbn [dom].
        rewrite FExprResultOn_rename_result_fresh; [reflexivity | |].
        - apply fresh_for_not_in.
        - exact HνΣ.
      }
      unfold formula_scoped_in_world. simpl.
      rewrite FExprResultOn_fv.
      pose proof (fresh_for_not_in (dom Σ)) as Ha.
      pose proof (HPfv (fresh_for (dom Σ))) as HP.
      pose proof (formula_rename_atom_fv_subset_pair
        (dom Σ) (fresh_for (dom Σ)) ν (P (fresh_for (dom Σ)))
        Ha HνΣ HP) as HPren.
      rewrite Hdom', Hdom.
      set_solver.
    }
    assert (Himpl :
      m' ⊨ formula_rename_atom (fresh_for (dom Σ)) ν
        (FImpl (FExprResultOn (dom Σ) e (fresh_for (dom Σ)))
               (P (fresh_for (dom Σ))))).
    {
      eapply res_models_with_store_impl_intro.
      - exact Hscope_impl.
      - intros m'' Hle Hant.
        assert (Hantν : m'' ⊨ FExprResultOn (dom Σ) e ν).
        {
          cbn [dom] in Hant |- *.
          rewrite (FExprResultOn_rename_result_fresh
            (dom Σ) e (fresh_for (dom Σ)) ν) in Hant.
          + exact Hant.
          + apply fresh_for_not_in.
          + exact HνΣ.
        }
        set (S := dom Σ ∪ {[ν]}).
        assert (HS_eq : S = world_dom (m' : World)).
        { unfold S. rewrite Hdom', Hdom. set_solver. }
        assert (Hmin_eq : res_restrict m'' S = m').
        {
          unfold S.
          rewrite <- Hdom, <- Hdom'.
          apply res_restrict_eq_of_le. exact Hle.
        }
        assert (Hant_min : res_restrict m'' S ⊨ FExprResultOn (dom Σ) e ν).
        {
          pose proof (res_models_minimal_on S m'' (FExprResultOn (dom Σ) e ν)
            ltac:(rewrite FExprResultOn_fv; unfold S; set_solver))
            as Hminimal.
          exact (proj1 Hminimal Hantν).
        }
        assert (Hdom_min :
          world_dom (res_restrict m'' S : World) = dom Σ ∪ {[ν]}).
        {
          rewrite Hmin_eq, Hdom'. rewrite Hdom. reflexivity.
        }
        assert (Hrestr_min :
          res_restrict (res_restrict m'' S) (dom Σ) = m).
        {
          rewrite Hmin_eq. rewrite <- Hdom. exact Hrestr.
        }
        pose proof (FExprResultOn_dom_exact_domain_eq_let_result_world_on
          Σ T e ν m (res_restrict m'' S) Hfreshν Hresultν
          Hty Hdom Hclosed Hdom_min Hrestr_min Hant_min) as Hexact.
        assert (Hbody_m'' : m'' ⊨ P ν).
        {
          eapply (res_models_kripke
            (let_result_world_on e ν m Hfreshν Hresultν) m'' (P ν)).
          - rewrite <- Hexact. apply res_restrict_le.
          - exact Hbody.
        }
        apply (proj2 (HPrename (fresh_for (dom Σ)) ν m''
          ltac:(apply fresh_for_not_in) HνΣ)).
        exact Hbody_m''.
    }
    unfold res_models, res_models_with_store in Himpl.
    rewrite formula_rename_preserves_measure in Himpl.
    exact Himpl.
Qed.

Lemma FExprContIn_iff_let_result_world_on_exact_domain
    (Σ : gmap atom ty) (T : ty) e
    (P : atom → FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_store_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  (∀ ν, formula_fv (P ν) ⊆ dom Σ ∪ {[ν]}) →
  formula_family_rename_stable_on (dom Σ) P →
  m ⊨ FExprContIn Σ e P ↔
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ P ν.
Proof.
  intros Hty Hdom Hclosed Htotal HPfv HPrename.
  split.
  - eapply (FExprContIn_to_let_result_world_on_exact_domain Σ T e P m); eauto.
  - eapply (let_result_world_on_to_FExprContIn_exact_domain Σ T e P m); eauto.
Qed.
