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
