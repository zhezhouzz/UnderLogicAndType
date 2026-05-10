(** * ChoiceTyping.ResultWorldFreshForall

    Bridges from cofinite [fresh_forall] expression-result formulas to the
    concrete result world used by the tlet proof.

    The representative chosen by [fresh_forall] is explicit-name/cofinite, so
    the primitive lemma returns the renamed body.  Callers that know the body is
    equivariant can use the wrapper lemma to transport it back to [body y]. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Import ResultWorldBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma let_result_world_on_models_FExprResultOn :
  ∀ X e ν (n : WfWorld) Hfresh Hresult,
    fv_tm e ⊆ X →
    lc_tm e →
    ν ∉ X →
    X ⊆ world_dom (n : World) →
    world_store_closed_on X n →
    let_result_world_on X e ν n Hfresh Hresult ⊨ FExprResultOn X e ν.
Proof.
  intros X e ν n Hfresh Hresult Hfv Hlc HνX HXn Hclosed.
  apply (proj2 ((FExprResultOn_iff_let_result_world_on
    X e ν (let_result_world_on X e ν n Hfresh Hresult))
    Hfv Hlc HνX
    ltac:(simpl; unfold let_result_world_on, let_result_raw_world_on; simpl; set_solver)
    ltac:(by apply let_result_world_on_store_closed_on))).
  - assert (Hfresh0 :
      ν ∉ world_dom (res_restrict (let_result_world_on X e ν n Hfresh Hresult) X : World))
      by (simpl; set_solver).
    assert (Hresult0 :
      ∀ σ, (res_restrict (let_result_world_on X e ν n Hfresh Hresult) X : World) σ →
        ∃ vx, subst_map (store_restrict σ X) e →* tret vx).
    {
      intros σ Hσ.
      simpl in Hσ.
      destruct Hσ as [sigmanu [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
      rewrite store_restrict_insert_notin in Hrestrict by exact HνX.
      subst σ.
      exists vx.
      store_norm.
      exact Hsteps.
    }
    exists Hfresh0, Hresult0.
    apply wfworld_ext. apply world_ext.
    + simpl. set_solver.
    + intros sigmanu. simpl. split.
      * intros [σfull [[σ0 [vx [Hσ0 [Hsteps ->]]]] Hrestrict]].
        rewrite store_restrict_insert_in in Hrestrict by set_solver.
        inversion Hrestrict. subst sigmanu.
        exists (store_restrict σ0 X), vx.
        split.
        -- exists (<[ν := vx]> σ0). split.
           ++ exists σ0, vx. repeat split; eauto.
           ++ rewrite store_restrict_insert_notin by exact HνX.
              reflexivity.
        -- split.
           ++ rewrite store_restrict_idemp.
              ** exact Hsteps.
              ** rewrite store_restrict_dom.
                 pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
                 set_solver.
           ++ f_equal.
              apply store_restrict_union_singleton_fresh_eq.
              apply not_elem_of_dom.
              pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
              rewrite Hdomσ0. exact Hfresh.
      * intros [σ [vx [Hσ [Hsteps ->]]]].
        destruct Hσ as [sigmanu [[σ0 [vx0 [Hσ0 [Hsteps0 ->]]]] Hrestrict]].
        rewrite store_restrict_insert_notin in Hrestrict by exact HνX.
        subst σ.
        exists (<[ν := vx]> σ0). split.
        -- exists σ0, vx. repeat split; eauto.
           store_norm.
           exact Hsteps.
        -- rewrite store_restrict_insert_in by set_solver.
           rewrite store_restrict_union_singleton_fresh_eq.
           2:{
             apply not_elem_of_dom.
             pose proof (wfworld_store_dom n σ0 Hσ0) as Hdomσ0.
             rewrite Hdomσ0. exact Hfresh.
           }
           reflexivity.
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
        (∀ n,
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        let_result_world_on X e y m Hfresh Hresult ⊨
          formula_rename_atom (fresh_for D) y (body (fresh_for D)).
Proof.
  intros Hfv Hlc HX Hclosed.
  unfold fresh_forall, res_models, res_models_with_store.
  simpl. intros [_ [L [HL Hforall]]].
  exists (L ∪ D ∪ X ∪ fv_tm e).
  split; [set_solver |].
  intros y Hy Hfresh Hresult Hante.
  assert (HyL : y ∉ L) by set_solver.
  set (w := let_result_world_on X e y m Hfresh Hresult).
  pose proof (Hforall y HyL w) as Himpl_fuel.
  specialize (Himpl_fuel ltac:(subst w; reflexivity)).
  specialize (Himpl_fuel (let_result_world_on_restrict X e y m Hfresh Hresult)).
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
    subst w.
    apply let_result_world_on_models_FExprResultOn.
    + exact Hfv.
    + exact Hlc.
    + set_solver.
    + simpl. set_solver.
    + exact Hclosed.
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
        (∀ n,
          n ⊨ FExprResultOn X e y →
          n ⊨ formula_rename_atom (fresh_for D) y
                 (FExprResultOn X e (fresh_for D))) →
        (∀ n,
          n ⊨ formula_rename_atom (fresh_for D) y (body (fresh_for D)) →
          n ⊨ body y) →
        let_result_world_on X e y m Hfresh Hresult ⊨ body y.
Proof.
  intros Hfv Hlc HX Hclosed Hforall.
  destruct (fresh_forall_expr_result_to_let_result_world_renamed
    X e D body m Hfv Hlc HX Hclosed Hforall) as [L [HL Huse]].
  exists L. split; [exact HL |].
  intros y Hy Hfresh Hresult Hante Hbody.
  apply Hbody.
  eapply Huse; eauto.
Qed.
