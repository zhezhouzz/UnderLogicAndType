(** * ChoiceTyping.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From ChoiceTyping Require Export SoundnessHelpers.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma basic_const_world_from_lookup c ν Σ m :
  (∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some (vconst c)) →
  m ⊨ basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]}.
Proof.
  intros Hlookup.
  eapply res_models_atom_intro.
  - unfold formula_scoped_in_world. simpl.
    unfold stale, stale_logic_qualifier, basic_world_lqual, lqual_dom.
    destruct (wf_ne _ (world_wf (res_restrict m {[ν]}))) as [σ Hσ].
    pose proof (Hlookup σ Hσ) as Hν.
    pose proof (wfworld_store_dom (res_restrict m {[ν]}) σ Hσ) as Hdom.
    assert (Hνdom : ν ∈ dom σ) by (apply elem_of_dom; eexists; exact Hν).
    simpl in Hdom. set_solver.
  - unfold logic_qualifier_denote, basic_world_formula, basic_world_lqual.
    simpl. unfold world_has_type_on, store_has_type_on.
    split.
    { destruct (wf_ne _ (world_wf (res_restrict m {[ν]}))) as [σ Hσ].
      pose proof (Hlookup σ Hσ) as Hν.
      pose proof (wfworld_store_dom (res_restrict m {[ν]}) σ Hσ) as Hdom.
      assert (Hνdom : ν ∈ dom σ) by (apply elem_of_dom; eexists; exact Hν).
      simpl in Hdom. set_solver. }
    intros σ Hσ x T v Hx HΣ Hσv.
    apply elem_of_singleton in Hx. subst x.
    rewrite lookup_insert in HΣ.
    destruct (decide (ν = ν)) as [_ | Hneq]; [| congruence].
    inversion HΣ; subst T.
    pose proof (Hlookup σ Hσ) as Hν.
    rewrite Hν in Hσv. inversion Hσv; subst v.
    constructor.
Qed.

Lemma basic_const_world_from_expr_atom c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨ basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]}.
Proof.
  intros Hexpr.
  apply basic_const_world_from_lookup.
  apply expr_logic_qual_ret_const_lookup. exact Hexpr.
Qed.

Lemma lifted_const_qualifier_from_projection c ν m σ
    (Hproj : res_restrict m {[ν]} σ) :
  σ !! ν = Some (vconst c) →
  res_models_with_store σ
    (res_fiber_from_projection m {[ν]} σ Hproj)
    (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))).
Proof.
  intros Hlookup.
  assert (Hdomσ : dom σ = {[ν]}).
  {
    pose proof (wfworld_store_dom (res_restrict m {[ν]}) σ Hproj) as Hdom.
    simpl in Hdom.
    assert (Hνdom : ν ∈ dom σ) by (apply elem_of_dom; eexists; exact Hlookup).
    set_solver.
  }
  assert (Hνm : ν ∈ world_dom (m : World)).
  {
    pose proof (wfworld_store_dom (res_restrict m {[ν]}) σ Hproj) as Hdom.
    simpl in Hdom. rewrite Hdomσ in Hdom. set_solver.
  }
  eapply res_models_with_store_FTypeQualifier_intro.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_FTypeQualifier.
    unfold qual_open_atom, mk_q_eq, qual_dom. simpl.
    rewrite decide_True by set_solver.
    simpl. rewrite Hdomσ. set_solver.
  - unfold qual_open_atom, mk_q_eq. simpl.
    rewrite decide_True by set_solver. simpl.
    assert (Hfiber_singleton_raw :
      raw_restrict (raw_fiber m σ) ({[ν]} ∪ (∅ ∪ ∅)) = singleton_world σ).
    {
      replace ({[ν]} ∪ (∅ ∪ ∅)) with ({[ν]} : aset) by set_solver.
      apply raw_restrict_fiber_from_projection_eq_singleton; [exact Hproj | exact Hdomσ].
    }
    split; [set_solver |].
    exists σ. split; [exact Hfiber_singleton_raw |].
    exists (vconst c). split.
    + apply store_restrict_lookup_some_2; [exact Hlookup | set_solver].
    + reflexivity.
Qed.

Lemma const_over_consequent_from_expr c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨
    FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FOver (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))).
Proof.
  intros Hexpr.
  pose proof (basic_const_world_from_expr_atom c ν Σ m Hexpr) as Hbasic.
  pose proof (expr_logic_qual_ret_const_lookup c ν m Hexpr) as Hlookup.
  eapply res_models_and_intro.
  - pose proof (res_models_with_store_fuel_scoped _
      ∅ m _ Hbasic) as Hscope_basic.
    unfold formula_scoped_in_world in *. simpl in *.
    rewrite fib_vars_singleton. simpl.
    unfold stale, stale_logic_qualifier.
    rewrite formula_fv_FTypeQualifier.
    unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
    rewrite decide_True by set_solver. simpl.
    set_solver.
  - exact Hbasic.
  - rewrite fib_vars_singleton.
    eapply res_models_fib_intro.
    + pose proof (res_models_with_store_fuel_scoped _
        ∅ m _ Hbasic) as Hscope_basic.
      unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier.
      rewrite formula_fv_FTypeQualifier.
      unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
      rewrite decide_True by set_solver. simpl.
      set_solver.
    + intros σ Hproj.
      pose proof (Hlookup σ Hproj) as Hσν.
      pose proof (lifted_const_qualifier_from_projection c ν m σ Hproj Hσν)
        as Hatom.
      eapply res_models_with_store_over_intro_same.
      * pose proof (res_models_with_store_fuel_scoped _
          σ (res_fiber_from_projection m {[ν]} σ Hproj) _ Hatom) as Hscope_atom.
        unfold formula_scoped_in_world in *. simpl in *.
        exact Hscope_atom.
      * exact Hatom.
Qed.

Lemma const_under_consequent_from_expr c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨
    FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FUnder (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))).
Proof.
  intros Hexpr.
  pose proof (basic_const_world_from_expr_atom c ν Σ m Hexpr) as Hbasic.
  pose proof (expr_logic_qual_ret_const_lookup c ν m Hexpr) as Hlookup.
  eapply res_models_and_intro.
  - pose proof (res_models_with_store_fuel_scoped _
      ∅ m _ Hbasic) as Hscope_basic.
    unfold formula_scoped_in_world in *. simpl in *.
    rewrite fib_vars_singleton. simpl.
    unfold stale, stale_logic_qualifier.
    rewrite formula_fv_FTypeQualifier.
    unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
    rewrite decide_True by set_solver. simpl.
    set_solver.
  - exact Hbasic.
  - rewrite fib_vars_singleton.
    eapply res_models_fib_intro.
    + pose proof (res_models_with_store_fuel_scoped _
        ∅ m _ Hbasic) as Hscope_basic.
      unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier.
      rewrite formula_fv_FTypeQualifier.
      unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
      rewrite decide_True by set_solver. simpl.
      set_solver.
    + intros σ Hproj.
      pose proof (Hlookup σ Hproj) as Hσν.
      pose proof (lifted_const_qualifier_from_projection c ν m σ Hproj Hσν)
        as Hatom.
      eapply res_models_with_store_under_intro_same.
      * pose proof (res_models_with_store_fuel_scoped _
          σ (res_fiber_from_projection m {[ν]} σ Hproj) _ Hatom) as Hscope_atom.
        unfold formula_scoped_in_world in *. simpl in *.
        exact Hscope_atom.
      * exact Hatom.
Qed.

Lemma const_over_consequent_from_expr_on c ν Σ m :
  m ⊨ FExprResultOn (dom Σ) (tret (vconst c)) ν →
  m ⊨
    FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
        ({[ν]} ∪ qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))
      (fib_vars (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
        (FOver (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))).
Proof.
  intros Hexpr.
  replace (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
    with ({[ν]} : aset)
    by (unfold qual_open_atom, mk_q_eq, qual_dom; simpl;
        rewrite decide_True by set_solver; simpl; set_solver).
  replace ({[ν]} ∪ {[ν]}) with ({[ν]} : aset) by set_solver.
  pose proof (expr_logic_qual_on_ret_const_lookup (dom Σ) c ν m Hexpr) as Hlookup.
  pose proof (basic_const_world_from_lookup c ν Σ m Hlookup) as Hbasic.
  eapply res_models_and_intro.
  - pose proof (res_models_with_store_fuel_scoped _
      ∅ m _ Hbasic) as Hscope_basic.
    unfold formula_scoped_in_world in *. simpl in *.
    rewrite fib_vars_singleton. simpl.
    unfold stale, stale_logic_qualifier.
    rewrite formula_fv_FTypeQualifier.
    unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
    rewrite decide_True by set_solver. simpl.
    set_solver.
  - exact Hbasic.
  - rewrite fib_vars_singleton.
    eapply res_models_fib_intro.
    + pose proof (res_models_with_store_fuel_scoped _
        ∅ m _ Hbasic) as Hscope_basic.
      unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier.
      rewrite formula_fv_FTypeQualifier.
      unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
      rewrite decide_True by set_solver. simpl.
      set_solver.
    + intros σ Hproj.
      pose proof (Hlookup σ Hproj) as Hσν.
      pose proof (lifted_const_qualifier_from_projection c ν m σ Hproj Hσν)
        as Hatom.
      eapply res_models_with_store_over_intro_same.
      * pose proof (res_models_with_store_fuel_scoped _
          σ (res_fiber_from_projection m {[ν]} σ Hproj) _ Hatom) as Hscope_atom.
        unfold formula_scoped_in_world in *. simpl in *.
        exact Hscope_atom.
      * exact Hatom.
Qed.

Lemma const_under_consequent_from_expr_on c ν Σ m :
  m ⊨ FExprResultOn (dom Σ) (tret (vconst c)) ν →
  m ⊨
    FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
        ({[ν]} ∪ qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))
      (fib_vars (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
        (FUnder (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))).
Proof.
  intros Hexpr.
  replace (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
    with ({[ν]} : aset)
    by (unfold qual_open_atom, mk_q_eq, qual_dom; simpl;
        rewrite decide_True by set_solver; simpl; set_solver).
  replace ({[ν]} ∪ {[ν]}) with ({[ν]} : aset) by set_solver.
  pose proof (expr_logic_qual_on_ret_const_lookup (dom Σ) c ν m Hexpr) as Hlookup.
  pose proof (basic_const_world_from_lookup c ν Σ m Hlookup) as Hbasic.
  eapply res_models_and_intro.
  - pose proof (res_models_with_store_fuel_scoped _
      ∅ m _ Hbasic) as Hscope_basic.
    unfold formula_scoped_in_world in *. simpl in *.
    rewrite fib_vars_singleton. simpl.
    unfold stale, stale_logic_qualifier.
    rewrite formula_fv_FTypeQualifier.
    unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
    rewrite decide_True by set_solver. simpl.
    set_solver.
  - exact Hbasic.
  - rewrite fib_vars_singleton.
    eapply res_models_fib_intro.
    + pose proof (res_models_with_store_fuel_scoped _
        ∅ m _ Hbasic) as Hscope_basic.
      unfold formula_scoped_in_world in *. simpl in *.
      unfold stale, stale_logic_qualifier.
      rewrite formula_fv_FTypeQualifier.
      unfold qual_open_atom, mk_q_eq, qual_dom in *; simpl in *.
      rewrite decide_True by set_solver. simpl.
      set_solver.
    + intros σ Hproj.
      pose proof (Hlookup σ Hproj) as Hσν.
      pose proof (lifted_const_qualifier_from_projection c ν m σ Hproj Hσν)
        as Hatom.
      eapply res_models_with_store_under_intro_same.
      * pose proof (res_models_with_store_fuel_scoped _
          σ (res_fiber_from_projection m {[ν]} σ Hproj) _ Hatom) as Hscope_atom.
        unfold formula_scoped_in_world in *. simpl in *.
        exact Hscope_atom.
      * exact Hatom.
Qed.

Lemma const_over_consequent_from_renamed_expr c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FAtom (expr_logic_qual (tret (vconst c)) ν)) →
  m ⊨ formula_rename_atom ν y
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FOver (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply const_over_consequent_from_expr.
  apply res_models_swap.
  exact Hexpr.
Qed.

Lemma const_under_consequent_from_renamed_expr c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FAtom (expr_logic_qual (tret (vconst c)) ν)) →
  m ⊨ formula_rename_atom ν y
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FUnder (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply const_under_consequent_from_expr.
  apply res_models_swap.
  exact Hexpr.
Qed.

Lemma const_over_consequent_from_renamed_expr_on c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FExprResultOn (dom Σ) (tret (vconst c)) ν) →
  m ⊨ formula_rename_atom ν y
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
        ({[ν]} ∪ qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))
      (fib_vars (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
        (FOver (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply (const_over_consequent_from_expr_on c ν Σ).
  apply res_models_swap.
  exact Hexpr.
Qed.

Lemma const_under_consequent_from_renamed_expr_on c ν y Σ m :
  m ⊨ formula_rename_atom ν y
    (FExprResultOn (dom Σ) (tret (vconst c)) ν) →
  m ⊨ formula_rename_atom ν y
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
        ({[ν]} ∪ qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))
      (fib_vars (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
        (FUnder (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply (const_under_consequent_from_expr_on c ν Σ).
  apply res_models_swap.
  exact Hexpr.
Qed.

Definition const_over_body (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FAtom (expr_logic_qual (tret (vconst c)) ν))
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FOver (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).

Definition const_under_body (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FAtom (expr_logic_qual (tret (vconst c)) ν))
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FUnder (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).

Definition const_over_body_on
    (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FExprResultOn (dom Σ) (tret (vconst c)) ν)
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
        ({[ν]} ∪ qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))
      (fib_vars (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
        (FOver (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).

Definition const_under_body_on
    (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FExprResultOn (dom Σ) (tret (vconst c)) ν)
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ)
        ({[ν]} ∪ qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))
      (fib_vars (qual_dom (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))
        (FUnder (FTypeQualifier (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).

Lemma const_over_body_fv_subset Σ c ν :
  formula_fv (const_over_body Σ c ν) ⊆ {[ν]}.
Proof.
  unfold const_over_body.
  intros z Hz. simpl in Hz.
  unfold stale, stale_logic_qualifier in Hz.
  rewrite fib_vars_singleton in Hz. simpl in Hz.
  unfold expr_logic_qual, qual_open_atom, mk_q_eq, qual_dom in Hz; simpl in Hz.
  destruct (decide (0 ∈ ({[0]} ∪ ∅ : gset nat))); simpl in Hz;
    unfold FTypeQualifier in Hz; simpl in Hz;
    unfold stale, stale_logic_qualifier in Hz; simpl in Hz;
    change (stale (tret (vconst c))) with (∅ : aset) in Hz;
    set_solver.
Qed.

Lemma const_under_body_fv_subset Σ c ν :
  formula_fv (const_under_body Σ c ν) ⊆ {[ν]}.
Proof.
  unfold const_under_body.
  intros z Hz. simpl in Hz.
  unfold stale, stale_logic_qualifier in Hz.
  rewrite fib_vars_singleton in Hz. simpl in Hz.
  unfold expr_logic_qual, qual_open_atom, mk_q_eq, qual_dom in Hz; simpl in Hz.
  destruct (decide (0 ∈ ({[0]} ∪ ∅ : gset nat))); simpl in Hz;
    unfold FTypeQualifier in Hz; simpl in Hz;
    unfold stale, stale_logic_qualifier in Hz; simpl in Hz;
    change (stale (tret (vconst c))) with (∅ : aset) in Hz;
    set_solver.
Qed.

Lemma const_over_body_on_fv_subset Σ c ν :
  formula_fv (const_over_body_on Σ c ν) ⊆ dom Σ ∪ {[ν]}.
Proof.
Admitted.

Lemma const_under_body_on_fv_subset Σ c ν :
  formula_fv (const_under_body_on Σ c ν) ⊆ dom Σ ∪ {[ν]}.
Proof.
Admitted.

Lemma const_over_body_rename_scoped Σ c ν y (m : WfWorld) :
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m (formula_rename_atom ν y (const_over_body Σ c ν)).
Proof.
  intros Hym.
  unfold formula_scoped_in_world. intros z Hz.
  rewrite dom_empty_L in Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  rewrite formula_fv_rename_atom in Hz.
  rewrite elem_of_aset_swap in Hz.
  pose proof (const_over_body_fv_subset Σ c ν _ Hz) as Hν.
  apply elem_of_singleton in Hν.
  unfold atom_swap in Hν.
  repeat destruct decide; subst; try congruence; exact Hym.
Qed.

Lemma const_under_body_rename_scoped Σ c ν y (m : WfWorld) :
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m (formula_rename_atom ν y (const_under_body Σ c ν)).
Proof.
  intros Hym.
  unfold formula_scoped_in_world. intros z Hz.
  rewrite dom_empty_L in Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  rewrite formula_fv_rename_atom in Hz.
  rewrite elem_of_aset_swap in Hz.
  pose proof (const_under_body_fv_subset Σ c ν _ Hz) as Hν.
  apply elem_of_singleton in Hν.
  unfold atom_swap in Hν.
  repeat destruct decide; subst; try congruence; exact Hym.
Qed.

Lemma const_over_body_on_rename_scoped Σ c ν y (m : WfWorld) :
  dom Σ ⊆ world_dom (m : World) →
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m
    (formula_rename_atom ν y (const_over_body_on Σ c ν)).
Proof.
Admitted.

Lemma const_under_body_on_rename_scoped Σ c ν y (m : WfWorld) :
  dom Σ ⊆ world_dom (m : World) →
  y ∈ world_dom (m : World) →
  formula_scoped_in_world ∅ m
    (formula_rename_atom ν y (const_under_body_on Σ c ν)).
Proof.
Admitted.
