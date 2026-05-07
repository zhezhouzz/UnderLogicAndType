(** * ChoiceTyping.Soundness

    Soundness skeleton for the single declarative typing judgment. *)

From CoreLang Require Import Instantiation InstantiationProps.
From ChoiceTyping Require Export Typing.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** Compatibility of satisfaction with monotone/antitone structure *)

Lemma res_models_impl_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FImpl φ ψ →
  m ⊑ m' →
  m' ⊨ FImpl φ ψ.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.

Lemma res_models_and_mono (φ ψ : FormulaQ) (m m' : WfWorld) :
  m ⊨ FAnd φ ψ →
  m ⊑ m' →
  m' ⊨ FAnd φ ψ.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.

Lemma res_models_and_elim_l (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FAnd φ ψ →
  m ⊨ φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ [Hφ _]].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_and_elim_r (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FAnd φ ψ →
  m ⊨ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ [_ Hψ]].
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_and_intro (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FAnd φ ψ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ Hψ. split; [exact Hscope |].
  split.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_or_intro_l (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ φ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  left. eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_or_intro_r (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOr φ ψ) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hψ. split; [exact Hscope |].
  right. eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorld) (φ ψ : FormulaQ) (Hc : world_compat m1 m2) :
  formula_scoped_in_world ∅ m (FStar φ ψ) →
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hle Hφ Hψ. split; [exact Hscope |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorld) (φ ψ : FormulaQ) (Hdef : raw_sum_defined m1 m2) :
  formula_scoped_in_world ∅ m (FPlus φ ψ) →
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hle Hφ Hψ. split; [exact Hscope |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
  - eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia.
Qed.

Lemma res_models_atom_intro (m : WfWorld) (q : logic_qualifier) :
  formula_scoped_in_world ∅ m (FAtom q) →
  logic_qualifier_denote q ∅ m →
  m ⊨ FAtom q.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_with_store_atom_intro
    (ρ : Store) (m : WfWorld) (q : logic_qualifier) :
  formula_scoped_in_world ρ m (FAtom q) →
  logic_qualifier_denote q ρ m →
  res_models_with_store ρ m (FAtom q).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hq. split; [exact Hscope |].
  exists m. split; [exact Hq | reflexivity].
Qed.

Lemma res_models_over_intro_same (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FOver φ) →
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_with_store_over_intro_same
    (ρ : Store) (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ρ m (FOver φ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FOver φ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_under_intro_same (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FUnder φ) →
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_with_store_under_intro_same
    (ρ : Store) (m : WfWorld) (φ : FormulaQ) :
  formula_scoped_in_world ρ m (FUnder φ) →
  res_models_with_store ρ m φ →
  res_models_with_store ρ m (FUnder φ).
Proof.
  unfold res_models_with_store.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia.
Qed.

Lemma res_models_fib_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FFib x φ) →
  (∀ σ,
     ∀ Hproj : res_restrict m {[x]} σ,
     res_models_with_store σ
       (res_fiber_from_projection m {[x]} σ Hproj)
       φ) →
  m ⊨ FFib x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Hfib. split; [exact Hscope |].
  split.
  - set_solver.
  - intros σ Hproj.
    rewrite map_empty_union.
    eapply res_models_with_store_fuel_irrel; [| | exact (Hfib σ Hproj)];
      simpl; lia.
Qed.

Lemma res_models_impl_intro (m : WfWorld) (φ ψ : FormulaQ) :
  formula_scoped_in_world ∅ m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
         m' ⊨ φ → m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope Himpl. split; [exact Hscope |].
  intros m' Hle Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ + formula_measure ψ) (formula_measure φ)
    ∅ m' φ ltac:(simpl; lia) ltac:(lia) Hφ) as Hφ_exact.
  pose proof (Himpl m' Hle Hφ_exact) as Hψ_exact.
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ_exact]; simpl; lia.
Qed.

Lemma res_models_forall_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FForall x φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∀ m' : WfWorld,
        world_dom m' = world_dom m ∪ {[y]} →
        res_restrict m' (world_dom m) = m →
        m' ⊨ formula_rename_atom x y φ) →
  m ⊨ FForall x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hforall]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy m' Hdom Hrestr.
  eapply res_models_with_store_fuel_irrel; [| | exact (Hforall y Hy m' Hdom Hrestr)];
    rewrite ?formula_rename_preserves_measure; simpl; lia.
Qed.

Lemma basic_const_world_from_expr_atom c ν Σ m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  m ⊨ basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]}.
Proof.
  intros Hexpr.
  pose proof (expr_logic_qual_ret_const_lookup c ν m Hexpr) as Hlookup.
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

Lemma lifted_const_qualifier_from_projection c ν m σ
    (Hproj : res_restrict m {[ν]} σ) :
  σ !! ν = Some (vconst c) →
  res_models_with_store σ
    (res_fiber_from_projection m {[ν]} σ Hproj)
    (FAtom (lift_type_qualifier_to_logic
      (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))).
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
  eapply res_models_with_store_atom_intro.
  - unfold formula_scoped_in_world. simpl.
    unfold stale, stale_logic_qualifier.
    rewrite lqual_dom_lift_type_qualifier_to_logic.
    unfold qual_open_atom, mk_q_eq, qual_dom. simpl.
    rewrite decide_True by set_solver.
    simpl. rewrite Hdomσ. set_solver.
  - unfold logic_qualifier_denote, lift_type_qualifier_to_logic.
    unfold qual_open_atom, mk_q_eq. simpl.
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
        (FOver (FAtom (lift_type_qualifier_to_logic
          (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).
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
    rewrite lqual_dom_lift_type_qualifier_to_logic.
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
      rewrite lqual_dom_lift_type_qualifier_to_logic.
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
        (FUnder (FAtom (lift_type_qualifier_to_logic
          (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c))))))).
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
    rewrite lqual_dom_lift_type_qualifier_to_logic.
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
      rewrite lqual_dom_lift_type_qualifier_to_logic.
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
        (FOver (FAtom (lift_type_qualifier_to_logic
          (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))))).
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
        (FUnder (FAtom (lift_type_qualifier_to_logic
          (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))))).
Proof.
  intros Hexpr.
  apply res_models_swap.
  apply const_under_consequent_from_expr.
  apply res_models_swap.
  exact Hexpr.
Qed.

Definition const_over_body (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FAtom (expr_logic_qual (tret (vconst c)) ν))
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FOver (FAtom (lift_type_qualifier_to_logic
          (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))))).

Definition const_under_body (Σ : gmap atom ty) (c : constant) (ν : atom) : FormulaQ :=
  FImpl
    (FAtom (expr_logic_qual (tret (vconst c)) ν))
    (FAnd
      (basic_world_formula (<[ν := TBase (base_ty_of_const c)]> Σ) {[ν]})
      (fib_vars {[ν]}
        (FUnder (FAtom (lift_type_qualifier_to_logic
          (qual_open_atom 0 ν (mk_q_eq (vbvar 0) (vconst c)))))))).

Lemma const_over_body_fv_subset Σ c ν :
  formula_fv (const_over_body Σ c ν) ⊆ {[ν]}.
Proof.
  unfold const_over_body.
  intros z Hz. simpl in Hz.
  unfold stale, stale_logic_qualifier in Hz.
  rewrite fib_vars_singleton in Hz. simpl in Hz.
  unfold expr_logic_qual, qual_open_atom, mk_q_eq, qual_dom in Hz; simpl in Hz.
  destruct (decide (0 ∈ ({[0]} ∪ ∅ : gset nat))); simpl in Hz;
    unfold lift_type_qualifier_to_logic in Hz; simpl in Hz;
    unfold stale, stale_logic_qualifier in Hz; simpl in Hz;
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
    unfold lift_type_qualifier_to_logic in Hz; simpl in Hz;
    unfold stale, stale_logic_qualifier in Hz; simpl in Hz;
    set_solver.
Qed.

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

(** Kripke implication elimination at the current world. *)
Lemma res_models_impl_elim (m : WfWorld) (φ ψ : FormulaQ) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros [_ Himpl] Hφ.
  pose proof (res_models_with_store_fuel_irrel
    (formula_measure φ) (formula_measure φ + formula_measure ψ)
    ∅ m φ ltac:(lia) ltac:(simpl; lia) Hφ) as Hφ_big.
  pose proof (Himpl m ltac:(reflexivity) Hφ_big) as Hψ_big.
  eapply res_models_with_store_fuel_irrel; [| | exact Hψ_big]; simpl; lia.
Qed.

(** The environment-indexed context denotation always carries a reusable
    basic-world component.  Keeping these as named destructors avoids
    repeatedly unfolding the [FAnd] shape in fundamental-theorem cases. *)
Lemma denot_ctx_in_env_basic Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ basic_world_formula Σ (dom Σ).
Proof.
  unfold denot_ctx_in_env.
  apply res_models_and_elim_l.
Qed.

Lemma denot_ctx_in_env_ctx Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  m ⊨ denot_ctx_under (erase_ctx_under Σ Γ) Γ.
Proof.
  unfold denot_ctx_in_env.
  apply res_models_and_elim_r.
Qed.

Lemma denot_ctx_in_env_world_has_type Σ Γ m :
  m ⊨ denot_ctx_in_env Σ Γ →
  world_has_type_on Σ (dom Σ) (res_restrict m (dom Σ)).
Proof.
  intros HΓ.
  apply basic_world_formula_current.
  apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
Qed.

Lemma denot_ctx_in_env_world_has_type_on Σ Γ X m :
  X ⊆ dom Σ →
  m ⊨ denot_ctx_in_env Σ Γ →
  world_has_type_on Σ X (res_restrict m X).
Proof.
  intros HXΣ HΓ.
  eapply basic_world_formula_subset_current; [exact HXΣ |].
  apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
Qed.

Lemma denot_ctx_in_env_store_typed Σ Γ m σ :
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  store_has_type_on Σ (dom Σ) (store_restrict σ (dom Σ)).
Proof.
  intros HΓ Hσ.
  eapply basic_world_formula_store_restrict_typed.
  - apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
  - exact Hσ.
Qed.

Lemma denot_ctx_in_env_store_restrict_closed Σ Γ m σ :
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  closed_env (store_restrict σ (dom Σ)).
Proof.
  intros HΓ Hσ.
  eapply basic_world_formula_store_restrict_closed_env.
  - apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
  - set_solver.
  - exact Hσ.
Qed.

Lemma denot_ctx_in_env_store_restrict_lc Σ Γ m σ :
  m ⊨ denot_ctx_in_env Σ Γ →
  (m : World) σ →
  lc_env (store_restrict σ (dom Σ)).
Proof.
  intros HΓ Hσ.
  eapply basic_world_formula_store_restrict_lc_env.
  - apply denot_ctx_in_env_basic with (Γ := Γ). exact HΓ.
  - set_solver.
  - exact Hσ.
Qed.

(** The semantic-subtyping case of the fundamental theorem. *)
Lemma fundamental_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ1 τ2 : choice_ty) :
  choice_typing_wf Σ Γ e τ2 →
  sub_type_under Σ Γ τ1 τ2 →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 e.
Proof.
  intros Hwf Hsub IH m HΓ.
  destruct Hsub as [_ [_ [_ Hent]]].
  pose proof (choice_typing_wf_fv_tm_subset Σ Γ e τ2 Hwf) as Hfv.
  pose proof (Hent e Hfv m HΓ) as Himpl.
  eapply res_models_impl_elim; [exact Himpl |].
  apply IH. exact HΓ.
Qed.

(** The context-subtyping case of the fundamental theorem. *)
Lemma fundamental_ctx_sub_case
    (Φ : primop_ctx) (Σ : gmap atom ty) (Γ1 Γ2 : ctx) (e : tm) (τ : choice_ty) :
  ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
  (denot_ctx_in_env Σ Γ2 ⊫ denot_ty_in_ctx_under Σ Γ2 τ e) →
  denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ e.
Proof.
  intros Hsub IH m HΓ1.
  destruct Hsub as [_ [_ [Hagree Hrestrict]]].
  destruct (denot_ty_under_env_equiv
    (erase_ctx_under Σ Γ2) (erase_ctx_under Σ Γ1) τ e) as [H21 _].
  { intros z Hz. symmetry. apply Hagree. set_solver. }
  apply H21.
  eapply res_models_kripke.
  - apply res_restrict_le.
  - apply IH. apply Hrestrict. exact HΓ1.
Qed.

(** The variable case is exactly the singleton context denotation. *)
Lemma fundamental_var_case Σ (x : atom) (τ : choice_ty) :
  denot_ctx_in_env Σ (CtxBind x τ) ⊫
    denot_ty_in_ctx_under Σ (CtxBind x τ) τ (tret (vfvar x)).
Proof.
  intros m Hm.
  unfold denot_ctx_in_env in Hm.
  pose proof (res_models_and_elim_r m
    (basic_world_formula Σ (dom Σ))
    (denot_ctx_under (erase_ctx_under Σ (CtxBind x τ)) (CtxBind x τ))
    Hm) as Hbind.
  exact Hbind.
Qed.

Lemma fundamental_const_over_case Σ c :
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty
      (CTOver (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
      (tret (vconst c)).
Proof.
  intros m _.
  unfold denot_ty_in_ctx_under, denot_ty_under, denot_ty_avoiding.
  simpl.
  set (ν := fresh_for (∅ ∪ ∅ ∪ ∅ ∪ (∅ ∪ ∅))).
  change (m ⊨ FForall ν (const_over_body (erase_ctx_under Σ CtxEmpty) c ν)).
  eapply res_models_forall_intro.
  - unfold formula_scoped_in_world. intros z Hz.
    rewrite dom_empty_L in Hz.
    apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
    simpl in Hz.
    apply elem_of_difference in Hz as [Hzbody Hzν].
    pose proof (const_over_body_fv_subset (erase_ctx_under Σ CtxEmpty) c ν _ Hzbody)
      as Hzν'.
    set_solver.
  - exists (world_dom (m : World) ∪ {[ν]}). split; [set_solver |].
    intros y Hy m' Hdom Hrestr.
    eapply res_models_impl_intro.
    + apply const_over_body_rename_scoped.
      simpl. rewrite Hdom. set_solver.
    + intros m'' Hle Hexpr.
      apply const_over_consequent_from_renamed_expr.
      exact Hexpr.
Qed.

Lemma fundamental_const_under_case Σ c :
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty
      (CTUnder (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
      (tret (vconst c)).
Proof.
  intros m _.
  unfold denot_ty_in_ctx_under, denot_ty_under, denot_ty_avoiding.
  simpl.
  set (ν := fresh_for (∅ ∪ ∅ ∪ ∅ ∪ (∅ ∪ ∅))).
  change (m ⊨ FForall ν (const_under_body (erase_ctx_under Σ CtxEmpty) c ν)).
  eapply res_models_forall_intro.
  - unfold formula_scoped_in_world. intros z Hz.
    rewrite dom_empty_L in Hz.
    apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
    simpl in Hz.
    apply elem_of_difference in Hz as [Hzbody Hzν].
    pose proof (const_under_body_fv_subset (erase_ctx_under Σ CtxEmpty) c ν _ Hzbody)
      as Hzν'.
    set_solver.
  - exists (world_dom (m : World) ∪ {[ν]}). split; [set_solver |].
    intros y Hy m' Hdom Hrestr.
    eapply res_models_impl_intro.
    + apply const_under_body_rename_scoped.
      simpl. rewrite Hdom. set_solver.
    + intros m'' Hle Hexpr.
      apply const_under_consequent_from_renamed_expr.
      exact Hexpr.
Qed.

(** Constants need the first value-adequacy lemma for the new
    basic-world-aware refinement denotation: evaluating [tret c] at a fresh
    result coordinate produces a singleton world satisfying the opened
    equality qualifier. *)
Lemma fundamental_const_case Σ c :
  denot_ctx_in_env Σ CtxEmpty ⊫
    denot_ty_in_ctx_under Σ CtxEmpty (const_precise_ty c) (tret (vconst c)).
Proof.
  intros m HΓ.
  unfold const_precise_ty, precise_ty.
  eapply res_models_and_intro.
  - unfold formula_scoped_in_world. simpl. intros z Hz.
    assert (Hzφ : z ∈ formula_fv
      (denot_ty_in_ctx_under Σ CtxEmpty
        (CTInter
          (over_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
          (under_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
        (tret (vconst c)))) by set_solver.
    pose proof (denot_ty_under_formula_fv_subset
      (erase_ctx_under Σ CtxEmpty)
      (CTInter
        (over_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)))
        (under_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c))))
      (tret (vconst c)) z Hzφ) as Hfoot.
    simpl in Hfoot. set_solver.
  - apply fundamental_const_over_case. exact HΓ.
  - apply fundamental_const_under_case. exact HΓ.
Qed.

Lemma fundamental_let_case (Φ : primop_ctx) Σ Γ τ1 τ2 e1 e2 (L : aset) :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ2 (tlete e1 e2).
Proof. Admitted.

Lemma fundamental_letd_case (Φ : primop_ctx) Σ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 τ1 e1) →
  (∀ x, x ∉ L →
    denot_ctx_in_env Σ (CtxStar Γ2 (CtxBind x τ1)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ2 (CtxBind x τ1)) τ2 (e2 ^^ x)) →
  denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) τ2 (tlete e1 e2).
Proof. Admitted.

Lemma fundamental_lam_case (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx)) ({0 ~> y} τ) (e ^^ y)) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret (vlam (erase_ty τx) e)).
Proof. Admitted.

Lemma fundamental_lamd_case (Φ : primop_ctx) Σ Γ τx τ e (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx)) ({0 ~> y} τ) (e ^^ y)) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ) (tret (vlam (erase_ty τx) e)).
Proof. Admitted.

Lemma fundamental_app_case (Φ : primop_ctx) Σ Γ τx τ v1 x :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ (CTArrow τx τ) (tret v1)) →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τx (tret (vfvar x))) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof. Admitted.

Lemma fundamental_appd_case (Φ : primop_ctx) Σ Γ1 Γ2 τx τ v1 x :
  (denot_ctx_in_env Σ Γ1 ⊫ denot_ty_in_ctx_under Σ Γ1 (CTWand τx τ) (tret v1)) →
  (denot_ctx_in_env Σ Γ2 ⊫ denot_ty_in_ctx_under Σ Γ2 τx (tret (vfvar x))) →
  denot_ctx_in_env Σ (CtxStar Γ1 Γ2) ⊫
    denot_ty_in_ctx_under Σ (CtxStar Γ1 Γ2) ({0 ~> x} τ) (tapp v1 (vfvar x)).
Proof. Admitted.

Lemma fundamental_fix_case (Φ : primop_ctx) Σ Γ τx τ vf (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxComma Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxComma Γ (CtxBind y τx))
        (CTArrow (CTArrow τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTArrow τx τ)
      (tret (vfix (erase_ty (CTArrow τx τ)) vf)).
Proof. Admitted.

Lemma fundamental_fixd_case (Φ : primop_ctx) Σ Γ τx τ vf (L : aset) :
  (∀ y, y ∉ L →
    denot_ctx_in_env Σ (CtxStar Γ (CtxBind y τx)) ⊫
      denot_ty_in_ctx_under Σ (CtxStar Γ (CtxBind y τx))
        (CTWand (CTWand τx τ) ({0 ~> y} τ))
        (tret ({0 ~> vfvar y} vf))) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (CTWand τx τ)
      (tret (vfix (erase_ty (CTWand τx τ)) vf)).
Proof. Admitted.

Lemma fundamental_appop_case (Φ : primop_ctx) Σ Γ op x :
  wf_primop_sig op (Φ op) →
  choice_typing_wf Σ Γ
    (tprim op (vfvar x))
    ({0 ~> x} (primop_result_ty (Φ op))) →
  (denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ (primop_arg_ty (Φ op)) (tret (vfvar x))) →
  denot_ctx_in_env Σ Γ ⊫
    denot_ty_in_ctx_under Σ Γ ({0 ~> x} (primop_result_ty (Φ op))) (tprim op (vfvar x)).
Proof.
  intros Hwf Hchoice Harg m HΓ.
  set (sig := Φ op).
  set (τarg := primop_arg_ty sig).
  set (τres := primop_result_ty sig).
  pose proof (wf_primop_semantic op (Φ op) Hwf x) as [Hop _].
  assert (Harg_empty : fv_cty τarg ⊆ ∅).
  {
    subst τarg sig.
    eapply basic_choice_ty_fv_subset.
    apply wf_primop_sig_arg_basic with (op := op). exact Hwf.
  }
  assert (Harg_single :
    m ⊨ denot_ty_in_ctx (CtxBind x τarg) τarg (tret (vfvar x))).
  {
    destruct (denot_ty_under_env_equiv
      (erase_ctx_under Σ Γ) (erase_ctx (CtxBind x τarg)) τarg
      (tret (vfvar x))) as [Henv _].
    { intros z Hz. pose proof (Harg_empty z Hz). set_solver. }
    apply Henv. subst τarg sig. apply Harg. exact HΓ.
  }
  assert (Hsingle_ctx : m ⊨ ⟦CtxBind x τarg⟧).
  { apply denot_ctx_bind. exact Harg_single. }
  pose proof (Hop m Hsingle_ctx) as Hres_single.
  assert (Hx_lookup : erase_ctx_under Σ Γ !! x = Some (erase_ty τarg)).
  {
    destruct Hchoice as [_ Herase].
    subst τarg τres sig.
    simpl in Herase.
    inversion Herase; subst.
    pose proof (wf_primop_sig_erased_bases op (Φ op) Hwf) as HopErase.
    rewrite HopErase in H3. inversion H3; subst.
    inversion H4; subst. simpl. exact H1.
  }
  assert (Hres_fv : fv_cty ({0 ~> x} τres) ⊆ {[x]}).
  {
    pose proof (cty_open_fv_subset 0 x τres) as Hopen.
    assert (fv_cty τres ⊆ ∅).
    {
      subst τres sig.
      eapply basic_choice_ty_fv_subset.
      apply wf_primop_sig_result_basic with (op := op). exact Hwf.
    }
    set_solver.
  }
  destruct (denot_ty_under_env_equiv
    (erase_ctx (CtxBind x τarg)) (erase_ctx_under Σ Γ) ({0 ~> x} τres)
    (tprim op (vfvar x))) as [Hres_env _].
  {
    intros z Hz.
    pose proof (Hres_fv z Hz) as Hzx.
    apply elem_of_singleton in Hzx. subst z.
    subst τarg. simpl in Hx_lookup. simpl.
    rewrite lookup_singleton_eq. symmetry. exact Hx_lookup.
  }
  subst τres sig. apply Hres_env. exact Hres_single.
Qed.

Lemma fundamental_match_both_case (Φ : primop_ctx) Σ Γt Γf v τt τf et ef :
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt (bool_precise_ty true) (tret v)) →
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf (bool_precise_ty false) (tret v)) →
  (denot_ctx_in_env Σ Γt ⊫ denot_ty_in_ctx_under Σ Γt τt et) →
  (denot_ctx_in_env Σ Γf ⊫ denot_ty_in_ctx_under Σ Γf τf ef) →
  denot_ctx_in_env Σ (CtxSum Γt Γf) ⊫
    denot_ty_in_ctx_under Σ (CtxSum Γt Γf) (CTSum τt τf) (tmatch v et ef).
Proof. Admitted.

Lemma fundamental_match_true_case (Φ : primop_ctx) Σ Γ v τ et ef :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ (bool_precise_ty true) (tret v)) →
  branch_unreachable Σ Γ v false →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ et) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof. Admitted.

Lemma fundamental_match_false_case (Φ : primop_ctx) Σ Γ v τ et ef :
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ (bool_precise_ty false) (tret v)) →
  branch_unreachable Σ Γ v true →
  (denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ ef) →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ (tmatch v et ef).
Proof. Admitted.

(** ** Fundamental theorem *)

Theorem Fundamental (Φ : primop_ctx) (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : choice_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ Σ Γ e τ →
  denot_ctx_in_env Σ Γ ⊫ denot_ty_in_ctx_under Σ Γ τ e.
Proof.
  intros HΦ Hty.
  induction Hty; eauto using fundamental_var_case, fundamental_const_case.
  - eapply fundamental_sub_case; eauto.
  - eapply fundamental_ctx_sub_case; eauto.
  - eapply fundamental_let_case; eauto.
  - eapply fundamental_letd_case; eauto.
  - eapply fundamental_lam_case; eauto.
  - eapply fundamental_lamd_case; eauto.
  - eapply fundamental_app_case; eauto.
  - eapply fundamental_appd_case; eauto.
  - eapply fundamental_fix_case; eauto.
  - eapply fundamental_fixd_case; eauto.
  - eapply fundamental_appop_case; eauto.
  - eapply fundamental_match_both_case; eauto.
  - eapply fundamental_match_true_case; eauto.
  - eapply fundamental_match_false_case; eauto.
Qed.

(** ** Corollaries

    The theorem statements follow the single typing judgment.  The proof
    bodies remain as admitted skeletons while the definition layer is being
    aligned with the paper. *)

Corollary safety (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTOver b qual_top) →
  ∀ e', steps e e' → is_val e' ∨ ∃ e'', step e' e''.
Proof. Admitted.

Corollary coverage (Φ : primop_ctx) (e : tm) (b : base_ty) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTUnder b qual_top) →
  ∃ v, steps e (tret v).
Proof. Admitted.

Corollary refinement (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTOver b φ) →
  ∀ v, steps e (tret v) →
       ∃ x, qual_interp {[x := v]} (φ ^q^ x).
Proof. Admitted.

Corollary incorrectness (Φ : primop_ctx) (e : tm) (b : base_ty) (φ : type_qualifier) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTUnder b φ) →
  ∃ v x, steps e (tret v) ∧ qual_interp {[x := v]} (φ ^q^ x).
Proof. Admitted.

Corollary exact_result (Φ : primop_ctx) (e : tm) (b : base_ty) (c : constant) :
  wf_primop_ctx Φ →
  has_choice_type Φ ∅ CtxEmpty e (CTUnder b (b0:c= c)) →
  steps e (tret (vconst c)).
Proof. Admitted.

(** ** Structural soundness lemmas *)

Lemma denot_ctx_comma_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_comma. Qed.

Lemma denot_ctx_comma_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_under Σ Γ1 ∧ m ⊨ denot_ctx_under Σ Γ2.
Proof. apply denot_ctx_under_comma. Qed.

Lemma denot_ctx_in_env_comma_agree Σ Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1)
    (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1) →
  ty_env_agree_on (ctx_stale Γ2)
    (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2) →
  m ⊨ denot_ctx_in_env Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_in_env Σ Γ1 ∧ m ⊨ denot_ctx_in_env Σ Γ2.
Proof.
  intros Hagree1 Hagree2.
  unfold denot_ctx_in_env.
  split.
  - intros Hm.
    pose proof (res_models_and_elim_l m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ (CtxComma Γ1 Γ2))
        (CtxComma Γ1 Γ2)) Hm) as Hbasic.
    pose proof (res_models_and_elim_r m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ (CtxComma Γ1 Γ2))
        (CtxComma Γ1 Γ2)) Hm) as Hctx.
    apply denot_ctx_under_comma in Hctx as [HΓ1 HΓ2].
    split.
    + eapply res_models_and_intro.
      * unfold formula_scoped_in_world in *. simpl in *.
        pose proof (res_models_with_store_fuel_scoped _
          ∅ m (basic_world_formula Σ (dom Σ)) Hbasic).
        destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1)
          Γ1 Hagree1) as [Hequiv _].
        pose proof (Hequiv m HΓ1) as HΓ1'.
        pose proof (res_models_with_store_fuel_scoped _
          ∅ m (denot_ctx_under (erase_ctx_under Σ Γ1) Γ1) HΓ1').
        set_solver.
      * exact Hbasic.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1)
          Γ1 Hagree1) as [Hequiv _].
        apply Hequiv. exact HΓ1.
    + eapply res_models_and_intro.
      * unfold formula_scoped_in_world in *. simpl in *.
        pose proof (res_models_with_store_fuel_scoped _
          ∅ m (basic_world_formula Σ (dom Σ)) Hbasic).
        destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2)
          Γ2 Hagree2) as [Hequiv _].
        pose proof (Hequiv m HΓ2) as HΓ2'.
        pose proof (res_models_with_store_fuel_scoped _
          ∅ m (denot_ctx_under (erase_ctx_under Σ Γ2) Γ2) HΓ2').
        set_solver.
      * exact Hbasic.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2)
          Γ2 Hagree2) as [Hequiv _].
        apply Hequiv. exact HΓ2.
  - intros [HΓ1 HΓ2].
    pose proof (res_models_and_elim_l m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ Γ1) Γ1) HΓ1) as Hbasic.
    pose proof (res_models_and_elim_r m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ Γ1) Γ1) HΓ1) as Hctx1.
    pose proof (res_models_and_elim_r m
      (basic_world_formula Σ (dom Σ))
      (denot_ctx_under (erase_ctx_under Σ Γ2) Γ2) HΓ2) as Hctx2.
    eapply res_models_and_intro.
    + unfold formula_scoped_in_world in *. simpl in *.
      pose proof (res_models_with_store_fuel_scoped _
        ∅ m (basic_world_formula Σ (dom Σ)) Hbasic) as Hscope_basic.
      destruct (denot_ctx_under_env_equiv
        (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1)
        Γ1 Hagree1) as [_ H1].
      destruct (denot_ctx_under_env_equiv
        (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2)
        Γ2 Hagree2) as [_ H2].
      pose proof (H1 m Hctx1) as Hctx1'.
      pose proof (H2 m Hctx2) as Hctx2'.
      pose proof (proj2 (denot_ctx_under_comma
        (erase_ctx_under Σ (CtxComma Γ1 Γ2)) Γ1 Γ2 m)
        (conj Hctx1' Hctx2')) as Hcomma.
      pose proof (res_models_with_store_fuel_scoped _
        ∅ m (denot_ctx_under (erase_ctx_under Σ (CtxComma Γ1 Γ2))
          (CtxComma Γ1 Γ2)) Hcomma) as Hscope_comma.
      intros z Hz.
      rewrite dom_empty_L in Hz.
      apply elem_of_union in Hz as [Hzempty | Hz].
      { exfalso. set_solver. }
      apply elem_of_union in Hz as [Hzbasic | Hzcomma].
      * apply Hscope_basic. apply elem_of_union. right. exact Hzbasic.
      * apply Hscope_comma. apply elem_of_union. right. exact Hzcomma.
    + exact Hbasic.
    + apply denot_ctx_under_comma. split.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ1)
          Γ1 Hagree1) as [_ Hequiv].
        apply Hequiv. exact Hctx1.
      * destruct (denot_ctx_under_env_equiv
          (erase_ctx_under Σ (CtxComma Γ1 Γ2)) (erase_ctx_under Σ Γ2)
          Γ2 Hagree2) as [_ Hequiv].
        apply Hequiv. exact Hctx2.
Qed.

Lemma denot_ctx_star_split (Γ1 Γ2 : ctx) (m : WfWorld) :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_star. Qed.

Lemma denot_ctx_star_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof. apply denot_ctx_under_star. Qed.

Lemma denot_ctx_sum_split_under Σ (Γ1 Γ2 : ctx) (m : WfWorld) :
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof. apply denot_ctx_under_sum. Qed.

Lemma res_models_exists_intro (m : WfWorld) (x : atom) (φ : FormulaQ) :
  formula_scoped_in_world ∅ m (FExists x φ) →
  (∃ L : aset,
    world_dom m ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom m' = world_dom m ∪ {[y]} ∧
        res_restrict m' (world_dom m) = m ∧
        m' ⊨ formula_rename_atom x y φ) →
  m ⊨ FExists x φ.
Proof.
  unfold res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hexists]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hφ]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  eapply res_models_with_store_fuel_irrel; [| | exact Hφ];
    rewrite ?formula_rename_preserves_measure; simpl; lia.
Qed.

Lemma ctx_res_models_mono (Γ : ctx) (m m' : WfWorld) :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof.
  intros Hmodel Hle.
  eapply res_models_kripke; eauto.
Qed.
