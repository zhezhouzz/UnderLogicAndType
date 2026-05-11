(** * ChoiceType.DenotationExprProps

    Auxiliary expression-result lemmas used by type denotation. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceType Require Export DenotationResultBridge.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

Definition FLetResult (e1 e2 : tm) (ν : atom) : FQ :=
  let x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}) in
  FExists x
    (FAnd
      (FExprResultOn (fv_tm e1) e1 x)
      (FFib x (FExprResultOn (fv_tm (e2 ^^ x)) (e2 ^^ x) ν))).

(** [FLetResult] remains a useful auxiliary formula for examples and local
    decompositions, but the operational bridge for [tlete] is handled at the
    Rocq predicate level by [expr_result_in_world_let_elim] and
    [expr_result_in_world_let_intro].  This avoids forcing a precise
    expression-result relation through [FAtom]'s upward-closed semantics. *)

Lemma FExprResultOn_expr_fv e ν :
  formula_fv (FExprResultOn (fv_tm e) e ν) = fv_tm e ∪ {[ν]}.
Proof.
  apply FExprResultOn_fv.
Qed.

Lemma FLetResult_fv_subset e1 e2 ν :
  formula_fv (FLetResult e1 e2 ν) ⊆ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}.
Proof.
  unfold FLetResult.
  set (x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  simpl. rewrite !FExprResultOn_expr_fv.
  pose proof (open_fv_tm e2 (vfvar x) 0) as Hopen.
  set_solver.
Qed.

Lemma FLetResultOn_scoped_intro X e1 e2 ν (m : WfWorld) :
  X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]} ⊆ world_dom (m : World) →
  formula_scoped_in_world ∅ m (FLetResultOn X e1 e2 ν).
Proof.
  intros Hdom z Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  pose proof (FLetResultOn_fv_subset X e1 e2 ν z Hz) as Hz'.
  apply Hdom. exact Hz'.
Qed.

Lemma FExprResultOn_scoped_intro X e ν (m : WfWorld) :
  X ∪ {[ν]} ⊆ world_dom (m : World) →
  formula_scoped_in_world ∅ m (FExprResultOn X e ν).
Proof.
  intros Hdom z Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  rewrite FExprResultOn_fv in Hz.
  apply Hdom. exact Hz.
Qed.

Lemma FLetResult_expr_scope_from_basic Σ X e1 e2 ν m :
  fv_tm e1 ∪ fv_tm e2 ∪ {[ν]} ⊆ X →
  m ⊨ FAnd (basic_world_formula Σ X) (FLetResult e1 e2 ν) →
  formula_scoped_in_world ∅ m (FExprResultOn X (tlete e1 e2) ν).
Proof.
Admitted.

Lemma FLetResult_models_elim e1 e2 ν m :
  m ⊨ FLetResult e1 e2 ν →
  ∃ L : aset,
    world_dom (m : World) ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom (m' : World) = world_dom (m : World) ∪ {[y]} ∧
        res_restrict m' (world_dom (m : World)) = m ∧
        m' ⊨ formula_rename_atom
          (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) y
          (FAnd
            (FExprResultOn (fv_tm e1) e1 (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})))
            (FFib (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}))
              (FExprResultOn
                (fv_tm (e2 ^^ fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})))
                (e2 ^^ fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) ν))).
Proof.
  unfold FLetResult.
  set (x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  set (body :=
    FAnd (FExprResultOn (fv_tm e1) e1 x)
      (FFib x (FExprResultOn (fv_tm (e2 ^^ x)) (e2 ^^ x) ν))).
  change (res_models_with_store (∅ : Store) m (FExists x body) →
    ∃ L : aset,
      world_dom (m : World) ⊆ L ∧
      ∀ y : atom,
        y ∉ L →
        ∃ m' : WfWorld,
          world_dom (m' : World) = world_dom (m : World) ∪ {[y]} ∧
          res_restrict m' (world_dom (m : World)) = m ∧
          res_models_with_store (∅ : Store) m' (formula_rename_atom x y body)).
  unfold res_models_with_store. simpl.
  intros [Hscope [L [HL Hcof]]].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hcof y Hy) as [m' [Hdom [Hrestrict Hmodel]]].
  exists m'. split; [exact Hdom |].
  split; [exact Hrestrict |].
  change (res_models_with_store (∅ : Store) m' (formula_rename_atom x y body)).
  unfold res_models_with_store.
  change (res_models_with_store_fuel (formula_measure body)
    (∅ : Store) m' (formula_rename_atom x y body)) in Hmodel.
  models_fuel_irrel Hmodel.
Qed.

Lemma FLetResult_models_intro e1 e2 ν m :
  formula_scoped_in_world ∅ m (FLetResult e1 e2 ν) →
  (∃ L : aset,
    world_dom (m : World) ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom (m' : World) = world_dom (m : World) ∪ {[y]} ∧
        res_restrict m' (world_dom (m : World)) = m ∧
        m' ⊨ formula_rename_atom
          (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) y
          (FAnd
            (FExprResultOn (fv_tm e1) e1 (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})))
            (FFib (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}))
              (FExprResultOn
                (fv_tm (e2 ^^ fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})))
                (e2 ^^ fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) ν)))) →
  m ⊨ FLetResult e1 e2 ν.
Proof.
  unfold FLetResult.
  set (x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  set (body :=
    FAnd (FExprResultOn (fv_tm e1) e1 x)
      (FFib x (FExprResultOn (fv_tm (e2 ^^ x)) (e2 ^^ x) ν))).
  change (formula_scoped_in_world (∅ : Store) m (FExists x body) →
    (∃ L : aset,
      world_dom (m : World) ⊆ L ∧
      ∀ y : atom,
        y ∉ L →
        ∃ m' : WfWorld,
          world_dom (m' : World) = world_dom (m : World) ∪ {[y]} ∧
          res_restrict m' (world_dom (m : World)) = m ∧
          res_models_with_store (∅ : Store) m' (formula_rename_atom x y body)) →
    res_models_with_store (∅ : Store) m (FExists x body)).
  unfold res_models_with_store. simpl.
  intros Hscope [L [HL Hcof]].
  split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hcof y Hy) as [m' [Hdom [Hrestrict Hmodel]]].
  exists m'. split; [exact Hdom |].
  split; [exact Hrestrict |].
  unfold res_models_with_store in Hmodel.
  change (res_models_with_store_fuel (formula_measure (formula_rename_atom x y body))
    (∅ : Store) m' (formula_rename_atom x y body)) in Hmodel.
  change (res_models_with_store_fuel (formula_measure body)
    (∅ : Store) m' (formula_rename_atom x y body)).
  models_fuel_irrel Hmodel.
Qed.

Lemma expr_logic_qual_renamed_result_steps e x y ρ w σw :
  x ∉ stale e →
  y ∉ stale e →
  closed_env ρ →
  closed_env σw →
  logic_qualifier_denote (lqual_swap x y (expr_logic_qual e x)) ρ w →
  (res_restrict w (stale e ∪ {[y]}) : World) σw →
  ∃ v, σw !! y = Some v ∧ steps (m{σw} (m{ρ} e)) (tret v).
Proof.
Admitted.

Lemma expr_logic_qual_renamed_open_steps e x y ν ρ w σw vx :
  x ∉ stale e →
  y ∉ stale e →
  ν ≠ x →
  ν ≠ y →
  closed_env ρ →
  lc_env ρ →
  ρ !! y = Some vx →
  closed_env σw →
  stale vx = ∅ →
  lc_value vx →
  logic_qualifier_denote (lqual_swap x y (expr_logic_qual (e ^^ x) ν)) ρ w →
  (res_restrict w (aset_swap x y (stale (e ^^ x) ∪ {[ν]})) : World) σw →
  ∃ v, σw !! ν = Some v ∧
    steps (m{σw} (open_tm 0 vx (m{delete y ρ} e))) (tret v).
Proof.
Admitted.

Lemma expr_logic_qual_ret_closed_value_denote_lookup v ν w σ :
  stale v = ∅ →
  logic_qualifier_denote (expr_logic_qual (tret v) ν) ∅ w →
  (res_restrict w {[ν]} : World) σ →
  σ !! ν = Some v.
Proof.
  intros Hvclosed Hden Hσ.
  unfold logic_qualifier_denote, expr_logic_qual in Hden. simpl in Hden.
  rewrite store_restrict_empty in Hden.
  assert (Hσproj : (res_restrict (res_restrict w {[ν]}) {[ν]} : World) σ).
  {
    exists σ. split; [exact Hσ |].
    apply store_restrict_idemp.
    pose proof (wfworld_store_dom (res_restrict w {[ν]}) σ Hσ) as Hdomσ.
    simpl in Hdomσ. set_solver.
  }
  pose proof (expr_result_in_world_sound ∅ (tret v) ν
    (res_restrict w {[ν]}) σ Hden Hσproj) as Hstore.
  destruct (expr_result_store_lookup ν (subst_map ∅ (tret v)) σ Hstore)
    as [v' [Hlookup Hsteps]].
  change (subst_map ∅ (tret v)) with (m{∅} (tret v)) in Hsteps.
  rewrite msubst_empty in Hsteps.
  pose proof (value_steps_self v (tret v') Hsteps) as Heq.
  inversion Heq. subst v'. exact Hlookup.
Qed.

Lemma expr_logic_qual_ret_value_denote_lookup v ν w σ :
  logic_qualifier_denote (expr_logic_qual (tret v) ν) ∅ w →
  (res_restrict w (stale v ∪ {[ν]}) : World) σ →
  σ !! ν = Some (m{σ} v).
Proof.
  intros Hden Hσ.
  set (σν := store_restrict σ {[ν]}).
  assert (Hσν : (res_restrict w {[ν]} : World) σν).
  {
    destruct Hσ as [σw [Hσw Hrestrict]].
    exists σw. split; [exact Hσw |].
    subst σν.
    rewrite <- Hrestrict.
    rewrite store_restrict_restrict.
    replace ((stale v ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
    reflexivity.
  }
  unfold logic_qualifier_denote, expr_logic_qual in Hden. simpl in Hden.
  rewrite store_restrict_empty in Hden.
  assert (Hσνproj : (res_restrict (res_restrict w {[ν]}) {[ν]} : World) σν).
  {
    exists σν. split; [exact Hσν |].
    apply store_restrict_idemp.
    pose proof (wfworld_store_dom (res_restrict w {[ν]}) σν Hσν) as Hdomσν.
    simpl in Hdomσν. set_solver.
  }
  pose proof (expr_result_in_world_sound ∅ (tret v) ν
    (res_restrict w {[ν]}) σν Hden Hσνproj) as Hstore.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret v)) σν Hstore)
    as [v' [Hσν_eq [Hv'_closed [_ Hsteps]]]].
  change (subst_map ∅ (tret v)) with (m{∅} (tret v)) in Hsteps.
  rewrite msubst_empty in Hsteps.
  pose proof (value_steps_self v (tret v') Hsteps) as Heq.
  inversion Heq. subst v'.
  assert (Hvclosed : stale v = ∅) by exact Hv'_closed.
  rewrite (msubst_fresh σ v) by (rewrite Hvclosed; set_solver).
  assert (Hlookupν : σν !! ν = Some v).
  {
    rewrite Hσν_eq.
    change (({[ν := v]} : Store) !! ν = Some v).
    rewrite lookup_singleton. rewrite decide_True by reflexivity.
    reflexivity.
  }
  subst σν.
  apply store_restrict_lookup_some in Hlookupν as [_ Hlookupν].
  exact Hlookupν.
Qed.

Lemma expr_logic_qual_ret_closed_value_lookup v ν m :
  stale v = ∅ →
  m ⊨ FAtom (expr_logic_qual (tret v) ν) →
  ∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some v.
Proof.
  intros Hvclosed Hmodel σ Hσ.
  unfold res_models, res_models_with_store in Hmodel. simpl in Hmodel.
  destruct Hmodel as [_ [m0 [_ [Hqual Hle]]]].
  assert (Hνm0 : {[ν]} ⊆ world_dom (m0 : World)).
  {
    destruct (wf_ne _ (world_wf (res_restrict m0 {[ν]}))) as [σ0 Hσ0].
    pose proof (expr_logic_qual_ret_closed_value_denote_lookup
      v ν m0 σ0 Hvclosed Hqual Hσ0) as Hν.
    pose proof (wfworld_store_dom (res_restrict m0 {[ν]}) σ0 Hσ0) as Hdomσ0.
    intros z Hz. apply elem_of_singleton in Hz. subst z.
    assert (Hνdomσ0 : ν ∈ dom σ0).
    { apply elem_of_dom. eexists. exact Hν. }
    rewrite Hdomσ0 in Hνdomσ0. simpl in Hνdomσ0. set_solver.
  }
  assert (Hrestrict_eq : res_restrict m {[ν]} = res_restrict m0 {[ν]}).
  { symmetry. apply res_restrict_le_eq; [exact Hle | exact Hνm0]. }
  assert (Hσm0 : (res_restrict m0 {[ν]} : World) σ).
  { rewrite <- Hrestrict_eq. exact Hσ. }
  exact (expr_logic_qual_ret_closed_value_denote_lookup
    v ν m0 σ Hvclosed Hqual Hσm0).
Qed.

Lemma expr_logic_qual_ret_const_lookup c ν m :
  m ⊨ FAtom (expr_logic_qual (tret (vconst c)) ν) →
  ∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some (vconst c).
Proof.
  apply expr_logic_qual_ret_closed_value_lookup.
  reflexivity.
Qed.

Lemma foldr_fib_vars_acc_fst xs φ R :
  fst (foldr fib_vars_acc_step (φ, R) xs) = foldr FFib φ xs.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite <- IH. destruct (foldr fib_vars_acc_step (φ, R) xs); reflexivity.
Qed.

Lemma foldr_fib_ret_const_lookup xs X c ν ρ m :
  res_models_with_store ρ m
    (foldr FFib (FAtom (expr_logic_qual_on X (tret (vconst c)) ν)) xs) →
  ∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some (vconst c).
Proof.
  revert ρ m.
  induction xs as [|x xs IH]; simpl; intros ρ m Hm σν Hσν.
  - pose proof (FAtom_expr_logic_qual_on_exact
      X (tret (vconst c)) ν ρ m Hm) as Hexact.
    pose proof (expr_result_in_world_sound
      (store_restrict ρ X) (tret (vconst c)) ν m σν Hexact Hσν) as Hstore.
    destruct (expr_result_store_elim ν
      (subst_map (store_restrict ρ X) (tret (vconst c))) σν Hstore)
      as [v [Hσν_eq [_ [_ Hsteps]]]].
    change (subst_map (store_restrict ρ X) (tret (vconst c))) with
      (m{store_restrict ρ X} (tret (vconst c))) in Hsteps.
    rewrite msubst_ret in Hsteps.
    rewrite (msubst_fresh (store_restrict ρ X) (vconst c)) in Hsteps
      by (simpl; set_solver).
    pose proof (val_steps_self (vconst c) (tret v) Hsteps) as Hret.
    injection Hret as Hv. subst v.
    rewrite Hσν_eq, lookup_singleton, decide_True by reflexivity.
    reflexivity.
  - unfold res_models_with_store in Hm. simpl in Hm.
    destruct Hm as [_ [_ Hfib]].
    destruct Hσν as [σw [Hσw Hσν]].
    set (σx := store_restrict σw {[x]}).
    assert (Hprojx : res_restrict m {[x]} σx).
    {
      exists σw. split; [exact Hσw | reflexivity].
    }
    specialize (Hfib σx Hprojx).
    eapply IH.
    + models_fuel_irrel Hfib.
    + exists σw. split.
      * apply res_fiber_from_projection_member; [exact Hσw | reflexivity].
      * exact Hσν.
Qed.

Lemma expr_logic_qual_on_ret_const_lookup X c ν m :
  m ⊨ FExprResultOn X (tret (vconst c)) ν →
  ∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some (vconst c).
Proof.
Admitted.

Lemma expr_logic_qual_ret_fvar_denote_lookup x ν w σ vx :
  logic_qualifier_denote (expr_logic_qual (tret (vfvar x)) ν) ∅ w →
  (res_restrict w ({[x]} ∪ {[ν]}) : World) σ →
  closed_env σ →
  σ !! x = Some vx →
  σ !! ν = Some vx.
Proof.
  intros Hden Hσ _ _.
  exfalso.
  set (σν := store_restrict σ {[ν]}).
  assert (Hσν : (res_restrict w {[ν]} : World) σν).
  {
    destruct Hσ as [σw [Hσw Hrestrict]].
    exists σw. split; [exact Hσw |].
    subst σν.
    rewrite <- Hrestrict.
    rewrite store_restrict_restrict.
    replace (({[x]} ∪ {[ν]}) ∩ {[ν]}) with ({[ν]} : aset) by set_solver.
    reflexivity.
  }
  unfold logic_qualifier_denote, expr_logic_qual in Hden. simpl in Hden.
  rewrite store_restrict_empty in Hden.
  assert (Hσνproj : (res_restrict (res_restrict w {[ν]}) {[ν]} : World) σν).
  {
    exists σν. split; [exact Hσν |].
    apply store_restrict_idemp.
    pose proof (wfworld_store_dom (res_restrict w {[ν]}) σν Hσν) as Hdomσν.
    simpl in Hdomσν. set_solver.
  }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν
    (res_restrict w {[ν]}) σν Hden Hσνproj) as Hstore.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hstore)
    as [v [-> [Hv_closed [_ Hsteps]]]].
  change (subst_map ∅ (tret (vfvar x))) with (m{∅} (tret (vfvar x))) in Hsteps.
  rewrite msubst_empty in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_closed. set_solver.
Qed.

(** ** Type measure for denotation fuel

    As in HATs' denotation, the first argument of [denot_ty_fuel] is an
    over-approximation of the syntactic size of the type.  This lets the
    denotation recurse on opened locally-nameless bodies such as
    [{0 ~> x} τ], which are not syntactic subterms accepted by Rocq's
    structural termination checker. *)
