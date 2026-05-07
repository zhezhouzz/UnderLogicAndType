(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    [expr_logic_qual], and type qualifiers are embedded through
    [lift_type_qualifier_to_logic] after they have been opened to closed
    atom-based qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceType Require Export Syntax.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Local abbreviation for the ChoiceType formula instantiation.  The exported
    name from [Prelude] is [FormulaQ]. *)
Local Notation FQ := FormulaQ.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Logic atoms and fresh variable helpers for denotation *)

Definition fib_vars (X : aset) (p : FQ) : FQ :=
  set_fold FFib p X.

Lemma fib_vars_singleton x p :
  fib_vars {[x]} p = FFib x p.
Proof. unfold fib_vars. apply set_fold_singleton. Qed.

Lemma fib_vars_formula_fv_subset X p :
  formula_fv (fib_vars X p) ⊆ X ∪ formula_fv p.
Proof.
  unfold fib_vars.
  apply (set_fold_ind_L (fun r Y => formula_fv r ⊆ Y ∪ formula_fv p));
    simpl; set_solver.
Qed.

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σw,
    (w : World) σw →
    ∃ v,
      σw !! ν = Some v ∧
      subst_map σw (subst_map ρ e) →* tret v.

Definition expr_logic_qual (e : tm) (ν : atom) : logic_qualifier :=
  lqual (stale e ∪ {[ν]}) (fun σ w => expr_result_in_world σ e ν w).

Definition FExprResult (e : tm) (ν : atom) : FQ :=
  FAtom (expr_logic_qual e ν).

Lemma expr_result_in_world_let_elim ρ e1 e2 ν (w : WfWorld) :
  expr_result_in_world ρ (tlete e1 e2) ν w →
  ∀ σw,
    (w : World) σw →
    ∃ v vx,
      σw !! ν = Some v ∧
      subst_map σw (subst_map ρ e1) →* tret vx ∧
      open_tm 0 vx (subst_map σw (subst_map ρ e2)) →* tret v.
Proof.
  intros Hres σw Hσw.
  destruct (Hres σw Hσw) as [v [Hν Hsteps]].
  exists v.
  change (subst_map σw (subst_map ρ (tlete e1 e2)) →* tret v) in Hsteps.
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)) in Hsteps.
  rewrite (msubst_lete ρ e1 e2) in Hsteps.
  change (subst_map σw (tlete (m{ρ} e1) (m{ρ} e2)))
    with (m{σw} (tlete (m{ρ} e1) (m{ρ} e2))) in Hsteps.
  rewrite (msubst_lete σw (m{ρ} e1) (m{ρ} e2)) in Hsteps.
  apply reduction_lete in Hsteps as [vx [He1 He2]].
  exists vx. repeat split; assumption.
Qed.

Lemma expr_result_in_world_let_intro ρ e1 e2 ν (w : WfWorld) :
  (∀ σw,
    (w : World) σw →
    ∃ v vx,
      σw !! ν = Some v ∧
      body_tm (subst_map σw (subst_map ρ e2)) ∧
      subst_map σw (subst_map ρ e1) →* tret vx ∧
      open_tm 0 vx (subst_map σw (subst_map ρ e2)) →* tret v) →
  expr_result_in_world ρ (tlete e1 e2) ν w.
Proof.
  intros Hres σw Hσw.
  destruct (Hres σw Hσw) as [v [vx [Hν [Hbody [He1 He2]]]]].
  exists v. split; [exact Hν |].
  change (subst_map σw (subst_map ρ (tlete e1 e2)) →* tret v).
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)).
  rewrite (msubst_lete ρ e1 e2).
  change (subst_map σw (tlete (m{ρ} e1) (m{ρ} e2)))
    with (m{σw} (tlete (m{ρ} e1) (m{ρ} e2))).
  rewrite (msubst_lete σw (m{ρ} e1) (m{ρ} e2)).
  eapply reduction_lete_intro; eauto.
Qed.

Lemma FExprResult_models_elim e ν m :
  m ⊨ FExprResult e ν →
  ∃ w : WfWorld,
    expr_result_in_world
      (store_restrict ∅ (stale e ∪ {[ν]})) e ν
      (res_restrict w (stale e ∪ {[ν]})) ∧
    w ⊑ m.
Proof.
  unfold FExprResult, res_models, res_models_with_store.
  simpl. intros [_ [w [Hres Hle]]].
  exists w. split; [exact Hres | exact Hle].
Qed.

Lemma FExprResult_models_intro e ν m w :
  formula_scoped_in_world ∅ m (FExprResult e ν) →
  expr_result_in_world
    (store_restrict ∅ (stale e ∪ {[ν]})) e ν
    (res_restrict w (stale e ∪ {[ν]})) →
  w ⊑ m →
  m ⊨ FExprResult e ν.
Proof.
  unfold FExprResult, res_models, res_models_with_store.
  simpl. intros Hscope Hres Hle.
  split; [exact Hscope |].
  exists w. split; [exact Hres | exact Hle].
Qed.

Lemma FExprResult_models_from_result_inclusion e1 e2 ν m :
  formula_scoped_in_world ∅ m (FExprResult e1 ν) →
  (∀ w,
    expr_result_in_world
      (store_restrict ∅ (stale e2 ∪ {[ν]})) e2 ν
      (res_restrict w (stale e2 ∪ {[ν]})) →
    expr_result_in_world
      (store_restrict ∅ (stale e1 ∪ {[ν]})) e1 ν
      (res_restrict w (stale e1 ∪ {[ν]}))) →
  m ⊨ FExprResult e2 ν →
  m ⊨ FExprResult e1 ν.
Proof.
  intros Hscope Hincl Hexpr.
  destruct (FExprResult_models_elim e2 ν m Hexpr) as [w [Hres Hle]].
  eapply FExprResult_models_intro.
  - exact Hscope.
  - apply Hincl. exact Hres.
  - exact Hle.
Qed.

(** Formula-level result-set view for [let].

    [FLetResult e1 e2 ν] says that the final result coordinate [ν] is
    obtained by choosing an intermediate coordinate [x], evaluating [e1] into
    [x], and then evaluating the opened body in the [x]-fiber.  This is the
    Choice Logic form of the operational result-set decomposition

      [tlete e1 e2 ⇓ ν] iff ∃x. [e1 ⇓ x] and [e2[x] ⇓ ν].

    The representative [x] is chosen fresh for the two expressions and the
    final coordinate; [FExists]'s cofinite semantics later interprets the
    representative by any sufficiently fresh atom. *)
Definition FLetResult (e1 e2 : tm) (ν : atom) : FQ :=
  let x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}) in
  FExists x
    (FAnd
      (FExprResult e1 x)
      (FFib x (FExprResult (e2 ^^ x) ν))).

(** [FLetResult] remains a useful auxiliary formula for examples and local
    decompositions, but the operational bridge for [tlete] is handled at the
    Rocq predicate level by [expr_result_in_world_let_elim] and
    [expr_result_in_world_let_intro].  This avoids forcing a precise
    expression-result relation through [FAtom]'s upward-closed semantics. *)

Lemma FExprResult_fv e ν :
  formula_fv (FExprResult e ν) = fv_tm e ∪ {[ν]}.
Proof. reflexivity. Qed.

Lemma FLetResult_fv_subset e1 e2 ν :
  formula_fv (FLetResult e1 e2 ν) ⊆ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}.
Proof.
  unfold FLetResult, FExprResult.
  set (x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  simpl. unfold stale, stale_logic_qualifier. simpl.
  pose proof (open_fv_tm e2 (vfvar x) 0) as Hopen.
  set_solver.
Qed.

Lemma FLetResult_expr_scope_from_basic Σ X e1 e2 ν m :
  fv_tm e1 ∪ fv_tm e2 ∪ {[ν]} ⊆ X →
  m ⊨ FAnd (basic_world_formula Σ X) (FLetResult e1 e2 ν) →
  formula_scoped_in_world ∅ m (FExprResult (tlete e1 e2) ν).
Proof.
  intros Hfv Hm.
  unfold formula_scoped_in_world. intros z Hz.
  pose proof (res_models_with_store_fuel_scoped _ ∅ m _ Hm) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  apply Hscope. simpl.
  apply elem_of_union. right.
  apply elem_of_union. left.
  apply Hfv.
  unfold FExprResult, expr_logic_qual in Hz. simpl in Hz.
  unfold stale, stale_logic_qualifier in Hz. simpl in Hz.
  set_solver.
Qed.

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
            (FExprResult e1 (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})))
            (FFib (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}))
              (FExprResult
                (e2 ^^ fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) ν))).
Proof.
  unfold FLetResult, res_models, res_models_with_store.
  simpl. intros [_ [L [HL Hexists]]].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hmodel]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  unfold res_models, res_models_with_store.
  exact Hmodel.
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
            (FExprResult e1 (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})))
            (FFib (fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}))
              (FExprResult
                (e2 ^^ fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) ν)))) →
  m ⊨ FLetResult e1 e2 ν.
Proof.
  unfold FLetResult, res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hexists]].
  split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hmodel]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  unfold res_models, res_models_with_store in Hmodel.
  exact Hmodel.
Qed.

Lemma expr_logic_qual_denote_store_restrict e ν ρ w X :
  closed_env ρ →
  stale e ⊆ X →
  logic_qualifier_denote (expr_logic_qual e ν) (map_restrict value ρ X) w ↔
  logic_qualifier_denote (expr_logic_qual e ν) ρ w.
Proof.
  intros Hclosed HeX.
  unfold logic_qualifier_denote, expr_logic_qual. simpl.
  assert (Hleft :
    m{store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})} e =
    m{ρ} e).
  {
    rewrite <- (msubst_restrict ρ X e Hclosed HeX).
    apply msubst_restrict.
    - apply closed_env_restrict. exact Hclosed.
    - set_solver.
  }
  assert (Hright :
    m{store_restrict ρ (stale e ∪ {[ν]})} e =
    m{ρ} e).
  {
    apply msubst_restrict; [exact Hclosed | set_solver].
  }
  split.
  - intros Hq σw Hσw.
    specialize (Hq σw Hσw) as [v [Hν Hsteps]].
    exists v. split; [exact Hν |].
    change (subst_map σw
      (subst_map (store_restrict ρ (stale e ∪ {[ν]})) e) →* tret v).
    change (subst_map σw
      (subst_map (store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})) e)
      →* tret v) in Hsteps.
    change (subst_map (store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})) e)
      with (m{store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})} e) in Hsteps.
    change (subst_map (store_restrict ρ (stale e ∪ {[ν]})) e)
      with (m{store_restrict ρ (stale e ∪ {[ν]})} e).
    rewrite Hleft in Hsteps. rewrite Hright. exact Hsteps.
  - intros Hq σw Hσw.
    specialize (Hq σw Hσw) as [v [Hν Hsteps]].
    exists v. split; [exact Hν |].
    change (subst_map σw
      (subst_map (store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})) e)
      →* tret v).
    change (subst_map σw
      (subst_map (store_restrict ρ (stale e ∪ {[ν]})) e) →* tret v) in Hsteps.
    change (subst_map (store_restrict ρ (stale e ∪ {[ν]})) e)
      with (m{store_restrict ρ (stale e ∪ {[ν]})} e) in Hsteps.
    change (subst_map (store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})) e)
      with (m{store_restrict (map_restrict value ρ X) (stale e ∪ {[ν]})} e).
    rewrite Hright in Hsteps. rewrite Hleft. exact Hsteps.
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
  intros Hxe Hye Hρ Hσw Hq Hproj.
  apply logic_qualifier_denote_swap in Hq.
  assert (Hdomswap : aset_swap x y (stale e ∪ {[y]}) = stale e ∪ {[x]}).
  {
    rewrite aset_swap_union, aset_swap_fresh by set_solver.
    rewrite aset_swap_singleton. unfold atom_swap.
    repeat destruct decide; try congruence; set_solver.
  }
  assert (Hproj_swap :
    (res_restrict (res_swap x y w) (stale e ∪ {[x]}) : World)
      (store_swap x y σw)).
  {
    rewrite <- Hdomswap.
    apply res_restrict_swap_projection. exact Hproj.
  }
  unfold logic_qualifier_denote, expr_logic_qual in Hq. simpl in Hq.
  destruct (Hq (store_swap x y σw) Hproj_swap) as [v [Hlookup Hsteps]].
  exists v. split.
  - rewrite store_swap_lookup_inv in Hlookup.
    unfold atom_swap in Hlookup.
    repeat destruct decide; try congruence; exact Hlookup.
  - assert (Hinner :
      m{store_restrict (store_swap x y ρ) (stale e ∪ {[x]})} e =
      m{ρ} e).
    {
      rewrite (msubst_restrict (store_swap x y ρ) (stale e ∪ {[x]}) e)
        by (try apply closed_env_store_swap; try exact Hρ; set_solver).
      rewrite (msubst_store_swap_fresh tm x y ρ e)
        by (try exact Hρ; set_solver).
      reflexivity.
    }
    change (steps
      (m{store_swap x y σw}
        (m{store_restrict (store_swap x y ρ) (stale e ∪ {[x]})} e))
      (tret v)) in Hsteps.
    rewrite Hinner in Hsteps.
    rewrite (msubst_store_swap_fresh tm x y σw (m{ρ} e)) in Hsteps.
    + exact Hsteps.
    + exact Hσw.
    + pose proof (msubst_fv ρ e Hρ) as Hfv. set_solver.
    + pose proof (msubst_fv ρ e Hρ) as Hfv. set_solver.
Qed.

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
  intros Hxe Hye Hνx Hνy Hρ Hlcρ Hlookup Hσw Hvx_closed Hvx_lc Hq Hproj.
  apply logic_qualifier_denote_swap in Hq.
  assert (Hproj_swap :
    (res_restrict (res_swap x y w) (stale (e ^^ x) ∪ {[ν]}) : World)
      (store_swap x y σw)).
  {
    replace (stale (e ^^ x) ∪ {[ν]})
      with (aset_swap x y (aset_swap x y (stale (e ^^ x) ∪ {[ν]}))).
    - apply res_restrict_swap_projection. exact Hproj.
    - rewrite aset_swap_involutive. reflexivity.
  }
  unfold logic_qualifier_denote, expr_logic_qual in Hq. simpl in Hq.
  destruct (Hq (store_swap x y σw) Hproj_swap) as [v [Hν Hsteps]].
  exists v. split.
  - rewrite store_swap_lookup_inv in Hν.
    rewrite atom_swap_fresh in Hν by congruence.
    exact Hν.
  - assert (Hinner :
      m{store_restrict (store_swap x y ρ) (stale (e ^^ x) ∪ {[ν]})}
        (e ^^ x) =
      m{ρ} (e ^^ y)).
    {
      rewrite (msubst_restrict (store_swap x y ρ)
        (stale (e ^^ x) ∪ {[ν]}) (e ^^ x))
        by (try apply closed_env_store_swap; try exact Hρ; set_solver).
      apply (msubst_open_lookup_swap_tm ρ e 0 x y vx); eauto.
    }
    assert (Hopen :
      m{ρ} (e ^^ y) = open_tm 0 vx (m{delete y ρ} e)).
    { apply msubst_open_lookup_tm; eauto. }
    change (steps
      (m{store_swap x y σw}
        (m{store_restrict (store_swap x y ρ) (stale (e ^^ x) ∪ {[ν]})}
          (e ^^ x)))
      (tret v)) in Hsteps.
    rewrite Hinner, Hopen in Hsteps.
    rewrite (msubst_store_swap_fresh tm x y σw
      (open_tm 0 vx (m{delete y ρ} e))) in Hsteps.
    + exact Hsteps.
    + exact Hσw.
    + pose proof (msubst_fv (delete y ρ) e (closed_env_delete ρ y Hρ)) as Hfv.
      pose proof (open_fv_tm e vx 0) as Hopen_fv.
      pose proof (open_fv_tm (m{delete y ρ} e) vx 0) as Hopen_msubst_fv.
      change (fv_value vx) with (stale vx) in Hopen_msubst_fv.
      rewrite Hvx_closed in Hopen_msubst_fv.
      set_solver.
    + pose proof (msubst_fv (delete y ρ) e (closed_env_delete ρ y Hρ)) as Hfv.
      pose proof (open_fv_tm (m{delete y ρ} e) vx 0) as Hopen_msubst_fv.
      change (fv_value vx) with (stale vx) in Hopen_msubst_fv.
      rewrite Hvx_closed in Hopen_msubst_fv.
      set_solver.
Qed.

Lemma expr_logic_qual_ret_closed_value_denote_lookup v ν w σ :
  stale v = ∅ →
  logic_qualifier_denote (expr_logic_qual (tret v) ν) ∅ w →
  (res_restrict w {[ν]} : World) σ →
  σ !! ν = Some v.
Proof.
  intros Hvclosed Hqual Hσ.
  unfold logic_qualifier_denote, expr_logic_qual in Hqual. simpl in Hqual.
  change (stale (tret v)) with (stale v) in Hqual.
  rewrite Hvclosed in Hqual.
  replace ((∅ : aset) ∪ {[ν]}) with ({[ν]} : aset) in Hqual by set_solver.
  destruct (Hqual σ Hσ) as [v' [Hν Hsteps]].
  change (subst_map (store_restrict ∅ {[ν]}) (tret v))
    with (m{store_restrict ∅ {[ν]}} (tret v)) in Hsteps.
  rewrite store_restrict_empty in Hsteps.
  change (subst_map ∅ (tret v)) with (m{∅} (tret v)) in Hsteps.
  rewrite msubst_empty in Hsteps.
  change (subst_map σ (tret v)) with (m{σ} (tret v)) in Hsteps.
  rewrite msubst_fresh in Hsteps by (change (dom σ ∩ stale v = ∅); rewrite Hvclosed; set_solver).
  apply val_steps_self in Hsteps.
  inversion Hsteps. subst. exact Hν.
Qed.

Lemma expr_logic_qual_ret_value_denote_lookup v ν w σ :
  logic_qualifier_denote (expr_logic_qual (tret v) ν) ∅ w →
  (res_restrict w (stale v ∪ {[ν]}) : World) σ →
  σ !! ν = Some (m{σ} v).
Proof.
  intros Hqual Hσ.
  unfold logic_qualifier_denote, expr_logic_qual in Hqual. simpl in Hqual.
  destruct (Hqual σ Hσ) as [v' [Hν Hsteps]].
  change (subst_map (store_restrict ∅ (stale v ∪ {[ν]})) (tret v))
    with (m{store_restrict ∅ (stale v ∪ {[ν]})} (tret v)) in Hsteps.
  rewrite store_restrict_empty in Hsteps.
  change (subst_map ∅ (tret v)) with (m{∅} (tret v)) in Hsteps.
  rewrite msubst_empty in Hsteps.
  change (subst_map σ (tret v)) with (m{σ} (tret v)) in Hsteps.
  rewrite msubst_ret in Hsteps.
  apply val_steps_self in Hsteps.
  inversion Hsteps. subst. exact Hν.
Qed.

Lemma expr_logic_qual_ret_closed_value_lookup v ν m :
  stale v = ∅ →
  m ⊨ FAtom (expr_logic_qual (tret v) ν) →
  ∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some v.
Proof.
  intros Hvclosed Hmodel σ Hσ.
  unfold res_models, res_models_with_store in Hmodel. simpl in Hmodel.
  destruct Hmodel as [_ [m0 [Hqual Hle]]].
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

Lemma expr_logic_qual_ret_fvar_denote_lookup x ν w σ vx :
  logic_qualifier_denote (expr_logic_qual (tret (vfvar x)) ν) ∅ w →
  (res_restrict w ({[x]} ∪ {[ν]}) : World) σ →
  closed_env σ →
  σ !! x = Some vx →
  σ !! ν = Some vx.
Proof.
  intros Hqual Hσ Hclosed Hx.
  unfold logic_qualifier_denote, expr_logic_qual in Hqual. simpl in Hqual.
  replace (({[x]} : aset) ∪ {[ν]}) with ({[x]} ∪ {[ν]} : aset) in Hqual
    by reflexivity.
  destruct (Hqual σ Hσ) as [v [Hν Hsteps]].
  change (subst_map (store_restrict ∅ ({[x]} ∪ {[ν]})) (tret x))
    with (m{store_restrict ∅ ({[x]} ∪ {[ν]})} (tret (vfvar x))) in Hsteps.
  rewrite store_restrict_empty in Hsteps.
  change (subst_map ∅ (tret x)) with (m{∅} (tret (vfvar x))) in Hsteps.
  rewrite msubst_empty in Hsteps.
  change (subst_map σ (tret x)) with (m{σ} (tret (vfvar x))) in Hsteps.
  rewrite (msubst_ret_fvar_lookup_closed σ x vx Hclosed Hx) in Hsteps.
  apply val_steps_self in Hsteps.
  inversion Hsteps. subst. exact Hν.
Qed.

(** ** Type measure for denotation fuel

    As in HATs' denotation, the first argument of [denot_ty_fuel] is an
    over-approximation of the syntactic size of the type.  This lets the
    denotation recurse on opened locally-nameless bodies such as
    [{0 ~> x} τ], which are not syntactic subterms accepted by Rocq's
    structural termination checker. *)
Fixpoint cty_measure (τ : choice_ty) : nat :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => 1
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => 1 + cty_measure τ1 + cty_measure τ2
  end.

Lemma cty_measure_gt_0 τ : cty_measure τ > 0.
Proof. induction τ; simpl; lia. Qed.

Lemma cty_open_preserves_measure τ k x :
  cty_measure ({k ~> x} τ) = cty_measure τ.
Proof. induction τ in k |- *; simpl; eauto; lia. Qed.

Lemma cty_swap_preserves_measure x y τ :
  cty_measure (cty_swap_atom x y τ) = cty_measure τ.
Proof. induction τ; simpl; eauto; lia. Qed.

(** ** Type denotation

    [denot_ty_fuel gas D Σ τ e] encodes the proposition "expression [e] has
    type [τ]" as a Choice Logic formula under erased basic environment [Σ].
    The finite set [D] is an avoidance set for generated binder
    representatives.  These names only make the syntax concrete:
    [FForall]'s cofinite semantics interprets each binder by renaming the
    representative to every sufficiently fresh atom. *)

Fixpoint denot_ty_fuel
    (gas : nat) (D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      fresh_forall (D ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FAtom (expr_logic_qual e ν))
               (FAnd
                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
                 (fib_vars (qual_dom φν)
                   (FOver (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      fresh_forall (D ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FAtom (expr_logic_qual e ν))
               (FAnd
                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
                 (fib_vars (qual_dom φν)
                   (FUnder (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty_fuel gas' D Σ τ1 e) (denot_ty_fuel gas' D Σ τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty_fuel gas' D Σ τ1 e) (denot_ty_fuel gas' D Σ τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty_fuel gas' D Σ τ1 e) (denot_ty_fuel gas' D Σ τ2 e)

  (** τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (y x)). *)
  | CTArrow τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FAtom (expr_logic_qual e y))
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
            FFib y
              (FImpl
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  (** τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (y x)). *)
  | CTWand τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FAtom (expr_logic_qual e y))
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
            FFib y
              (FWand
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  end
  end.

Definition denot_ty_avoiding
    (D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) D Σ τ e.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_avoiding (fv_cty τ ∪ fv_tm e) Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx_under Σ Γ) τ e.

Definition ty_env_agree_on (X : aset) (Σ1 Σ2 : gmap atom ty) : Prop :=
  ∀ x, x ∈ X → Σ1 !! x = Σ2 !! x.

Lemma ty_env_agree_on_mono X Y Σ1 Σ2 :
  X ⊆ Y →
  ty_env_agree_on Y Σ1 Σ2 →
  ty_env_agree_on X Σ1 Σ2.
Proof.
  intros HXY Hagree z Hz. apply Hagree. apply HXY. exact Hz.
Qed.

Lemma ty_env_agree_on_insert_same X Σ1 Σ2 x T :
  ty_env_agree_on (X ∖ {[x]}) Σ1 Σ2 →
  ty_env_agree_on X (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = x)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ x T). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_insert_same_keep X Σ1 Σ2 x T :
  ty_env_agree_on X Σ1 Σ2 →
  ty_env_agree_on (X ∪ {[x]}) (<[x := T]> Σ1) (<[x := T]> Σ2).
Proof.
  intros Hagree.
  apply ty_env_agree_on_insert_same.
  intros z Hz. apply Hagree. set_solver.
Qed.

Lemma ty_env_agree_on_open_qual_result D Σ1 Σ2 b φ ν :
  ty_env_agree_on (D ∪ qual_dom φ) Σ1 Σ2 →
  ty_env_agree_on ({[ν]} ∪ qual_dom (qual_open_atom 0 ν φ))
    (<[ν := TBase b]> Σ1) (<[ν := TBase b]> Σ2).
Proof.
  intros Hagree z Hz.
  destruct (decide (z = ν)) as [->|Hne].
  - rewrite !(lookup_insert_eq _ ν (TBase b)). reflexivity.
  - rewrite !lookup_insert_ne by congruence.
    apply Hagree.
    pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
    set_solver.
Qed.

Definition formula_equiv (φ ψ : FQ) : Prop :=
  (φ ⊫ ψ) ∧ (ψ ⊫ φ).

Notation "φ '⊣⊢' ψ" := (formula_equiv φ ψ)
  (at level 85, no associativity).

Lemma formula_equiv_refl φ : φ ⊣⊢ φ.
Proof. split; intros m Hm; exact Hm. Qed.

Lemma formula_equiv_sym φ ψ :
  φ ⊣⊢ ψ → ψ ⊣⊢ φ.
Proof. intros [H1 H2]. split; assumption. Qed.

Lemma formula_equiv_trans φ ψ χ :
  φ ⊣⊢ ψ → ψ ⊣⊢ χ → φ ⊣⊢ χ.
Proof.
  intros [Hφψ Hψφ] [Hψχ Hχψ]. split; intros m Hm; eauto.
Qed.

Lemma denot_ty_fuel_env_agree gas D Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_fuel gas D Σ1 τ e = denot_ty_fuel gas D Σ2 τ e.
Proof.
  revert D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros D Σ1 Σ2 τ e Hagree; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    assert (Hbasic :
      basic_world_formula (<[ν:=TBase b]> Σ1) ({[ν]} ∪ qual_dom φν) =
      basic_world_formula (<[ν:=TBase b]> Σ2) ({[ν]} ∪ qual_dom φν)).
    {
      apply basic_world_formula_agree.
      intros z Hz.
      destruct (decide (z = ν)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
        set_solver.
    }
    rewrite Hbasic. reflexivity.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    assert (Hbasic :
      basic_world_formula (<[ν:=TBase b]> Σ1) ({[ν]} ∪ qual_dom φν) =
      basic_world_formula (<[ν:=TBase b]> Σ2) ({[ν]} ∪ qual_dom φν)).
    {
      apply basic_world_formula_agree.
      intros z Hz.
      destruct (decide (z = ν)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (qual_open_atom_dom_subset 0 ν φ z) as Hdom.
        set_solver.
    }
    rewrite Hbasic. reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e).
    + rewrite (IH D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH D Σ1 Σ2 τ1 e).
    + rewrite (IH D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH D Σ1 Σ2 τ1 e).
    + rewrite (IH D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    assert (Harg :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        simpl in Hz. set_solver.
    }
    repeat (f_equal; try assumption).
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    assert (Harg :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree.
        pose proof (cty_open_fv_subset 0 x τ) as Hopen.
        simpl in Hz. set_solver.
    }
    repeat (f_equal; try assumption).
Qed.

Lemma denot_ty_under_env_agree Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hagree.
  unfold denot_ty_under, denot_ty_avoiding.
  apply denot_ty_fuel_env_agree. exact Hagree.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  unfold denot_ty_in_ctx. apply denot_ty_under_env_agree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e ⊣⊢ denot_ty_in_ctx Γ2 τ e.
Proof.
  unfold denot_ty_in_ctx. apply denot_ty_under_env_equiv.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under, denot_ty_avoiding.
  assert (Hfuel :
    ∀ gas D Σ τ0 e0,
      cty_measure τ0 <= gas →
      formula_fv (denot_ty_fuel gas D Σ τ0 e0) ⊆
        D ∪ fv_tm e0 ∪ fv_cty τ0).
  {
    induction gas as [|gas IH]; intros D Σ τ0 e0 Hgas.
    { pose proof (cty_measure_gt_0 τ0). lia. }
    destruct τ0 as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ0|τx τ0]; simpl in *.
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ fv_tm e0 ∪ qual_dom φ)).
      pose proof (qual_open_atom_dom_subset 0 ν φ) as Hopen.
      pose proof (fib_vars_formula_fv_subset (qual_dom (qual_open_atom 0 ν φ))
        (FOver (FAtom (lift_type_qualifier_to_logic (qual_open_atom 0 ν φ)))))
        as Hfib.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzν].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzrhs].
      {
        unfold expr_logic_qual in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        change (stale e0) with (fv_tm e0) in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzνin].
        - apply elem_of_union. left. apply elem_of_union. right. exact Hzfv.
        - exfalso. apply Hzν. exact Hzνin.
      }
      apply elem_of_union in Hzrhs as [Hzbasic | Hzfib].
      {
        unfold basic_world_formula, basic_world_lqual in Hzbasic.
        simpl in Hzbasic.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzbasic.
        apply elem_of_union in Hzbasic as [Hzνin | Hzopen].
        - exfalso. apply Hzν. exact Hzνin.
        - apply Hopen in Hzopen.
          apply elem_of_union in Hzopen as [Hzφ | Hzνin].
          + apply elem_of_union. right. exact Hzφ.
          + exfalso. apply Hzν. exact Hzνin.
      }
      apply Hfib in Hzfib. simpl in Hzfib.
      unfold stale, stale_logic_qualifier in Hzfib.
      rewrite lqual_dom_lift_type_qualifier_to_logic in Hzfib.
      destruct φ as [B d p]. unfold qual_open_atom in *. simpl in *.
      destruct (decide (0 ∈ B)); simpl in *; set_solver.
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ fv_tm e0 ∪ qual_dom φ)).
      pose proof (qual_open_atom_dom_subset 0 ν φ) as Hopen.
      pose proof (fib_vars_formula_fv_subset (qual_dom (qual_open_atom 0 ν φ))
        (FUnder (FAtom (lift_type_qualifier_to_logic (qual_open_atom 0 ν φ)))))
        as Hfib.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzν].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzrhs].
      {
        unfold expr_logic_qual in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        change (stale e0) with (fv_tm e0) in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzνin].
        - apply elem_of_union. left. apply elem_of_union. right. exact Hzfv.
        - exfalso. apply Hzν. exact Hzνin.
      }
      apply elem_of_union in Hzrhs as [Hzbasic | Hzfib].
      {
        unfold basic_world_formula, basic_world_lqual in Hzbasic.
        simpl in Hzbasic.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzbasic.
        apply elem_of_union in Hzbasic as [Hzνin | Hzopen].
        - exfalso. apply Hzν. exact Hzνin.
        - apply Hopen in Hzopen.
          apply elem_of_union in Hzopen as [Hzφ | Hzνin].
          + apply elem_of_union. right. exact Hzφ.
          + exfalso. apply Hzν. exact Hzνin.
      }
      apply Hfib in Hzfib. simpl in Hzfib.
      unfold stale, stale_logic_qualifier in Hzfib.
      rewrite lqual_dom_lift_type_qualifier_to_logic in Hzfib.
      destruct φ as [B d p]. unfold qual_open_atom in *. simpl in *.
      destruct (decide (0 ∈ B)); simpl in *; set_solver.
    - pose proof (IH D Σ τ1 e0 ltac:(lia)) as H1.
      pose proof (IH D Σ τ2 e0 ltac:(lia)) as H2.
      set_solver.
    - pose proof (IH D Σ τ1 e0 ltac:(lia)) as H1.
      pose proof (IH D Σ τ2 e0 ltac:(lia)) as H2.
      set_solver.
    - pose proof (IH D Σ τ1 e0 ltac:(lia)) as H1.
      pose proof (IH D Σ τ2 e0 ltac:(lia)) as H2.
      set_solver.
    - unfold fresh_forall. simpl.
      set (Dy := D ∪ fv_tm e0 ∪ fv_cty τx ∪ fv_cty τ0).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      pose proof (IH D2 (<[x := erase_ty τx]> Σ) τx
        (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ0)
        (tapp (vfvar y) (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
        as Hres.
      pose proof (cty_open_fv_subset 0 x τ0) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hy].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzinner].
      {
        unfold expr_logic_qual in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        change (stale e0) with (fv_tm e0) in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzyin].
        - apply elem_of_union. left. apply elem_of_union. right. exact Hzfv.
        - exfalso. apply Hy. exact Hzyin.
      }
      apply elem_of_difference in Hzinner as [Hzinner Hx].
      simpl in Hzinner.
      apply elem_of_union in Hzinner as [Hzyin | Hzimpl].
      { exfalso. apply Hy. exact Hzyin. }
      apply elem_of_union in Hzimpl as [Hzarg | Hzres].
      + apply Harg in Hzarg. simpl in Hzarg. set_solver.
      + apply Hres in Hzres. simpl in Hzres. set_solver.
    - unfold fresh_forall. simpl.
      set (Dy := D ∪ fv_tm e0 ∪ fv_cty τx ∪ fv_cty τ0).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      pose proof (IH D2 (<[x := erase_ty τx]> Σ) τx
        (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ0)
        (tapp (vfvar y) (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
        as Hres.
      pose proof (cty_open_fv_subset 0 x τ0) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hy].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzinner].
      {
        unfold expr_logic_qual in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        change (stale e0) with (fv_tm e0) in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzyin].
        - apply elem_of_union. left. apply elem_of_union. right. exact Hzfv.
        - exfalso. apply Hy. exact Hzyin.
      }
      apply elem_of_difference in Hzinner as [Hzinner Hx].
      simpl in Hzinner.
      apply elem_of_union in Hzinner as [Hzyin | Hzimpl].
      { exfalso. apply Hy. exact Hzyin. }
      apply elem_of_union in Hzimpl as [Hzarg | Hzres].
      + apply Harg in Hzarg. simpl in Hzarg. set_solver.
      + apply Hres in Hzres. simpl in Hzres. set_solver.
  }
  pose proof (Hfuel (cty_measure τ) (fv_cty τ ∪ fv_tm e) ∅ τ e ltac:(lia)).
  set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_env_agree gas D Σ1 Σ2 τ e :
  formula_fv (denot_ty_fuel gas D Σ1 τ e) =
  formula_fv (denot_ty_fuel gas D Σ2 τ e).
Proof.
  revert D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros D Σ1 Σ2 τ e; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e), (IH D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e), (IH D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH D Σ1 Σ2 τ1 e), (IH D Σ1 Σ2 τ2 e). reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
Qed.

Lemma denot_ty_under_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_under, denot_ty_avoiding.
  rewrite (denot_ty_fuel_formula_fv_env_agree
    (cty_measure τ) (fv_cty τ ∪ fv_tm e) Σ ∅ τ e).
  exact (denot_ty_formula_fv_subset τ e).
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  unfold denot_ty_under, denot_ty_avoiding.
  assert (Hfuel :
    ∀ gas D Σ0 τ0 z,
      cty_measure τ0 <= gas →
      z ∈ D →
      z ∈ formula_fv (denot_ty_fuel gas D Σ0 τ0 (tret (vfvar z)))).
  {
    induction gas as [|gas IH]; intros D Σ0 τ0 z Hgas HzD.
    { pose proof (cty_measure_gt_0 τ0). lia. }
    destruct τ0 as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2|τ1 τ2]; simpl in *.
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ {[z]} ∪ qual_dom φ)).
      assert (Hzν : z ≠ ν).
      {
        subst ν. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ qual_dom φ)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[ν]}). simpl. set_solver.
      + intros Hzνin. apply elem_of_singleton in Hzνin.
        exact (Hzν Hzνin).
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ {[z]} ∪ qual_dom φ)).
      assert (Hzν : z ≠ ν).
      {
        subst ν. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ qual_dom φ)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[ν]}). simpl. set_solver.
      + intros Hzνin. apply elem_of_singleton in Hzνin.
        exact (Hzν Hzνin).
    - apply elem_of_union. left.
      apply IH; [lia | exact HzD].
    - apply elem_of_union. left.
      apply IH; [lia | exact HzD].
    - apply elem_of_union. left.
      apply IH; [lia | exact HzD].
    - unfold fresh_forall. simpl.
      set (y := fresh_for (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
      assert (Hzy : z ≠ y).
      {
        subst y. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[y]}). simpl. set_solver.
      + intros Hzyin. apply elem_of_singleton in Hzyin.
        exact (Hzy Hzyin).
    - unfold fresh_forall. simpl.
      set (y := fresh_for (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
      assert (Hzy : z ≠ y).
      {
        subst y. pose proof (fresh_for_not_in (D ∪ {[z]} ∪ fv_cty τ1 ∪ fv_cty τ2)).
        set_solver.
      }
      apply elem_of_difference. split.
      + apply elem_of_union. left.
        change (z ∈ fv_tm (tret (vfvar z)) ∪ {[y]}). simpl. set_solver.
      + intros Hzyin. apply elem_of_singleton in Hzyin.
        exact (Hzy Hzyin).
  }
  apply Hfuel.
  - reflexivity.
  - simpl. set_solver.
Qed.

Lemma denot_ty_result_atom_fv x τ :
  x ∈ formula_fv (denot_ty τ (tret (vfvar x))).
Proof. apply denot_ty_under_result_atom_fv. Qed.

Lemma denot_ty_restrict_fv τ e m :
  m ⊨ denot_ty τ e →
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊨ denot_ty τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

Lemma denot_ty_under_restrict_fv Σ τ e m :
  m ⊨ denot_ty_under Σ τ e →
  res_restrict m (fv_tm e ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ty_under_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

(** ** Context denotation

    [denot_ctx_under Σ Γ] is the formula that holds when [Γ] is satisfied
    under the ambient erased basic environment [Σ].  The public
    [denot_ctx Γ] instantiates [Σ] with [erase_ctx Γ], so later binders in a
    comma context can be checked against earlier erased bindings. *)
Fixpoint denot_ctx_under (Σ : gmap atom ty) (Γ : ctx) : FQ :=
  match Γ with
  | CtxEmpty        => FTrue
  | CtxBind x τ    => denot_ty_under Σ τ (tret (vfvar x))
  | CtxComma Γ1 Γ2 => FAnd  (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  | CtxStar  Γ1 Γ2 => FStar (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  | CtxSum   Γ1 Γ2 => FPlus (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  end.

Definition denot_ctx (Γ : ctx) : FQ :=
  denot_ctx_under (erase_ctx Γ) Γ.

Definition denot_ctx_in_env (Σ : gmap atom ty) (Γ : ctx) : FQ :=
  FAnd (basic_world_formula Σ (dom Σ))
       (denot_ctx_under (erase_ctx_under Σ Γ) Γ).

(** ** Typeclass instances for [⟦⟧] notation *)

#[global] Instance denot_cty_inst :
    Denotation choice_ty (tm → FQ) := denot_ty.
#[global] Instance denot_ctx_inst :
    Denotation ctx FQ := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.

Lemma denot_ctx_under_dom_subset_formula_fv Σ Γ :
  ctx_dom Γ ⊆ formula_fv (denot_ctx_under Σ Γ).
Proof.
  induction Γ; simpl; try set_solver.
  intros z Hz. apply elem_of_singleton in Hz. subst.
  apply denot_ty_under_result_atom_fv.
Qed.

Lemma denot_ctx_in_env_dom_subset_formula_fv Σ Γ :
  dom Σ ∪ ctx_dom Γ ⊆ formula_fv (denot_ctx_in_env Σ Γ).
Proof.
  unfold denot_ctx_in_env. simpl.
  pose proof (denot_ctx_under_dom_subset_formula_fv (erase_ctx_under Σ Γ) Γ).
  set_solver.
Qed.

Lemma denot_ctx_dom_subset_formula_fv Γ :
  ctx_dom Γ ⊆ formula_fv (denot_ctx Γ).
Proof.
  unfold denot_ctx. apply denot_ctx_under_dom_subset_formula_fv.
Qed.

Lemma denot_ctx_models_dom Γ m :
  m ⊨ ⟦Γ⟧ →
  ctx_dom Γ ⊆ world_dom m.
Proof.
  intros Hmodels z Hz.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure (denot_ctx Γ)) ∅ m (denot_ctx Γ) Hmodels) as Hscope.
  unfold formula_scoped_in_world in Hscope.
  apply Hscope.
  pose proof (denot_ctx_dom_subset_formula_fv Γ z Hz).
  set_solver.
Qed.

(** With these instances:
      [⟦τ⟧ e]  unfolds to [denot_ty τ e]
      [⟦Γ⟧]    unfolds to [denot_ctx Γ]              *)

(** ** Key semantic lemmas *)

Local Ltac solve_ctx_fuel Γ1 Γ2 :=
  unfold denote, denot_ctx_inst in *;
  simpl;
  repeat rewrite Nat.add_0_l;
  repeat rewrite Nat.add_0_r;
  pose proof (formula_measure_pos (denot_ctx Γ1));
  pose proof (formula_measure_pos (denot_ctx Γ2));
  lia.

Local Ltac change_ctx_fuel H Γ1 Γ2 :=
  match type of H with
  | res_models_with_store_fuel ?gas ?ρ ?m ?φ =>
      eapply (res_models_with_store_fuel_irrel gas _ ρ m φ);
      [solve_ctx_fuel Γ1 Γ2 | solve_ctx_fuel Γ1 Γ2 | exact H]
  end.

(** Monotonicity: if m ⊨ ⟦Γ⟧ and m ≤ m', then m' ⊨ ⟦Γ⟧ for comma contexts. *)
Lemma denot_ctx_mono_comma (Γ : ctx) m m' :
  m ⊨ ⟦Γ⟧ →
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof.
  unfold denot_ctx_inst, res_models, res_models_with_store.
  intros Hmodels Hle. eapply res_models_with_store_fuel_kripke; eauto.
Qed.

(** Environment-indexed context denotations distribute structurally when the
    same ambient erased environment is used for both subcontexts. *)
Lemma denot_ctx_under_comma Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_under Σ Γ1 ∧ m ⊨ denot_ctx_under Σ Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [Hscope [HΓ1 HΓ2]]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [HΓ1 HΓ2]. split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx_under Σ Γ2) HΓ2).
      set_solver.
    + split.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
Qed.

Lemma denot_ctx_under_star Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxStar Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [_ [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx_under Σ Γ2) HΓ2).
      pose proof (raw_le_dom _ _ Hprod). set_solver.
    + exists m1, m2, Hc. split; [exact Hprod |]. split.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
Qed.

Lemma denot_ctx_under_sum Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxSum Γ1 Γ2) ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ denot_ctx_under Σ Γ1 ∧ m2 ⊨ denot_ctx_under Σ Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [_ [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx_under Σ Γ1) HΓ1) as Hscope1.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx_under Σ Γ2) HΓ2) as Hscope2.
      pose proof (raw_le_dom _ _ Hsum) as Hdom_sum_m.
      unfold raw_sum_defined in Hdef. simpl in Hdom_sum_m.
      intros z Hz. apply elem_of_union in Hz as [Hzempty | Hzfv]; [set_solver |].
      apply elem_of_union in Hzfv as [Hz | Hz].
      * apply Hdom_sum_m. apply Hscope1. set_solver.
      * apply Hdom_sum_m. rewrite Hdef. apply Hscope2. set_solver.
    + exists m1, m2, Hdef. split; [exact Hsum |]. split.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
      * eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
Qed.

Lemma denot_ctx_under_bind Σ x τ m :
  m ⊨ denot_ctx_under Σ (CtxBind x τ) ↔
  m ⊨ denot_ty_under Σ τ (tret (vfvar x)).
Proof. reflexivity. Qed.

Lemma denot_ctx_under_env_equiv Σ1 Σ2 Γ :
  ty_env_agree_on (ctx_stale Γ) Σ1 Σ2 →
  denot_ctx_under Σ1 Γ ⊣⊢ denot_ctx_under Σ2 Γ.
Proof.
  induction Γ in Σ1, Σ2 |- *; intros Hagree.
  - apply formula_equiv_refl.
  - simpl in Hagree.
    apply denot_ty_under_env_equiv.
    intros z Hz. apply Hagree. simpl. set_solver.
  - simpl in Hagree.
    pose proof (IHΓ1 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_1 H21_1].
    pose proof (IHΓ2 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_2 H21_2].
    split; intros m Hm.
    + apply denot_ctx_under_comma in Hm as [HΓ1 HΓ2].
      apply denot_ctx_under_comma. split; eauto.
    + apply denot_ctx_under_comma in Hm as [HΓ1 HΓ2].
      apply denot_ctx_under_comma. split; eauto.
  - simpl in Hagree.
    pose proof (IHΓ1 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_1 H21_1].
    pose proof (IHΓ2 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_2 H21_2].
    split; intros m Hm.
    + apply denot_ctx_under_star in Hm as [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_star.
      exists m1, m2, Hc. split; [exact Hprod |]. split; eauto.
    + apply denot_ctx_under_star in Hm as [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_star.
      exists m1, m2, Hc. split; [exact Hprod |]. split; eauto.
  - simpl in Hagree.
    pose proof (IHΓ1 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_1 H21_1].
    pose proof (IHΓ2 Σ1 Σ2 ltac:(intros z Hz; apply Hagree; set_solver))
      as [H12_2 H21_2].
    split; intros m Hm.
    + apply denot_ctx_under_sum in Hm as [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_sum.
      exists m1, m2, Hdef. split; [exact Hsum |]. split; eauto.
    + apply denot_ctx_under_sum in Hm as [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
      apply denot_ctx_under_sum.
      exists m1, m2, Hdef. split; [exact Hsum |]. split; eauto.
Qed.

(** The public context denotation uses each context's own erased environment.
    These wrappers require environment-locality facts to bridge from the
    ambient environment of the compound context to the standalone subcontext
    environments. *)
Lemma denot_ctx_comma_agree Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof.
  intros Hagree1 Hagree2.
  change (m ⊨ denot_ctx_under (erase_ctx (CtxComma Γ1 Γ2)) (CtxComma Γ1 Γ2) ↔
    m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧).
  rewrite denot_ctx_under_comma.
  split.
  - intros [HΓ1 HΓ2]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [H _].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [H _].
      apply H. exact HΓ2.
  - intros [HΓ1 HΓ2]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [_ H].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [_ H].
      apply H. exact HΓ2.
Qed.

Lemma denot_ctx_star_agree Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof.
  intros Hagree1 Hagree2.
  change (m ⊨ denot_ctx_under (erase_ctx (CtxStar Γ1 Γ2)) (CtxStar Γ1 Γ2) ↔
    ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
      res_product m1 m2 Hc ⊑ m ∧
      m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧).
  rewrite denot_ctx_under_star.
  split.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [H _].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [H _].
      apply H. exact HΓ2.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    exists m1, m2, Hc. split; [exact Hprod |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [_ H].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [_ H].
      apply H. exact HΓ2.
Qed.

Lemma denot_ctx_sum_agree Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof.
  intros Hagree1 Hagree2.
  change (m ⊨ denot_ctx_under (erase_ctx (CtxSum Γ1 Γ2)) (CtxSum Γ1 Γ2) ↔
    ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
      res_sum m1 m2 Hdef ⊑ m ∧
      m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧).
  rewrite denot_ctx_under_sum.
  split.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [H _].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [H _].
      apply H. exact HΓ2.
  - intros [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    exists m1, m2, Hdef. split; [exact Hsum |]. split.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) Γ1 Hagree1) as [_ H].
      apply H. exact HΓ1.
    + destruct (denot_ctx_under_env_equiv
        (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) Γ2 Hagree2) as [_ H].
      apply H. exact HΓ2.
Qed.

Lemma denot_ctx_comma Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxComma Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_comma_agree. Qed.

(** The context denotation of a star-context distributes over FStar. *)
Lemma denot_ctx_star Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxStar Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_star_agree. Qed.

(** The context denotation of a sum-context distributes over FPlus. *)
Lemma denot_ctx_sum Γ1 Γ2 m :
  ty_env_agree_on (ctx_stale Γ1) (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ1) →
  ty_env_agree_on (ctx_stale Γ2) (erase_ctx (CtxSum Γ1 Γ2)) (erase_ctx Γ2) →
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. apply denot_ctx_sum_agree. Qed.

(** [⟦CtxBind x τ⟧] is [⟦τ⟧ (return x)]. *)
Lemma denot_ctx_bind x τ m :
  m ⊨ ⟦CtxBind x τ⟧ ↔
  m ⊨ denot_ty_in_ctx (CtxBind x τ) τ (tret (vfvar x)).
Proof. reflexivity. Qed.

Lemma denot_ctx_under_restrict_stale Σ Γ m :
  m ⊨ denot_ctx_under Σ Γ →
  res_restrict m (ctx_stale Γ) ⊨ denot_ctx_under Σ Γ.
Proof.
  induction Γ in m |- *; simpl.
  - intros _. unfold res_models, res_models_with_store. simpl.
    split; [unfold formula_scoped_in_world; simpl; set_solver | exact I].
  - intros Hbind. apply denot_ty_under_restrict_fv. exact Hbind.
  - intros Hctx.
    apply denot_ctx_under_comma in Hctx as [HΓ1 HΓ2].
    apply denot_ctx_under_comma. split.
    + eapply res_models_kripke; [| exact (IHΓ1 m HΓ1)].
      apply res_restrict_mono. set_solver.
    + eapply res_models_kripke; [| exact (IHΓ2 m HΓ2)].
      apply res_restrict_mono. set_solver.
  - intros Hctx.
    apply denot_ctx_under_star in Hctx as [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    apply denot_ctx_under_star.
    set (r1 := res_restrict m1 (ctx_stale Γ1)).
    set (r2 := res_restrict m2 (ctx_stale Γ2)).
    assert (Hc' : world_compat r1 r2).
    {
      subst r1 r2.
      eapply world_compat_le_l.
      - apply res_restrict_le.
      - eapply world_compat_le_r.
        + apply res_restrict_le.
        + exact Hc.
    }
    exists r1, r2, Hc'. split.
    + eapply res_le_restrict.
      * etrans.
        -- eapply (res_product_le_mono r1 r2 m1 m2 Hc' Hc);
             apply res_restrict_le.
        -- exact Hprod.
      * subst r1 r2. simpl. set_solver.
    + split; [apply IHΓ1 | apply IHΓ2]; assumption.
  - intros Hctx.
    apply denot_ctx_under_sum in Hctx as [m1 [m2 [Hdef [Hsum [HΓ1 HΓ2]]]]].
    apply denot_ctx_under_sum.
    set (S := ctx_stale Γ1 ∪ ctx_stale Γ2).
    set (r1 := res_restrict m1 S).
    set (r2 := res_restrict m2 S).
    assert (Hdef' : raw_sum_defined r1 r2).
    {
      subst r1 r2 S. unfold raw_sum_defined. simpl.
      rewrite Hdef. reflexivity.
    }
    exists r1, r2, Hdef'. split.
    + eapply res_le_restrict.
      * etrans.
        -- eapply (res_sum_le_mono r1 r2 m1 m2 Hdef' Hdef);
             apply res_restrict_le.
        -- exact Hsum.
      * subst r1 r2 S. simpl. set_solver.
    + split.
      * eapply res_models_kripke; [| exact (IHΓ1 m1 HΓ1)].
        subst r1 S. apply res_restrict_mono. set_solver.
      * eapply res_models_kripke; [| exact (IHΓ2 m2 HΓ2)].
        subst r2 S. apply res_restrict_mono. set_solver.
Qed.

Lemma denot_ctx_restrict_stale Γ m :
  m ⊨ ⟦Γ⟧ →
  res_restrict m (ctx_stale Γ) ⊨ ⟦Γ⟧.
Proof.
  unfold denot_ctx.
  apply denot_ctx_under_restrict_stale.
Qed.
