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

Definition expr_result_in_store (ρ : Store) (e : tm) (ν : atom) (σw : Store) : Prop :=
    ∃ v,
      σw !! ν = Some v ∧
      subst_map σw (subst_map ρ e) →* tret v.

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σw,
    (w : World) σw →
    expr_result_in_store ρ e ν σw.

Definition expr_logic_qual (e : tm) (ν : atom) : logic_qualifier :=
  lqual (stale e ∪ {[ν]}) (fun σ w => expr_result_in_world σ e ν w).

Definition FExprResult (e : tm) (ν : atom) : FQ :=
  FAtom (expr_logic_qual e ν).

(** Domain-explicit expression-result atom.

    [FExprResult e ν] uses [fv_tm e] as the input domain.  That is fine for a
    single expression, but comparisons between open expressions need both sides
    interpreted over the same input domain.  [FExprResultOn X e ν] records that
    common domain explicitly; callers should provide [fv_tm e ⊆ X] and choose
    [ν ∉ X]. *)
Definition expr_logic_qual_on (X : aset) (e : tm) (ν : atom) : logic_qualifier :=
  lqual (X ∪ {[ν]})
    (fun σ w => expr_result_in_world (store_restrict σ X) e ν w).

Definition FExprResultOn (X : aset) (e : tm) (ν : atom) : FQ :=
  FAtom (expr_logic_qual_on X e ν).

Lemma stale_expr_logic_qual_on X e ν :
  stale (expr_logic_qual_on X e ν) = X ∪ {[ν]}.
Proof. reflexivity. Qed.

(** Prop-level totality for the expression component of a type denotation.

    This is intentionally not encoded as a ChoiceLogic formula.  The logic
    describes resource/domain behavior; operational totality is a meta-level
    obligation used by the fundamental theorem.  Keeping it here lets the let
    proof combine the formula denotation with the fact that the bound
    expression has an actual result in every admissible store. *)
Definition expr_total_on (X : aset) (e : tm) (m : WfWorld) : Prop :=
  fv_tm e ⊆ X ∧
  ∀ σ, (m : World) σ → ∃ v, subst_map (store_restrict σ X) e →* tret v.

(** [world_closed_on X m] is the ChoiceType-level invariant saying that every
    store in [m] is operationally usable on the coordinates [X].  This belongs
    here rather than in ChoiceAlgebra: the algebra is polymorphic in store
    values, while closedness is a CoreLang [value] property. *)
Definition world_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → closed_env (store_restrict σ X).

Lemma world_closed_on_le X m n :
  m ⊑ n →
  world_closed_on X n →
  world_closed_on X m.
Proof.
  intros Hle Hclosed σ Hσ.
  unfold world_closed_on in Hclosed.
  unfold sqsubseteq, wf_world_sqsubseteq, raw_le in Hle.
  change ((m : World) σ) in Hσ.
  rewrite Hle in Hσ. simpl in Hσ.
  destruct Hσ as [σn [Hσn Hrestrict]].
  rewrite <- Hrestrict.
  rewrite !store_restrict_restrict.
  replace (world_dom (m : World) ∩ X) with (X ∩ world_dom (m : World))
    by set_solver.
  rewrite <- store_restrict_restrict.
  apply closed_env_restrict.
  exact (Hclosed σn Hσn).
Qed.

Lemma basic_world_formula_world_closed_on Σ X m :
  X ⊆ dom Σ →
  m ⊨ basic_world_formula Σ X →
  world_closed_on X m.
Proof.
  intros HXΣ Hbasic σ Hσ.
  eapply basic_world_formula_store_restrict_closed_env; eauto.
Qed.

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

Lemma expr_result_in_store_let_elim ρ e1 e2 ν σw :
  expr_result_in_store ρ (tlete e1 e2) ν σw →
  ∃ v vx,
    σw !! ν = Some v ∧
    subst_map σw (subst_map ρ e1) →* tret vx ∧
    open_tm 0 vx (subst_map σw (subst_map ρ e2)) →* tret v.
Proof.
  intros [v [Hν Hsteps]].
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

Lemma expr_result_in_store_let_intro ρ e1 e2 ν σw :
  (∃ v vx,
    σw !! ν = Some v ∧
    body_tm (subst_map σw (subst_map ρ e2)) ∧
    subst_map σw (subst_map ρ e1) →* tret vx ∧
    open_tm 0 vx (subst_map σw (subst_map ρ e2)) →* tret v) →
  expr_result_in_store ρ (tlete e1 e2) ν σw.
Proof.
  intros [v [vx [Hν [Hbody [He1 He2]]]]].
  exists v. split; [exact Hν |].
  change (subst_map σw (subst_map ρ (tlete e1 e2)) →* tret v).
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)).
  rewrite (msubst_lete ρ e1 e2).
  change (subst_map σw (tlete (m{ρ} e1) (m{ρ} e2)))
    with (m{σw} (tlete (m{ρ} e1) (m{ρ} e2))).
  rewrite (msubst_lete σw (m{ρ} e1) (m{ρ} e2)).
  eapply reduction_lete_intro; eauto.
Qed.

Lemma expr_result_in_store_ret_fvar_lookup x ν σw vx :
  stale vx = ∅ →
  σw !! x = Some vx →
  expr_result_in_store ∅ (tret (vfvar x)) ν σw →
  σw !! ν = Some vx.
Proof.
  intros Hvclosed Hx [v [Hν Hsteps]].
  change (subst_map σw (subst_map ∅ (tret (vfvar x))) →* tret v) in Hsteps.
  change (subst_map ∅ (tret (vfvar x))) with (m{∅} (tret (vfvar x))) in Hsteps.
  rewrite msubst_empty in Hsteps.
  change (subst_map σw (tret (vfvar x))) with (m{σw} (tret (vfvar x))) in Hsteps.
  rewrite (msubst_ret_fvar_lookup_closed_value σw x vx Hvclosed Hx) in Hsteps.
  apply val_steps_self in Hsteps.
  inversion Hsteps. subst. exact Hν.
Qed.

Lemma expr_result_in_store_ret_fvar_trans ρ e x ν σw :
  (∀ vx, subst_map σw (subst_map ρ e) →* tret vx → stale vx = ∅) →
  expr_result_in_store ρ e x σw →
  expr_result_in_store ∅ (tret (vfvar x)) ν σw →
  expr_result_in_store ρ e ν σw.
Proof.
  intros Hclosed_result [vx [Hx Hsteps]] Hret.
  exists vx. split.
  - eapply expr_result_in_store_ret_fvar_lookup; eauto.
  - exact Hsteps.
Qed.

Lemma expr_result_in_world_ret_fvar_trans ρ e x ν (w : WfWorld) :
  (∀ σw vx,
    (w : World) σw →
    subst_map σw (subst_map ρ e) →* tret vx →
    stale vx = ∅) →
  expr_result_in_world ρ e x w →
  expr_result_in_world ∅ (tret (vfvar x)) ν w →
  expr_result_in_world ρ e ν w.
Proof.
  intros Hclosed_result He Hret σw Hσw.
  eapply expr_result_in_store_ret_fvar_trans; eauto.
Qed.

Lemma FExprResult_models_elim e ν m :
  m ⊨ FExprResult e ν →
  ∃ w : WfWorld,
    formula_scoped_in_world ∅ w (FExprResult e ν) ∧
    expr_result_in_world
      (store_restrict ∅ (stale e ∪ {[ν]})) e ν
      (res_restrict w (stale e ∪ {[ν]})) ∧
    w ⊑ m.
Proof.
  unfold FExprResult, res_models, res_models_with_store.
  simpl. intros [_ [w [Hscopew [Hres Hle]]]].
  exists w. split; [exact Hscopew |]. split; [exact Hres | exact Hle].
Qed.

Lemma FExprResult_models_intro e ν m w :
  formula_scoped_in_world ∅ m (FExprResult e ν) →
  formula_scoped_in_world ∅ w (FExprResult e ν) →
  expr_result_in_world
    (store_restrict ∅ (stale e ∪ {[ν]})) e ν
    (res_restrict w (stale e ∪ {[ν]})) →
  w ⊑ m →
  m ⊨ FExprResult e ν.
Proof.
  unfold FExprResult, res_models, res_models_with_store.
  simpl. intros Hscope Hscopew Hres Hle.
  split; [exact Hscope |].
  exists w. split; [exact Hscopew |]. split; [exact Hres | exact Hle].
Qed.

Lemma FExprResult_models_from_result_inclusion e1 e2 ν m :
  formula_scoped_in_world ∅ m (FExprResult e1 ν) →
  (∀ w,
    formula_scoped_in_world ∅ w (FExprResult e2 ν) →
    formula_scoped_in_world ∅ w (FExprResult e1 ν)) →
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
  intros Hscope Hscope_incl Hincl Hexpr.
  destruct (FExprResult_models_elim e2 ν m Hexpr) as [w [Hscopew [Hres Hle]]].
  eapply FExprResult_models_intro.
  - exact Hscope.
  - apply Hscope_incl. exact Hscopew.
  - apply Hincl. exact Hres.
  - exact Hle.
Qed.

(** Operational result comparison for open expressions.

    This relation is intentionally stated outside Choice Logic.  Logic
    entailment [⊫] follows the Kripke/domain-restriction order on worlds; it is
    not a same-domain subset relation on result sets.  For open terms, the
    result set is really a relation from an input store domain [X] to possible
    results, so the comparison must name [X] explicitly. *)
Definition expr_result_incl_on (X : aset) (e_to e_from : tm) : Prop :=
  fv_tm e_to ∪ fv_tm e_from ⊆ X ∧
  ∀ σ v,
    dom σ = X →
    closed_env σ →
    subst_map σ e_to →* tret v →
    subst_map σ e_from →* tret v.

Definition expr_result_equiv_on (X : aset) (e1 e2 : tm) : Prop :=
  expr_result_incl_on X e1 e2 ∧ expr_result_incl_on X e2 e1.

Lemma expr_result_incl_on_refl X e :
  fv_tm e ⊆ X →
  expr_result_incl_on X e e.
Proof.
  intros Hfv. split; [set_solver |].
  intros σ v _ _ Hsteps. exact Hsteps.
Qed.

Lemma expr_result_incl_on_trans X e3 e2 e1 :
  expr_result_incl_on X e3 e2 →
  expr_result_incl_on X e2 e1 →
  expr_result_incl_on X e3 e1.
Proof.
  intros [Hfv32 H32] [Hfv21 H21]. split; [set_solver |].
  intros σ v Hdom Hclosed Hsteps.
  pose proof (H32 σ v Hdom Hclosed Hsteps) as Hsteps2.
  exact (H21 σ v Hdom Hclosed Hsteps2).
Qed.

Lemma expr_result_equiv_on_refl X e :
  fv_tm e ⊆ X →
  expr_result_equiv_on X e e.
Proof.
  intros Hfv. split; apply expr_result_incl_on_refl; exact Hfv.
Qed.

Lemma expr_result_equiv_on_sym X e1 e2 :
  expr_result_equiv_on X e1 e2 →
  expr_result_equiv_on X e2 e1.
Proof. intros [H12 H21]. split; assumption. Qed.

Lemma expr_result_equiv_on_trans X e3 e2 e1 :
  expr_result_equiv_on X e3 e2 →
  expr_result_equiv_on X e2 e1 →
  expr_result_equiv_on X e3 e1.
Proof.
  intros [H32 H23] [H21 H12]. split.
  - eapply expr_result_incl_on_trans; eauto.
  - eapply expr_result_incl_on_trans; eauto.
Qed.

Lemma FExprResultOn_models_result_equiv X e_to e_from ν m :
  formula_scoped_in_world ∅ m (FExprResultOn X e_to ν) →
  world_closed_on X m →
  expr_result_equiv_on X e_to e_from →
  m ⊨ FExprResultOn X e_from ν →
  m ⊨ FExprResultOn X e_to ν.
Proof.
  intros Hscope Hclosed [_ Hincl] Hfrom.
  unfold FExprResultOn, res_models, res_models_with_store in *.
  simpl in *.
  destruct Hfrom as [_ [m0 [Hscope0 [Hden Hle]]]].
  split; [exact Hscope |].
  exists m0. split; [exact Hscope0 |]. split; [| exact Hle].
  unfold logic_qualifier_denote, expr_logic_qual_on in *.
  simpl in *.
  intros σw Hσw.
  specialize (Hden σw Hσw) as [v [Hν Hsteps_from]].
  exists v. split; [exact Hν |].
  rewrite !store_restrict_empty in Hsteps_from |- *.
  assert (Hclosed0 : world_closed_on X m0).
  { eapply world_closed_on_le; eauto. }
  assert (Hclosedσ : closed_env (map_restrict value σw X)).
  {
    simpl in Hσw.
    destruct Hσw as [σ1 [Hσ1 Hrestrict1]].
    subst σw.
    change (closed_env (map_restrict value (map_restrict value σ1 (X ∪ {[ν]})) X)).
    rewrite map_restrict_restrict.
    replace ((X ∪ {[ν]}) ∩ X) with X by set_solver.
    exact (Hclosed0 σ1 Hσ1).
  }
  assert (HdomσX : dom (map_restrict value σw X) = X).
  {
    pose proof (wfworld_store_dom
      (res_restrict m0 (X ∪ {[ν]})) σw Hσw)
      as Hdom.
    simpl in Hdom.
    unfold formula_scoped_in_world in Hscope0.
    simpl in Hscope0.
    rewrite dom_empty_L in Hscope0.
    unfold stale, stale_logic_qualifier in Hscope0.
    simpl in Hscope0.
    apply set_eq. intros z. split.
    - intros Hz. rewrite map_restrict_dom in Hz. set_solver.
    - intros Hz.
      assert (Hzdom : z ∈ dom σw).
      { rewrite Hdom. set_solver. }
      apply elem_of_dom in Hzdom as [vz Hvz].
      eapply elem_of_dom_2.
      unfold map_restrict. apply map_lookup_filter_Some_2; last exact Hz.
      exact Hvz.
  }
  assert (Hfv : fv_tm e_to ∪ fv_tm e_from ⊆ X).
  { destruct Hincl as [Hfv _]. set_solver. }
  assert (Hsteps_from_X : subst_map (map_restrict value σw X) e_from →* tret v).
  {
    change (m{map_restrict value σw X} e_from →* tret v).
    change (m{σw} e_from →* tret v) in Hsteps_from.
    rewrite (msubst_restrict_closed_on stale_tm_inst subst_tm_inst
      ltac:(typeclasses eauto) ltac:(typeclasses eauto) ltac:(typeclasses eauto)
      σw X e_from Hclosedσ ltac:(set_solver)).
    exact Hsteps_from.
  }
  pose proof (proj2 Hincl (map_restrict value σw X) v HdomσX Hclosedσ Hsteps_from_X)
    as Hsteps_to_X.
  change (m{σw} e_to →* tret v).
  change (m{map_restrict value σw X} e_to →* tret v) in Hsteps_to_X.
  rewrite <- (msubst_restrict_closed_on stale_tm_inst subst_tm_inst
    ltac:(typeclasses eauto) ltac:(typeclasses eauto) ltac:(typeclasses eauto)
    σw X e_to Hclosedσ ltac:(set_solver)).
  exact Hsteps_to_X.
Qed.

Lemma FExprResultOn_models_shrink X Y e ν m :
  fv_tm e ⊆ X →
  X ⊆ Y →
  world_closed_on X m →
  world_closed_on Y m →
  m ⊨ FExprResultOn Y e ν →
  m ⊨ FExprResultOn X e ν.
Proof.
  intros HeX HXY HclosedX HclosedY Hmodel.
  unfold FExprResultOn, res_models, res_models_with_store in *.
  simpl in *.
  destruct Hmodel as [Hscope [m0 [Hscope0 [Hden Hle]]]].
  split.
  - unfold formula_scoped_in_world in *.
    intros z Hz. apply Hscope.
    unfold formula_fv, stale, stale_logic_qualifier in *.
    simpl in *. set_solver.
  - exists m0. split.
    + unfold formula_scoped_in_world in *.
      intros z Hz. apply Hscope0.
      unfold formula_fv, stale, stale_logic_qualifier in *.
      simpl in *. set_solver.
    + split; [| exact Hle].
      unfold logic_qualifier_denote, expr_logic_qual_on in *.
      simpl in *.
      intros σX HσX.
      simpl in HσX.
      destruct HσX as [σfull [Hσfull HrestrictX]].
      set (σY := store_restrict σfull (Y ∪ {[ν]})).
      assert (HσY : (res_restrict m0 (Y ∪ {[ν]}) : World) σY).
      {
        simpl. exists σfull. split; [exact Hσfull | reflexivity].
      }
      specialize (Hden σY HσY) as [v [HνY HstepsY]].
      exists v. split.
      * rewrite <- HrestrictX.
        apply store_restrict_lookup_some in HνY as [Hνdom Hνfull].
        apply store_restrict_lookup_some_2; [exact Hνfull | set_solver].
      * rewrite <- HrestrictX.
        change (subst_map (store_restrict σfull (X ∪ {[ν]})) e →* tret v).
        change (subst_map σY e →* tret v) in HstepsY.
        assert (HclosedX0 : world_closed_on X m0).
        { eapply world_closed_on_le; eauto. }
        assert (HclosedY0 : world_closed_on Y m0).
        { eapply world_closed_on_le; eauto. }
        assert (HclosedσX : closed_env (store_restrict σfull X)).
        { exact (HclosedX0 σfull Hσfull). }
        assert (HclosedσY : closed_env (store_restrict σfull Y)).
        { exact (HclosedY0 σfull Hσfull). }
        change (subst_map (store_restrict σfull (X ∪ {[ν]})) e)
          with (m{store_restrict σfull (X ∪ {[ν]})} e).
        change (subst_map σY e) with (m{σY} e) in HstepsY.
        assert (HclosedXX :
          closed_env (store_restrict (store_restrict σfull (X ∪ {[ν]})) X)).
        {
          rewrite store_restrict_restrict.
          replace ((X ∪ {[ν]}) ∩ X) with X by set_solver.
          exact HclosedσX.
        }
        assert (HclosedYY : closed_env (store_restrict σY Y)).
        {
          unfold σY. rewrite store_restrict_restrict.
          replace ((Y ∪ {[ν]}) ∩ Y) with Y by set_solver.
          exact HclosedσY.
        }
        rewrite <- (msubst_restrict_closed_on stale_tm_inst subst_tm_inst
          ltac:(typeclasses eauto) ltac:(typeclasses eauto) ltac:(typeclasses eauto)
          (store_restrict σfull (X ∪ {[ν]})) X e) by
          (try exact HclosedXX; set_solver).
        rewrite store_restrict_restrict.
        replace ((X ∪ {[ν]}) ∩ X) with X by set_solver.
        rewrite <- (msubst_restrict_closed_on stale_tm_inst subst_tm_inst
          ltac:(typeclasses eauto) ltac:(typeclasses eauto) ltac:(typeclasses eauto)
          σY Y e) in HstepsY by
          (try exact HclosedYY; set_solver).
        unfold σY in HstepsY. rewrite store_restrict_restrict in HstepsY.
        replace ((Y ∪ {[ν]}) ∩ Y) with Y in HstepsY by set_solver.
        assert (Hagree :
          m{store_restrict σfull Y} e = m{store_restrict σfull X} e).
        {
          eapply (@msubst_agree tm stale_tm_inst subst_tm_inst
            stale_tm_inst subst_tm_inst MsubstRestrict_tm).
          - exact HclosedσY.
          - exact HclosedσX.
          - exact HeX.
          - intros z Hz.
            rewrite !(store_restrict_lookup (V := value)).
            rewrite !decide_True by set_solver. reflexivity.
        }
        rewrite <- Hagree.
        exact HstepsY.
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

Lemma expr_logic_qual_on_ret_const_lookup X c ν m :
  m ⊨ FExprResultOn X (tret (vconst c)) ν →
  ∀ σ, (res_restrict m {[ν]} : World) σ → σ !! ν = Some (vconst c).
Proof.
  intros Hmodel σ Hσ.
  unfold FExprResultOn, res_models, res_models_with_store in Hmodel.
  simpl in Hmodel.
  destruct Hmodel as [_ [m0 [Hscope0 [Hqual Hle]]]].
  assert (Hνm0 : {[ν]} ⊆ world_dom (m0 : World)).
  {
    unfold formula_scoped_in_world in Hscope0.
    simpl in Hscope0.
    unfold stale, stale_logic_qualifier in Hscope0. simpl in Hscope0.
    set_solver.
  }
  assert (Hrestrict_eq : res_restrict m {[ν]} = res_restrict m0 {[ν]}).
  { symmetry. apply res_restrict_le_eq; [exact Hle | exact Hνm0]. }
  assert (Hσm0 : (res_restrict m0 {[ν]} : World) σ).
  { rewrite <- Hrestrict_eq. exact Hσ. }
  simpl in Hσm0.
  destruct Hσm0 as [σ0 [Hσ0 Hrestrict0]].
  unfold logic_qualifier_denote, expr_logic_qual_on in Hqual. simpl in Hqual.
  assert (Hσfull : (res_restrict m0 (X ∪ {[ν]}) : World)
      (store_restrict σ0 (X ∪ {[ν]}))).
  { simpl. exists σ0. split; [exact Hσ0 | reflexivity]. }
  destruct (Hqual (store_restrict σ0 (X ∪ {[ν]})) Hσfull) as
    [v [Hν Hsteps]].
  rewrite store_restrict_empty in Hsteps.
  change (subst_map (store_restrict ∅ X) (tret (vconst c)))
    with (m{store_restrict ∅ X} (tret (vconst c))) in Hsteps.
  rewrite store_restrict_empty in Hsteps.
  rewrite msubst_empty in Hsteps.
  change (subst_map (store_restrict σ0 (X ∪ {[ν]})) (tret (vconst c)))
    with (m{store_restrict σ0 (X ∪ {[ν]})} (tret (vconst c))) in Hsteps.
  rewrite msubst_fresh in Hsteps by set_solver.
  apply val_steps_self in Hsteps.
  inversion Hsteps. subst v.
  apply store_restrict_lookup_some in Hν as [_ Hν0].
  rewrite <- Hrestrict0.
  apply store_restrict_lookup_some_2; [exact Hν0 | set_solver].
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

    [denot_ty_fuel gas X D Σ τ e] encodes the proposition "expression [e] has
    type [τ]" as a Choice Logic formula under erased basic environment [Σ].
    [X] is the common input domain used to interpret expression-result atoms.
    The finite set [D] is an avoidance set for generated binder
    representatives.  These names only make the syntax concrete:
    [FForall]'s cofinite semantics interprets each binder by renaming the
    representative to every sufficiently fresh atom. *)

Fixpoint denot_ty_fuel
    (gas : nat) (X D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      fresh_forall (D ∪ X ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FExprResultOn X e ν)
               (FAnd
                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
                 (fib_vars (qual_dom φν)
                   (FOver (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      fresh_forall (D ∪ X ∪ fv_tm e ∪ qual_dom φ) (fun ν =>
      let φν := qual_open_atom 0 ν φ in
        (FImpl (FExprResultOn X e ν)
               (FAnd
                 (basic_world_formula (<[ν := TBase b]> Σ) ({[ν]} ∪ qual_dom φν))
                 (fib_vars (qual_dom φν)
                   (FUnder (FAtom (lift_type_qualifier_to_logic φν)))))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty_fuel gas' X D Σ τ1 e) (denot_ty_fuel gas' X D Σ τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty_fuel gas' X D Σ τ1 e) (denot_ty_fuel gas' X D Σ τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty_fuel gas' X D Σ τ1 e) (denot_ty_fuel gas' X D Σ τ2 e)

  (** τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (y x)). *)
  | CTArrow τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FExprResultOn X e y)
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
          let X2 := X ∪ {[y]} ∪ {[x]} in
            FFib y
              (FImpl
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  (** τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (y x)). *)
  | CTWand τx τ =>
      let Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ in
      fresh_forall Dy (fun y =>
      let Dx := {[y]} ∪ Dy in
        (FImpl
          (FExprResultOn X e y)
          (fresh_forall Dx (fun x =>
          let D2 := {[x]} ∪ Dx in
          let X2 := X ∪ {[y]} ∪ {[x]} in
            FFib y
              (FWand
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) τx (tret (vfvar x)))
                (denot_ty_fuel gas' X2 D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
                   (tapp (vfvar y) (vfvar x))))))))

  end
  end.

Definition denot_ty_avoiding
    (X D : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) X D Σ τ e.

Definition denot_ty_on
    (X : aset) (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_avoiding X (dom Σ ∪ fv_cty τ ∪ fv_tm e ∪ X) Σ τ e.

Definition denot_ty_under (Σ : gmap atom ty) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (fv_tm e) Σ τ e.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under ∅ τ e.

Definition denot_ty_in_ctx (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_under (erase_ctx Γ) τ e.

Definition erase_ctx_under (Σ : gmap atom ty) (Γ : ctx) : gmap atom ty :=
  Σ ∪ erase_ctx Γ.

Definition denot_ty_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_on (dom (erase_ctx_under Σ Γ)) (erase_ctx_under Σ Γ) τ e.

Definition denot_ty_total_in_ctx_under
    (Σ : gmap atom ty) (Γ : ctx) (τ : choice_ty) (e : tm)
    (m : WfWorld) : Prop :=
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e ∧
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.

Definition entails_total (φ : FQ) (P : WfWorld → Prop) : Prop :=
  ∀ m, m ⊨ φ → P m.

Lemma denot_ty_total_formula Σ Γ τ e m :
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  m ⊨ denot_ty_in_ctx_under Σ Γ τ e.
Proof. intros [H _]. exact H. Qed.

Lemma denot_ty_total_expr_total Σ Γ τ e m :
  denot_ty_total_in_ctx_under Σ Γ τ e m →
  expr_total_on (dom (erase_ctx_under Σ Γ)) e m.
Proof. intros [_ H]. exact H. Qed.

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

Definition formula_store_equiv (φ ψ : FQ) : Prop :=
  ∀ ρ m, res_models_with_store ρ m φ ↔ res_models_with_store ρ m ψ.

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

Lemma formula_store_equiv_refl φ : formula_store_equiv φ φ.
Proof. intros ρ m; reflexivity. Qed.

Lemma formula_store_equiv_sym φ ψ :
  formula_store_equiv φ ψ → formula_store_equiv ψ φ.
Proof. intros H ρ m. symmetry. apply H. Qed.

Lemma formula_store_equiv_trans φ ψ χ :
  formula_store_equiv φ ψ →
  formula_store_equiv ψ χ →
  formula_store_equiv φ χ.
Proof.
  intros Hφψ Hψχ ρ m.
  transitivity (res_models_with_store ρ m ψ); [apply Hφψ | apply Hψχ].
Qed.

Lemma formula_store_equiv_and φ1 φ2 ψ1 ψ2 :
  formula_fv φ1 = formula_fv ψ1 →
  formula_fv φ2 = formula_fv ψ2 →
  formula_store_equiv φ1 ψ1 →
  formula_store_equiv φ2 ψ2 →
  formula_store_equiv (FAnd φ1 φ2) (FAnd ψ1 ψ2).
Proof.
  intros Hfv1 Hfv2 H1 H2 ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope Hmodel]; split.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite <- Hfv1, <- Hfv2. exact Hscope.
  - destruct Hmodel as [Hφ1 Hφ2]. split.
    + pose proof (proj1 (H1 ρ m)) as H.
      assert (Hφ1_exact : res_models_with_store ρ m φ1).
      { eapply res_models_with_store_fuel_irrel; [| | exact Hφ1]; simpl; lia. }
      eapply res_models_with_store_fuel_irrel; [| | exact (H Hφ1_exact)];
        simpl; lia.
    + pose proof (proj1 (H2 ρ m)) as H.
      assert (Hφ2_exact : res_models_with_store ρ m φ2).
      { eapply res_models_with_store_fuel_irrel; [| | exact Hφ2]; simpl; lia. }
      eapply res_models_with_store_fuel_irrel; [| | exact (H Hφ2_exact)];
        simpl; lia.
  - unfold formula_scoped_in_world in *. simpl in *.
    rewrite Hfv1, Hfv2. exact Hscope.
  - destruct Hmodel as [Hψ1 Hψ2]. split.
    + pose proof (proj2 (H1 ρ m)) as H.
      assert (Hψ1_exact : res_models_with_store ρ m ψ1).
      { eapply res_models_with_store_fuel_irrel; [| | exact Hψ1]; simpl; lia. }
      eapply res_models_with_store_fuel_irrel; [| | exact (H Hψ1_exact)];
        simpl; lia.
    + pose proof (proj2 (H2 ρ m)) as H.
      assert (Hψ2_exact : res_models_with_store ρ m ψ2).
      { eapply res_models_with_store_fuel_irrel; [| | exact Hψ2]; simpl; lia. }
      eapply res_models_with_store_fuel_irrel; [| | exact (H Hψ2_exact)];
        simpl; lia.
Qed.

Lemma formula_store_equiv_over φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FOver φ) (FOver ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia. }
    eapply res_models_with_store_fuel_irrel; [| | exact (H Hφ_exact)]; simpl; lia.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia. }
    eapply res_models_with_store_fuel_irrel; [| | exact (H Hψ_exact)]; simpl; lia.
Qed.

Lemma formula_store_equiv_under φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FUnder φ) (FUnder ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [m0 [Hsub Hφ]]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj1 (Heq ρ m0)) as H.
    assert (Hφ_exact : res_models_with_store ρ m0 φ).
    { eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia. }
    eapply res_models_with_store_fuel_irrel; [| | exact (H Hφ_exact)]; simpl; lia.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - exists m0. split; [exact Hsub |].
    pose proof (proj2 (Heq ρ m0)) as H.
    assert (Hψ_exact : res_models_with_store ρ m0 ψ).
    { eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia. }
    eapply res_models_with_store_fuel_irrel; [| | exact (H Hψ_exact)]; simpl; lia.
Qed.

Lemma formula_store_equiv_fib x φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_store_equiv (FFib x φ) (FFib x ψ).
Proof.
  intros Hfv Heq ρ m.
  unfold res_models_with_store. simpl. split; intros [Hscope [Hdisj Hfib]]; split.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite <- Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hφ.
    pose proof (proj1 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hφ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) φ).
    { eapply res_models_with_store_fuel_irrel; [| | exact Hφ]; simpl; lia. }
    eapply res_models_with_store_fuel_irrel; [| | exact (H Hφ_exact)]; simpl; lia.
  - unfold formula_scoped_in_world in *. simpl in *. rewrite Hfv. exact Hscope.
  - split; [exact Hdisj |].
    intros σ Hproj.
    pose proof (Hfib σ Hproj) as Hψ.
    pose proof (proj2 (Heq (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj))) as H.
    assert (Hψ_exact : res_models_with_store (ρ ∪ σ)
      (res_fiber_from_projection m {[x]} σ Hproj) ψ).
    { eapply res_models_with_store_fuel_irrel; [| | exact Hψ]; simpl; lia. }
    eapply res_models_with_store_fuel_irrel; [| | exact (H Hψ_exact)]; simpl; lia.
Qed.

Lemma foldr_fib_store_equiv xs φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (foldr FFib φ xs) = formula_fv (foldr FFib ψ xs) ∧
  formula_store_equiv (foldr FFib φ xs) (foldr FFib ψ xs).
Proof.
  induction xs as [|x xs IH]; simpl; intros Hfv Heq.
  - split; [exact Hfv | exact Heq].
  - destruct (IH Hfv Heq) as [Hfv' Heq'].
    split.
    + simpl. rewrite Hfv'. reflexivity.
    + apply formula_store_equiv_fib; assumption.
Qed.

Lemma fib_vars_store_equiv X φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (fib_vars X φ) = formula_fv (fib_vars X ψ) ∧
  formula_store_equiv (fib_vars X φ) (fib_vars X ψ).
Proof.
  intros Hfv Heq.
  unfold fib_vars, set_fold.
  apply foldr_fib_store_equiv; assumption.
Qed.

Lemma denot_ty_fuel_env_agree gas X D Σ1 Σ2 τ e :
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_fuel gas X D Σ1 τ e = denot_ty_fuel gas X D Σ2 τ e.
Proof.
  revert X D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros X D Σ1 Σ2 τ e Hagree; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
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
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
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
  - rewrite (IH X D Σ1 Σ2 τ1 e).
    + rewrite (IH X D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH X D Σ1 Σ2 τ1 e).
    + rewrite (IH X D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - rewrite (IH X D Σ1 Σ2 τ1 e).
    + rewrite (IH X D Σ1 Σ2 τ2 e); [reflexivity |].
      intros z Hz. apply Hagree. set_solver.
    + intros z Hz. apply Hagree. set_solver.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    assert (Harg :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
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
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    assert (Harg :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) τx (tret (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) τx (tret (vfvar x))).
    {
      apply IH.
      intros z Hz.
      destruct (decide (z = x)) as [->|Hne].
      - rewrite !lookup_insert_eq. reflexivity.
      - rewrite !lookup_insert_ne by congruence.
        apply Hagree. simpl in Hz. set_solver.
    }
    assert (Hres :
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ1) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) =
      denot_ty_fuel gas X2 D2 (<[x:=erase_ty τx]> Σ2) ({0 ~> x} τ)
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
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e = denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  unfold denot_ty_under, denot_ty_on, denot_ty_avoiding.
  rewrite Hdom.
  apply denot_ty_fuel_env_agree. exact Hagree.
Qed.

Lemma denot_ty_under_env_equiv Σ1 Σ2 τ e :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (fv_cty τ) Σ1 Σ2 →
  denot_ty_under Σ1 τ e ⊣⊢ denot_ty_under Σ2 τ e.
Proof.
  intros Hdom Hagree.
  rewrite (denot_ty_under_env_agree Σ1 Σ2 τ e Hdom Hagree).
  apply formula_equiv_refl.
Qed.

Lemma denot_ty_in_ctx_env_agree Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e = denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_agree.
  - exact Hdom.
  - exact Hagree.
Qed.

Lemma denot_ty_in_ctx_env_equiv Γ1 Γ2 τ e :
  dom (erase_ctx Γ1) = dom (erase_ctx Γ2) →
  ty_env_agree_on (fv_cty τ) (erase_ctx Γ1) (erase_ctx Γ2) →
  denot_ty_in_ctx Γ1 τ e ⊣⊢ denot_ty_in_ctx Γ2 τ e.
Proof.
  intros Hdom Hagree. unfold denot_ty_in_ctx.
  apply denot_ty_under_env_equiv.
  - exact Hdom.
  - exact Hagree.
Qed.

(** ** Denotation scoping regularity

    These syntactic facts isolate the variable-accounting needed by semantic
    subtyping reflexivity.  They are intentionally stated at the denotation
    layer: typing proofs should consume these regularity lemmas rather than
    unfolding the formula generated for each type constructor. *)

Lemma denot_ty_fuel_formula_fv_subset gas X D Σ τ e :
  cty_measure τ <= gas →
  formula_fv (denot_ty_fuel gas X D Σ τ e) ⊆
    D ∪ X ∪ fv_tm e ∪ fv_cty τ.
Proof.
  revert X D Σ τ e.
  induction gas as [|gas IH]; intros X D Σ τ e Hgas.
  { pose proof (cty_measure_gt_0 τ). lia. }
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      pose proof (qual_open_atom_dom_subset 0 ν φ) as Hopen.
      pose proof (fib_vars_formula_fv_subset (qual_dom (qual_open_atom 0 ν φ))
        (FOver (FAtom (lift_type_qualifier_to_logic (qual_open_atom 0 ν φ)))))
        as Hfib.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzν].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzrhs].
      {
        unfold expr_logic_qual_on in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzνin].
        - set_solver.
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
          + set_solver.
          + exfalso. apply Hzν. exact Hzνin.
      }
      apply Hfib in Hzfib. simpl in Hzfib.
      unfold stale, stale_logic_qualifier in Hzfib.
      rewrite lqual_dom_lift_type_qualifier_to_logic in Hzfib.
      destruct φ as [B d p]. unfold qual_open_atom in *. simpl in *.
      destruct (decide (0 ∈ B)); simpl in *; set_solver.
    - unfold fresh_forall. simpl.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      pose proof (qual_open_atom_dom_subset 0 ν φ) as Hopen.
      pose proof (fib_vars_formula_fv_subset (qual_dom (qual_open_atom 0 ν φ))
        (FUnder (FAtom (lift_type_qualifier_to_logic (qual_open_atom 0 ν φ)))))
        as Hfib.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzν].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzrhs].
      {
        unfold expr_logic_qual_on in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzνin].
        - set_solver.
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
          + set_solver.
          + exfalso. apply Hzν. exact Hzνin.
      }
      apply Hfib in Hzfib. simpl in Hzfib.
      unfold stale, stale_logic_qualifier in Hzfib.
      rewrite lqual_dom_lift_type_qualifier_to_logic in Hzfib.
      destruct φ as [B d p]. unfold qual_open_atom in *. simpl in *.
      destruct (decide (0 ∈ B)); simpl in *; set_solver.
    - pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    - pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    - pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    - unfold fresh_forall. simpl.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      set (X2 := X ∪ {[y]} ∪ {[x]}).
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ) τx
        (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
        as Hres.
      pose proof (cty_open_fv_subset 0 x τ) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hy].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzinner].
      {
        unfold expr_logic_qual_on in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzyin].
        - set_solver.
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
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      set (X2 := X ∪ {[y]} ∪ {[x]}).
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ) τx
        (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ) ({0 ~> x} τ)
        (tapp (vfvar y) (vfvar x)) ltac:(rewrite cty_open_preserves_measure; lia))
        as Hres.
      pose proof (cty_open_fv_subset 0 x τ) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hy].
      simpl in Hz.
      apply elem_of_union in Hz as [Hzexpr | Hzinner].
      {
        unfold expr_logic_qual_on in Hzexpr. simpl in Hzexpr.
        unfold stale, stale_logic_qualifier, lqual_dom in Hzexpr.
        apply elem_of_union in Hzexpr as [Hzfv | Hzyin].
        - set_solver.
        - exfalso. apply Hy. exact Hzyin.
      }
      apply elem_of_difference in Hzinner as [Hzinner Hx].
      simpl in Hzinner.
      apply elem_of_union in Hzinner as [Hzyin | Hzimpl].
      { exfalso. apply Hy. exact Hzyin. }
      apply elem_of_union in Hzimpl as [Hzarg | Hzres].
      + apply Harg in Hzarg. simpl in Hzarg. set_solver.
      + apply Hres in Hzres. simpl in Hzres. set_solver.
Qed.

Lemma denot_ty_formula_fv_subset τ e :
  formula_fv (denot_ty τ e) ⊆ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty, denot_ty_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) (fv_tm e) (dom (∅ : gmap atom ty) ∪ fv_cty τ ∪ fv_tm e ∪ fv_tm e) ∅ τ e ltac:(lia)) as Hfv.
  replace (fv_cty τ ∪ fv_tm e ∪ ∅) with (fv_cty τ ∪ fv_tm e) by set_solver.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_formula_fv_env_agree gas X D Σ1 Σ2 τ e :
  formula_fv (denot_ty_fuel gas X D Σ1 τ e) =
  formula_fv (denot_ty_fuel gas X D Σ2 τ e).
Proof.
  revert X D Σ1 Σ2 τ e.
  induction gas as [|gas IH]; intros X D Σ1 Σ2 τ e; [reflexivity |].
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - unfold fresh_forall.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
    set (φν := qual_open_atom 0 ν φ).
    reflexivity.
  - rewrite (IH X D Σ1 Σ2 τ1 e), (IH X D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH X D Σ1 Σ2 τ1 e), (IH X D Σ1 Σ2 τ2 e). reflexivity.
  - rewrite (IH X D Σ1 Σ2 τ1 e), (IH X D Σ1 Σ2 τ2 e). reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
  - unfold fresh_forall.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    set (Dx := {[y]} ∪ Dy).
    set (x := fresh_for Dx).
    set (D2 := {[x]} ∪ Dx).
    set (X2 := X ∪ {[y]} ∪ {[x]}).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      τx (tret (vfvar x))).
    rewrite (IH X2 D2 (<[x:=erase_ty τx]> Σ1) (<[x:=erase_ty τx]> Σ2)
      ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))).
    reflexivity.
Qed.

Lemma denot_ty_under_formula_fv_subset Σ τ e :
  formula_fv (denot_ty_under Σ τ e) ⊆ dom Σ ∪ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) (fv_tm e)
    (dom Σ ∪ fv_cty τ ∪ fv_tm e ∪ fv_tm e) Σ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_on_formula_fv_subset X Σ τ e :
  formula_fv (denot_ty_on X Σ τ e) ⊆ dom Σ ∪ X ∪ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) X (dom Σ ∪ fv_cty τ ∪ fv_tm e ∪ X)
    Σ τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_in_ctx_under_formula_fv_subset Σ Γ τ e :
  formula_fv (denot_ty_in_ctx_under Σ Γ τ e) ⊆
    dom (erase_ctx_under Σ Γ) ∪ fv_tm e ∪ fv_cty τ.
Proof.
  unfold denot_ty_in_ctx_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_formula_fv_subset
    (cty_measure τ) (dom (erase_ctx_under Σ Γ))
    (dom (erase_ctx_under Σ Γ) ∪ fv_cty τ ∪ fv_tm e ∪ dom (erase_ctx_under Σ Γ))
    (erase_ctx_under Σ Γ) τ e ltac:(lia)) as Hfv.
  intros z Hz. apply Hfv in Hz. set_solver.
Qed.

Lemma denot_ty_fuel_expr_fv_subset gas X D Σ τ e :
  cty_measure τ <= gas →
  fv_tm e ⊆ X →
  fv_tm e ⊆ formula_fv (denot_ty_fuel gas X D Σ τ e).
Proof.
  revert X D Σ τ e.
  induction gas as [|gas IH]; intros X D Σ τ e Hgas HX.
  { pose proof (cty_measure_gt_0 τ). lia. }
  destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
  - unfold fresh_forall. simpl.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
    pose proof (fresh_for_not_in (D ∪ X ∪ fv_tm e ∪ qual_dom φ)) as Hν.
    intros z Hz. apply elem_of_difference. split.
    + simpl. apply elem_of_union_l. rewrite stale_expr_logic_qual_on. set_solver.
    + set_solver.
  - unfold fresh_forall. simpl.
    set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
    pose proof (fresh_for_not_in (D ∪ X ∪ fv_tm e ∪ qual_dom φ)) as Hν.
    intros z Hz. apply elem_of_difference. split.
    + simpl. apply elem_of_union_l. rewrite stale_expr_logic_qual_on. set_solver.
    + set_solver.
  - pose proof (IH X D Σ τ1 e ltac:(lia) HX) as H1.
    pose proof (IH X D Σ τ2 e ltac:(lia) HX) as H2.
    set_solver.
  - pose proof (IH X D Σ τ1 e ltac:(lia) HX) as H1.
    pose proof (IH X D Σ τ2 e ltac:(lia) HX) as H2.
    set_solver.
  - pose proof (IH X D Σ τ1 e ltac:(lia) HX) as H1.
    pose proof (IH X D Σ τ2 e ltac:(lia) HX) as H2.
    set_solver.
  - unfold fresh_forall. simpl.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    pose proof (fresh_for_not_in Dy) as Hy.
    intros z Hz. apply elem_of_difference. split.
    + simpl. apply elem_of_union_l. rewrite stale_expr_logic_qual_on. set_solver.
    + set_solver.
  - unfold fresh_forall. simpl.
    set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
    set (y := fresh_for Dy).
    pose proof (fresh_for_not_in Dy) as Hy.
    intros z Hz. apply elem_of_difference. split.
    + simpl. apply elem_of_union_l. rewrite stale_expr_logic_qual_on. set_solver.
    + set_solver.
Qed.

Lemma denot_ty_under_result_atom_fv Σ x τ :
  x ∈ formula_fv (denot_ty_under Σ τ (tret (vfvar x))).
Proof.
  unfold denot_ty_under, denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_expr_fv_subset
    (cty_measure τ) (fv_tm (tret (vfvar x)))
    (dom Σ ∪ fv_cty τ ∪ fv_tm (tret (vfvar x)) ∪ fv_tm (tret (vfvar x))) Σ τ
    (tret (vfvar x)) ltac:(lia) ltac:(set_solver)) as Hfv.
  apply Hfv. simpl. set_solver.
Qed.

Lemma denot_ty_on_result_atom_fv X Σ x τ :
  x ∈ X →
  x ∈ formula_fv (denot_ty_on X Σ τ (tret (vfvar x))).
Proof.
  intros Hx.
  unfold denot_ty_on, denot_ty_avoiding.
  pose proof (denot_ty_fuel_expr_fv_subset
    (cty_measure τ) X
    (dom Σ ∪ fv_cty τ ∪ fv_tm (tret (vfvar x)) ∪ X) Σ τ
    (tret (vfvar x)) ltac:(lia) ltac:(simpl; set_solver)) as Hfv.
  apply Hfv. simpl. set_solver.
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
  res_restrict m (dom Σ ∪ fv_tm e ∪ fv_cty τ) ⊨ denot_ty_under Σ τ e.
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

Lemma erase_ctx_dom_subset Γ :
  dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ; simpl.
  - rewrite dom_empty_L. set_solver.
  - rewrite dom_singleton_L. set_solver.
  - rewrite dom_union_L. set_solver.
  - rewrite dom_union_L. set_solver.
  - set_solver.
Qed.

Lemma ctx_dom_subset_stale Γ :
  ctx_dom Γ ⊆ ctx_stale Γ.
Proof.
  induction Γ; simpl; set_solver.
Qed.

Fixpoint denot_ctx_under (Σ : gmap atom ty) (Γ : ctx) : FQ :=
  match Γ with
  | CtxEmpty        => FTrue
  | CtxBind x τ    =>
      denot_ty_on (dom Σ ∪ {[x]}) (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))
  | CtxComma Γ1 Γ2 =>
      FAnd
        (denot_ctx_under Σ Γ1)
        (denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2)
  | CtxStar  Γ1 Γ2 => FStar (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  | CtxSum   Γ1 Γ2 => FPlus (denot_ctx_under Σ Γ1) (denot_ctx_under Σ Γ2)
  end.

Definition denot_ctx (Γ : ctx) : FQ :=
  denot_ctx_under (erase_ctx Γ) Γ.

Definition denot_ctx_in_env (Σ : gmap atom ty) (Γ : ctx) : FQ :=
  FAnd (basic_world_formula Σ (dom Σ))
       (FAnd
          (basic_world_formula (erase_ctx_under Σ Γ) (dom (erase_ctx_under Σ Γ)))
          (denot_ctx_under Σ Γ)).

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
  induction Γ in Σ |- *; simpl.
  - set_solver.
  - intros z Hz. apply elem_of_singleton in Hz. subst.
    apply denot_ty_on_result_atom_fv. set_solver.
  - pose proof (IHΓ1 Σ) as H1.
    pose proof (IHΓ2 (Σ ∪ erase_ctx Γ1)) as H2.
    set_solver.
  - pose proof (IHΓ1 Σ) as H1.
    pose proof (IHΓ2 Σ) as H2.
    set_solver.
  - pose proof (IHΓ1 Σ) as H1.
    pose proof (IHΓ2 Σ) as H2.
    set_solver.
Qed.

Lemma denot_ctx_in_env_dom_subset_formula_fv Σ Γ :
  dom Σ ∪ ctx_dom Γ ⊆ formula_fv (denot_ctx_in_env Σ Γ).
Proof.
  unfold denot_ctx_in_env. simpl.
  pose proof (denot_ctx_under_dom_subset_formula_fv Σ Γ)
    as Hctx.
  intros z Hz.
  apply elem_of_union in Hz as [HzΣ | HzΓ].
  - apply elem_of_union. right. apply elem_of_union. left.
    unfold erase_ctx_under.
    change (z ∈ dom (Σ ∪ erase_ctx Γ)).
    rewrite dom_union_L. set_solver.
  - apply elem_of_union. right. apply elem_of_union. right.
    apply Hctx. exact HzΓ.
Qed.

Lemma denot_ctx_dom_subset_formula_fv Γ :
  ctx_dom Γ ⊆ formula_fv (denot_ctx Γ).
Proof.
  unfold denot_ctx. apply denot_ctx_under_dom_subset_formula_fv.
Qed.

Lemma denot_ctx_under_formula_fv_subset Σ Γ :
  formula_fv (denot_ctx_under Σ Γ) ⊆ dom Σ ∪ ctx_stale Γ.
Proof.
  induction Γ in Σ |- *; simpl.
  - set_solver.
  - pose proof (denot_ty_on_formula_fv_subset (dom Σ ∪ {[x]})
      (<[x:=erase_ty τ]> Σ) τ (tret (vfvar x))) as Hτ.
    intros z Hz. apply Hτ in Hz. simpl in Hz. set_solver.
  - pose proof (IHΓ1 Σ) as H1.
    pose proof (IHΓ2 (Σ ∪ erase_ctx Γ1)) as H2.
    intros z Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply H1 in Hz. set_solver.
    + apply H2 in Hz.
      rewrite dom_union_L in Hz.
      pose proof (ctx_dom_subset_stale Γ1).
      pose proof (erase_ctx_dom_subset Γ1).
      set_solver.
  - pose proof (IHΓ1 Σ) as H1.
    pose proof (IHΓ2 Σ) as H2.
    intros z Hz. apply elem_of_union in Hz as [Hz|Hz]; [apply H1 in Hz|apply H2 in Hz]; set_solver.
  - pose proof (IHΓ1 Σ) as H1.
    pose proof (IHΓ2 Σ) as H2.
    intros z Hz. apply elem_of_union in Hz as [Hz|Hz]; [apply H1 in Hz|apply H2 in Hz]; set_solver.
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

(** Environment-indexed comma context denotations are sequential: the right
    subcontext is interpreted under the environment extended by the erased
    left subcontext. *)
Lemma denot_ctx_under_comma Σ Γ1 Γ2 m :
  m ⊨ denot_ctx_under Σ (CtxComma Γ1 Γ2) ↔
  m ⊨ denot_ctx_under Σ Γ1 ∧
  m ⊨ denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2.
Proof.
  unfold res_models, res_models_with_store. simpl.
  split.
  - intros [Hscope [HΓ1 HΓ2]]. split.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ1]; simpl; lia.
    + eapply res_models_with_store_fuel_irrel; [| | exact HΓ2]; simpl; lia.
  - intros [HΓ1 HΓ2]. split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m
        (denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2) HΓ2).
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
  m ⊨ denot_ty_on (dom Σ ∪ {[x]}) (<[x := erase_ty τ]> Σ) τ (tret (vfvar x)).
Proof. reflexivity. Qed.

Lemma denot_ctx_under_env_equiv Σ1 Σ2 Γ :
  dom Σ1 = dom Σ2 →
  ty_env_agree_on (ctx_stale Γ) Σ1 Σ2 →
  denot_ctx_under Σ1 Γ ⊣⊢ denot_ctx_under Σ2 Γ.
Proof.
Admitted.

(** [⟦CtxBind x τ⟧] is [⟦τ⟧ (return x)]. *)
Lemma denot_ctx_bind x τ m :
  m ⊨ ⟦CtxBind x τ⟧ ↔
  m ⊨ denot_ty_on
    (dom (erase_ctx (CtxBind x τ)) ∪ {[x]})
    (<[x := erase_ty τ]> (erase_ctx (CtxBind x τ)))
    τ (tret (vfvar x)).
Proof. reflexivity. Qed.

Lemma denot_ctx_under_restrict_stale Σ Γ m :
  m ⊨ denot_ctx_under Σ Γ →
  res_restrict m (dom Σ ∪ ctx_stale Γ) ⊨ denot_ctx_under Σ Γ.
Proof.
  intros Hm.
  eapply res_models_kripke.
  - apply res_restrict_mono. apply denot_ctx_under_formula_fv_subset.
  - apply res_models_restrict_fv. exact Hm.
Qed.

Lemma denot_ctx_restrict_stale Γ m :
  m ⊨ ⟦Γ⟧ →
  res_restrict m (dom (erase_ctx Γ) ∪ ctx_stale Γ) ⊨ ⟦Γ⟧.
Proof.
  unfold denot_ctx.
  apply denot_ctx_under_restrict_stale.
Qed.
