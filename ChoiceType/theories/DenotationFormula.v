(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Core expressions are embedded through
    [expr_logic_qual], and type qualifiers are embedded directly as
    store/resource atoms after they have been opened to closed atom-based
    qualifiers.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.
From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps StrongNormalization.
From ChoiceType Require Export DenotationFibers.
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


Definition expr_result_store (ν : atom) (eρ : tm) (σw : Store) : Prop :=
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    eρ →* tret v.

Lemma expr_result_store_elim ν eρ σw :
  expr_result_store ν eρ σw →
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    eρ →* tret v.
Proof. intros H. exact H. Qed.

Lemma expr_result_store_intro ν eρ v :
  stale v = ∅ →
  is_lc v →
  eρ →* tret v →
  expr_result_store ν eρ ({[ν := v]}).
Proof. intros Hstale Hlc Hsteps. exists v. repeat split; auto. Qed.

Lemma expr_result_store_swap_result a ν eρ σ :
  expr_result_store ν eρ σ →
  expr_result_store a eρ (store_swap a ν σ).
Proof.
  intros [v [-> [Hstale [Hlc Hsteps]]]].
  exists v. repeat split; auto.
  unfold store_swap. rewrite kmap_singleton.
  replace (atom_swap a ν ν) with a
    by (unfold atom_swap; repeat destruct decide; congruence).
  reflexivity.
Qed.

Lemma expr_result_store_lookup ν eρ σw :
  expr_result_store ν eρ σw →
  ∃ v, σw !! ν = Some v ∧ eρ →* tret v.
Proof.
  intros [v [-> [_ [_ Hsteps]]]].
  exists v. split; [rewrite lookup_singleton; rewrite decide_True by reflexivity; reflexivity |].
  exact Hsteps.
Qed.

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    expr_result_store ν (subst_map ρ e) σν.

Lemma expr_result_in_world_sound ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof. intros H Hw. exact (proj1 (H σw) Hw). Qed.

Lemma expr_result_in_world_complete ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  expr_result_store ν (subst_map ρ e) σw →
  (res_restrict w {[ν]} : World) σw.
Proof. intros H Hσ. exact (proj2 (H σw) Hσ). Qed.

Lemma expr_result_in_world_swap_result ρ e a ν (m : WfWorld) :
  expr_result_in_world ρ e ν m →
  expr_result_in_world ρ e a (res_swap a ν m).
Proof.
  intros H σa. split.
  - intros Hproj_a.
    assert (Hproj_ν : (res_restrict m {[ν]} : World) (store_swap a ν σa)).
    {
      pose proof (res_restrict_swap_projection a ν (res_swap a ν m) {[a]} σa
        Hproj_a) as Hproj_swap.
      rewrite res_swap_involutive in Hproj_swap.
      rewrite aset_swap_singleton in Hproj_swap.
      replace (atom_swap a ν a) with ν in Hproj_swap
        by (unfold atom_swap; repeat destruct decide; congruence).
      exact Hproj_swap.
    }
    pose proof (expr_result_in_world_sound ρ e ν m
      (store_swap a ν σa) H Hproj_ν) as Hstoreν.
    pose proof (expr_result_store_swap_result a ν (subst_map ρ e)
      (store_swap a ν σa) Hstoreν) as Hstorea.
    rewrite store_swap_involutive in Hstorea. exact Hstorea.
  - intros Hstorea.
    assert (Hstoreν : expr_result_store ν (subst_map ρ e) (store_swap a ν σa)).
    {
      pose proof (expr_result_store_swap_result ν a (subst_map ρ e) σa Hstorea)
        as Htmp.
      rewrite store_swap_sym in Htmp. exact Htmp.
    }
    pose proof (expr_result_in_world_complete ρ e ν m
      (store_swap a ν σa) H Hstoreν) as Hprojν.
    change ((res_restrict (res_swap a ν m) {[a]} : World) σa).
    replace ({[a]} : aset) with (aset_swap a ν ({[ν]} : aset)).
    2:{
      rewrite aset_swap_singleton.
      replace (atom_swap a ν ν) with a
        by (unfold atom_swap; repeat destruct decide; congruence).
      reflexivity.
    }
    rewrite res_restrict_swap. simpl.
    exists (store_swap a ν σa). split; [exact Hprojν | apply store_swap_involutive].
Qed.

Lemma expr_result_in_world_store_elim ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    subst_map ρ e →* tret v.
Proof.
  intros Hres Hw.
  exact (expr_result_store_elim ν (subst_map ρ e) σw
    (expr_result_in_world_sound ρ e ν w σw Hres Hw)).
Qed.

Definition expr_logic_qual (e : tm) (ν : atom) : logic_qualifier :=
  lqual {[ν]} (fun σ w => expr_result_in_world σ e ν w).

Definition expr_logic_qual_on (X : aset) (e : tm) (ν : atom) : logic_qualifier :=
  lqual (X ∪ {[ν]})
    (fun σ w => expr_result_in_world (store_restrict σ X) e ν w).

Definition FExprResultAtomOn (X : aset) (e : tm) (ν : atom) : FQ :=
  FStoreResourceAtom (X ∪ {[ν]})
    (fun σ w => expr_result_in_world (store_restrict σ X) e ν w).

Lemma expr_logic_qual_on_swap_result X e a ν :
  a ∉ X →
  ν ∉ X →
  lqual_swap a ν (expr_logic_qual_on X e a) = expr_logic_qual_on X e ν.
Proof.
  intros Ha Hν.
  unfold expr_logic_qual_on, lqual_swap. simpl.
  f_equal.
  - rewrite aset_swap_union, aset_swap_singleton.
    replace (atom_swap a ν a) with ν
      by (unfold atom_swap; repeat destruct decide; congruence).
    rewrite aset_swap_fresh by assumption. reflexivity.
  - apply functional_extensionality. intros σ.
    apply functional_extensionality. intros w.
    apply propositional_extensionality. split; intros Hres.
    + rewrite map_restrict_store_swap_fresh in Hres by assumption.
      pose proof (expr_result_in_world_swap_result (store_restrict σ X) e
        ν a (res_swap a ν w) Hres) as Hback.
      rewrite (res_swap_sym ν a), res_swap_involutive in Hback.
      exact Hback.
    + rewrite map_restrict_store_swap_fresh by assumption.
      apply expr_result_in_world_swap_result. exact Hres.
Qed.

Definition FExprResultOn (X : aset) (e : tm) (ν : atom) : FQ :=
  fib_vars X (FExprResultAtomOn X e ν).

Lemma FExprResultOn_fv X e ν :
  formula_fv (FExprResultOn X e ν) = X ∪ {[ν]}.
Proof.
  unfold FExprResultOn.
  rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
  set_solver.
Qed.

Lemma FExprResultOn_fv_subset X e ν :
  formula_fv (FExprResultOn X e ν) ⊆ X ∪ {[ν]}.
Proof.
  rewrite FExprResultOn_fv. set_solver.
Qed.

Lemma FExprResultOn_rename_result_fresh X e a ν :
  a ∉ X →
  ν ∉ X →
  formula_rename_atom a ν (FExprResultOn X e a) = FExprResultOn X e ν.
Proof.
  intros Ha Hν.
  unfold FExprResultOn.
  rewrite <- formula_rename_atom_fib_vars_fresh by assumption.
  change (fib_vars X (FAtom (lqual_swap a ν (expr_logic_qual_on X e a))) =
          fib_vars X (FAtom (expr_logic_qual_on X e ν))).
  rewrite expr_logic_qual_on_swap_result by assumption.
  reflexivity.
Qed.

(** Expression-result continuation:
    [FExprContIn Σ e Q] abbreviates the recurring formula
    [∀ν. FExprResultOn (dom Σ) e ν ⇒ Q ν].  The cofinite avoidance set is
    exactly [dom Σ]: well-formed typing premises, kept at the Rocq [Prop]
    level rather than inside the logic, ensure that [fv_tm e] and the relevant
    type variables already live in this domain. *)
Definition FExprContIn (Σ : gmap atom ty) (e : tm) (Q : atom → FQ) : FQ :=
  fresh_forall (dom Σ) (fun ν => FImpl (FExprResultOn (dom Σ) e ν) (Q ν)).

Lemma FExprContIn_formula_fv_subset
    (Σ : gmap atom ty) e (S : aset) (Q : atom → FQ) :
  dom Σ ⊆ S →
  (∀ ν, ν ∉ dom Σ → formula_fv (Q ν) ⊆ S ∪ {[ν]}) →
  formula_fv (FExprContIn Σ e Q) ⊆ S.
Proof.
  intros Hdom HQ.
  unfold FExprContIn.
  apply fresh_forall_formula_fv_subset; first exact Hdom.
  intros ν Hν.
  simpl. rewrite FExprResultOn_fv.
  pose proof (HQ ν Hν) as HQν.
  set_solver.
Qed.

Definition formula_family_rename_stable_on
    (D : aset) (P : atom → FQ) : Prop :=
  ∀ x y n,
    x ∉ D →
    y ∉ D →
    n ⊨ formula_rename_atom x y (P x) ↔ n ⊨ P y.

Lemma FExprContIn_post_eq_at_fresh
    (Σ : gmap atom ty) e (P Q : atom → FQ) :
  P (fresh_for (dom Σ)) = Q (fresh_for (dom Σ)) →
  FExprContIn Σ e P = FExprContIn Σ e Q.
Proof.
  intros Heq.
  unfold FExprContIn, fresh_forall.
  rewrite Heq. reflexivity.
Qed.

(** Expression-result atom.

    The operational input domain is exactly [fv_tm e].  Earlier versions kept an
    explicit [X] parameter so several expressions could be compared over a
    common larger domain, but that made the Prop-level specification drift away
    from the formula itself. *)
Definition expr_let_result_in_store_on
    (X : aset) (e1 e2 : tm) (x ν : atom) (σw : Store) : Prop :=
  ∃ vx v,
    σw !! x = Some vx ∧
    σw !! ν = Some v ∧
    subst_map (store_restrict σw X) e1 →* tret vx ∧
    open_tm 0 vx (subst_map (store_restrict σw X) e2) →* tret v.

Definition expr_let_result_in_world_on
    (X : aset) (e1 e2 : tm) (x ν : atom) (w : WfWorld) : Prop :=
  ∀ σw,
    (w : World) σw ↔ expr_let_result_in_store_on X e1 e2 x ν σw.

Lemma expr_let_result_in_world_on_sound X e1 e2 x ν w σw :
  expr_let_result_in_world_on X e1 e2 x ν w →
  (w : World) σw →
  expr_let_result_in_store_on X e1 e2 x ν σw.
Proof. intros H Hw. exact (proj1 (H σw) Hw). Qed.

Lemma expr_let_result_in_world_on_complete X e1 e2 x ν w σw :
  expr_let_result_in_world_on X e1 e2 x ν w →
  expr_let_result_in_store_on X e1 e2 x ν σw →
  (w : World) σw.
Proof. intros H Hstore. exact (proj2 (H σw) Hstore). Qed.

Definition FLetResultOnWith
    (X : aset) (e1 e2 : tm) (x ν : atom) : FQ :=
  fib_vars (X ∪ {[x]})
    (FStoreResourceAtom (X ∪ {[x]} ∪ {[ν]})
      (fun _ w => expr_let_result_in_world_on X e1 e2 x ν w)).

Definition FLetResultOn (X : aset) (e1 e2 : tm) (ν : atom) : FQ :=
  let x := fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}) in
  FExists x (FLetResultOnWith X e1 e2 x ν).

Lemma FLetResultOn_models_elim X e1 e2 ν m :
  m ⊨ FLetResultOn X e1 e2 ν →
  ∃ L : aset,
    world_dom (m : World) ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom (m' : World) = world_dom (m : World) ∪ {[y]} ∧
        res_restrict m' (world_dom (m : World)) = m ∧
        m' ⊨ formula_rename_atom
          (fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) y
          (FLetResultOnWith X e1 e2
            (fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) ν).
Proof.
  unfold FLetResultOn, res_models, res_models_with_store.
  simpl. intros [_ [L [HL Hexists]]].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hbody]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  models_fuel_irrel Hbody.
Qed.

Lemma FLetResultOn_models_intro X e1 e2 ν m :
  formula_scoped_in_world ∅ m (FLetResultOn X e1 e2 ν) →
  (∃ L : aset,
    world_dom (m : World) ⊆ L ∧
    ∀ y : atom,
      y ∉ L →
      ∃ m' : WfWorld,
        world_dom (m' : World) = world_dom (m : World) ∪ {[y]} ∧
        res_restrict m' (world_dom (m : World)) = m ∧
        m' ⊨ formula_rename_atom
          (fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) y
          (FLetResultOnWith X e1 e2
            (fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) ν)) →
  m ⊨ FLetResultOn X e1 e2 ν.
Proof.
  unfold FLetResultOn, res_models, res_models_with_store.
  simpl. intros Hscope [L [HL Hexists]]. split; [exact Hscope |].
  exists L. split; [exact HL |].
  intros y Hy.
  destruct (Hexists y Hy) as [m' [Hdom [Hrestr Hbody]]].
  exists m'. split; [exact Hdom |]. split; [exact Hrestr |].
  models_fuel_irrel Hbody.
Qed.

Lemma FLetResultOnWith_fv X e1 e2 x ν :
  formula_fv (FLetResultOnWith X e1 e2 x ν) = X ∪ {[x]} ∪ {[ν]}.
Proof.
  unfold FLetResultOnWith.
  rewrite fib_vars_formula_fv.
  rewrite formula_fv_FStoreResourceAtom.
  set_solver.
Qed.

Lemma FLetResultOnWith_scoped_intro X e1 e2 x ν (m : WfWorld) :
  X ∪ {[x]} ∪ {[ν]} ⊆ world_dom (m : World) →
  formula_scoped_in_world ∅ m (FLetResultOnWith X e1 e2 x ν).
Proof.
  intros Hdom z Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  rewrite FLetResultOnWith_fv in Hz.
  apply Hdom. exact Hz.
Qed.

Lemma FLetResultOn_fv_subset X e1 e2 ν :
  formula_fv (FLetResultOn X e1 e2 ν) ⊆ X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}.
Proof.
  unfold FLetResultOn.
  set (x := fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  simpl. unfold FLetResultOnWith.
  rewrite fib_vars_formula_fv, formula_fv_FStoreResourceAtom.
  subst x.
  pose proof (fresh_for_not_in (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) as Hx.
  intros z Hz.
  apply elem_of_difference in Hz as [Hz Hzfresh].
  apply elem_of_union in Hz as [Hz | Hz].
  - apply elem_of_union in Hz as [HzX | Hzfresh'].
    + set_solver.
    + exfalso. apply Hzfresh. exact Hzfresh'.
  - apply elem_of_union in Hz as [Hz | Hzν].
    + apply elem_of_union in Hz as [HzX | Hzfresh'].
      * set_solver.
      * exfalso. apply Hzfresh. exact Hzfresh'.
    + set_solver.
Qed.

Lemma FLetResultOn_fv_contains_X X e1 e2 ν :
  X ⊆ formula_fv (FLetResultOn X e1 e2 ν).
Proof.
  unfold FLetResultOn.
  set (x := fresh_for (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  simpl. unfold FLetResultOnWith.
  rewrite fib_vars_formula_fv, formula_fv_FStoreResourceAtom.
  intros z Hz.
  apply elem_of_difference. split; [set_solver |].
  subst x.
  pose proof (fresh_for_not_in (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) as Hfresh.
  intros Hzx. apply elem_of_singleton in Hzx. subst z.
  exact (Hfresh ltac:(set_solver)).
Qed.

Lemma FLetResultOnWith_models_elim_obligation X e1 e2 x ν m :
  m ⊨ FLetResultOnWith X e1 e2 x ν →
  fib_vars_obligation (X ∪ {[x]})
    (FStoreResourceAtom (X ∪ {[x]} ∪ {[ν]})
      (fun _ w => expr_let_result_in_world_on X e1 e2 x ν w)) ∅ m.
Proof.
  unfold FLetResultOnWith, res_models.
  apply fib_vars_models_elim.
Qed.

Lemma FLetResultOnWith_models_intro_obligation X e1 e2 x ν m :
  formula_scoped_in_world ∅ m (FLetResultOnWith X e1 e2 x ν) →
  fib_vars_obligation (X ∪ {[x]})
    (FStoreResourceAtom (X ∪ {[x]} ∪ {[ν]})
      (fun _ w => expr_let_result_in_world_on X e1 e2 x ν w)) ∅ m →
  m ⊨ FLetResultOnWith X e1 e2 x ν.
Proof.
  unfold FLetResultOnWith, res_models.
  apply fib_vars_models_intro.
Qed.

Lemma stale_expr_logic_qual e ν :
  stale (expr_logic_qual e ν) = {[ν]}.
Proof. reflexivity. Qed.

Lemma stale_expr_logic_qual_on X e ν :
  stale (expr_logic_qual_on X e ν) = X ∪ {[ν]}.
Proof. reflexivity. Qed.

Lemma FExprResultOn_scoped_dom X e ν m :
  formula_scoped_in_world ∅ m (FExprResultOn X e ν) →
  X ∪ {[ν]} ⊆ world_dom (m : World).
Proof.
  intros Hscope z Hz.
  apply Hscope.
  apply elem_of_union. right.
  rewrite FExprResultOn_fv.
  set_solver.
Qed.

Lemma FAtom_expr_logic_qual_on_exact X e ν ρ m :
  res_models_with_store ρ m (FAtom (expr_logic_qual_on X e ν)) →
  expr_result_in_world (store_restrict ρ X) e ν m.
Proof.
  unfold res_models_with_store. simpl.
  intros [Hscope [m0 [Hscope0 [Hden Hle]]]] σν.
  unfold logic_qualifier_denote, expr_logic_qual_on in Hden. simpl in Hden.
  rewrite store_restrict_restrict in Hden.
  replace ((X ∪ {[ν]}) ∩ X) with X in Hden by set_solver.
  specialize (Hden σν).
  rewrite !res_restrict_restrict_eq in Hden.
  replace ((X ∪ {[ν]}) ∩ ({[ν]} : aset)) with ({[ν]} : aset) in Hden by set_solver.
  assert (Hνdom : ({[ν]} : aset) ⊆ world_dom (m0 : World)).
  {
    unfold formula_scoped_in_world in Hscope0.
    simpl in Hscope0. unfold stale, stale_logic_qualifier in Hscope0. simpl in Hscope0.
    set_solver.
  }
  rewrite (res_restrict_le_eq m0 m ({[ν]} : aset)) in Hden.
  - exact Hden.
  - exact Hle.
  - exact Hνdom.
Qed.

Lemma FAtom_expr_logic_qual_on_intro X e ν ρ m :
  formula_scoped_in_world ρ m (FAtom (expr_logic_qual_on X e ν)) →
  expr_result_in_world (store_restrict ρ X) e ν m →
  res_models_with_store ρ m (FAtom (expr_logic_qual_on X e ν)).
Proof.
  intros Hscope Hexact.
  unfold res_models_with_store. simpl. split; [exact Hscope |].
  exists m. split; [exact Hscope |]. split; [| reflexivity].
  unfold logic_qualifier_denote, expr_logic_qual_on. simpl.
  rewrite store_restrict_restrict.
  replace ((X ∪ {[ν]}) ∩ X) with X by set_solver.
  intros σν. specialize (Hexact σν).
  rewrite res_restrict_restrict_eq.
  replace ((X ∪ {[ν]}) ∩ ({[ν]} : aset)) with ({[ν]} : aset) by set_solver.
  exact Hexact.
Qed.

(** Prop-level must-totality for the expression component of a type denotation.

    This is intentionally not encoded as a ChoiceLogic formula.  In the
    nondeterministic core language, totality must mean uniform strong
    normalization: there is one fuel bound for all stores in the world.  A
    pointwise existential bound is too weak for [let] when the bound expression
    can produce infinitely many results. *)
Definition expr_total_on (X : aset) (e : tm) (m : WfWorld) : Prop :=
  fv_tm e ⊆ X ∧
  ∃ n, ∀ σ, (m : World) σ →
    strongly_normalizing_fuel n (subst_map (store_restrict σ X) e).

(** [world_closed_on X m] is the ChoiceType-level invariant saying that every
    store in [m] is operationally usable on the coordinates [X].  This belongs
    here rather than in ChoiceAlgebra: the algebra is polymorphic in store
    values, while closedness is a CoreLang [value] property. *)
Definition world_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → store_closed (store_restrict σ X).

Lemma world_closed_on_swap x y X (m : WfWorld) :
  world_closed_on X m →
  world_closed_on (aset_swap x y X) (res_swap x y m).
Proof.
  intros Hclosed σ Hσ.
  simpl in Hσ.
  destruct Hσ as [σ0 [Hσ0 Hswap]]. subst σ.
  rewrite store_restrict_swap.
  apply store_closed_store_swap.
  exact (Hclosed σ0 Hσ0).
Qed.

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
  apply store_closed_restrict.
  exact (Hclosed σn Hσn).
Qed.

Lemma basic_world_formula_world_closed_on Σ X m :
  X ⊆ dom Σ →
  m ⊨ basic_world_formula Σ X →
  world_closed_on X m.
Proof.
  intros HXΣ Hbasic σ Hσ.
  split.
  - eapply basic_world_formula_store_restrict_closed_env; eauto.
  - eapply basic_world_formula_store_restrict_lc_env; eauto.
Qed.

Lemma expr_result_store_let_elim ρ e1 e2 ν σw :
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σw →
  ∃ v vx,
    σw = {[ν := v]} ∧
    subst_map ρ e1 →* tret vx ∧
    open_tm 0 vx (subst_map ρ e2) →* tret v.
Proof.
  intros Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σw Hstore)
    as [v [Hσw [_ [_ Hsteps]]]].
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)) in Hsteps.
  rewrite msubst_lete in Hsteps.
  destruct (reduction_lete (m{ρ} e1) (m{ρ} e2) v Hsteps)
    as [vx [Hsteps1 Hsteps2]].
  exists v, vx. repeat split; assumption.
Qed.

Lemma expr_result_in_world_let_elim ρ e1 e2 ν (w : WfWorld) :
  expr_result_in_world ρ (tlete e1 e2) ν w →
  ∀ σν,
    (res_restrict w {[ν]} : World) σν →
    ∃ v vx,
      σν = {[ν := v]} ∧
      subst_map ρ e1 →* tret vx ∧
      open_tm 0 vx (subst_map ρ e2) →* tret v.
Proof.
  intros Hworld σν Hσν.
  pose proof (expr_result_in_world_sound ρ (tlete e1 e2) ν w σν
    Hworld Hσν) as Hstore.
  exact (expr_result_store_let_elim ρ e1 e2 ν σν Hstore).
Qed.

Lemma expr_result_store_let_intro ρ e1 e2 ν v vx :
  stale v = ∅ →
  is_lc v →
  body_tm (subst_map ρ e2) →
  subst_map ρ e1 →* tret vx →
  open_tm 0 vx (subst_map ρ e2) →* tret v →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) {[ν := v]}.
Proof.
  intros Hv_closed Hv_lc Hbody Hsteps1 Hsteps2.
  apply expr_result_store_intro; [exact Hv_closed | exact Hv_lc |].
  change (subst_map ρ (tlete e1 e2)) with (m{ρ} (tlete e1 e2)).
  rewrite msubst_lete.
  eapply reduction_lete_intro; eauto.
Qed.

Lemma expr_let_result_in_store_on_to_tlete_result X e1 e2 x ν σw v :
  expr_let_result_in_store_on X e1 e2 x ν σw →
  σw !! ν = Some v →
  stale v = ∅ →
  is_lc v →
  body_tm (subst_map (store_restrict σw X) e2) →
  expr_result_store ν
    (subst_map (store_restrict σw X) (tlete e1 e2)) {[ν := v]}.
Proof.
  intros [vx [v' [_ [Hν [Hsteps1 Hsteps2]]]]] Hνv Hv_closed Hv_lc Hbody.
  rewrite Hνv in Hν. inversion Hν. subst v'.
  eapply expr_result_store_let_intro; eauto.
Qed.

Lemma expr_result_in_world_let_intro ρ e1 e2 ν (w : WfWorld) :
  body_tm (subst_map ρ e2) →
  (∀ σν,
    (res_restrict w {[ν]} : World) σν ↔
    ∃ v vx,
      σν = {[ν := v]} ∧
      stale v = ∅ ∧
      is_lc v ∧
      subst_map ρ e1 →* tret vx ∧
      open_tm 0 vx (subst_map ρ e2) →* tret v) →
  expr_result_in_world ρ (tlete e1 e2) ν w.
Proof.
  intros Hbody Hexact σν. split.
  - intros Hσν.
    destruct (proj1 (Hexact σν) Hσν)
      as [v [vx [Hσν_eq [Hv_closed [Hv_lc [Hsteps1 Hsteps2]]]]]].
    subst σν.
    eapply expr_result_store_let_intro; eauto.
  - intros Hstore.
    destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
      as [v [Hσν_eq [Hv_closed [Hv_lc Hsteps]]]].
    destruct (expr_result_store_let_elim ρ e1 e2 ν σν Hstore)
      as [v' [vx [Hσν_eq' [Hsteps1 Hsteps2]]]].
    subst σν.
    assert (Hv' : v' = v).
    {
      assert (({[ν := v']} : Store) !! ν = Some v).
      {
        rewrite <- Hσν_eq'.
        rewrite lookup_singleton. rewrite decide_True by reflexivity.
        reflexivity.
      }
      rewrite lookup_singleton in H.
      rewrite decide_True in H by reflexivity.
      inversion H. reflexivity.
    }
    subst v'.
    apply (proj2 (Hexact {[ν := v]})).
    exists v, vx. repeat split; eauto.
Qed.

Lemma expr_result_store_tlete_to_body_open_atom ρ e1 e2 x ν σν :
  closed_env ρ →
  lc_env ρ →
  x ∉ dom ρ ∪ fv_tm e2 →
  (∀ vx, subst_map ρ e1 →* tret vx → stale vx = ∅ ∧ is_lc vx) →
  expr_result_store ν (subst_map ρ (tlete e1 e2)) σν →
  ∃ vx,
    subst_map ρ e1 →* tret vx ∧
    expr_result_store ν (subst_map (<[x := vx]> ρ) (e2 ^^ x)) σν.
Proof.
  intros Hclosed Hlc Hx Hresult_closed Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
    as [v [Hσν [Hv_closed [Hv_lc _]]]].
  destruct (expr_result_store_let_elim ρ e1 e2 ν σν Hstore)
    as [v' [vx [Hσν' [Hsteps1 Hsteps2]]]].
  subst σν.
  assert (Hv' : v' = v).
  {
    assert (({[ν := v']} : Store) !! ν = Some v).
    {
      rewrite <- Hσν'.
      rewrite lookup_singleton. rewrite decide_True by reflexivity.
      reflexivity.
    }
    rewrite lookup_singleton in H.
    rewrite decide_True in H by reflexivity.
    inversion H. reflexivity.
  }
  subst v'.
  exists vx. split; [exact Hsteps1 |].
  apply expr_result_store_intro; [exact Hv_closed | exact Hv_lc |].
  change (subst_map (<[x := vx]> ρ) (e2 ^^ x)) with
    (m{<[x := vx]> ρ} (open_tm 0 (vfvar x) e2)).
  rewrite (msubst_intro_open_tm e2 0 vx x ρ).
  - exact Hsteps2.
  - exact Hclosed.
  - apply (proj1 (Hresult_closed vx Hsteps1)).
  - apply (proj2 (Hresult_closed vx Hsteps1)).
  - exact Hlc.
  - exact Hx.
Qed.

Lemma expr_result_store_ret_fvar_lookup x ν σw vx :
  stale vx = ∅ →
  σw !! x = Some vx →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σw →
  σw !! ν = Some vx.
Proof.
  intros _ _ Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σw Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.

Lemma expr_result_store_ret_fvar_trans ρ e x ν σw :
  (∀ vx, subst_map σw (subst_map ρ e) →* tret vx → stale vx = ∅) →
  expr_result_store x (subst_map ρ e) σw →
  expr_result_store ν (subst_map ∅ (tret (vfvar x))) σw →
  expr_result_store ν (subst_map ρ e) σw.
Proof.
  intros _ _ Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σw Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
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
  intros _ _ Hret_world.
  exfalso.
  destruct (world_wf w) as [[σ Hσ] _].
  set (σν := store_restrict σ {[ν]}).
  assert (Hprojν : (res_restrict w {[ν]} : World) σν).
  { exists σ. split; [exact Hσ | reflexivity]. }
  pose proof (expr_result_in_world_sound ∅ (tret (vfvar x)) ν w σν
    Hret_world Hprojν) as Hret.
  destruct (expr_result_store_elim ν (subst_map ∅ (tret (vfvar x))) σν Hret)
    as [v [-> [Hv_stale [_ Hsteps]]]].
  simpl in Hsteps.
  pose proof (value_steps_self (vfvar x) (tret v) Hsteps) as Heq.
  inversion Heq. subst v.
  simpl in Hv_stale. set_solver.
Qed.
