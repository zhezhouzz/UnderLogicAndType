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

Definition fib_vars_obligation_step
    (x : atom)
    (R : Store → WfWorld → Prop)
    (ρ : Store) (m : WfWorld) : Prop :=
  dom ρ ## {[x]} ∧
  ∀ σ (Hproj : res_restrict m {[x]} σ),
    R (ρ ∪ σ) (res_fiber_from_projection m {[x]} σ Hproj).

Definition fib_vars_acc_step
    (x : atom)
    (acc : FQ * (Store → WfWorld → Prop))
    : FQ * (Store → WfWorld → Prop) :=
  let '(p, R) := acc in
  (FFib x p, fib_vars_obligation_step x R).

Definition fib_vars_acc
    (X : aset) (p : FQ) : FQ * (Store → WfWorld → Prop) :=
  set_fold fib_vars_acc_step
    (p, fun ρ m => res_models_with_store ρ m p) X.

Definition fib_vars (X : aset) (p : FQ) : FQ :=
  fst (fib_vars_acc X p).

Definition fib_vars_obligation
    (X : aset) (p : FQ) (ρ : Store) (m : WfWorld) : Prop :=
  snd (fib_vars_acc X p) ρ m.

Lemma fib_vars_singleton x p :
  fib_vars {[x]} p = FFib x p.
Proof.
  unfold fib_vars, fib_vars_acc.
  rewrite set_fold_singleton. reflexivity.
Qed.

Lemma fib_vars_formula_fv_subset X p :
  formula_fv (fib_vars X p) ⊆ X ∪ formula_fv p.
Proof.
  unfold fib_vars, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc Y => formula_fv (fst acc) ⊆ Y ∪ formula_fv p)).
  - simpl. set_solver.
  - intros x Y acc Hx HY.
    destruct acc as [q R]. simpl in *.
    intros z Hz.
    apply elem_of_union in Hz as [Hzx | Hzq].
    + set_solver.
    + apply HY in Hzq. set_solver.
Qed.

Lemma fib_vars_formula_fv X p :
  formula_fv (fib_vars X p) = X ∪ formula_fv p.
Proof.
  unfold fib_vars, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc Y => formula_fv (fst acc) = Y ∪ formula_fv p)).
  - simpl. set_solver.
  - intros x Y acc Hx HY.
    destruct acc as [q R]. simpl in *.
    rewrite HY. set_solver.
Qed.

Lemma fib_vars_models_elim X p ρ m :
  res_models_with_store ρ m (fib_vars X p) →
  fib_vars_obligation X p ρ m.
Proof.
  unfold fib_vars, fib_vars_obligation, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc _ =>
      ∀ ρ m, res_models_with_store ρ m (fst acc) → snd acc ρ m)).
  - simpl. auto.
  - intros x Y acc Hx IH ρ0 m0 Hm.
    destruct acc as [q R]. simpl in *.
    unfold fib_vars_obligation_step.
    unfold res_models_with_store in Hm. simpl in Hm.
    destruct Hm as [_ [Hdisj Hfib]].
    split; [exact Hdisj |].
    intros σ Hproj.
    specialize (Hfib σ Hproj).
    eapply IH.
    eapply res_models_with_store_fuel_irrel; [| | exact Hfib]; simpl; lia.
Qed.

Lemma fib_vars_models_intro X p ρ m :
  formula_scoped_in_world ρ m (fib_vars X p) →
  fib_vars_obligation X p ρ m →
  res_models_with_store ρ m (fib_vars X p).
Proof.
  unfold fib_vars, fib_vars_obligation, fib_vars_acc.
  apply (set_fold_ind_L
    (fun acc _ =>
      ∀ ρ m,
        formula_scoped_in_world ρ m (fst acc) →
        snd acc ρ m →
        res_models_with_store ρ m (fst acc))).
  - simpl. auto.
  - intros x Y acc Hx IH ρ0 m0 Hscope Hobl.
    destruct acc as [q R]. simpl in *.
    unfold fib_vars_obligation_step in Hobl.
    destruct Hobl as [Hdisj Hfib].
    unfold res_models_with_store. simpl.
    split; [exact Hscope |].
    split; [exact Hdisj |].
    intros σ Hproj.
    specialize (Hfib σ Hproj).
    assert (Hscope_q :
      formula_scoped_in_world (ρ0 ∪ σ)
        (res_fiber_from_projection m0 {[x]} σ Hproj) q).
    {
      unfold formula_scoped_in_world in *.
      simpl in Hscope.
      pose proof (wfworld_store_dom (res_restrict m0 {[x]}) σ Hproj) as Hdomσ.
      simpl in Hdomσ.
      rewrite dom_union_L.
      intros z Hz.
      apply elem_of_union in Hz as [Hzρσ | Hzq].
      - apply elem_of_union in Hzρσ as [Hzρ | Hzσ].
        + assert (Hzscope : z ∈ dom ρ0 ∪ ({[x]} ∪ formula_fv q)).
          { set_solver. }
          pose proof (Hscope z Hzscope) as Hzdom.
          simpl in Hzdom. exact Hzdom.
        + rewrite Hdomσ in Hzσ.
          pose proof (Hscope z ltac:(set_solver)) as Hzdom.
          simpl in Hzdom. exact Hzdom.
      - assert (Hzscope : z ∈ dom ρ0 ∪ ({[x]} ∪ formula_fv q)).
        { set_solver. }
        pose proof (Hscope z Hzscope) as Hzdom.
        simpl in Hzdom. exact Hzdom.
    }
    eapply IH; eauto.
Qed.

Definition expr_result_value (eρ : tm) (v : value) : Prop :=
  eρ →* tret v.

Definition expr_result_store (ν : atom) (eρ : tm) (σw : Store) : Prop :=
  ∃ v,
    σw = {[ν := v]} ∧
    stale v = ∅ ∧
    is_lc v ∧
    expr_result_value eρ v.

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

Lemma expr_result_store_lookup ν eρ σw :
  expr_result_store ν eρ σw →
  ∃ v, σw !! ν = Some v ∧ eρ →* tret v.
Proof.
  intros [v [-> [_ [_ Hsteps]]]].
  exists v. split; [rewrite lookup_singleton; rewrite decide_True by reflexivity; reflexivity |].
  exact Hsteps.
Qed.

Definition expr_result_in_store (ρ : Store) (e : tm) (ν : atom) (σw : Store) : Prop :=
  expr_result_store ν (subst_map ρ e) σw.

Definition expr_result_in_world (ρ : Store) (e : tm) (ν : atom) (w : WfWorld) : Prop :=
  ∀ σν,
    (res_restrict w {[ν]} : World) σν ↔ expr_result_in_store ρ e ν σν.

Lemma expr_result_in_world_sound ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  (res_restrict w {[ν]} : World) σw →
  expr_result_in_store ρ e ν σw.
Proof. intros H Hw. exact (proj1 (H σw) Hw). Qed.

Lemma expr_result_in_world_complete ρ e ν w σw :
  expr_result_in_world ρ e ν w →
  expr_result_in_store ρ e ν σw →
  (res_restrict w {[ν]} : World) σw.
Proof. intros H Hσ. exact (proj2 (H σw) Hσ). Qed.

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

Definition FExprResult (e : tm) (ν : atom) : FQ :=
  fib_vars (fv_tm e) (FAtom (expr_logic_qual_on (fv_tm e) e ν)).

(** Domain-explicit expression-result atom.

    [FExprResult e ν] uses [fv_tm e] as the input domain.  That is fine for a
    single expression, but comparisons between open expressions need both sides
    interpreted over the same input domain.  [FExprResultOn X e ν] records that
    common domain explicitly; callers should provide [fv_tm e ⊆ X] and choose
    [ν ∉ X]. *)
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

Definition let_expr_logic_qual_on
    (X : aset) (e1 e2 : tm) (x ν : atom) : logic_qualifier :=
  lqual (X ∪ {[x]} ∪ {[ν]})
    (fun _ w => expr_let_result_in_world_on X e1 e2 x ν w).

Definition FLetResultOnWith
    (X : aset) (e1 e2 : tm) (x ν : atom) : FQ :=
  fib_vars (X ∪ {[x]}) (FAtom (let_expr_logic_qual_on X e1 e2 x ν)).

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
  eapply res_models_with_store_fuel_irrel; [| | exact Hbody];
    rewrite formula_rename_preserves_measure; lia.
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
  eapply res_models_with_store_fuel_irrel; [| | exact Hbody];
    rewrite formula_rename_preserves_measure; lia.
Qed.

Definition FExprResultOnRaw (X : aset) (e : tm) (ν : atom) : FQ :=
  fib_vars X (FAtom (expr_logic_qual_on X e ν)).

Definition FExprResultOn (X : aset) (e : tm) (ν : atom) : FQ :=
  FExprResultOnRaw X e ν.

Lemma stale_let_expr_logic_qual_on X e1 e2 x ν :
  stale (let_expr_logic_qual_on X e1 e2 x ν) = X ∪ {[x]} ∪ {[ν]}.
Proof. reflexivity. Qed.

Lemma FLetResultOnWith_fv X e1 e2 x ν :
  formula_fv (FLetResultOnWith X e1 e2 x ν) = X ∪ {[x]} ∪ {[ν]}.
Proof.
  unfold FLetResultOnWith.
  rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
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
  simpl. unfold FLetResultOnWith. rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
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
  simpl. unfold FLetResultOnWith. rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
  intros z Hz.
  apply elem_of_difference. split; [set_solver |].
  subst x.
  pose proof (fresh_for_not_in (X ∪ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})) as Hfresh.
  intros Hzx. apply elem_of_singleton in Hzx. subst z.
  exact (Hfresh ltac:(set_solver)).
Qed.

Lemma FExprResultOn_fv_subset X e ν :
  formula_fv (FExprResultOn X e ν) ⊆ X ∪ {[ν]}.
Proof.
  unfold FExprResultOn, FExprResultOnRaw.
  rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
  set_solver.
Qed.

Lemma FExprResultOn_expr_fv_subset X e ν :
  fv_tm e ⊆ X →
  fv_tm e ⊆ formula_fv (FExprResultOn X e ν).
Proof.
  intros Hfv.
  unfold FExprResultOn, FExprResultOnRaw.
  rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
  set_solver.
Qed.

Lemma FLetResultOnWith_models_elim_obligation X e1 e2 x ν m :
  m ⊨ FLetResultOnWith X e1 e2 x ν →
  fib_vars_obligation (X ∪ {[x]})
    (FAtom (let_expr_logic_qual_on X e1 e2 x ν)) ∅ m.
Proof.
  unfold FLetResultOnWith, res_models.
  apply fib_vars_models_elim.
Qed.

Lemma FLetResultOnWith_models_intro_obligation X e1 e2 x ν m :
  formula_scoped_in_world ∅ m (FLetResultOnWith X e1 e2 x ν) →
  fib_vars_obligation (X ∪ {[x]})
    (FAtom (let_expr_logic_qual_on X e1 e2 x ν)) ∅ m →
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
  unfold FExprResultOn, FExprResultOnRaw.
  rewrite fib_vars_formula_fv. simpl.
  unfold stale, stale_logic_qualifier. simpl.
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

Lemma expr_result_in_store_let_elim ρ e1 e2 ν σw :
  expr_result_in_store ρ (tlete e1 e2) ν σw →
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
  exact (expr_result_in_store_let_elim ρ e1 e2 ν σν Hstore).
Qed.

Lemma expr_result_in_store_let_intro ρ e1 e2 ν v vx :
  stale v = ∅ →
  is_lc v →
  body_tm (subst_map ρ e2) →
  subst_map ρ e1 →* tret vx →
  open_tm 0 vx (subst_map ρ e2) →* tret v →
  expr_result_in_store ρ (tlete e1 e2) ν {[ν := v]}.
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
  expr_result_in_store (store_restrict σw X) (tlete e1 e2) ν {[ν := v]}.
Proof.
  intros [vx [v' [_ [Hν [Hsteps1 Hsteps2]]]]] Hνv Hv_closed Hv_lc Hbody.
  rewrite Hνv in Hν. inversion Hν. subst v'.
  eapply expr_result_in_store_let_intro; eauto.
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
    eapply expr_result_in_store_let_intro; eauto.
  - intros Hstore.
    destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
      as [v [Hσν_eq [Hv_closed [Hv_lc Hsteps]]]].
    destruct (expr_result_in_store_let_elim ρ e1 e2 ν σν Hstore)
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

Lemma expr_result_in_store_tlete_to_body_open_atom ρ e1 e2 x ν σν :
  closed_env ρ →
  lc_env ρ →
  x ∉ dom ρ ∪ fv_tm e2 →
  (∀ vx, subst_map ρ e1 →* tret vx → stale vx = ∅ ∧ is_lc vx) →
  expr_result_in_store ρ (tlete e1 e2) ν σν →
  ∃ vx,
    subst_map ρ e1 →* tret vx ∧
    expr_result_in_store (<[x := vx]> ρ) (e2 ^^ x) ν σν.
Proof.
  intros Hclosed Hlc Hx Hresult_closed Hstore.
  destruct (expr_result_store_elim ν (subst_map ρ (tlete e1 e2)) σν Hstore)
    as [v [Hσν [Hv_closed [Hv_lc _]]]].
  destruct (expr_result_in_store_let_elim ρ e1 e2 ν σν Hstore)
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

Lemma expr_result_in_store_ret_fvar_lookup x ν σw vx :
  stale vx = ∅ →
  σw !! x = Some vx →
  expr_result_in_store ∅ (tret (vfvar x)) ν σw →
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

Lemma expr_result_in_store_ret_fvar_trans ρ e x ν σw :
  (∀ vx, subst_map σw (subst_map ρ e) →* tret vx → stale vx = ∅) →
  expr_result_in_store ρ e x σw →
  expr_result_in_store ∅ (tret (vfvar x)) ν σw →
  expr_result_in_store ρ e ν σw.
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

(** Formula-level transport for expression-result atoms.

    [expr_result_incl_on] is an operational same-input-domain comparison.  The
    type denotation needs a stronger, resource-aware bridge: when the target
    expression-result atom holds in a target extension, we can find a source
    extension where the source atom holds, and any continuation formula whose
    free variables already live in the target extension can be transported
    back to that target extension.

    This last condition is deliberately weaker than [nsrc ⊑ ntgt].  In the
    tlet proof the source extension may be a graph world that contains the
    auxiliary intermediate coordinate [x]; continuations that do not mention
    [x] should still transport by restricting to their free variables. *)
Definition model_transport (nsrc ntgt : WfWorld) : Prop :=
  ∀ φ : FQ,
    formula_fv φ ⊆ world_dom (ntgt : World) →
    nsrc ⊨ φ →
    ntgt ⊨ φ.

(** Resource-aware expression-result bridge.

    The freshness side condition [ν ∉ Xsrc ∪ Xtgt] is essential for tlet:
    the source expression may already use an intermediate result coordinate
    [x] in its input domain [Xsrc = X ∪ {[x]}].  The final result coordinate
    [ν] must stay distinct from that intermediate coordinate, otherwise the
    bridge would conflate the paired [X -> x -> ν] relation that the result
    world is meant to track exactly. *)
Definition expr_result_model_bridge
    (Xsrc : aset) (esrc : tm)
    (Xtgt : aset) (etgt : tm)
    (msrc mtgt : WfWorld) : Prop :=
  ∀ ν ntgt,
    ν ∉ Xsrc ∪ Xtgt →
    ν ∉ world_dom (mtgt : World) →
    mtgt ⊑ ntgt →
    ntgt ⊨ FExprResultOn Xtgt etgt ν →
    ∃ nsrc,
      msrc ⊑ nsrc ∧
      nsrc ⊨ FExprResultOn Xsrc esrc ν ∧
      model_transport nsrc ntgt.

Lemma model_transport_kripke (nsrc ntgt : WfWorld) :
  nsrc ⊑ ntgt →
  model_transport nsrc ntgt.
Proof.
  intros Hle φ _ Hφ.
  eapply res_models_kripke; eauto.
Qed.

Lemma model_transport_restrict_eq (nsrc ntgt : WfWorld) :
  res_restrict nsrc (world_dom (ntgt : World)) = ntgt →
  model_transport nsrc ntgt.
Proof.
  intros Hrestrict φ Hfv Hφ.
  pose proof (res_models_restrict_fv nsrc φ Hφ) as Hsmall.
  eapply res_models_kripke.
  - rewrite <- Hrestrict.
    apply res_restrict_mono. exact Hfv.
  - exact Hsmall.
Qed.

Lemma model_transport_restrict_common (nsrc ntgt : WfWorld) S :
  world_dom (nsrc : World) ∩ world_dom (ntgt : World) ⊆ S →
  res_restrict nsrc S = res_restrict ntgt S →
  model_transport nsrc ntgt.
Proof.
  intros Hcommon Heq φ Hfv Hφ.
  pose proof (res_models_with_store_fuel_scoped
    (formula_measure φ) ∅ nsrc φ Hφ) as Hscope_src.
  assert (HfvS : formula_fv φ ⊆ S).
  {
    unfold formula_scoped_in_world in Hscope_src.
    intros z Hz.
    apply Hcommon. apply elem_of_intersection. split.
    - apply Hscope_src. set_solver.
    - apply Hfv. exact Hz.
  }
  pose proof (res_models_restrict_fv nsrc φ Hφ) as Hsmall.
  assert (Hsmall_eq :
    res_restrict nsrc (formula_fv φ) =
    res_restrict ntgt (formula_fv φ)).
  {
    transitivity (res_restrict (res_restrict nsrc S) (formula_fv φ)).
    - rewrite res_restrict_restrict_eq.
      replace (S ∩ formula_fv φ) with (formula_fv φ) by set_solver.
      reflexivity.
    - rewrite Heq.
      rewrite res_restrict_restrict_eq.
      replace (S ∩ formula_fv φ) with (formula_fv φ) by set_solver.
      reflexivity.
  }
  rewrite Hsmall_eq in Hsmall.
  eapply res_models_kripke.
  - apply res_restrict_le.
  - exact Hsmall.
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
