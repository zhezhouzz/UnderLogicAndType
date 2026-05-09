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

Lemma FExprResultOn_models_elim X e ν m :
  m ⊨ FExprResultOn X e ν →
  ∃ w : WfWorld,
    formula_scoped_in_world ∅ w (FExprResultOn X e ν) ∧
    expr_result_in_world ∅ e ν (res_restrict w (X ∪ {[ν]})) ∧
    w ⊑ m.
Proof.
Admitted.

Lemma FExprResultOn_models_intro X e ν m w :
  formula_scoped_in_world ∅ m (FExprResultOn X e ν) →
  formula_scoped_in_world ∅ w (FExprResultOn X e ν) →
  expr_result_in_world ∅ e ν (res_restrict w (X ∪ {[ν]})) →
  w ⊑ m →
  m ⊨ FExprResultOn X e ν.
Proof.
Admitted.

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
Admitted.

Lemma expr_let_result_in_world_on_to_tlete
    X e1 e2 x ν (w : WfWorld) :
  fv_tm e1 ⊆ X →
  fv_tm e2 ⊆ X →
  world_closed_on X w →
  (∀ σw, (w : World) σw →
    body_tm (subst_map (store_restrict σw X) e2)) →
  expr_let_result_in_world_on X e1 e2 x ν w →
  expr_result_in_world ∅ (tlete e1 e2) ν (res_restrict w (X ∪ {[ν]})).
Proof.
Admitted.

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

Lemma FExprResult_models_elim e ν m :
  m ⊨ FExprResult e ν →
  ∃ w : WfWorld,
    formula_scoped_in_world ∅ w (FExprResult e ν) ∧
    expr_result_in_world
      (store_restrict ∅ (stale e ∪ {[ν]})) e ν
      (res_restrict w (stale e ∪ {[ν]})) ∧
    w ⊑ m.
Proof.
Admitted.

Lemma FExprResult_models_intro e ν m w :
  formula_scoped_in_world ∅ m (FExprResult e ν) →
  formula_scoped_in_world ∅ w (FExprResult e ν) →
  expr_result_in_world
    (store_restrict ∅ (stale e ∪ {[ν]})) e ν
    (res_restrict w (stale e ∪ {[ν]})) →
  w ⊑ m →
  m ⊨ FExprResult e ν.
Proof.
Admitted.

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
Admitted.

Lemma FExprResultOn_models_shrink X Y e ν m :
  fv_tm e ⊆ X →
  X ⊆ Y →
  world_closed_on X m →
  world_closed_on Y m →
  m ⊨ FExprResultOn Y e ν →
  m ⊨ FExprResultOn X e ν.
Proof.
Admitted.

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
Proof.
  unfold FExprResult. rewrite fib_vars_formula_fv.
  simpl. unfold stale, stale_logic_qualifier. simpl. set_solver.
Qed.

Lemma FLetResult_fv_subset e1 e2 ν :
  formula_fv (FLetResult e1 e2 ν) ⊆ fv_tm e1 ∪ fv_tm e2 ∪ {[ν]}.
Proof.
  unfold FLetResult.
  set (x := fresh_for (fv_tm e1 ∪ fv_tm e2 ∪ {[ν]})).
  simpl. rewrite !FExprResult_fv.
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
  X ∪ fv_tm e ∪ {[ν]} ⊆ world_dom (m : World) →
  formula_scoped_in_world ∅ m (FExprResultOn X e ν).
Proof.
  intros Hdom z Hz.
  apply elem_of_union in Hz as [Hzempty | Hz]; [set_solver |].
  pose proof (FExprResultOn_fv_subset X e ν z Hz) as Hz'.
  apply Hdom. set_solver.
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
  rewrite FExprResult_fv in Hz. simpl in Hz.
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
Admitted.

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
Admitted.

Lemma expr_logic_qual_denote_store_restrict e ν ρ w X :
  closed_env ρ →
  stale e ⊆ X →
  logic_qualifier_denote (expr_logic_qual e ν) (map_restrict value ρ X) w ↔
  logic_qualifier_denote (expr_logic_qual e ν) ρ w.
Proof.
Admitted.

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
Admitted.

Lemma expr_logic_qual_ret_value_denote_lookup v ν w σ :
  logic_qualifier_denote (expr_logic_qual (tret v) ν) ∅ w →
  (res_restrict w (stale v ∪ {[ν]}) : World) σ →
  σ !! ν = Some (m{σ} v).
Proof.
Admitted.

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
Admitted.

Lemma expr_logic_qual_ret_fvar_denote_lookup x ν w σ vx :
  logic_qualifier_denote (expr_logic_qual (tret (vfvar x)) ν) ∅ w →
  (res_restrict w ({[x]} ∪ {[ν]}) : World) σ →
  closed_env σ →
  σ !! x = Some vx →
  σ !! ν = Some vx.
Proof.
Admitted.

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

Lemma foldr_fib_vars_acc_fst xs φ R :
  fst (foldr fib_vars_acc_step (φ, R) xs) = foldr FFib φ xs.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite <- IH. destruct (foldr fib_vars_acc_step (φ, R) xs); reflexivity.
Qed.

Lemma fib_vars_store_equiv X φ ψ :
  formula_fv φ = formula_fv ψ →
  formula_store_equiv φ ψ →
  formula_fv (fib_vars X φ) = formula_fv (fib_vars X ψ) ∧
  formula_store_equiv (fib_vars X φ) (fib_vars X ψ).
Proof.
  intros Hfv Heq.
  unfold fib_vars, fib_vars_acc, set_fold.
  simpl.
  rewrite !foldr_fib_vars_acc_fst.
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
  - destruct τ; simpl in Hgas; lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      set (φν := qual_open_atom 0 ν φ).
      assert (Hφν : qual_dom φν ⊆ qual_dom φ ∪ {[ν]})
        by (subst φν; apply qual_open_atom_dom_subset).
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      change (stale e) with (fv_tm e).
      rewrite lqual_dom_lift_type_qualifier_to_logic.
	      pose proof (FExprResultOn_fv_subset X e ν) as Hres_fv.
	      intros z Hz.
	      apply elem_of_difference in Hz as [Hz Hzν].
	      set_solver.
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      set (φν := qual_open_atom 0 ν φ).
      assert (Hφν : qual_dom φν ⊆ qual_dom φ ∪ {[ν]})
        by (subst φν; apply qual_open_atom_dom_subset).
      rewrite fib_vars_formula_fv. simpl.
      unfold stale, stale_logic_qualifier. simpl.
      change (stale e) with (fv_tm e).
      rewrite lqual_dom_lift_type_qualifier_to_logic.
	      pose proof (FExprResultOn_fv_subset X e ν) as Hres_fv.
	      intros z Hz.
	      apply elem_of_difference in Hz as [Hz Hzν].
	      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia)) as H1.
      pose proof (IH X D Σ τ2 e ltac:(lia)) as H2.
      set_solver.
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      set (X2 := X ∪ {[y]} ∪ {[x]}).
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))
        ltac:(rewrite cty_open_preserves_measure; lia)) as Hres.
      pose proof (cty_open_fv_subset 0 x τ) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzy].
      apply elem_of_union in Hz as [Hzres_e | Hzrest].
	      * pose proof (FExprResultOn_fv_subset X e y) as Hres_fv.
	        apply Hres_fv in Hzres_e. set_solver.
      * apply elem_of_difference in Hzrest as [Hzrest Hzx].
        apply elem_of_union in Hzrest as [Hzy0 | Hzrest].
        { set_solver. }
        apply elem_of_union in Hzrest as [Hzarg | Hzbody].
        -- apply Harg in Hzarg. simpl in Hzarg. set_solver.
        -- apply Hres in Hzbody. simpl in Hzbody. set_solver.
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      set (Dx := {[y]} ∪ Dy).
      set (x := fresh_for Dx).
      set (D2 := {[x]} ∪ Dx).
      set (X2 := X ∪ {[y]} ∪ {[x]}).
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        τx (tret (vfvar x)) ltac:(lia)) as Harg.
      pose proof (IH X2 D2 (<[x := erase_ty τx]> Σ)
        ({0 ~> x} τ) (tapp (vfvar y) (vfvar x))
        ltac:(rewrite cty_open_preserves_measure; lia)) as Hres.
      pose proof (cty_open_fv_subset 0 x τ) as Hopen.
      intros z Hz.
      apply elem_of_difference in Hz as [Hz Hzy].
      apply elem_of_union in Hz as [Hzres_e | Hzrest].
	      * pose proof (FExprResultOn_fv_subset X e y) as Hres_fv.
	        apply Hres_fv in Hzres_e. set_solver.
      * apply elem_of_difference in Hzrest as [Hzrest Hzx].
        apply elem_of_union in Hzrest as [Hzy0 | Hzrest].
        { set_solver. }
        apply elem_of_union in Hzrest as [Hzarg | Hzbody].
        -- apply Harg in Hzarg. simpl in Hzarg. set_solver.
        -- apply Hres in Hzbody. simpl in Hzbody. set_solver.
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
  induction gas as [|gas IH]; intros X D Σ τ e Hgas Hfv.
  - destruct τ; simpl in Hgas; lia.
  - destruct τ as [b φ|b φ|τ1 τ2|τ1 τ2|τ1 τ2|τx τ|τx τ]; simpl in *.
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      assert (Hνe : ν ∉ fv_tm e)
        by (subst ν; pose proof (fresh_for_not_in (D ∪ X ∪ fv_tm e ∪ qual_dom φ)); set_solver).
	      pose proof (FExprResultOn_expr_fv_subset X e ν Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzν. apply elem_of_singleton in Hzν. subst z. exact (Hνe Hz).
    + unfold fresh_forall.
      set (ν := fresh_for (D ∪ X ∪ fv_tm e ∪ qual_dom φ)).
      assert (Hνe : ν ∉ fv_tm e)
        by (subst ν; pose proof (fresh_for_not_in (D ∪ X ∪ fv_tm e ∪ qual_dom φ)); set_solver).
	      pose proof (FExprResultOn_expr_fv_subset X e ν Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzν. apply elem_of_singleton in Hzν. subst z. exact (Hνe Hz).
    + pose proof (IH X D Σ τ1 e ltac:(lia) Hfv) as H1.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia) Hfv) as H1.
      set_solver.
    + pose proof (IH X D Σ τ1 e ltac:(lia) Hfv) as H1.
      set_solver.
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      assert (Hye : y ∉ fv_tm e)
        by (subst y Dy; pose proof (fresh_for_not_in (D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ)); set_solver).
	      pose proof (FExprResultOn_expr_fv_subset X e y Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzy. apply elem_of_singleton in Hzy. subst z. exact (Hye Hz).
    + unfold fresh_forall.
      set (Dy := D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ).
      set (y := fresh_for Dy).
      assert (Hye : y ∉ fv_tm e)
        by (subst y Dy; pose proof (fresh_for_not_in (D ∪ fv_tm e ∪ fv_cty τx ∪ fv_cty τ)); set_solver).
	      pose proof (FExprResultOn_expr_fv_subset X e y Hfv) as Hres_fv.
	      intros z Hz. apply elem_of_difference. split; [set_solver |].
	      intros Hzy. apply elem_of_singleton in Hzy. subst z. exact (Hye Hz).
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
  intros Hdom Hagree.
  assert (Heq : denot_ctx_under Σ1 Γ = denot_ctx_under Σ2 Γ).
  {
    revert Σ1 Σ2 Hdom Hagree.
    induction Γ as [|x τ|Γ1 IH1 Γ2 IH2|Γ1 IH1 Γ2 IH2|Γ1 IH1 Γ2 IH2];
      intros Σ1 Σ2 Hdom Hagree; simpl.
    - reflexivity.
    - unfold denot_ty_on, denot_ty_avoiding.
      replace (dom Σ1 ∪ {[x]}) with (dom Σ2 ∪ {[x]}) by set_solver.
      replace (dom (<[x:=erase_ty τ]> Σ1))
        with (dom (<[x:=erase_ty τ]> Σ2)).
      + apply denot_ty_fuel_env_agree.
        intros z Hz.
        destruct (decide (z = x)) as [->|Hne].
        * rewrite !lookup_insert_eq. reflexivity.
        * rewrite !lookup_insert_ne by congruence.
          apply Hagree. simpl. set_solver.
      + rewrite !dom_insert_L. set_solver.
    - rewrite (IH1 Σ1 Σ2 Hdom).
      2:{ intros z Hz. apply Hagree. simpl. set_solver. }
      assert (HdomU :
        dom (Σ1 ∪ erase_ctx Γ1) = dom (Σ2 ∪ erase_ctx Γ1)).
      { rewrite !dom_union_L. set_solver. }
      rewrite (IH2 (Σ1 ∪ erase_ctx Γ1) (Σ2 ∪ erase_ctx Γ1) HdomU).
      + reflexivity.
      + intros z Hz.
        destruct (Σ1 !! z) as [T1|] eqn:H1;
          destruct (Σ2 !! z) as [T2|] eqn:H2.
        * assert (HT : T1 = T2).
          {
            pose proof (Hagree z ltac:(simpl; set_solver)) as Hzagree.
            rewrite H1, H2 in Hzagree. inversion Hzagree. reflexivity.
          }
          subst T2. rewrite !lookup_union, H1, H2. reflexivity.
        * exfalso.
          apply elem_of_dom_2 in H1.
          apply not_elem_of_dom in H2.
          apply H2. rewrite <- Hdom. exact H1.
        * exfalso.
          apply elem_of_dom_2 in H2.
          apply not_elem_of_dom in H1.
          apply H1. rewrite Hdom. exact H2.
        * rewrite !lookup_union, H1, H2. reflexivity.
    - rewrite (IH1 Σ1 Σ2 Hdom).
      2:{ intros z Hz. apply Hagree. simpl. set_solver. }
      rewrite (IH2 Σ1 Σ2 Hdom).
      + reflexivity.
      + intros z Hz. apply Hagree. simpl. set_solver.
    - rewrite (IH1 Σ1 Σ2 Hdom).
      2:{ intros z Hz. apply Hagree. simpl. set_solver. }
      rewrite (IH2 Σ1 Σ2 Hdom).
      + reflexivity.
      + intros z Hz. apply Hagree. simpl. set_solver.
  }
  rewrite Heq. apply formula_equiv_refl.
Qed.

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
