(** * ChoiceType.DenotationContext

    Context denotation and context-locality lemmas. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceType Require Export DenotationType.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

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
      denot_ty_on (<[x := erase_ty τ]> Σ) τ (tret (vfvar x))
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
  unfold denot_ctx_in_env.
  cbn [formula_fv].
  rewrite !basic_world_formula_fv.
  pose proof (erase_ctx_dom_subset Γ) as Herase.
  pose proof (denot_ctx_under_dom_subset_formula_fv Σ Γ) as Hctx.
  unfold erase_ctx_under.
  rewrite dom_union_L.
  set_solver.
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
  - pose proof (denot_ty_on_fv_subset
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
    + models_fuel_irrel HΓ1.
    + models_fuel_irrel HΓ2.
  - intros [HΓ1 HΓ2]. split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m
        (denot_ctx_under (Σ ∪ erase_ctx Γ1) Γ2) HΓ2).
      set_solver.
    + split.
      * models_fuel_irrel HΓ1.
      * models_fuel_irrel HΓ2.
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
    + models_fuel_irrel HΓ1.
    + models_fuel_irrel HΓ2.
  - intros [m1 [m2 [Hc [Hprod [HΓ1 HΓ2]]]]].
    split.
    + unfold formula_scoped_in_world in *. simpl.
      pose proof (res_models_with_store_fuel_scoped _ ∅ m1 (denot_ctx_under Σ Γ1) HΓ1).
      pose proof (res_models_with_store_fuel_scoped _ ∅ m2 (denot_ctx_under Σ Γ2) HΓ2).
      pose proof (raw_le_dom _ _ Hprod). set_solver.
    + exists m1, m2, Hc. split; [exact Hprod |]. split.
      * models_fuel_irrel HΓ1.
      * models_fuel_irrel HΓ2.
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
    + models_fuel_irrel HΓ1.
    + models_fuel_irrel HΓ2.
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
      * models_fuel_irrel HΓ1.
      * models_fuel_irrel HΓ2.
Qed.

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
    - apply denot_ty_on_env_agree.
      + rewrite !dom_insert_L. set_solver.
      + intros z Hz.
        destruct (decide (z = x)) as [->|Hne].
        * rewrite !lookup_insert_eq. reflexivity.
        * rewrite !lookup_insert_ne by congruence.
          apply Hagree. simpl. set_solver.
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
