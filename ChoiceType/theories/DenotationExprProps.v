(** * ChoiceType.DenotationExprProps

    Auxiliary expression-result lemmas used by type denotation. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceType Require Export DenotationFormula.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

Lemma FExprResultOn_expr_fv e ν :
  formula_fv (FExprResultAt (fv_tm e) e ν) = fv_tm e ∪ {[ν]}.
Proof.
  apply FExprResultAt_fv.
Qed.

Lemma expr_logic_qual_ret_closed_value_denote_lookup v ν w σ :
  stale v = ∅ →
  logic_qualifier_denote (expr_logic_qual (tret v) ν) ∅ w →
  (res_restrict w {[ν]} : World) σ →
  σ !! ν = Some v.
Proof.
  intros Hvclosed Hden Hσ.
  unfold logic_qualifier_denote, expr_logic_qual in Hden. simpl in Hden.
  rewrite lvars_fv_of_atoms in Hden.
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
  rewrite lvars_fv_of_atoms in Hden.
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

(** ** Type measure for denotation fuel

    As in HATs' denotation, the first argument of [denot_ty_fuel] is an
    over-approximation of the syntactic size of the type.  This lets the
    denotation recurse on opened locally-nameless bodies such as
    [{0 ~> x} τ], which are not syntactic subterms accepted by Rocq's
    structural termination checker. *)
