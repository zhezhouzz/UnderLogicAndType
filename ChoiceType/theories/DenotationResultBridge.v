(** * ChoiceType.DenotationResultBridge

    Operational and resource-aware comparison principles for expression-result
    atoms.  These lemmas sit after [DenotationFormula]: they depend on
    [FExprResult], but the core denotation atoms do not depend on these
    proof-side transport notions. *)

From LocallyNameless Require Import Tactics.
From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps OperationalResults.
From ChoiceType Require Export DenotationFormula.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Local Notation FQ := FormulaQ.

(** Formula-level transport for expression-result atoms.

    [expr_result_incl_on] is an operational same-input-domain comparison.  The
    type denotation needs a stronger, resource-aware bridge: when the target
    expression-result atom holds in a target extension, we can find a source
    extension where the source atom holds, and any continuation formula whose
    free variables already live in the target extension can be transported
    back to that target extension.

    This last condition is deliberately weaker than [nsrc ⊑ ntgt].  In the
    tlet proof the source extension may contain the auxiliary intermediate
    coordinate [x]; continuations that do not mention [x] should still
    transport by restricting to their free variables.

    [model_transport_on S] makes the relevant continuation scope explicit. *)
Definition model_transport_on (S : aset) (nsrc ntgt : WfWorld) : Prop :=
  ∀ φ : FQ,
    formula_fv φ ⊆ S →
    nsrc ⊨ φ →
    ntgt ⊨ φ.

Definition model_transport (nsrc ntgt : WfWorld) : Prop :=
  model_transport_on (world_dom (ntgt : World)) nsrc ntgt.

(** Resource-aware expression-result bridge.

    The freshness side condition [ν ∉ Xsrc ∪ Xtgt] is essential for tlet:
    the source expression may already use an intermediate result coordinate
    [x] in its input domain [Xsrc = X ∪ {[x]}].  The final result coordinate
    [ν] must stay distinct from that intermediate coordinate, otherwise the
    bridge would conflate the paired [X -> x -> ν] relation that the result
    world is meant to track exactly.

    The disjointness premise for [Xsrc ∖ Xtgt] says that source-only coordinates
    are proof auxiliaries, not coordinates already present in the target world.
    For tlet this is the usual fresh-bound-variable condition [x ∉ dom target].

    The first transport component replaces a too-strong old requirement
    [msrc ⊑ nsrc].  In the tlet proof [nsrc] is a graph world carrying the
    final result coordinate [ν], while [msrc] is the ordinary let-result world.
    They only need to agree on the variables that the source continuation can
    observe, namely [Xsrc]; requiring a full domain restriction would
    incorrectly force graph witnesses to preserve target coordinates that are
    outside the expression-result fiber. *)
Definition expr_result_model_bridge
    (Xsrc : aset) (esrc : tm)
    (Xtgt : aset) (etgt : tm)
    (msrc mtgt : WfWorld) : Prop :=
  ∀ (ν : atom) (ntgt : WfWorld),
    ν ∉ Xsrc ∪ Xtgt →
    (Xsrc ∖ Xtgt) ## world_dom (ntgt : World) →
    ν ∉ world_dom (mtgt : World) →
    mtgt ⊑ ntgt →
    ntgt ⊨ FExprResultAt Xtgt etgt ν →
    ∃ nsrc,
      model_transport_on Xsrc msrc nsrc ∧
      nsrc ⊨ FExprResultAt Xsrc esrc ν ∧
      model_transport_on (Xtgt ∪ {[ν]}) nsrc ntgt.

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

Lemma model_transport_on_restrict_common (S : aset) (nsrc ntgt : WfWorld) :
  S ⊆ world_dom (nsrc : World) ∩ world_dom (ntgt : World) →
  res_restrict nsrc S = res_restrict ntgt S →
  model_transport_on S nsrc ntgt.
Proof.
  intros HS Heq φ Hfv Hφ.
  pose proof (res_models_restrict_fv nsrc φ Hφ) as Hsmall.
  assert (Hsmall_eq :
    res_restrict nsrc (formula_fv φ) =
    res_restrict ntgt (formula_fv φ)).
  {
    transitivity (res_restrict (res_restrict nsrc S) (formula_fv φ)).
    - resource_norm. reflexivity.
    - rewrite Heq.
      resource_norm. reflexivity.
  }
  rewrite Hsmall_eq in Hsmall.
  eapply res_models_kripke.
  - apply res_restrict_le.
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
    - resource_norm. reflexivity.
    - rewrite Heq.
      resource_norm. reflexivity.
  }
  rewrite Hsmall_eq in Hsmall.
  eapply res_models_kripke.
  - apply res_restrict_le.
  - exact Hsmall.
Qed.
