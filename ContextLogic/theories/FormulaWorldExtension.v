(** * ContextLogic.FormulaWorldExtension

    Formula-level transport principles for explicit world extensions under the
    store-free semantics.  The old forall-by-extension equivalence lemmas are
    intentionally absent: forall is now defined directly by extension. *)

From ContextAlgebra Require Import ResourceInterface ResourceCompat.
From ContextLogic Require Import FormulaSemantics FormulaConnectives.

Section FormulaWorldExtension.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Lemma res_models_extend_mono
    (m : WfWorldT) (F : fiber_extension (V := V))
    (n : WfWorldT) (φ : FormulaT) :
  res_extend_by m F n →
  res_models m φ →
  res_models n φ.
Proof.
  intros Hext Hmodel.
  eapply res_models_kripke; [| exact Hmodel].
  apply res_extend_by_le with (F := F). exact Hext.
Qed.

Lemma res_models_pullback_subset_projection
    (n p : WfWorldT) Hsub (φ : FormulaT) :
  res_models p φ →
  res_models (res_pullback_subset_projection n p Hsub) φ.
Proof.
  intros Hp.
  pose proof (res_models_scoped p φ Hp) as Hfv.
  set (pb := res_pullback_subset_projection n p Hsub).
  assert (Hpb : res_restrict pb (world_dom (p : WorldT)) = p).
  { subst pb. apply res_pullback_subset_projection_restrict. }
  fold pb.
  unfold res_models in *.
  eapply res_models_fuel_projection; [| exact Hp].
  rewrite <- Hpb.
  rewrite res_restrict_restrict_eq.
  replace (world_dom (p : WorldT) ∩ formula_fv φ) with (formula_fv φ)
    by set_solver.
  reflexivity.
Qed.

End FormulaWorldExtension.
