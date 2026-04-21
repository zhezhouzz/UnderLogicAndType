From UnderLogicAndType Require Import Prelude Substitution.

Section S.
Context `{Countable Var} `{EqDecision Value}.

Lemma subst_restrict_dom σ X :
  dom (subst_restrict σ X) = dom σ ∩ X.
Proof.
  unfold subst_restrict.
  rewrite <- (filter_dom_L (λ k : Var, k ∈ X) σ).
  apply (anti_raw (=)). intros i.
  rewrite elem_of_intersection, elem_of_filter, !elem_of_dom.
  unfold is_Some. naive_solver.
Qed.

End S.
