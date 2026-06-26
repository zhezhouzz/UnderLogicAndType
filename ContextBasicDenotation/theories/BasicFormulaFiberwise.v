(** * BasicDenotation.BasicFormulaFiberwise

    Fiberwise aggregation facts for the basic denotation atoms.  These lemmas
    keep denotation proofs from unfolding the atom encodings when they only
    need the generic Logic-layer joinability principles. *)

From ContextBasicDenotation Require Import
  Notation StoreTyping TermEval TermOpen BasicTypingFormula.
From ContextLogic Require Import FormulaFiberwise.

Section BasicFormulaFiberwise.

Lemma fiberwise_joinable_on_qualifier_atom X (q : qualifier (V := value)) :
  fiberwise_joinable_on X (FAtom q).
Proof. apply fiberwise_joinable_on_atom. Qed.

Lemma fiberwise_joinable_on_basic_world_formula X Σ :
  fiberwise_joinable_on X (basic_world_formula Σ).
Proof.
  unfold basic_world_formula.
  apply fiberwise_joinable_on_fiber_atom.
Qed.

Lemma fiberwise_joinable_on_context_ty_wf_formula X Σ τ :
  fiberwise_joinable_on X (context_ty_wf_formula Σ τ).
Proof.
  unfold context_ty_wf_formula.
  apply fiberwise_joinable_on_fiber_atom.
Qed.

Lemma fiberwise_joinable_on_expr_basic_typing_formula X Σ e T :
  fiberwise_joinable_on X (expr_basic_typing_formula Σ e T).
Proof.
  unfold expr_basic_typing_formula.
  apply fiberwise_joinable_on_fiber_atom.
Qed.

Lemma fiberwise_joinable_on_expr_total_formula X e :
  fiberwise_joinable_on X (expr_total_formula e).
Proof.
  unfold expr_total_formula.
  apply fiberwise_joinable_on_fiber_atom.
Qed.

Lemma fiberwise_joinable_on_expr_result_atom_formula X e x :
  fiberwise_joinable_on X (expr_result_atom_formula e x).
Proof.
  unfold expr_result_atom_formula.
  apply fiberwise_joinable_on_atom.
Qed.

Lemma fiberwise_joinable_on_expr_result_formula_at X D e x :
  X ∩ lvars_fv (tm_lvars e ∪ {[x]}) ⊆ lvars_fv D ->
  fiberwise_joinable_on X (expr_result_formula_at D e x).
Proof.
  intros HXD.
  unfold expr_result_formula_at.
  eapply fiberwise_joinable_on_fibvars.
  - rewrite formula_fv_atom.
    unfold expr_result_qual, qual_vars.
    exact HXD.
  - intros σ.
    change (fiberwise_joinable_on X
      (FAtom (qual_msubst_store σ (expr_result_qual e x)))).
    apply fiberwise_joinable_on_atom.
Qed.

Lemma fiberwise_joinable_on_expr_result_formula X e x :
  X ∩ lvars_fv (tm_lvars e ∪ {[x]}) ⊆ lvars_fv (tm_lvars e) ->
  fiberwise_joinable_on X (expr_result_formula e x).
Proof.
  intros HXD.
  unfold expr_result_formula.
  eapply fiberwise_joinable_on_expr_result_formula_at.
  exact HXD.
Qed.

Lemma fiberwise_joinable_basic_world_formula Σ :
  fiberwise_joinable (basic_world_formula Σ).
Proof. intros X. apply fiberwise_joinable_on_basic_world_formula. Qed.

Lemma fiberwise_joinable_context_ty_wf_formula Σ τ :
  fiberwise_joinable (context_ty_wf_formula Σ τ).
Proof. intros X. apply fiberwise_joinable_on_context_ty_wf_formula. Qed.

Lemma fiberwise_joinable_expr_basic_typing_formula Σ e T :
  fiberwise_joinable (expr_basic_typing_formula Σ e T).
Proof. intros X. apply fiberwise_joinable_on_expr_basic_typing_formula. Qed.

Lemma fiberwise_joinable_expr_total_formula e :
  fiberwise_joinable (expr_total_formula e).
Proof. intros X. apply fiberwise_joinable_on_expr_total_formula. Qed.

Lemma fiberwise_joinable_expr_result_atom_formula e x :
  fiberwise_joinable (expr_result_atom_formula e x).
Proof. intros X. apply fiberwise_joinable_on_expr_result_atom_formula. Qed.

End BasicFormulaFiberwise.
