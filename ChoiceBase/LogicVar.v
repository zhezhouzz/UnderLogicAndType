(** * ChoiceBase.LogicVar

    Locally-nameless logic-variable keys and finite-set support. *)

From ChoiceBase Require Export Prelude.

Inductive logic_var : Type :=
  | LVBound (k : nat)
  | LVFree  (x : atom).

#[global] Instance logic_var_eqdec : EqDecision logic_var.
Proof. solve_decision. Qed.
#[global] Instance logic_var_countable : Countable logic_var.
Proof.
  refine (inj_countable'
    (λ v, match v with LVBound k => inl k | LVFree x => inr x end)
    (λ s, match s with inl k => LVBound k | inr x => LVFree x end) _).
  intros []; reflexivity.
Qed.

Notation lvset := (gset logic_var).

Definition logic_var_fv (v : logic_var) : aset :=
  match v with
  | LVBound _ => ∅
  | LVFree x => {[x]}
  end.

Definition logic_var_bv (v : logic_var) : gset nat :=
  match v with
  | LVBound k => {[k]}
  | LVFree _ => ∅
  end.

Definition logic_var_support (v : logic_var) : lvset := {[v]}.

Definition lvars_fv (D : lvset) : aset :=
  set_fold (λ v acc, logic_var_fv v ∪ acc) ∅ D.

Definition lvars_bv (D : lvset) : gset nat :=

  set_fold (λ v acc, logic_var_bv v ∪ acc) ∅ D.

Lemma lvars_fv_elem D x :
  x ∈ lvars_fv D ↔ LVFree x ∈ D.
Proof.
  unfold lvars_fv.
  refine (set_fold_ind_L
    (fun acc D => ∀ x, x ∈ acc ↔ LVFree x ∈ D)
    (λ v acc, logic_var_fv v ∪ acc) ∅ _ _ D x).
  - intros y. set_solver.
  - intros v D' acc Hfresh IH z.
    destruct v as [k|a]; cbn [logic_var_fv];
      pose proof (IH z); set_solver.
Qed.

Lemma lvars_bv_elem D k :
  k ∈ lvars_bv D ↔ LVBound k ∈ D.
Proof.
  unfold lvars_bv.
  refine (set_fold_ind_L
    (fun acc D => ∀ k, k ∈ acc ↔ LVBound k ∈ D)
    (λ v acc, logic_var_bv v ∪ acc) ∅ _ _ D k).
  - intros j. set_solver.
  - intros v D' acc Hfresh IH j.
    destruct v as [i|y]; cbn [logic_var_bv];
      pose proof (IH j); set_solver.
Qed.
