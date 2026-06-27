(** * Small program witnesses for Section 3 (logic and denotation) *)

From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section Section3LogicExamples.

Definition x : atom := 301%positive.
Definition y : atom := 302%positive.
Definition p : atom := 303%positive.
Definition q : atom := 304%positive.
Definition c : atom := 305%positive.

Definition logic_project_x : tm :=
  ret x.

Definition logic_correlated_xy : tm :=
  let y := x ⟨ + ⟩ vnat 1 in
  x ⟨ + ⟩ y.

Definition logic_branch_atom_example : tm :=
  let c := x ⟨ ≤ ⟩ vnat 2 in
  if c then
    ret x
  else
    y ⟨ + ⟩ vnat 1.

Definition logic_product_style_example : tm :=
  x ⟨ + ⟩ y.

Definition logic_implication_witness : tm :=
  ret (ƛ x : ℕ => x ⟨ + ⟩ vnat 1).

Definition nat_increment_ty : ty := (ℕ : ty) →ᵦ ℕ.

Lemma logic_project_x_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ logic_project_x ⋮ ℕ.
Proof. unfold logic_project_x. basic_check. Qed.

Lemma logic_project_x_extended_type :
  ∅; x ∷ ONat ⊢ₓ logic_project_x ⋮ ONat.
Proof.
  unfold logic_project_x.
  eapply EXT_Var.
  extended_wf.
Qed.

Lemma logic_correlated_xy_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ logic_correlated_xy ⋮ ℕ.
Proof. unfold logic_correlated_xy. basic_check. Qed.

Lemma logic_branch_atom_example_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ logic_branch_atom_example ⋮ ℕ.
Proof. unfold logic_branch_atom_example. basic_check. Qed.

Lemma logic_product_style_example_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ logic_product_style_example ⋮ ℕ.
Proof. unfold logic_product_style_example. basic_check. Qed.

Lemma logic_product_style_example_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    logic_product_style_example ⋮ binop_precise_ty bop_plus (avar x) (avar y).
Proof.
  unfold logic_product_style_example.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma logic_implication_witness_basic_type :
  ∅ ⊢ₑ logic_implication_witness ⋮ nat_increment_ty.
Proof. unfold logic_implication_witness, nat_increment_ty. basic_check. Qed.

End Section3LogicExamples.
