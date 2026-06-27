(** * Small programs from Section 1 (Introduction) *)

From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section Section1IntroExamples.

Definition x : atom := 101%positive.
Definition y : atom := 102%positive.
Definition f : atom := 103%positive.
Definition c : atom := 104%positive.
Definition c1 : atom := 105%positive.
Definition c2 : atom := 106%positive.
Definition f1 : atom := 107%positive.
Definition f2 : atom := 108%positive.
Definition inner : atom := 109%positive.

Definition nat_minus_program : tm :=
  ret (ƛ x : ℕ =>
    ret (ƛ y : ℕ =>
      let c := x ⟨ ≤ ⟩ y in
      if c then
        ret (vnat 0)
      else
        x ⟨ - ⟩ y)).

Definition captured_minus_fun : tm :=
  ret (ƛ y : ℕ => x ⟨ - ⟩ y).

Definition higher_order_apply_x : tm :=
  ret (ƛ f : ℕ →ᵦ ℕ => f @ x).

Definition static_alias_counterexample : tm :=
  let x := op_natGen ·₁ vnat 0 in
  (ƛ f : ℕ →ᵦ ℕ => f @ x) @ (ƛ y : ℕ => x ⟨ - ⟩ y).

Definition f2_value : value :=
  ƛ y : ℕ =>
    let c1 := y ⟨ ≤ ⟩ vnat 1 in
    let c2 := vnat 1 ⟨ ≤ ⟩ y in
    let c := c1 ⟨ && ⟩ c2 in
    if c then
      ret x
    else
      ret (vnat 2).

Definition dynamic_dependency_counterexample : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := op_natGen ·₁ vnat 0 in
  (ƛ f : ℕ →ᵦ ℕ =>
    let inner := f @ y in
    f @ inner) @ f2_value.

Definition nat_minus_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ ℕ.

Definition unary_nat_fun_ty : ty :=
  ℕ →ᵦ ℕ.

Definition higher_order_apply_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ.

Lemma f2_value_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ᵥ f2_value ⋮ unary_nat_fun_ty.
Proof.
  unfold f2_value, unary_nat_fun_ty.
  eapply basic_typing_lam_named.
  - basic_type_fresh.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply basic_typing_let_named.
      * basic_type_fresh.
      * basic_check.
      * eapply basic_typing_let_named.
        -- basic_type_fresh.
        -- basic_check.
        -- basic_check.
Qed.

Lemma nat_minus_program_basic_type :
  ∅ ⊢ₑ nat_minus_program ⋮ nat_minus_basic_ty.
Proof.
  unfold nat_minus_program, nat_minus_basic_ty.
  basic_check.
Qed.

Lemma captured_minus_fun_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ captured_minus_fun ⋮ unary_nat_fun_ty.
Proof.
  unfold captured_minus_fun, unary_nat_fun_ty.
  basic_check.
Qed.

Lemma intro_minus_body_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    x ⟨ - ⟩ y ⋮ binop_precise_ty bop_minus (avar x) (avar y).
Proof.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma intro_le_guard_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    x ⟨ ≤ ⟩ y ⋮ binop_precise_ty bop_le (avar x) (avar y).
Proof.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma higher_order_apply_x_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ higher_order_apply_x ⋮ higher_order_apply_basic_ty.
Proof.
  unfold higher_order_apply_x, higher_order_apply_basic_ty.
  basic_check.
Qed.

Lemma static_alias_counterexample_basic_type :
  ∅ ⊢ₑ static_alias_counterexample ⋮ ℕ.
Proof.
  unfold static_alias_counterexample, f2_value.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - basic_check.
  - eapply TT_App.
    + eapply basic_typing_lam_named; [basic_type_fresh|basic_check].
    + eapply basic_typing_lam_named; [basic_type_fresh|basic_check].
Qed.

Lemma dynamic_dependency_counterexample_basic_type :
  ∅ ⊢ₑ dynamic_dependency_counterexample ⋮ ℕ.
Proof.
  unfold dynamic_dependency_counterexample, f2_value.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - basic_check.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply TT_App.
      * eapply basic_typing_lam_named; [basic_type_fresh|basic_check].
      * eapply weakening_value.
        -- apply f2_value_basic_type.
        -- apply insert_subseteq.
           apply not_elem_of_dom. basic_type_fresh.
Qed.

End Section1IntroExamples.
