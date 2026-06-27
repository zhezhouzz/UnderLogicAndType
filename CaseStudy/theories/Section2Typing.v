(** * Small programs from Section 2 (typing overview) *)

From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section Section2TypingExamples.

Definition x : atom := 201%positive.
Definition y : atom := 202%positive.
Definition z : atom := 203%positive.
Definition g : atom := 204%positive.
Definition gx : atom := 205%positive.
Definition cmp : atom := 206%positive.
Definition ylet : atom := 207%positive.
Definition cond : atom := 208%positive.
Definition c1 : atom := 209%positive.
Definition c2 : atom := 210%positive.
Definition f : atom := 211%positive.
Definition a : atom := 212%positive.
Definition r1 : atom := 213%positive.
Definition r2 : atom := 214%positive.

Definition one_program : tm :=
  ret (vnat 1).

Definition minus_three_program : tm :=
  ret (ƛ x : ℕ => x ⟨ - ⟩ vnat 3).

Definition x_minus_three : tm :=
  x ⟨ - ⟩ vnat 3.

Definition may_must_intro_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let cond := y ⟨ > ⟩ vnat 10 in
        if cond then
          let gx := g @ x in
          gx ⟨ + ⟩ vnat 1
        else
          x ⟨ + ⟩ vnat 1))).

Definition dependent_context_program : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := x ⟨ + ⟩ vnat 1 in
  x ⟨ - ⟩ y.

Definition independent_context_program : tm :=
  let x := op_natGen ·₁ vnat 0 in
  let y := op_natGen ·₁ vnat 0 in
  x ⟨ - ⟩ y.

Definition x_minus_y : tm :=
  x ⟨ - ⟩ y.

Definition x_minus_z_plus_y : tm :=
  let a := z ⟨ + ⟩ y in
  x ⟨ - ⟩ a.

Definition y_minus_z : tm :=
  y ⟨ - ⟩ z.

Definition branch_three_five : tm :=
  let cond := op_eq0 ·₁ x in
  if cond then ret (vnat 3) else ret (vnat 5).

Definition branch_five_three : tm :=
  let cond := x ⟨ > ⟩ vnat 0 in
  if cond then ret (vnat 5) else ret (vnat 3).

Definition let_duplication_program : tm :=
  let ylet := x ⟨ - ⟩ vnat 3 in
  x ⟨ - ⟩ ylet.

Definition minus_curried_program : tm :=
  ret (ƛ x : ℕ =>
    ret (ƛ y : ℕ => x ⟨ - ⟩ y)).

Definition nested_apply_program : tm :=
  ret (ƛ f : ℕ →ᵦ ℕ =>
    let r1 := f @ y in
    let r2 := f @ r1 in
    x ⟨ - ⟩ r2).

Definition ack_like_program : tm :=
  ret (μ f, x : ℕ ~> ℕ →ᵦ ℕ =>
    ret (ƛ y : ℕ =>
      let c1 := op_eq0 ·₁ x in
      if c1 then
        ret (vnat 0)
      else
        let c2 := op_eq0 ·₁ y in
        if c2 then
          ret x
        else
          let r1 := x ⟨ - ⟩ vnat 1 in
          let r2 := y ⟨ - ⟩ vnat 1 in
          f @@ (r1, r2))).

Definition nat_match_like_program : tm :=
  let cond := op_eq0 ·₁ x in
  if cond then ret (vnat 3) else ret (vnat 5).

Definition nat_to_nat_ty : ty := (ℕ : ty) →ᵦ ℕ.
Definition nat_to_nat_to_nat_ty : ty := (ℕ : ty) →ᵦ ℕ →ᵦ ℕ.
Definition may_must_intro_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ ℕ.

Lemma one_program_basic_type :
  ∅ ⊢ₑ one_program ⋮ ℕ.
Proof. unfold one_program. basic_check. Qed.

Lemma one_program_extended_type :
  ∅; Emp ⊢ₓ one_program ⋮ const_precise_ty (cnat 1).
Proof.
  unfold one_program.
  eapply EXT_Const.
  extended_wf.
Qed.

Lemma minus_three_program_basic_type :
  ∅ ⊢ₑ minus_three_program ⋮ nat_to_nat_ty.
Proof. unfold minus_three_program, nat_to_nat_ty. basic_check. Qed.

Lemma x_minus_three_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ x_minus_three ⋮ ℕ.
Proof. unfold x_minus_three. basic_check. Qed.

Lemma x_minus_three_extended_type :
  ∅; x ∷ ONat ⊢ₓ
    x_minus_three ⋮ binop_precise_ty bop_minus (avar x) (vnat 3).
Proof.
  unfold x_minus_three.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma may_must_intro_program_basic_type :
  ∅ ⊢ₑ may_must_intro_program ⋮ may_must_intro_basic_ty.
Proof. unfold may_must_intro_program, may_must_intro_basic_ty. basic_check. Qed.

Lemma dependent_context_program_basic_type :
  ∅ ⊢ₑ dependent_context_program ⋮ ℕ.
Proof. unfold dependent_context_program. basic_check. Qed.

Lemma independent_context_program_basic_type :
  ∅ ⊢ₑ independent_context_program ⋮ ℕ.
Proof. unfold independent_context_program. basic_check. Qed.

Lemma x_minus_y_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ x_minus_y ⋮ ℕ.
Proof. unfold x_minus_y. basic_check. Qed.

Lemma x_minus_y_extended_type :
  ∅; (x ∷ ONat) ,, (y ∷ ONat) ⊢ₓ
    x_minus_y ⋮ binop_precise_ty bop_minus (avar x) (avar y).
Proof.
  unfold x_minus_y.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma x_minus_z_plus_y_basic_type :
  <[z := (ℕ : ty)]> (<[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅)) ⊢ₑ x_minus_z_plus_y ⋮ ℕ.
Proof. unfold x_minus_z_plus_y. basic_check. Qed.

Lemma y_minus_z_basic_type :
  <[z := (ℕ : ty)]> (<[y := (ℕ : ty)]> ∅) ⊢ₑ y_minus_z ⋮ ℕ.
Proof. unfold y_minus_z. basic_check. Qed.

Lemma y_minus_z_extended_type :
  ∅; (y ∷ ONat) ,, (z ∷ ONat) ⊢ₓ
    y_minus_z ⋮ binop_precise_ty bop_minus (avar y) (avar z).
Proof.
  unfold y_minus_z.
  eapply EXT_BinOp.
  extended_wf.
Qed.

Lemma branch_three_five_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ branch_three_five ⋮ ℕ.
Proof. unfold branch_three_five. basic_check. Qed.

Lemma branch_five_three_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ branch_five_three ⋮ ℕ.
Proof. unfold branch_five_three. basic_check. Qed.

Lemma let_duplication_program_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ let_duplication_program ⋮ ℕ.
Proof. unfold let_duplication_program. basic_check. Qed.

Lemma minus_curried_program_basic_type :
  ∅ ⊢ₑ minus_curried_program ⋮ nat_to_nat_to_nat_ty.
Proof. unfold minus_curried_program, nat_to_nat_to_nat_ty. basic_check. Qed.

Lemma nested_apply_program_basic_type :
  <[y := (ℕ : ty)]> (<[x := (ℕ : ty)]> ∅) ⊢ₑ
    nested_apply_program ⋮ ((ℕ →ᵦ ℕ) →ᵦ ℕ).
Proof.
  unfold nested_apply_program, nat_to_nat_ty.
  basic_check.
Qed.

Lemma ack_like_program_basic_type :
  ∅ ⊢ₑ ack_like_program ⋮ nat_to_nat_to_nat_ty.
Proof.
  unfold ack_like_program, nat_to_nat_to_nat_ty.
  basic_check.
Qed.

Lemma nat_match_like_program_basic_type :
  <[x := (ℕ : ty)]> ∅ ⊢ₑ nat_match_like_program ⋮ ℕ.
Proof. unfold nat_match_like_program. basic_check. Qed.

End Section2TypingExamples.
