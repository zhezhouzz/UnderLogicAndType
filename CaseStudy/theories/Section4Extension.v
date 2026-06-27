(** * Small programs from Section 4 (nondeterminism and persistence) *)

From ProofAutomation Require Import BasicTypeInfer ExtendedTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section Section4ExtensionExamples.

Definition z : atom := 401%positive.
Definition x : atom := 402%positive.
Definition y : atom := 403%positive.
Definition f : atom := 404%positive.
Definition y1 : atom := 405%positive.
Definition y2 : atom := 406%positive.
Definition r : atom := 407%positive.
Definition c : atom := 408%positive.
Definition c1 : atom := 409%positive.
Definition c2 : atom := 410%positive.

Definition bool_gen_program : tm :=
  op_boolGen ·₁ vbool false.

Definition nat_gen_program : tm :=
  op_natGen ·₁ vnat 0.

Definition nondet_choice_program : tm :=
  ret (vnat 0) ⊕ₙ ret (vnat 1).

Definition envir_x_program : tm :=
  let x := nat_gen_program in
  x ⟨ + ⟩ vnat 1.

Definition captured_z_fun : tm :=
  ret (ƛ x : 𝔹 => ret z).

Definition double_call_captured_z : tm :=
  let f := captured_z_fun in
  let y1 := f @ vbool true in
  let y2 := f @ vbool false in
  ret y2.

Definition nat_gen_fun : tm :=
  ret (ƛ x : 𝔹 => nat_gen_program).

Definition choice_fun : tm :=
  ret (ƛ x : 𝔹 => ret (vnat 0)) ⊕ₙ
  ret (ƛ x : 𝔹 => nat_gen_program).

Definition nonpersistent_choice_use : tm :=
  let f := choice_fun in
  let r := f @ vbool true in
  let c := op_eq0 ·₁ r in
  if c then
    f @ vbool false
  else
    ret (vnat 0).

Definition bool_equality_body : tm :=
  if y then
    if x then ret (vbool true) else ret (vbool false)
  else
    if x then ret (vbool false) else ret (vbool true).

Definition bool_gen_closure_program : tm :=
  let x := bool_gen_program in
  ret (ƛ y : 𝔹 => bool_equality_body).

Definition bool_gen_sum_program : tm :=
  bool_gen_program.

Definition bool_to_nat_ty : ty := (𝔹 : ty) →ᵦ ℕ.
Definition bool_to_bool_ty : ty := (𝔹 : ty) →ᵦ 𝔹.

Lemma bool_gen_program_basic_type :
  ∅ ⊢ₑ bool_gen_program ⋮ 𝔹.
Proof. unfold bool_gen_program. basic_check. Qed.

Lemma bool_gen_program_extended_type :
  ∅; Emp ⊢ₓ bool_gen_program ⋮
    primop_precise_ty op_boolGen (vbool false).
Proof. unfold bool_gen_program. eapply EXT_AppOpValue. extended_wf. Qed.

Lemma nat_gen_program_basic_type :
  ∅ ⊢ₑ nat_gen_program ⋮ ℕ.
Proof. unfold nat_gen_program. basic_check. Qed.

Lemma nat_gen_program_extended_type :
  ∅; Emp ⊢ₓ nat_gen_program ⋮
    primop_precise_ty op_natGen (vnat 0).
Proof. unfold nat_gen_program. eapply EXT_AppOpValue. extended_wf. Qed.

Lemma nondet_choice_program_basic_type :
  ∅ ⊢ₑ nondet_choice_program ⋮ ℕ.
Proof. unfold nondet_choice_program. basic_check. Qed.

Lemma envir_x_program_basic_type :
  ∅ ⊢ₑ envir_x_program ⋮ ℕ.
Proof. unfold envir_x_program, nat_gen_program. basic_check. Qed.

Lemma captured_z_fun_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ captured_z_fun ⋮ bool_to_nat_ty.
Proof. unfold captured_z_fun, bool_to_nat_ty. basic_check. Qed.

Lemma double_call_captured_z_basic_type :
  <[z := (ℕ : ty)]> ∅ ⊢ₑ double_call_captured_z ⋮ ℕ.
Proof.
  unfold double_call_captured_z, bool_to_nat_ty.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply captured_z_fun_basic_type.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply basic_typing_let_named.
      * basic_type_fresh.
      * basic_check.
      * basic_check.
Qed.

Lemma nat_gen_fun_basic_type :
  ∅ ⊢ₑ nat_gen_fun ⋮ bool_to_nat_ty.
Proof. unfold nat_gen_fun, nat_gen_program, bool_to_nat_ty. basic_check. Qed.

Lemma choice_fun_basic_type :
  ∅ ⊢ₑ choice_fun ⋮ bool_to_nat_ty.
Proof. unfold choice_fun, nat_gen_program, bool_to_nat_ty. basic_check. Qed.

Lemma nonpersistent_choice_use_basic_type :
  ∅ ⊢ₑ nonpersistent_choice_use ⋮ ℕ.
Proof.
  unfold nonpersistent_choice_use.
  eapply basic_typing_let_named.
  - basic_type_fresh.
  - apply choice_fun_basic_type.
  - eapply basic_typing_let_named.
    + basic_type_fresh.
    + basic_check.
    + eapply basic_typing_let_named.
      * basic_type_fresh.
      * basic_check.
      * basic_check.
Qed.

Lemma bool_equality_body_basic_type :
  <[y := (𝔹 : ty)]> (<[x := (𝔹 : ty)]> ∅) ⊢ₑ bool_equality_body ⋮ 𝔹.
Proof. unfold bool_equality_body. basic_check. Qed.

Lemma bool_gen_closure_program_basic_type :
  ∅ ⊢ₑ bool_gen_closure_program ⋮ bool_to_bool_ty.
Proof.
  unfold bool_gen_closure_program, bool_gen_program, bool_equality_body,
    bool_to_bool_ty.
  basic_check.
Qed.

Lemma bool_gen_sum_program_basic_type :
  ∅ ⊢ₑ bool_gen_sum_program ⋮ 𝔹.
Proof. unfold bool_gen_sum_program, bool_gen_program. basic_check. Qed.

End Section4ExtensionExamples.
