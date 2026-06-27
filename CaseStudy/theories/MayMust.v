(** * Figure 5.1-style may/must programs *)

From ProofAutomation Require Import BasicTypeInfer ExtendedSubsumption ExtendedTypeInfer.
From ContextTyping Require Import Typing.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section MayMustExamples.

Definition g : atom := 1%positive.
Definition x : atom := 2%positive.
Definition y : atom := 3%positive.
Definition gx : atom := 4%positive.
Definition gy : atom := 5%positive.
Definition px : atom := 6%positive.
Definition py : atom := 7%positive.
Definition cond : atom := 8%positive.
Definition a : atom := 9%positive.

(** The paper examples use arithmetic and boolean binary operators.  These are
    core binary-operation terms in the case-study syntax layer. *)

Definition may_may_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let gx := g @ x in
        let gy := g @ y in
        let px := gx ⟨ < ⟩ vnat 0 in
        let py := gy ⟨ < ⟩ vnat 0 in
        px ⟨ || ⟩ py))).

Definition must_may_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let gx := g @ x in
        let gy := g @ y in
        let px := vnat 0 ⟨ ≤ ⟩ gx in
        let py := vnat 0 ⟨ ≤ ⟩ gy in
        px ⟨ && ⟩ py))).

Definition may_reach_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let cond := y ⟨ > ⟩ vnat 10 in
        if cond then
          let gx := g @ x in
          gx ⟨ + ⟩ vnat 1
        else
          x ⟨ + ⟩ vnat 1))).

Definition must_inter_program : tm :=
  ret (ƛ g : ℕ →ᵦ ℕ =>
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let a := g @ x in
        let cond := a ⟨ > ⟩ vnat 10 in
        if cond then
          ret vnat 3
        else
          ret a))).

Definition may_must_guard_program := may_may_program.

Definition may_may_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition may_reach_basic_ty : ty :=
  (ℕ →ᵦ ℕ) →ᵦ ℕ →ᵦ ℕ →ᵦ ℕ.

Lemma may_may_program_basic_type :
  ∅ ⊢ₑ may_may_program ⋮ may_may_basic_ty.
Proof.
  unfold may_may_program, may_may_basic_ty.
  basic_check.
Qed.

Lemma may_may_after_g_basic_type :
  <[g := nat_unary_fun_ty]> ∅ ⊢ₑ
    ret (ƛ x : ℕ =>
      ret (ƛ y : ℕ =>
        let gx := g @ x in
        let gy := g @ y in
        let px := gx ⟨ < ⟩ vnat 0 in
        let py := gy ⟨ < ⟩ vnat 0 in
        px ⟨ || ⟩ py)) ⋮ (ℕ →ᵦ ℕ →ᵦ 𝔹).
Proof. basic_check. Qed.

Lemma must_may_program_basic_type :
  ∅ ⊢ₑ must_may_program ⋮ may_may_basic_ty.
Proof.
  unfold must_may_program, may_may_basic_ty.
  basic_check.
Qed.

Lemma may_reach_program_basic_type :
  ∅ ⊢ₑ may_reach_program ⋮ may_reach_basic_ty.
Proof.
  unfold may_reach_program, may_reach_basic_ty.
  basic_check.
Qed.

Lemma must_inter_program_basic_type :
  ∅ ⊢ₑ must_inter_program ⋮ may_reach_basic_ty.
Proof.
  unfold must_inter_program, may_reach_basic_ty.
  basic_check.
Qed.

(** Figure 5.1 context types, translated literally.  The programs above are
    closed functions taking [g] as their first argument, so each full program
    type is [g_summary -> f_summary]. *)

Definition q_nat_ge0 : type_qualifier :=
  q_nat_pred ν (fun n => 0%nat <= n).

Definition q_nat_gt0 : type_qualifier :=
  q_nat_pred ν (fun n => 0%nat < n).

Definition q_nat_ne0 : type_qualifier :=
  q_nat_pred ν (fun n => n <> 0%nat).

Definition q_nat_eq1 : type_qualifier :=
  q_nat_pred ν (fun n => n = 1%nat).

Definition q_bin_lt_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_lt v1 v2.

Definition q_bin_le_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_le v1 v2.

Definition q_bin_or_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_or v1 v2.

Definition q_bin_and_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_and v1 v2.

Definition q_bin_plus_result (v1 v2 : value) : type_qualifier :=
  binop_result_qual bop_plus v1 v2.

Definition may_may_g_ty : context_ty :=
  O[ ℕ ] → {: ℕ | q_nat_ge0 }.

Definition may_may_f_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → {: 𝔹 | q_false }.

Definition may_may_ref_ty : context_ty :=
  may_may_g_ty → may_may_f_ty.

Definition must_may_g_ty : context_ty :=
  U[ ℕ ] → [: ℕ | q_nat_ge0 ].

Definition must_may_f_ty : context_ty :=
  U[ ℕ ] → U[ ℕ ] → [: 𝔹 | q_true ].

Definition must_may_ref_ty : context_ty :=
  must_may_g_ty → must_may_f_ty.

Definition may_reach_g_ty : context_ty :=
  O[ ℕ ] → {: ℕ | q_nat_ne0 }.

Definition may_reach_f_ty : context_ty :=
  U[ ℕ ] → U[ ℕ ] → [: ℕ | q_nat_eq1 ].

Definition may_reach_ref_ty : context_ty :=
  may_reach_g_ty → may_reach_f_ty.

Definition must_inter_g_ty : context_ty :=
  (O[ ℕ ] → {: ℕ | q_nat_gt0 }) ⊓
  (U[ ℕ ] → [: ℕ | q_nat_gt0 ]).

Definition must_inter_f_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → {: ℕ | q_nat_ge0 }.

Definition must_inter_ref_ty : context_ty :=
  must_inter_g_ty → must_inter_f_ty.

Definition comprehensive_inter_f_ty : context_ty :=
  (O[ ℕ ] ⊓ U[ ℕ ]) →
  (O[ ℕ ] ⊓ U[ ℕ ]) →
  (O[ ℕ ] ⊓ [: ℕ | q_nat_eq1 ]).

Lemma may_may_g_ty_wf :
  basic_context_ty ∅ may_may_g_ty.
Proof.
  unfold may_may_g_ty, q_nat_ge0.
  case_type_wf_syntax.
Qed.

Lemma may_may_ref_ty_wf :
  basic_context_ty ∅ may_may_ref_ty.
Proof.
  unfold may_may_ref_ty, may_may_g_ty, may_may_f_ty,
    q_nat_ge0, q_false.
  case_type_wf_syntax.
Qed.

Lemma must_may_ref_ty_wf :
  basic_context_ty ∅ must_may_ref_ty.
Proof.
  unfold must_may_ref_ty, must_may_g_ty, must_may_f_ty,
    q_nat_ge0, q_true.
  case_type_wf_syntax.
Qed.

Lemma may_reach_ref_ty_wf :
  basic_context_ty ∅ may_reach_ref_ty.
Proof.
  unfold may_reach_ref_ty, may_reach_g_ty, may_reach_f_ty,
    q_nat_ne0, q_nat_eq1.
  case_type_wf_syntax.
Qed.

Lemma must_inter_ref_ty_wf :
  basic_context_ty ∅ must_inter_ref_ty.
Proof.
  unfold must_inter_ref_ty, must_inter_g_ty, must_inter_f_ty,
    q_nat_gt0, q_nat_ge0.
  case_type_wf_syntax.
Qed.

Lemma comprehensive_inter_f_ty_wf :
  basic_context_ty ∅ comprehensive_inter_f_ty.
Proof.
  unfold comprehensive_inter_f_ty, q_nat_eq1.
  case_type_wf_syntax.
Qed.

(** ** Figure 5.1 semantic subtyping checkpoints

    These are local [Γ |- τ1 <: τ2] obligations.  The tempting whole-program
    shortcuts are false: [O[Bool] <: {: Bool | false}] is refuted by [true],
    and [O[Nat] <: {: Nat | 0 <= ν}] would only be trivial because this case
    study currently uses [Nat] rather than the paper's [Int]. *)

Lemma may_may_lt_false_subtype z :
  extended_semantic_subtype ∅ (z ∷ {: ℕ | q_nat_ge0 })
    (({: 𝔹 | q_bin_lt_result (avar z) (vnat 0) }) ⊓
     ([: 𝔹 | q_bin_lt_result (avar z) (vnat 0) ]))
    ({: 𝔹 | q_false }).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ({: 𝔹 | q_bin_lt_result (avar z) (vnat 0) })).
  - apply subtype_inter_over_under_to_over_part.
Admitted.

Lemma may_may_or_false_false_subtype p q :
  extended_semantic_subtype ∅
    ((p ∷ {: 𝔹 | q_false }) ,, (q ∷ {: 𝔹 | q_false }))
    (({: 𝔹 | q_bin_or_result (avar p) (avar q) }) ⊓
     ([: 𝔹 | q_bin_or_result (avar p) (avar q) ]))
    ({: 𝔹 | q_false }).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ({: 𝔹 | q_bin_or_result (avar p) (avar q) })).
  - apply subtype_inter_over_under_to_over_part.
Admitted.

Lemma must_may_le_true_subtype z :
  extended_semantic_subtype ∅ (z ∷ [: ℕ | q_nat_ge0 ])
    (({: 𝔹 | q_bin_le_result (vnat 0) (avar z) }) ⊓
     ([: 𝔹 | q_bin_le_result (vnat 0) (avar z) ]))
    ([: 𝔹 | q_true ]).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ([: 𝔹 | qual_and
        (q_bin_le_result (vnat 0) (avar z))
        (q_bin_le_result (vnat 0) (avar z)) ])).
  - apply subtype_inter_over_under_to_under_and.
  - rewrite qual_and_idempotent.
Admitted.

Lemma must_may_and_true_true_subtype p q :
  extended_semantic_subtype ∅
    ((p ∷ [: 𝔹 | q_true ]) ,, (q ∷ [: 𝔹 | q_true ]))
    (({: 𝔹 | q_bin_and_result (avar p) (avar q) }) ⊓
     ([: 𝔹 | q_bin_and_result (avar p) (avar q) ]))
    ([: 𝔹 | q_true ]).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ([: 𝔹 | qual_and
        (q_bin_and_result (avar p) (avar q))
        (q_bin_and_result (avar p) (avar q)) ])).
  - apply subtype_inter_over_under_to_under_and.
  - rewrite qual_and_idempotent.
Admitted.

(** The then-branch of Figure 5.1(c) is intentionally not given a subtype to
    [[: Nat | ν = 1]]: with [g x : {Nat | ν <> 0}], [g x + 1] cannot produce
    [1].  The reachable branch is the else branch, where an under-top input can
    cover [0] and therefore [x + 1] can cover [1]. *)
Lemma may_reach_else_plus_one_eq1_subtype z :
  extended_semantic_subtype ∅ (z ∷ U[ ℕ ])
    (({: ℕ | q_bin_plus_result (avar z) (vnat 1) }) ⊓
     ([: ℕ | q_bin_plus_result (avar z) (vnat 1) ]))
    ([: ℕ | q_nat_eq1 ]).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ([: ℕ | qual_and
        (q_bin_plus_result (avar z) (vnat 1))
        (q_bin_plus_result (avar z) (vnat 1)) ])).
  - apply subtype_inter_over_under_to_under_and.
  - rewrite qual_and_idempotent.
Admitted.

Lemma must_inter_g_over_projection_subtype :
  extended_semantic_subtype ∅ Emp
    ((O[ ℕ ] → {: ℕ | q_nat_gt0 }) ⊓
     (U[ ℕ ] → [: ℕ | q_nat_gt0 ]))
    (O[ ℕ ] → {: ℕ | q_nat_gt0 }).
Proof.
  apply extended_semantic_subtype_inter_left.
Qed.

Lemma must_inter_then_three_ge0_subtype :
  extended_semantic_subtype ∅ Emp
    (({: ℕ | mk_q_eq ν (vnat 3) }) ⊓
     ([: ℕ | mk_q_eq ν (vnat 3) ]))
    ({: ℕ | q_nat_ge0 }).
Proof.
  eapply (extended_semantic_subtype_trans _ _ _
    ({: ℕ | mk_q_eq ν (vnat 3) })).
  - apply subtype_inter_over_under_to_over_part.
  - apply subtype_over_closed_by_qualifier.
    + unfold qual_dom, mk_q_eq, vnu, lvar_value_keys; cbn.
      set_solver.
    + unfold qual_dom, q_nat_ge0, q_nat_pred, q_const_pred,
        vnu, lvar_value_keys; cbn.
      set_solver.
Admitted.

Lemma must_inter_else_gt0_ge0_subtype z :
  extended_semantic_subtype ∅ (z ∷ {: ℕ | q_nat_gt0 })
    ({: ℕ | q_nat_gt0 })
    ({: ℕ | q_nat_ge0 }).
Proof.
  apply subtype_over_closed_by_qualifier.
Admitted.

Lemma basic_type_unary_nat_call Γ (f x : atom) :
  Γ !! f = Some nat_unary_fun_ty ->
  Γ !! x = Some (ℕ : ty) ->
  Γ ⊢ₑ tapp f x ⋮ ℕ.
Proof.
  intros Hf Hx.
  econstructor.
  - constructor. exact Hf.
  - constructor. exact Hx.
Qed.

Lemma basic_type_nat_cmp_first_call Γ (cmp x : atom) :
  Γ !! cmp = Some nat_cmp_ty ->
  Γ !! x = Some (ℕ : ty) ->
  Γ ⊢ₑ tapp cmp x ⋮ (ℕ →ᵦ 𝔹).
Proof.
  intros Hcmp Hx.
  econstructor.
  - constructor. exact Hcmp.
  - constructor. exact Hx.
Qed.

End MayMustExamples.
