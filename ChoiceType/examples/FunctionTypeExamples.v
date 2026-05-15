(** * Function-type examples

    Operational witnesses for the function-type readings discussed in the
    paper overview and in the "Simulate different reasoning styles" corollary.

    The core language is now deterministic: examples use constants, unary
    primitive operations, and ordinary boolean matching.  The file deliberately
    proves CoreLang reduction facts rather than full [has_choice_type]
    theorems; the typing/subtyping proof layer lives outside [ChoiceType]. *)

From CoreLang Require Import Sugar.

(** ** Core values used as functions *)

Definition nat_ty : ty := TBase TNat.
Definition bool_ty : ty := TBase TBool.

Definition zero : value := vnat 0.
Definition one : value := vnat 1.
Definition seven : value := vnat 7.

(** [λ x. x] *)
Definition fn_id : value :=
  vlam nat_ty (tret (vbvar 0)).

(** [λ x. 0] and [λ x. 1] *)
Definition fn_const0 : value :=
  vlam nat_ty (tret zero).

Definition fn_const1 : value :=
  vlam nat_ty (tret one).

(** [λ x. x + 1] *)
Definition fn_plus1 : value :=
  vlam nat_ty (tprim op_plus1 (vbvar 0)).

(** [λ x. if x == 0 then 0 else 1].

    This is the Nat/Bool-test analogue of the total dependency example in the
    overview.  It exposes that the result is determined by information about
    the argument. *)
Definition fn_iszero : value :=
  vlam nat_ty
    (tlete (tprim op_eq0 (vbvar 0))
       (tmatch (vbvar 0) (tret zero) (tret one))).

Definition app (f x : value) : tm := tapp f x.

Ltac solve_lc :=
  cbn; repeat (constructor || eassumption).

Lemma body_ret_bvar0 :
  body_tm (tret (vbvar 0)).
Proof.
  exists ∅. intros x _. solve_lc.
Qed.

Lemma body_ret_closed v :
  lc_value v →
  body_tm (tret v).
Proof.
  intros Hv. exists ∅. intros x _. cbn.
  change (lc_tm (tret (open_value 0 x v))).
  rewrite (open_rec_lc_value v Hv 0 x).
  constructor. exact Hv.
Qed.

Lemma body_tprim_plus1 :
  body_tm (tprim op_plus1 (vbvar 0)).
Proof.
  exists ∅. intros x _. solve_lc.
Qed.

Lemma body_match_zero_one :
  body_tm (tmatch (vbvar 0) (tret zero) (tret one)).
Proof.
  exists ∅. intros x _. unfold zero, one, vnat. solve_lc.
Qed.

Lemma body_fn_iszero :
  body_tm (tlete (tprim op_eq0 (vbvar 0))
    (tmatch (vbvar 0) (tret zero) (tret one))).
Proof.
  exists ∅. intros x _. cbn.
  eapply LC_lete with (L := ∅).
  - solve_lc.
  - intros y _. unfold zero, one, vnat. solve_lc.
Qed.

Lemma lc_fn_id : lc_value fn_id.
Proof. unfold fn_id. apply lc_lam_iff_body. apply body_ret_bvar0. Qed.

Lemma lc_fn_const0 : lc_value fn_const0.
Proof. unfold fn_const0. apply lc_lam_iff_body. apply body_ret_closed. unfold zero, vnat. solve_lc. Qed.

Lemma lc_fn_const1 : lc_value fn_const1.
Proof. unfold fn_const1. apply lc_lam_iff_body. apply body_ret_closed. unfold one, vnat. solve_lc. Qed.

Lemma lc_fn_plus1 : lc_value fn_plus1.
Proof. unfold fn_plus1. apply lc_lam_iff_body. apply body_tprim_plus1. Qed.

Lemma lc_fn_iszero : lc_value fn_iszero.
Proof.
  unfold fn_iszero. apply lc_lam_iff_body. apply body_fn_iszero.
Qed.

(** ** Basic function reduction facts *)

Lemma fn_id_reaches n :
  app fn_id (vnat n) →* tret (vnat n).
Proof.
  unfold app, fn_id, vnat.
  eapply reduction_beta_intro.
  - apply body_ret_bvar0.
  - solve_lc.
  - cbn. apply Steps_refl. solve_lc.
Qed.

Lemma fn_const0_reaches n :
  app fn_const0 (vnat n) →* tret zero.
Proof.
  unfold app, fn_const0, zero, vnat.
  eapply reduction_beta_intro.
  - apply body_ret_closed. solve_lc.
  - solve_lc.
  - cbn. apply Steps_refl. solve_lc.
Qed.

Lemma fn_const1_reaches n :
  app fn_const1 (vnat n) →* tret one.
Proof.
  unfold app, fn_const1, one, vnat.
  eapply reduction_beta_intro.
  - apply body_ret_closed. solve_lc.
  - solve_lc.
  - cbn. apply Steps_refl. solve_lc.
Qed.

Lemma op_plus1_result n :
  tprim op_plus1 (vnat n) →* tret (vnat (S n)).
Proof.
  unfold vnat.
  apply steps_R. apply Step_head. eapply HS_Op.
  - apply Prim_plus1.
  - solve_lc.
Qed.

Lemma fn_plus1_reaches n :
  app fn_plus1 (vnat n) →* tret (vnat (S n)).
Proof.
  unfold app, fn_plus1.
  eapply reduction_beta_intro.
  - apply body_tprim_plus1.
  - solve_lc.
  - cbn. apply op_plus1_result.
Qed.

Lemma op_eq0_zero_true :
  tprim op_eq0 zero →* tret vtrue.
Proof.
  unfold zero, vtrue, vnat.
  apply steps_R. apply Step_head. eapply HS_Op.
  - apply Prim_eq0.
  - solve_lc.
Qed.

Lemma op_eq0_one_false :
  tprim op_eq0 one →* tret vfalse.
Proof.
  unfold one, vfalse, vnat.
  apply steps_R. apply Step_head. eapply HS_Op.
  - apply Prim_eq0.
  - solve_lc.
Qed.

Lemma fn_iszero_zero_reaches_zero :
  app fn_iszero zero →* tret zero.
Proof.
  unfold app, fn_iszero.
  eapply reduction_beta_intro.
  - apply body_fn_iszero.
  - unfold zero, vnat. solve_lc.
  - cbn.
    eapply reduction_lete_intro.
    + apply body_match_zero_one.
    + apply op_eq0_zero_true.
    + cbn. eapply reduction_match_true_intro; solve_lc.
Qed.

Lemma fn_iszero_one_reaches_one :
  app fn_iszero one →* tret one.
Proof.
  unfold app, fn_iszero.
  eapply reduction_beta_intro.
  - apply body_fn_iszero.
  - unfold one, vnat. solve_lc.
  - cbn.
    eapply reduction_lete_intro.
    + apply body_match_zero_one.
    + apply op_eq0_one_false.
    + cbn. eapply reduction_match_false_intro; solve_lc.
Qed.

(** ** Corollary table witnesses and refutations *)

(** Over -> Over, ordinary refinement safety:
      [x:{Nat|⊤} -> {Nat|ν=0}]
    [fn_const0] is the positive example; [fn_const1] refutes it by returning
    [1] on every input. *)
Example over_over_good_const0 :
  app fn_const0 seven →* tret zero.
Proof. apply fn_const0_reaches. Qed.

Example over_over_bad_const1_counterexample :
  app fn_const1 seven →* tret one.
Proof. apply fn_const1_reaches. Qed.

(** Over -> Under, coverage on returns:
      [x:{Nat|⊤} -> [Nat|ν=x]]
    [fn_id] covers the requested result for each input; [fn_const0] fails for
    input [1] and requested result [1]. *)
Example over_under_good_id :
  app fn_id seven →* tret seven.
Proof. apply fn_id_reaches. Qed.

Example over_under_bad_const0_counterexample :
  app fn_const0 one →* tret zero.
Proof. apply fn_const0_reaches. Qed.

(** Under -> Under, incorrectness-style reading:
      [x:[Nat|⊤] -> [Nat|⊤]]
    In the deterministic core, [fn_id] witnesses any desired output by choosing
    that output as the input.  [fn_const0] cannot reach [1]. *)
Example under_under_good_id n :
  app fn_id (vnat n) →* tret (vnat n).
Proof. apply fn_id_reaches. Qed.

Example under_under_bad_const0_counterexample :
  app fn_const0 one →* tret zero.
Proof. apply fn_const0_reaches. Qed.

(** Under -> Over, existential witness:
      [x:[Nat|⊤] -> {Nat|ν=0}]
    [fn_iszero] has the witness input [0].  [fn_const1] has no operational
    witness for [ν=0], and its behavior below is the concrete obstruction. *)
Example under_over_good_iszero_witness :
  app fn_iszero zero →* tret zero.
Proof. apply fn_iszero_zero_reaches_zero. Qed.

Example under_over_bad_const1_counterexample :
  app fn_const1 zero →* tret one.
Proof. apply fn_const1_reaches. Qed.

(** Sufficient incorrectness:
      [x:{Nat|⊤} -> ({Nat|ν=0} ⊕ Nat)]
    [fn_const0] reaches [0] for every input.  [fn_iszero] is a useful contrast:
    it satisfies the existential style above but fails this stronger
    every-input style at input [1]. *)
Example sufficient_good_const0 n :
  app fn_const0 (vnat n) →* tret zero.
Proof. apply fn_const0_reaches. Qed.

Example sufficient_bad_iszero_counterexample :
  app fn_iszero one →* tret one.
Proof. apply fn_iszero_one_reaches_one. Qed.

(** Existential branch-local witness:
      [x:[Nat|⊤] -> ({Nat|ν=0} ⊕ Nat)]
    The same [fn_iszero] that failed sufficient incorrectness succeeds here by
    choosing input [0]. *)
Example existential_branch_good_iszero :
  app fn_iszero zero →* tret zero.
Proof. apply fn_iszero_zero_reaches_zero. Qed.

(** ** Overview insight examples *)

Example id_reaches_one :
  app fn_id one →* tret one.
Proof. apply fn_id_reaches. Qed.

Example id_reaches_seven :
  app fn_id seven →* tret seven.
Proof. apply fn_id_reaches. Qed.

Example plus1_dependency_zero :
  app fn_plus1 zero →* tret one.
Proof. apply fn_plus1_reaches. Qed.

Example iszero_dependency_zero :
  app fn_iszero zero →* tret zero.
Proof. apply fn_iszero_zero_reaches_zero. Qed.

Example iszero_dependency_one :
  app fn_iszero one →* tret one.
Proof. apply fn_iszero_one_reaches_one. Qed.

(** Higher-order branching location is now represented by ordinary boolean
    functions. *)

Definition unit_arg : value := vtrue.

Definition g_true : value :=
  vlam bool_ty (tret vtrue).

Definition g_false : value :=
  vlam bool_ty (tret vfalse).

Definition g2 : value :=
  vlam bool_ty (tmatch (vbvar 0) (tret vtrue) (tret vfalse)).

Lemma lc_g_true : lc_value g_true.
Proof.
  unfold g_true. apply lc_lam_iff_body. apply body_ret_closed.
  unfold vtrue. solve_lc.
Qed.

Lemma lc_g_false : lc_value g_false.
Proof.
  unfold g_false. apply lc_lam_iff_body. apply body_ret_closed.
  unfold vfalse. solve_lc.
Qed.

Lemma body_g2 :
  body_tm (tmatch (vbvar 0) (tret vtrue) (tret vfalse)).
Proof.
  exists ∅. intros x _. cbn.
  unfold vtrue, vfalse. solve_lc.
Qed.

Lemma lc_g2 : lc_value g2.
Proof.
  unfold g2. apply lc_lam_iff_body. apply body_g2.
Qed.

Example g_true_call_returns_true :
  app g_true unit_arg →* tret vtrue.
Proof.
  unfold app, g_true, unit_arg, bool_ty, vtrue.
  eapply reduction_beta_intro.
  - apply body_ret_closed. unfold vtrue. solve_lc.
  - solve_lc.
  - cbn. apply Steps_refl. solve_lc.
Qed.

Example g_false_call_returns_false :
  app g_false unit_arg →* tret vfalse.
Proof.
  unfold app, g_false, unit_arg, bool_ty, vfalse.
  eapply reduction_beta_intro.
  - apply body_ret_closed. unfold vfalse. solve_lc.
  - solve_lc.
  - cbn. apply Steps_refl. solve_lc.
Qed.

Example g2_call_true_returns_true :
  app g2 vtrue →* tret vtrue.
Proof.
  unfold app, g2, bool_ty.
  eapply reduction_beta_intro.
  - apply body_g2.
  - solve_lc.
  - cbn. eapply reduction_match_true_intro; solve_lc.
Qed.

Example g2_call_false_returns_false :
  app g2 vfalse →* tret vfalse.
Proof.
  unfold app, g2, bool_ty.
  eapply reduction_beta_intro.
  - apply body_g2.
  - solve_lc.
  - cbn. eapply reduction_match_false_intro; solve_lc.
Qed.
