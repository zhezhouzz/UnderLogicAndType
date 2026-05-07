(** * ChoiceType.Sugar

    Small type-level abbreviations used by the paper presentation and the
    unstable [ChoiceTyping] layer.  The core syntax remains in [Syntax.v];
    this file only names common derived choice types. *)

From ChoiceType Require Export Syntax.

Definition over_ty (b : base_ty) (φ : type_qualifier) : choice_ty :=
  CTOver b φ.

Definition under_ty (b : base_ty) (φ : type_qualifier) : choice_ty :=
  CTUnder b φ.

(** A precise refinement is both an over- and under-approximation by the same
    qualifier.  This is the type assigned to constants and primitive results
    in the current paper presentation. *)
Definition precise_ty (b : base_ty) (φ : type_qualifier) : choice_ty :=
  CTInter (over_ty b φ) (under_ty b φ).

(** Unary primitive-operation type: arguments are over-approximate while
    results are precise.  The result qualifier may mention bvar 0 for the
    argument coordinate and is opened by the application rule. *)
Definition primop_ty
    (arg_b : base_ty) (arg_φ : type_qualifier)
    (ret_b : base_ty) (ret_φ : type_qualifier) : choice_ty :=
  CTArrow (over_ty arg_b arg_φ) (precise_ty ret_b ret_φ).

Definition bool_qual (b : bool) : type_qualifier :=
  mk_q_eq (vbvar 0) (vconst (cbool b)).

Definition bool_precise_ty (b : bool) : choice_ty :=
  precise_ty TBool (bool_qual b).

Definition const_precise_ty (c : constant) : choice_ty :=
  precise_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)).

Lemma erase_over_ty b φ :
  erase_ty (over_ty b φ) = TBase b.
Proof. reflexivity. Qed.

Lemma erase_under_ty b φ :
  erase_ty (under_ty b φ) = TBase b.
Proof. reflexivity. Qed.

Lemma erase_precise_ty b φ :
  erase_ty (precise_ty b φ) = TBase b.
Proof. reflexivity. Qed.

Lemma erase_primop_ty arg_b arg_φ ret_b ret_φ :
  erase_ty (primop_ty arg_b arg_φ ret_b ret_φ) =
  (TBase arg_b →ₜ TBase ret_b).
Proof. reflexivity. Qed.

Lemma erase_bool_precise_ty b :
  erase_ty (bool_precise_ty b) = TBase TBool.
Proof. reflexivity. Qed.

Lemma erase_const_precise_ty c :
  erase_ty (const_precise_ty c) = TBase (base_ty_of_const c).
Proof. reflexivity. Qed.

Notation "'prt' b φ" := (precise_ty b φ)
  (at level 20, b at next level, φ at next level, only printing).
