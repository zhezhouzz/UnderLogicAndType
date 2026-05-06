(** * ChoiceTyping.PrimOpContext

    Paper-level primitive-operation signatures.  CoreLang keeps the erased
    unary type [prim_op_type]; this layer refines it with over-approximate
    argument qualifiers and precise result qualifiers. *)

From ChoiceType Require Export Sugar BasicTyping.

Record primop_sig := mk_primop_sig {
  prim_arg_base : base_ty;
  prim_arg_qual : type_qualifier;
  prim_ret_base : base_ty;
  prim_ret_qual : type_qualifier;
}.

Definition primop_sig_ty (sig : primop_sig) : choice_ty :=
  primop_ty
    sig.(prim_arg_base) sig.(prim_arg_qual)
    sig.(prim_ret_base) sig.(prim_ret_qual).

Definition primop_result_ty (sig : primop_sig) : choice_ty :=
  precise_ty sig.(prim_ret_base) sig.(prim_ret_qual).

Definition primop_arg_ty (sig : primop_sig) : choice_ty :=
  over_ty sig.(prim_arg_base) sig.(prim_arg_qual).

Definition primop_ctx : Type := prim_op → primop_sig.

Definition primop_erasure_ok (op : prim_op) (sig : primop_sig) : Prop :=
  prim_op_type op = (sig.(prim_arg_base), sig.(prim_ret_base)).

Definition wf_primop_sig (op : prim_op) (sig : primop_sig) : Prop :=
  primop_erasure_ok op sig ∧
  basic_choice_ty ∅ (primop_arg_ty sig) ∧
  basic_choice_ty ∅ (primop_result_ty sig).

Definition wf_primop_ctx (Φ : primop_ctx) : Prop :=
  ∀ op, wf_primop_sig op (Φ op).

Lemma erase_primop_arg_ty sig :
  erase_ty (primop_arg_ty sig) = TBase sig.(prim_arg_base).
Proof. destruct sig; reflexivity. Qed.

Lemma erase_primop_result_ty sig :
  erase_ty (primop_result_ty sig) = TBase sig.(prim_ret_base).
Proof. destruct sig; reflexivity. Qed.

Lemma erase_primop_sig_ty sig :
  erase_ty (primop_sig_ty sig) =
  (TBase sig.(prim_arg_base) →ₜ TBase sig.(prim_ret_base)).
Proof. destruct sig; reflexivity. Qed.

Lemma wf_primop_sig_erasure op sig :
  wf_primop_sig op sig →
  primop_erasure_ok op sig.
Proof. intros [Herase _]. exact Herase. Qed.

Lemma wf_primop_sig_arg_basic op sig :
  wf_primop_sig op sig →
  basic_choice_ty ∅ (primop_arg_ty sig).
Proof. intros [_ [Hbasic _]]. exact Hbasic. Qed.

Lemma wf_primop_sig_result_basic op sig :
  wf_primop_sig op sig →
  basic_choice_ty ∅ (primop_result_ty sig).
Proof. intros [_ [_ Hbasic]]. exact Hbasic. Qed.

Lemma wf_primop_sig_erased_bases op sig :
  wf_primop_sig op sig →
  prim_op_type op = (sig.(prim_arg_base), sig.(prim_ret_base)).
Proof. apply wf_primop_sig_erasure. Qed.

(** Default shallow signatures for the current unary CoreLang primitives.
    These are intentionally conservative: arguments and results are typed by
    top qualifiers except where examples can later refine them. *)
Definition default_primop_ctx : primop_ctx :=
  λ op,
    match prim_op_type op with
    | (arg_b, ret_b) => mk_primop_sig arg_b qual_top ret_b qual_top
    end.

Lemma default_primop_ctx_erasure_ok op :
  primop_erasure_ok op (default_primop_ctx op).
Proof.
  unfold primop_erasure_ok, default_primop_ctx.
  destruct (prim_op_type op) as [arg_b ret_b]. reflexivity.
Qed.
