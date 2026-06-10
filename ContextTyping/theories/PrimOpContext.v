(** * ContextTyping.PrimOpContext

    Primitive-operation signatures used by the context typing judgment.

    This file intentionally contains only the abstract interface.  Concrete
    primitive contexts, such as the graph-based one for the current core
    operators, live in separate instance files. *)

From CoreLang Require Import BasicTyping SmallStep.
From ContextLogic Require Import FormulaSemantics.
From ContextTypeLanguage Require Import WF.
From Denotation Require Import Context.

(** CoreLang keeps the erased unary type [prim_op_type]; this layer refines it
    with an over-approximate argument qualifier and a precise result qualifier. *)

Record primop_sig := mk_primop_sig {
  prim_arg_base : base_ty;
  prim_arg_qual : type_qualifier;
  prim_ret_base : base_ty;
  prim_ret_qual : type_qualifier;
}.

Definition primop_result_ty (sig : primop_sig) : context_ty :=
  precise_ty sig.(prim_ret_base) sig.(prim_ret_qual).

Definition primop_arg_ty (sig : primop_sig) : context_ty :=
  over_ty sig.(prim_arg_base) sig.(prim_arg_qual).

Definition primop_ctx : Type := prim_op -> primop_sig.

Definition primop_erasure_ok (op : prim_op) (sig : primop_sig) : Prop :=
  prim_op_type op = (sig.(prim_arg_base), sig.(prim_ret_base)).

(** Paper-level semantic well-formedness for primitive operators.

    The result type is scoped as an arrow body, so its qualifier may mention the
    surrounding primitive argument binder. *)
Definition primop_semantic_ok (op : prim_op) (sig : primop_sig) : Prop :=
  forall x : atom,
    let Γx := CtxBind x (primop_arg_ty sig) in
    (ctx_denote Γx ⊫
      ty_denote (erase_ctx Γx) ({0 ~> x} (primop_result_ty sig))
        (tprim op (vfvar x))) /\
    (ty_denote (erase_ctx Γx) ({0 ~> x} (primop_result_ty sig))
        (tprim op (vfvar x)) ⊫
      ctx_denote Γx).

Record wf_primop_sig (op : prim_op) (sig : primop_sig) : Prop := {
  wf_primop_erasure : primop_erasure_ok op sig;
  wf_primop_arg_basic : basic_context_ty ∅ (primop_arg_ty sig);
  wf_primop_result_basic : wf_context_ty_at 1 ∅ (primop_result_ty sig);
  wf_primop_semantic : primop_semantic_ok op sig;
}.

Definition wf_primop_ctx (Φ : primop_ctx) : Prop :=
  forall op, wf_primop_sig op (Φ op).
