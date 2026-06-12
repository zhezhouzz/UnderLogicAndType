(** * ContextTyping.PrimOpConcreteContext

    Concrete graph-based primitive-operation context for the current core
    operators. *)

From CoreLang Require Import BasicTyping SmallStep StrongNormalization.
From ContextLogic Require Import FormulaSemantics.
From ContextTypeLanguage Require Import WF.
From Denotation Require Import Context ConstDenote TypeEquivCore TypeEquiv.
From ContextTyping Require Import PrimOpContext.

(** The graph qualifier is written at the result-type binder depth: [#0] is
    the result value and [#1] is the surrounding primitive argument. *)
Definition primop_graph_qual (op : prim_op) : type_qualifier :=
  tqual ({[LVBound 0; LVBound 1]})
    (fun σ =>
       exists carg cret,
         denote_lvar_value (lso_store σ) (vbvar 1) = Some (vconst carg) /\
         denote_lvar_value (lso_store σ) (vbvar 0) = Some (vconst cret) /\
         prim_step op carg cret).

Definition concrete_primop_sig (op : prim_op) : primop_sig :=
  match prim_op_type op with
  | (arg_b, ret_b) =>
      mk_primop_sig arg_b qual_top ret_b (primop_graph_qual op)
  end.

Definition concrete_Φ : primop_ctx := concrete_primop_sig.

Lemma primop_result_ty_eq op :
  primop_result_ty (concrete_Φ op) =
  precise_ty (prim_ret_base (concrete_Φ op)) (primop_graph_qual op).
Proof.
Admitted.

Lemma primop_arg_ty_eq op :
  primop_arg_ty (concrete_Φ op) =
  over_ty (prim_arg_base (concrete_Φ op)) qual_top.
Proof.
Admitted.

Lemma primop_graph_qual_lc op :
  lvars_wf_at 2 ∅ (qual_vars (primop_graph_qual op)).
Proof.
Admitted.

Lemma primop_graph_qual_open_vars op x y :
  x <> y ->
  qual_vars
    (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) =
  ({[LVFree x; LVFree y]} : lvset).
Proof.
Admitted.

Lemma primop_graph_qual_arg_open_vars op x :
  qual_vars (qual_open_atom 1 x (primop_graph_qual op)) =
  ({[LVBound 0; LVFree x]} : lvset).
Proof.
Admitted.

Lemma primop_graph_qual_fibvars_set op x y :
  x <> y ->
  set_swap (LVBound 0) (LVFree y)
    (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
      {[LVBound 0]}) =
  qual_vars
    (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) ∖
    {[LVFree y]}.
Proof.
Admitted.

Lemma primop_graph_qual_open_prop_iff op x y
    (Hxy : x <> y)
    (s : LStoreOn (V := value)
      (qual_vars
        (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))))) :
  qual_prop
    (qual_open_atom 0 y (qual_open_atom 1 x (primop_graph_qual op))) s <->
  exists carg cret,
    (lso_store s : LStore (V := value)) !! LVFree x = Some (vconst carg) /\
    (lso_store s : LStore (V := value)) !! LVFree y = Some (vconst cret) /\
    prim_step op carg cret.
Proof.
Admitted.

Lemma prim_step_total_for_base op c arg_b ret_b :
  prim_op_type op = (arg_b, ret_b) ->
  base_ty_of_const c = arg_b ->
  exists c', prim_step op c c'.
Proof.
Admitted.

Lemma expr_eval_prim_fvar_const_elim σ op x carg cret :
  (σ : LStore (V := value)) !! LVFree x = Some (vconst carg) ->
  expr_eval_in_store σ (tprim op (vfvar x)) (vconst cret) ->
  prim_step op carg cret.
Proof.
Admitted.

Lemma expr_eval_prim_fvar_const_result σ op x carg v :
  (σ : LStore (V := value)) !! LVFree x = Some (vconst carg) ->
  expr_eval_in_store σ (tprim op (vfvar x)) v ->
  exists cret,
    prim_step op carg cret /\
    v = vconst cret.
Proof.
Admitted.

Lemma expr_result_formula_prim_fvar_lookup
    op x y (m : WfWorldT) σ carg :
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  (m : WorldT) σ ->
  σ !! x = Some (vconst carg) ->
  exists cret,
    σ !! y = Some (vconst cret) /\
    prim_step op carg cret.
Proof.
Admitted.

Lemma primop_arg_const_from_ctx op x (m : WfWorldT) σ :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  (m : WorldT) σ ->
  exists c,
    σ !! x = Some (vconst c) /\
    base_ty_of_const c = prim_arg_base (concrete_Φ op).
Proof.
Admitted.

Lemma primop_arg_in_world op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  x ∈ world_dom (m : WorldT).
Proof.
Admitted.

Lemma res_models_atom_top (m : WfWorldT) :
	  m ⊨ FAtom qual_top.
	Proof.
Admitted.

Lemma qual_top_open y :
  qual_open_atom 0 y (qual_top (V := value)) = qual_top.
Proof.
Admitted.

Lemma over_top_basic b :
  basic_context_ty ∅ (CTOver b qual_top).
Proof.
Admitted.

Lemma over_top_basic_lvars_relevant b x T :
  basic_context_ty_lvars
    (dom (relevant_env (<[LVFree x := T]> ∅)
      (CTOver b qual_top) (tret (vfvar x))))
    (CTOver b qual_top).
Proof.
Admitted.

Lemma basic_world_insert_relevant_ret_fvar_scope b x τ (m : WfWorldT) :
  wf_context_ty_at 0 ∅ τ ->
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  lvars_fv
    (dom (relevant_env (<[LVFree x := TBase b]> ∅)
      τ (tret (vfvar x)))) ⊆ world_dom (m : WorldT).
Proof.
Admitted.

Lemma over_top_ret_fvar_guard b x (m : WfWorldT) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  m ⊨ ty_guard_formula
    (relevant_env (<[LVFree x := TBase b]> ∅)
      (CTOver b qual_top) (tret (vfvar x)))
    (CTOver b qual_top) (tret (vfvar x)).
Proof.
Admitted.

Lemma over_top_ret_fvar_ty_denote_gas_scope gas b x (m : WfWorldT) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  formula_scoped_in_world m
    (ty_denote_gas gas (<[LVFree x := TBase b]> ∅)
      (CTOver b qual_top) (tret (vfvar x))).
Proof.
Admitted.

Lemma over_top_ret_fvar_denotation_gas gas b x (m : WfWorldT) :
  m ⊨ basic_world_formula (<[LVFree x := TBase b]> ∅) ->
  m ⊨ ty_denote_gas gas (<[LVFree x := TBase b]> ∅)
    (CTOver b qual_top) (tret (vfvar x)).
Proof.
Admitted.

Lemma expr_total_formula_tprim_from_primop_arg
    op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ expr_total_formula (tprim op (vfvar x)).
Proof.
Admitted.

Lemma primop_graph_qual_open_msubst_prop_iff
    op x y (σx : StoreT)
    (s : LStoreOn
      (qual_vars
        (qual_msubst_store σx
          (qual_open_atom 0 y
            (qual_open_atom 1 x (primop_graph_qual op)))))) :
  x <> y ->
  dom (σx : StoreT) = {[x]} ->
  qual_prop
    (qual_msubst_store σx
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op)))) s <->
  exists carg cret,
    σx !! x = Some (vconst carg) /\
    (lso_store s : LStore) !! LVFree y = Some (vconst cret) /\
    prim_step op carg cret.
Proof.
Admitted.

Lemma primop_graph_type_qualifier_open_msubst_from_expr
    op x y (m mfib : WfWorldT) σx :
  x <> y ->
  res_fiber_from_projection m ({[x]} : aset) σx mfib ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  mfib ⊨ formula_msubst_store σx
    (FAtom
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op)))).
Proof.
Admitted.

Lemma primop_graph_fib_over_from_expr
    op x y (m : WfWorldT) :
  x <> y ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))) ∖ {[LVFree y]})
    (FOver (FAtom
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))))).
Proof.
Admitted.

Lemma primop_graph_fib_under_from_expr
    op x y (m : WfWorldT) :
  x <> y ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ expr_result_formula (tprim op (vfvar x)) (LVFree y) ->
  m ⊨ FFibVars
    (qual_vars
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))) ∖ {[LVFree y]})
    (FUnder (FAtom
      (qual_open_atom 0 y
        (qual_open_atom 1 x (primop_graph_qual op))))).
Proof.
Admitted.

Lemma primop_opened_result_guard_formula
    op x τbody (τ : context_ty) (m : WfWorldT) :
  τ = ({0 ~> x} τbody) ->
  wf_context_ty_at 1 ∅ τbody ->
  erase_ty τbody = TBase (prim_ret_base (concrete_Φ op)) ->
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ ty_guard_formula
    (relevant_env
      (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
      τ (tprim op (vfvar x)))
    τ (tprim op (vfvar x)).
Proof.
Admitted.

Definition primop_graph_over_formula (op : prim_op) (x : atom) : FormulaT :=
  FForall
    (FImpl
      (expr_result_formula (tm_shift 0 (tprim op (vfvar x))) (LVBound 0))
      (FFibVars
        (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
          {[LVBound 0]})
        (FOver
          (FAtom
            (qual_open_atom 1 x (primop_graph_qual op)))))).

Definition primop_graph_under_formula (op : prim_op) (x : atom) : FormulaT :=
  FForall
    (FImpl
      (expr_result_formula (tm_shift 0 (tprim op (vfvar x))) (LVBound 0))
      (FFibVars
        (qual_vars (qual_open_atom 1 x (primop_graph_qual op)) ∖
          {[LVBound 0]})
        (FUnder
          (FAtom
            (qual_open_atom 1 x (primop_graph_qual op)))))).

Lemma formula_fv_primop_graph_over_formula op x :
  formula_fv (primop_graph_over_formula op x) = ({[x]} : aset).
Proof.
Admitted.

Lemma formula_fv_primop_graph_under_formula op x :
  formula_fv (primop_graph_under_formula op x) = ({[x]} : aset).
Proof.
Admitted.

Local Ltac primop_graph_scope_norm :=
  unfold formula_scoped_in_world;
	  rewrite ?formula_fv_forall, ?formula_fv_impl, ?formula_fv_fibvars,
	    ?formula_fv_over, ?formula_fv_under, ?formula_fv_basic_world_formula,
	    ?formula_fv_expr_result_formula, ?formula_fv_atom;
	  unfold qual_dom, basic_world_formula, expr_result_formula,
	    FFiberAtom;
	  cbn [tm_shift value_shift tm_lvars tm_lvars_at value_lvars_at
	    lvar_value_keys formula_lvars formula_lvars_at qual_vars
	    qual_lvars primop_graph_qual];
  rewrite ?lvars_at_depth_union, ?lvars_at_depth_empty,
    ?lvars_at_depth_singleton_bound0_succ,
    ?lvars_at_depth_singleton_free,
    ?lvars_fv_union, ?lvars_fv_empty, ?lvars_fv_singleton_bound,
    ?lvars_fv_singleton_free, ?dom_insert_L, ?dom_empty_L.

Local Ltac primop_graph_scope_from Hctx Hdom HFout :=
  primop_graph_scope_norm;
  try rewrite primop_graph_qual_arg_open_vars;
  try rewrite primop_graph_qual_open_vars by set_solver;
  repeat match goal with
  | |- context[({[?v]} ∖ {[?v]} : lvset)] =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) by set_solver
  | |- context[lvars_at_depth 1 ({[LVBound 0]} ∪ ∅)] =>
      replace (lvars_at_depth 1 ({[LVBound 0]} ∪ ∅))
        with (∅ : lvset)
        by (rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_empty; set_solver)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]} ∖ {[LVBound 0]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}))
        with ({[LVFree x]} : lvset)
        by (replace (({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_singleton_free; reflexivity)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]}))
        with ({[LVFree x]} : lvset)
        by (replace ({[LVBound 0; LVFree x]} : lvset)
              with ({[LVBound 0]} ∪ {[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_singleton_free; set_solver)
  | |- context[lvars_fv (({[LVFree ?x; LVFree ?y]} ∖ {[LVFree ?y]}) : lvset)] =>
      replace (lvars_fv (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset))
        with ({[x]} : aset)
        by (replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            symmetry; apply lvars_fv_singleton_free)
  end;
  try (rewrite Hdom, HFout);
  let Hx := fresh "Hx_world" in
  pose proof (primop_arg_in_world _ _ _ Hctx) as Hx;
  set_solver.

Local Ltac primop_graph_closed_scope_from Hctx :=
  primop_graph_scope_norm;
  try rewrite primop_graph_qual_arg_open_vars;
  try rewrite primop_graph_qual_open_vars by set_solver;
  repeat match goal with
  | |- context[({[?v]} ∖ {[?v]} : lvset)] =>
      replace ({[v]} ∖ {[v]} : lvset) with (∅ : lvset) by set_solver
  | |- context[lvars_at_depth 1 ({[LVBound 0]} ∪ ∅)] =>
      replace (lvars_at_depth 1 ({[LVBound 0]} ∪ ∅))
        with (∅ : lvset)
        by (rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_empty; set_solver)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]} ∖ {[LVBound 0]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}))
        with ({[LVFree x]} : lvset)
        by (replace (({[LVBound 0; LVFree x]} ∖ {[LVBound 0]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_singleton_free; reflexivity)
  | |- context[lvars_at_depth 1 ({[LVBound 0; LVFree ?x]})] =>
      replace (lvars_at_depth 1 ({[LVBound 0; LVFree x]}))
        with ({[LVFree x]} : lvset)
        by (replace ({[LVBound 0; LVFree x]} : lvset)
              with ({[LVBound 0]} ∪ {[LVFree x]} : lvset) by set_solver;
            rewrite lvars_at_depth_union,
              lvars_at_depth_singleton_bound0_succ,
              lvars_at_depth_singleton_free; set_solver)
  | |- context[lvars_fv (({[LVFree ?x; LVFree ?y]} ∖ {[LVFree ?y]}) : lvset)] =>
      replace (lvars_fv (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset))
        with ({[x]} : aset)
        by (replace (({[LVFree x; LVFree y]} ∖ {[LVFree y]}) : lvset)
              with ({[LVFree x]} : lvset) by set_solver;
            symmetry; apply lvars_fv_singleton_free)
  end;
  rewrite ?lvars_fv_empty, ?lvars_fv_singleton_free;
  let Hx := fresh "Hx_world" in
  pose proof (primop_arg_in_world _ _ _ Hctx) as Hx;
  better_set_solver.

Lemma primop_graph_over_formula_scope op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  formula_scoped_in_world m (primop_graph_over_formula op x).
Proof.
Admitted.

Lemma primop_graph_under_formula_scope op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  formula_scoped_in_world m (primop_graph_under_formula op x).
Proof.
Admitted.

Lemma primop_graph_over_denotation_gas
    gas op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
    ({0 ~> x}
      (CTOver (prim_ret_base (concrete_Φ op)) (primop_graph_qual op)))
    (tprim op (vfvar x)).
Proof.
Admitted.

Lemma primop_graph_under_denotation_gas
    gas op x (m : WfWorldT) :
  m ⊨ ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ->
  m ⊨ ty_denote_gas gas
    (atom_env_to_lty_env (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op)))))
    ({0 ~> x}
      (CTUnder (prim_ret_base (concrete_Φ op)) (primop_graph_qual op)))
    (tprim op (vfvar x)).
Proof.
Admitted.

Lemma primop_graph_result_denotation
    op x :
  ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))) ⊫
    ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
      ({0 ~> x} (primop_result_ty (concrete_Φ op)))
      (tprim op (vfvar x)).
Proof.
Admitted.

Lemma primop_result_denotation_arg_world
    op x (m : WfWorldT) :
  m ⊨ ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)) ->
  m ⊨ basic_world_formula (<[LVFree x := TBase (prim_arg_base (concrete_Φ op))]> ∅).
Proof.
Admitted.

Lemma primop_graph_result_to_arg_ctx
    op x :
  ty_denote (erase_ctx (CtxBind x (primop_arg_ty (concrete_Φ op))))
    ({0 ~> x} (primop_result_ty (concrete_Φ op)))
    (tprim op (vfvar x)) ⊫
  ctx_denote (CtxBind x (primop_arg_ty (concrete_Φ op))).
Proof.
Admitted.

Lemma primop_arg_basic op :
  basic_context_ty ∅ (primop_arg_ty (concrete_Φ op)).
Proof.
Admitted.

Lemma primop_result_wf op :
  wf_context_ty_at 1 ∅ (primop_result_ty (concrete_Φ op)).
Proof.
Admitted.

Lemma primop_erasure op :
  primop_erasure_ok op (concrete_Φ op).
Proof.
Admitted.

Theorem concrete_Φ_wf : wf_primop_ctx concrete_Φ.
Proof.
Admitted.
