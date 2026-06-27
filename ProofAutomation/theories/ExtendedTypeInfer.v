(** * Lightweight extended context-type checking for case studies *)

From ProofAutomation Require Export ExtendedTyping ExtendedSubsumption BasicTypeInfer.
From ContextTyping Require Import Typing.

Open Scope core_scope.
Open Scope case_scope.
Open Scope cty_scope.
Open Scope ctx_scope.

Ltac extended_destruct_matches :=
  repeat match goal with
  | |- context[match ?x with _ => _ end] => destruct x
  | H : context[match ?x with _ => _ end] |- _ => destruct x
  end.

Ltac extended_wf_type :=
  match goal with
  | |- wf_context_ty_at ?d ?D ?τ =>
      unfold primop_precise_ty, binop_precise_ty, binop_top_ty,
        tree_node_precise_ty, list_cons_precise_ty,
        tree_match_eq_ty, list_match_eq_ty, precise_const, const_precise_ty,
        precise_ty, over_ty, under_ty, primop_result_qual, binop_result_qual,
        tree_node_result_qual, list_cons_result_qual, mk_q_eq;
      extended_destruct_matches; case_type_wf_syntax
  | |- basic_context_ty ?D ?τ =>
      unfold primop_precise_ty, binop_precise_ty, binop_top_ty,
        tree_node_precise_ty, list_cons_precise_ty,
        tree_match_eq_ty, list_match_eq_ty, precise_const, const_precise_ty,
        precise_ty, over_ty, under_ty, primop_result_qual, binop_result_qual,
        tree_node_result_qual, list_cons_result_qual, mk_q_eq;
      extended_destruct_matches; case_type_wf_syntax
  end.

Ltac extended_wf_ctx :=
  unfold wf_ctx_under;
  repeat
    match goal with
    | |- basic_ctx _ CtxEmpty => apply basic_ctx_empty
    | |- basic_ctx _ (CtxBind _ _) =>
        apply basic_ctx_bind; [fast_set_solver!! | extended_wf_type]
    | |- basic_ctx _ (CtxComma _ _) =>
        cbn [basic_ctx ctx_dom]; repeat split;
        try extended_wf_ctx; try extended_wf_type; try fast_set_solver!!
    | |- basic_ctx _ (CtxStar _ _) =>
        apply basic_ctx_star; [extended_wf_ctx|extended_wf_ctx|fast_set_solver!!]
    | |- basic_ctx _ (CtxSum _ _) =>
        apply basic_ctx_sum; [extended_wf_ctx|extended_wf_ctx|reflexivity|reflexivity]
    end.

Ltac extended_basic_lookup :=
  first
    [ basic_lookup
    | vm_compute; reflexivity ].

Ltac extended_basic_value :=
  repeat progress basic_type_surface_norm;
  lazymatch goal with
  | |- _ ⊢ᵥ vconst _ ⋮ _ =>
      constructor
  | |- _ ⊢ᵥ vfvar _ ⋮ _ =>
      apply VT_FVar; extended_basic_lookup
  | |- _ ⊢ᵥ avar _ ⋮ _ =>
      change (avar _) with (vfvar _); apply VT_FVar; extended_basic_lookup
  end.

Ltac extended_basic_check :=
  unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
    over_ty, under_ty, qual_top in *;
  repeat rewrite erase_ctx_comma_bind_fresh by fast_set_solver!!;
  cbn [erase_ctx erase_ty] in *;
  repeat progress basic_type_surface_norm;
  lazymatch goal with
  | |- _ ⊢ₑ tprim _ _ ⋮ _ =>
      eapply TT_Op; [cbn [prim_op_type]; reflexivity|extended_basic_value]
  | |- _ ⊢ₑ tbinop _ _ _ ⋮ _ =>
      eapply TT_BinOp; [basic_solve_binop_type|extended_basic_value|extended_basic_value]
  | |- _ ⊢ₑ tret _ ⋮ _ =>
      apply TT_Ret; extended_basic_value
  | |- _ ⊢ₑ tnode _ _ _ ⋮ _ =>
      eapply TT_TreeNode; extended_basic_value
  | |- _ ⊢ₑ tcons _ _ ⋮ _ =>
      eapply TT_ListCons; extended_basic_value
  | |- _ ⊢ₑ _ ⋮ _ =>
      basic_check
  end.

Ltac extended_wf :=
  unfold context_typing_wf;
  repeat split;
  try solve
    [ extended_wf_ctx
    | extended_wf_type
    | fast_set_solver!!
    | extended_basic_check
    | unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
        over_ty, under_ty, qual_top in *;
      repeat rewrite erase_ctx_comma_bind_fresh by fast_set_solver!!;
      cbn [erase_ctx erase_ty] in *; basic_type ].

Ltac extended_case_surface_norm :=
  unfold Ret, avar, vbool, vnat, leaf_value, nil_value, vlist in *;
  cbn [Ret prim_op_type bin_op_type base_ty_of_const] in *;
  lazymatch goal with
  | |- context[tret (vfvar ?x)] =>
      change (tret (vfvar x)) with (tret (avar x))
  | _ => idtac
  end.

Ltac extended_check_fuel fuel :=
  lazymatch fuel with
  | O => fail "extended_check_fuel: fuel exhausted"
  | S ?fuel' =>
  extended_case_surface_norm;
  lazymatch goal with
  | |- ?Σ ; Emp ⊢ₓ ret (vconst ?c) ⋮ const_precise_ty ?c =>
      eapply EXT_Const; extended_wf
  | |- ?Σ ; Emp ⊢ₓ tret (vconst ?c) ⋮ const_precise_ty ?c =>
      change (tret (vconst c)) with (ret (vconst c));
      eapply EXT_Const; extended_wf
  | |- ?Σ ; Emp ⊢ₓ ret ?v ⋮ const_precise_ty ?c =>
      change v with (vconst c);
      eapply EXT_Const; extended_wf
  | Hsub : sub_type_under ?Σ ?Γ ?τ1 ?τ2
      |- ?Σ ; ?Γ ⊢ₓ ?e ⋮ ?τ2 =>
      eapply EXT_Sub;
      [extended_wf|extended_check_fuel fuel'|exact Hsub]
  | |- ?Σ ; ?x ∷ ?τ ⊢ₓ ret (avar ?x) ⋮ ?τ =>
      eapply EXT_Var; extended_wf
  | |- ?Σ ; ?Γ ⊢ₓ ?v1 ⟨ ?op ⟩ ?v2 ⋮ binop_precise_ty ?op ?v1 ?v2 =>
      eapply EXT_BinOp; extended_wf
  | |- ?Σ ; ?Γ ⊢ₓ ?v1 ⟨ ?op ⟩ ?v2 ⋮ binop_top_ty ?op =>
      eapply EXT_BinOpTop; extended_wf
  | |- ?Σ ; ?Γ ⊢ₓ ?op ·₁ ?v ⋮ primop_precise_ty ?op ?v =>
      eapply EXT_AppOpValue; extended_wf
  | |- ?Σ ; ?Γ ⊢ₓ ?f @ ?x ⋮ ?τ =>
      eapply EXT_AppFun with (τx := ONat);
      [extended_wf|fast_set_solver!!|extended_check_fuel fuel'|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ ret (vlam ?Tx (close_tm ?x 0 ?e)) ⋮ (?τx → ?τ) =>
      change (ret (vlam Tx (close_tm x 0 e)))
        with (ret (lam_named x Tx e));
      eapply EXT_LamNamedErased;
      [unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
         base_ty_as_ty, over_ty, under_ty, qual_top;
       cbn [erase_ty]; reflexivity|extended_wf|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ ret (lam_named ?x ?Tx ?e) ⋮ (?τx → ?τ) =>
      eapply EXT_LamNamedErased;
      [unfold ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
         base_ty_as_ty, over_ty, under_ty, qual_top;
       cbn [erase_ty]; reflexivity|extended_wf|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ tlete ?e1 (close_tm ?x 0 ?e2) ⋮ ?τ =>
      change (tlete e1 (close_tm x 0 e2)) with (let_named x e1 e2);
      eapply EXT_LetNamed; [extended_wf|extended_check_fuel fuel'|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ let ?x := ?e1 in ?e2 ⋮ ?τ =>
      eapply EXT_LetNamed; [extended_wf|extended_check_fuel fuel'|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ [| ?root, ?left, ?right |] ⋮
        tree_node_precise_ty ?root ?left ?right =>
      eapply EXT_TreeNode;
      [extended_wf|extended_check_fuel fuel'|extended_check_fuel fuel'|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ ?hd ::ᵗ ?tl ⋮ list_cons_precise_ty ?hd ?tl =>
      eapply EXT_ListCons; [extended_wf|extended_check_fuel fuel'|extended_check_fuel fuel']
  | |- ?Σ ; ?Γ ⊢ₓ ret ?v ⋮ ?τ =>
      eapply typing_to_extended_typing;
      eauto using has_context_type
  | |- ?Σ ; ?Γ ⊢ₓ ?e ⋮ ?τ =>
      eapply typing_to_extended_typing;
      eauto using has_context_type
  end
  end.

Ltac extended_check := extended_check_fuel 16.

Section Regression.

  Lemma extended_check_const_nat :
    ∅; Emp ⊢ₓ ret (vnat 1) ⋮ const_precise_ty (cnat 1).
  Proof.
    eapply EXT_Const.
    unfold context_typing_wf.
    repeat split; try extended_wf_type; try fast_set_solver!!.
  Qed.

  Lemma extended_check_binop_nat :
    ∅; (1%positive ∷ ONat) ,, (2%positive ∷ ONat) ⊢ₓ
      avar 1%positive ⟨ + ⟩ avar 2%positive ⋮
      binop_precise_ty bop_plus (avar 1%positive) (avar 2%positive).
  Proof.
    eapply EXT_BinOp.
    extended_wf.
  Qed.

End Regression.
