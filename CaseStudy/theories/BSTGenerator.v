(** * BST generator case-study program *)

From ProofAutomation Require Import BasicTypeInfer.

Open Scope case_scope.
Open Scope core_scope.
Open Scope cty_scope.

Section BSTGeneratorExample.

Definition r : atom := 20%positive.
Definition lo : atom := 21%positive.
Definition range_arg : atom := 22%positive.
Definition rec : atom := 23%positive.
Definition isz : atom := 24%positive.
Definition rp : atom := 25%positive.
Definition left_size : atom := 26%positive.
Definition right_size : atom := 27%positive.
Definition new_lo : atom := 28%positive.
Definition left_tree : atom := 29%positive.
Definition right_tree : atom := 30%positive.

Fixpoint tree_mem (n : nat) (t : tree) : Prop :=
  match t with
  | tr_leaf => False
  | tr_node r l rr => n = r \/ tree_mem n l \/ tree_mem n rr
  end.

Fixpoint bst_between (lo hi : nat) (t : tree) : Prop :=
  match t with
  | tr_leaf => True
  | tr_node r l rr =>
      lo <= r < hi /\
      bst_between lo r l /\
      bst_between r hi rr
  end.

Definition bst_spec (lo hi : nat) (t : tree) : Prop :=
  bst_between lo hi t.

Definition q_tree_bst_range (lo hi t : value) : type_qualifier :=
  tqual (lvar_value_keys lo ∪ lvar_value_keys hi ∪ lvar_value_keys t)
    (fun σ =>
       exists nlo nhi tr,
         denote_lvar_value (lso_store σ) lo = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) hi = Some (vconst (cnat nhi)) /\
         denote_lvar_value (lso_store σ) t = Some (vconst (ctree tr)) /\
         bst_spec nlo nhi tr).

Definition q_mem_tree_iff_range (lo hi t : value) : type_qualifier :=
  tqual (lvar_value_keys lo ∪ lvar_value_keys hi ∪ lvar_value_keys t)
    (fun σ =>
       exists nlo nhi tr,
         denote_lvar_value (lso_store σ) lo = Some (vconst (cnat nlo)) /\
         denote_lvar_value (lso_store σ) hi = Some (vconst (cnat nhi)) /\
         denote_lvar_value (lso_store σ) t = Some (vconst (ctree tr)) /\
         forall n, tree_mem n tr <-> nlo <= n < nhi).

Definition OBstBetween : context_ty :=
  over_ty TTree (q_tree_bst_range arg1 arg0 ν).

Definition UBstBetween : context_ty :=
  under_ty TTree (q_tree_bst_range arg1 arg0 ν).

Definition bst_range_pred := bst_between.
Definition bst_generator_spec := bst_spec.

Definition range_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → O[ ℕ ].

(** Outline of the paper type:
    [r -> lo -> range -> □(tree satisfying the generated BST spec)]. *)
Definition bst_gen_ty : context_ty :=
  O[ ℕ ] → O[ ℕ ] → range_ty → □ OBstBetween.

(** A readable recursive program.  Arithmetic and comparisons are core binary
    operations, and the paper's angelic choice [Leaf ⊕ body] is encoded by
    a nondeterministic boolean hidden behind [⊕ₙ]. *)
Definition bst_gen_program : tm :=
  ret (μ rec, r : ℕ ~> ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree =>
    ret (ƛ lo : ℕ =>
      ret (ƛ range_arg : ℕ →ᵦ ℕ →ᵦ ℕ =>
        let isz := r ⟨ ≤ ⟩ vnat 0 in
        if isz then
          ret leaf_value
        else
          ret leaf_value ⊕ₙ
            (
            let rp := range_arg @@ (vnat 1, r) in
            let left_size := rp ⟨ - ⟩ vnat 1 in
            let right_size := r ⟨ - ⟩ rp in
            let new_lo := lo ⟨ + ⟩ rp in
            let left_tree := rec @@@ (left_size, lo, range_arg) in
            let right_tree := rec @@@ (right_size, new_lo, range_arg) in
            [| new_lo, left_tree, right_tree |]
	            )))).

Definition bst_gen_basic_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ (ℕ →ᵦ ℕ →ᵦ ℕ) →ᵦ Tree.

Lemma bst_gen_program_basic_type :
  ∅ ⊢ₑ bst_gen_program ⋮ bst_gen_basic_ty.
Proof.
  unfold bst_gen_program, bst_gen_basic_ty.
  repeat progress basic_type_surface_norm.
  eapply TT_Ret.
  eapply basic_typing_fixfun_named; [basic_type_fresh|basic_type_fresh|idtac].
  eapply TT_Ret.
  eapply basic_typing_lam_named; [basic_type_fresh|idtac].
  eapply TT_Ret.
  eapply basic_typing_lam_named; [basic_type_fresh|idtac].
  eapply basic_typing_let_named; [basic_type_fresh|basic_type|idtac].
  eapply TT_Match; [basic_type|basic_type|idtac].
  eapply basic_typing_nondet_tm; basic_type.
Qed.

Lemma bst_between_leaf lo hi :
  bst_between lo hi tr_leaf.
Proof. cbn. exact I. Qed.

Lemma tree_mem_node_root n l r :
  tree_mem n (tr_node n l r).
Proof. cbn. left. reflexivity. Qed.

Lemma range_ty_wf :
  basic_context_ty ∅ range_ty.
Proof.
  unfold range_ty, ONat, over_ty, qual_top, basic_context_ty.
  cbn [wf_context_ty_at qual_vars qual_lvars].
  repeat split; intros [k|x] Hx; cbn [lvar_wf_at] in *; set_solver.
Qed.

Lemma basic_type_leaf_ret Γ :
  Γ ⊢ₑ Ret leaf_value ⋮ Tree.
Proof.
  unfold Ret, leaf_value.
  constructor. constructor.
Qed.

Lemma basic_type_node_const Γ n l r :
  Γ ⊢ₑ node_tm (vnat n) (vconst (ctree l)) (vconst (ctree r)) ⋮
    Tree.
Proof.
  unfold node_tm, vnat.
  econstructor; constructor.
Qed.

End BSTGeneratorExample.
