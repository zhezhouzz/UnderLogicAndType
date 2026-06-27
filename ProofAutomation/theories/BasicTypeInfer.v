(** * ProofAutomation.BasicTypeInfer

    A deterministic proof-search layer for the erased/basic type system.

    The tactic is intentionally small and syntax directed: it inspects the
    current [value_has_type] or [tm_has_type] goal, applies the matching basic
    typing rule, and leaves only lookup/freshness side conditions to ordinary
    stdpp/set automation.  It can be used as a checker when the result type is
    known, or as a lightweight inferencer by leaving the result type as an
    existential variable. *)

From stdpp Require Import gmap.
From ContextBase Require Import Tactics.
From ContextStore Require Import StoreCore.
From CoreLang Require Export BasicTyping.
From CoreLang Require Import BasicTypingProps.
From LocallyNameless Require Import Tactics.
From ProofAutomation Require Export CaseBasicAutomation.

Open Scope core_scope.
Open Scope case_scope.

Lemma subst_fresh_to_swap_atom_mutual :
  (forall v x y,
    y ∉ fv_value v ->
    value_subst x (vfvar y) v = value_swap_atom x y v) /\
  (forall e x y,
    y ∉ fv_tm e ->
    tm_subst x (vfvar y) e = tm_swap_atom x y e).
Proof.
  split.
  - intro v.
    induction v using value_mut with
      (P0 := fun e => forall x y,
        y ∉ fv_tm e ->
        tm_subst x (vfvar y) e = tm_swap_atom x y e);
      cbn [fv_value fv_tm value_subst tm_subst value_swap_atom tm_swap_atom];
      intros xsub yfresh Hy;
      try reflexivity; try solve [f_equal; eauto; set_solver].
    destruct (decide (xsub = x)) as [->|Hne].
    + rewrite swap_l. reflexivity.
    + rewrite swap_fresh by set_solver. reflexivity.
  - intro e.
    induction e using tm_mut with
      (P := fun v => forall x y,
        y ∉ fv_value v ->
        value_subst x (vfvar y) v = value_swap_atom x y v);
      cbn [fv_value fv_tm value_subst tm_subst value_swap_atom tm_swap_atom];
      intros xsub yfresh Hy;
      try reflexivity; try solve [f_equal; eauto; set_solver].
    destruct (decide (xsub = x)) as [->|Hne].
    + rewrite swap_l. reflexivity.
    + rewrite swap_fresh by set_solver. reflexivity.
Qed.

Lemma value_subst_fresh_to_swap_atom v x y :
  y ∉ fv_value v ->
  value_subst x (vfvar y) v = value_swap_atom x y v.
Proof. exact (proj1 subst_fresh_to_swap_atom_mutual v x y). Qed.

Lemma tm_subst_fresh_to_swap_atom e x y :
  y ∉ fv_tm e ->
  tm_subst x (vfvar y) e = tm_swap_atom x y e.
Proof.
  exact (proj2 subst_fresh_to_swap_atom_mutual e x y).
Qed.

Lemma atom_ty_env_insert_commute
    (Γ : gmap atom ty) x y Tx Ty :
  x <> y ->
  <[x := Tx]> (<[y := Ty]> Γ) =
  <[y := Ty]> (<[x := Tx]> Γ).
Proof.
  intros Hxy.
  apply insert_insert_ne. exact Hxy.
Qed.

Lemma value_has_type_insert_self Γ x T :
  <[x := T]> Γ ⊢ᵥ vfvar x ⋮ T.
Proof.
  apply VT_FVar.
  apply map_lookup_insert.
Qed.

Lemma fixfun_body_env_commute
    (Γ : gmap atom ty) self arg y sx T :
  arg <> y ->
  self <> y ->
  <[self := sx →ₜ T]> (<[arg := sx]> (<[y := sx]> Γ)) =
  <[y := sx]> (<[self := sx →ₜ T]> (<[arg := sx]> Γ)).
Proof.
  intros Hargy Hselfy.
  transitivity (<[self := sx →ₜ T]> (<[y := sx]> (<[arg := sx]> Γ))).
  - f_equal. apply atom_ty_env_insert_commute. exact Hargy.
  - apply atom_ty_env_insert_commute. exact Hselfy.
Qed.

Lemma basic_typing_lam_named Γ x s e T :
  x ∉ dom Γ ->
  <[x := s]> Γ ⊢ₑ e ⋮ T ->
  Γ ⊢ᵥ lam_named x s e ⋮ (s →ₜ T).
Proof.
  intros HxΓ Hbody.
  unfold lam_named.
  eapply VT_Lam with (L := dom Γ ∪ fv_tm e ∪ {[x]}).
  intros y Hy.
  change (<[y := s]> Γ ⊢ₑ open_tm 0 (vfvar y) (close_tm x 0 e) ⋮ T).
  eapply basic_typing_open_tm with (Γ := <[y := s]> Γ) (x := x) (U := s).
  - apply close_rm_fv_tm.
  - apply value_has_type_insert_self.
  - change (<[x := s]> (<[y := s]> Γ) ⊢ₑ
        open_tm 0 (vfvar x) (close_tm x 0 e) ⋮ T).
    rewrite open_close_var_tm by exact (typing_tm_lc _ _ _ Hbody).
    rewrite atom_ty_env_insert_commute by fast_set_solver!!.
    eapply basic_typing_weaken_insert_tm.
    + apply not_elem_of_dom.
      transitivity (Γ !! y).
      * apply map_lookup_insert_ne. fast_set_solver!!.
      * apply not_elem_of_dom. fast_set_solver!!.
    + exact Hbody.
Qed.

Lemma basic_typing_let_named Γ x e1 e2 T1 T2 :
  x ∉ dom Γ ->
  Γ ⊢ₑ e1 ⋮ T1 ->
  <[x := T1]> Γ ⊢ₑ e2 ⋮ T2 ->
  Γ ⊢ₑ let_named x e1 e2 ⋮ T2.
Proof.
  intros HxΓ He1 Hbody.
  unfold let_named.
  eapply TT_Let with (L := dom Γ ∪ fv_tm e2 ∪ {[x]}).
  - exact He1.
  - intros y Hy.
    change (<[y := T1]> Γ ⊢ₑ open_tm 0 (vfvar y) (close_tm x 0 e2) ⋮ T2).
    eapply basic_typing_open_tm with (Γ := <[y := T1]> Γ) (x := x) (U := T1).
    + apply close_rm_fv_tm.
    + apply value_has_type_insert_self.
    + change (<[x := T1]> (<[y := T1]> Γ) ⊢ₑ
          open_tm 0 (vfvar x) (close_tm x 0 e2) ⋮ T2).
      rewrite open_close_var_tm by exact (typing_tm_lc _ _ _ Hbody).
      rewrite atom_ty_env_insert_commute by fast_set_solver!!.
      eapply basic_typing_weaken_insert_tm.
      * apply not_elem_of_dom.
        transitivity (Γ !! y).
        -- apply map_lookup_insert_ne. fast_set_solver!!.
        -- apply not_elem_of_dom. fast_set_solver!!.
      * exact Hbody.
Qed.

Ltac basic_type_norm :=
  unfold Ret, avar, vbool, vnat, leaf_value, nil_value, vlist,
    if_named,
    case_app, prim_app, call2_tm, call3_tm, cons_tm, node_tm, nondet_tm,
    bin_lt, bin_le, bin_gt, bin_ge, bin_plus, bin_minus, bin_and, bin_or in *;
  cbn [open_one open_value open_tm close_value close_tm
       open_value_inst open_tm_inst open_value_atom_inst open_tm_atom_inst
       open_tree_node_branch open_tree_node_branch_value
       open_list_cons_branch open_list_cons_branch_value
       prim_op_type bin_op_type base_ty_of_const] in *;
  crush_binders;
  cbn [open_one open_value open_tm close_value close_tm
       open_value_inst open_tm_inst open_value_atom_inst open_tm_atom_inst
       open_tree_node_branch open_tree_node_branch_value
       open_list_cons_branch open_list_cons_branch_value
       prim_op_type bin_op_type base_ty_of_const] in *.

Ltac basic_type_surface_norm :=
  unfold Ret, avar, vbool, vnat, leaf_value, nil_value, vlist,
    case_app, prim_app, call2_tm, call3_tm, cons_tm, node_tm,
    if_named,
    bin_lt, bin_le, bin_gt, bin_ge, bin_plus, bin_minus, bin_and, bin_or in *;
  cbn [prim_op_type bin_op_type base_ty_of_const] in *.

Ltac basic_type_side :=
  basic_type_norm;
  cbn [prim_op_type bin_op_type base_ty_of_const] in *;
  solve [reflexivity | eassumption | better_set_solver].

Ltac basic_lookup :=
  basic_type_norm;
  cbn in *;
  first
    [ eassumption
    | apply map_lookup_insert
    | match goal with
      | |- <[?y := ?Ty]> ?Γ !! ?x = Some ?T =>
          transitivity (Γ !! x);
          [ apply map_lookup_insert_ne;
            solve [congruence | vm_compute; congruence | fast_set_solver!!]
          | basic_lookup ]
      end ].

Ltac basic_solve_primop_type :=
  cbn [prim_op_type];
  first [reflexivity | match goal with |- prim_op_type ?op = _ =>
                         destruct op; reflexivity
                       end].

Ltac basic_solve_binop_type :=
  cbn [bin_op_type];
  first [reflexivity | match goal with |- bin_op_type ?op = _ =>
                         destruct op; reflexivity
                       end].

Ltac basic_type_fresh :=
  first
    [ solve [fast_set_solver!!]
    | solve [congruence]
    | solve [vm_compute; congruence]
    | match goal with
      | |- ?x ∉ dom (<[?y := ?T]> ?Γ) =>
          apply not_elem_of_dom;
          transitivity (Γ !! x);
          [ apply map_lookup_insert_ne; basic_type_fresh
          | apply not_elem_of_dom; basic_type_fresh ]
      end ].

Ltac basic_atom_decide_norm :=
  repeat match goal with
  | |- context[decide (?a = ?b)] =>
      first
        [ rewrite (decide_True (a = b)) by (vm_compute; reflexivity)
        | rewrite (decide_False (a = b)) by (vm_compute; congruence) ]
  end;
  cbn [open_one open_tm open_value open_tm_atom_inst open_value_atom_inst
       open_tm_inst open_value_inst close_tm close_value] in *.

Ltac basic_goal_var_dec_simpl :=
  repeat match goal with
  | |- context[decide (?a = ?b)] =>
      destruct (decide (a = b)); subst;
      cbn [open_one open_tm open_value open_tm_atom_inst open_value_atom_inst
           open_tm_inst open_value_inst close_tm close_value];
      try (vm_compute; congruence)
  end.

Lemma basic_typing_fixfun_named Γ self arg sx T body :
  arg ∉ dom Γ ->
  self ∉ dom Γ ∪ {[arg]} ->
  <[self := sx →ₜ T]> (<[arg := sx]> Γ) ⊢ₑ body ⋮ T ->
  Γ ⊢ᵥ fixfun_named self arg sx T body ⋮ (sx →ₜ T).
Proof.
  intros HargΓ HselfΓ Hbody.
  unfold fixfun_named.
  eapply VT_Fix with (L := dom Γ ∪ fv_tm body ∪ {[arg; self]}).
  intros y Hy.
  change (<[y := sx]> Γ ⊢ᵥ open_value 0 (vfvar y)
      (close_value arg 0 (lam_named self (sx →ₜ T) body)) ⋮
    ((sx →ₜ T) →ₜ T)).
  eapply basic_typing_open_value with
    (Γ := <[y := sx]> Γ) (x := arg) (U := sx).
  - apply close_rm_fv_value.
  - apply value_has_type_insert_self.
  - assert (Hlam :
        <[arg := sx]> (<[y := sx]> Γ) ⊢ᵥ
          lam_named self (sx →ₜ T) body ⋮ ((sx →ₜ T) →ₜ T)).
    { eapply basic_typing_lam_named.
      - basic_type_fresh.
      - rewrite fixfun_body_env_commute by fast_set_solver!!.
        eapply basic_typing_weaken_insert_tm.
        + basic_type_fresh.
        + exact Hbody. }
    change (<[arg := sx]> (<[y := sx]> Γ) ⊢ᵥ
      open_value 0 (vfvar arg)
        (close_value arg 0 (lam_named self (sx →ₜ T) body)) ⋮
      ((sx →ₜ T) →ₜ T)).
    rewrite open_close_var_value by exact (typing_value_lc _ _ _ Hlam).
    exact Hlam.
Qed.

Lemma basic_typing_nondet_tm Γ e1 e2 T :
  Γ ⊢ₑ e1 ⋮ T ->
  Γ ⊢ₑ e2 ⋮ T ->
  Γ ⊢ₑ nondet_tm e1 e2 ⋮ T.
Proof.
  intros He1 He2.
  unfold nondet_tm.
  eapply TT_Let with (L := dom Γ ∪ fv_tm e1 ∪ fv_tm e2).
  - eapply TT_Op.
    + reflexivity.
    + apply VT_Const.
  - intros y Hy.
    cbn [open_one open_tm open_value open_tm_atom_inst open_value_atom_inst
         open_tm_inst open_value_inst tm_shift value_shift].
    crush_binders.
    eapply TT_Match.
    + apply value_has_type_insert_self.
    + rewrite (tm_shift_lc_id 0 e1) by exact (typing_tm_lc _ _ _ He1).
      change (<[y := (𝔹 : ty)]> Γ ⊢ₑ open_tm 0 (vfvar y) e1 ⋮ T).
      rewrite (open_rec_lc_tm e1) by exact (typing_tm_lc _ _ _ He1).
      eapply basic_typing_weaken_insert_tm.
      * basic_type_fresh.
      * exact He1.
    + rewrite (tm_shift_lc_id 0 e2) by exact (typing_tm_lc _ _ _ He2).
      change (<[y := (𝔹 : ty)]> Γ ⊢ₑ open_tm 0 (vfvar y) e2 ⋮ T).
      rewrite (open_rec_lc_tm e2) by exact (typing_tm_lc _ _ _ He2).
      eapply basic_typing_weaken_insert_tm.
      * basic_type_fresh.
      * exact He2.
Qed.

Ltac eapply_vt_lam_with_stales :=
  first
    [ let L := collect_stales tt in eapply VT_Lam with (L := L)
    | lazymatch goal with
      | |- ?Γ ⊢ᵥ ?v ⋮ _ => eapply VT_Lam with (L := stale Γ ∪ stale v)
      end ].

Ltac eapply_vt_fix_with_stales :=
  first
    [ let L := collect_stales tt in eapply VT_Fix with (L := L)
    | lazymatch goal with
      | |- ?Γ ⊢ᵥ ?v ⋮ _ => eapply VT_Fix with (L := stale Γ ∪ stale v)
      end ].

Ltac eapply_tt_let_with_stales :=
  first
    [ let L := collect_stales tt in eapply TT_Let with (L := L)
    | lazymatch goal with
      | |- ?Γ ⊢ₑ ?e ⋮ _ => eapply TT_Let with (L := stale Γ ∪ stale e)
      end ].

Ltac eapply_tt_tree_match_with_stales :=
  first
    [ let L := collect_stales tt in eapply TT_TreeMatch with (L := L)
    | lazymatch goal with
      | |- ?Γ ⊢ₑ ?e ⋮ _ => eapply TT_TreeMatch with (L := stale Γ ∪ stale e)
      end ].

Ltac eapply_tt_list_match_with_stales :=
  first
    [ let L := collect_stales tt in eapply TT_ListMatch with (L := L)
    | lazymatch goal with
      | |- ?Γ ⊢ₑ ?e ⋮ _ => eapply TT_ListMatch with (L := stale Γ ∪ stale e)
      end ].

Ltac basic_type :=
  basic_type_surface_norm;
  lazymatch goal with
  | |- ?Γ ⊢ᵥ lam_named ?x ?s ?e ⋮ (?s →ₜ ?T) =>
      eapply basic_typing_lam_named;
        [basic_type_fresh | basic_type]
  | |- ?Γ ⊢ₑ tret (lam_named ?x ?s ?e) ⋮ (?s →ₜ ?T) =>
      eapply TT_Ret;
      eapply basic_typing_lam_named;
        [basic_type_fresh | basic_type]
  | |- ?Γ ⊢ᵥ fixfun_named ?self ?arg ?sx ?T ?body ⋮ (?sx →ₜ ?T) =>
      eapply basic_typing_fixfun_named;
        [basic_type_fresh | basic_type_fresh | basic_type]
  | |- ?Γ ⊢ₑ tret (fixfun_named ?self ?arg ?sx ?T ?body) ⋮ (?sx →ₜ ?T) =>
      eapply TT_Ret;
      eapply basic_typing_fixfun_named;
        [basic_type_fresh | basic_type_fresh | basic_type]
  | |- ?Γ ⊢ₑ match_tree_named _ _ _ _ _ _ ⋮ _ =>
      unfold match_tree_named; basic_type
  | |- ?Γ ⊢ₑ match_list_named _ _ _ _ _ ⋮ _ =>
      unfold match_list_named; basic_type
  | |- ?Γ ⊢ₑ let_named ?x ?e1 ?e2 ⋮ ?T =>
      eapply basic_typing_let_named;
        [basic_type_fresh | basic_type | basic_type]
  | |- ?Γ ⊢ₑ nondet_tm ?e1 ?e2 ⋮ ?T =>
      eapply basic_typing_nondet_tm; [basic_type | basic_type]
	  | |- ?Γ ⊢ₑ tapp_tm ?ef ?vx ⋮ ?T =>
	      eapply basic_typing_tapp_tm; [basic_type | basic_type]
	  | |- ?Γ ⊢ₑ tlete ?ef (tapp (vbvar 0) ?vx) ⋮ ?T =>
	      change (Γ ⊢ₑ tapp_tm ef vx ⋮ T);
	      eapply basic_typing_tapp_tm; [basic_type | basic_type]
	  | _ =>
	      basic_type_norm;
      lazymatch goal with
  | |- ?Γ ⊢ᵥ vfvar _ ⋮ _ =>
      eapply VT_FVar; basic_lookup
  | |- ?Γ ⊢ᵥ vlam _ _ ⋮ _ =>
      eapply_vt_lam_with_stales; intros ? ?; basic_type
  | |- ?Γ ⊢ᵥ vfix _ _ ⋮ _ =>
      eapply_vt_fix_with_stales; intros ? ?; basic_type
  | |- ?Γ ⊢ᵥ vconst _ ⋮ _ =>
      eapply VT_Const

  | |- ?Γ ⊢ₑ tret _ ⋮ _ =>
      eapply TT_Ret; basic_type
  | |- ?Γ ⊢ₑ tlete _ _ ⋮ _ =>
      eapply_tt_let_with_stales; [basic_type | intros ? ?; basic_type]
  | |- ?Γ ⊢ₑ tprim _ _ ⋮ _ =>
      eapply TT_Op;
        [basic_solve_primop_type | basic_type]
  | |- ?Γ ⊢ₑ tbinop _ _ _ ⋮ _ =>
      eapply TT_BinOp;
        [basic_solve_binop_type | basic_type | basic_type]
  | |- ?Γ ⊢ₑ tapp _ _ ⋮ _ =>
      eapply TT_App; basic_type
  | |- ?Γ ⊢ₑ tmatch _ _ _ ⋮ _ =>
      eapply TT_Match; basic_type
  | |- ?Γ ⊢ₑ tnode _ _ _ ⋮ _ =>
      eapply TT_TreeNode; basic_type
  | |- ?Γ ⊢ₑ tmatchtree _ _ _ ⋮ _ =>
      eapply_tt_tree_match_with_stales;
        [basic_type | basic_type |
         intros ? ? ? ? ? ?; basic_type]
  | |- ?Γ ⊢ₑ tcons _ _ ⋮ _ =>
      eapply TT_ListCons; basic_type
  | |- ?Γ ⊢ₑ tmatchlist _ _ _ ⋮ _ =>
      eapply_tt_list_match_with_stales;
        [basic_type | basic_type |
         intros ? ? ? ?; basic_type]
	  | |- _ =>
	      basic_type_side
	      end
  end.

Ltac basic_check :=
  repeat progress basic_type_surface_norm;
  basic_type.

Ltac basic_infer :=
  eexists; basic_check.

(** ** Small regression examples *)

Section Examples.

  Lemma basic_infer_nat_const Γ n :
    Γ ⊢ₑ ret (vnat n) ⋮ ℕ.
  Proof. basic_check. Qed.

  Lemma basic_infer_var_app Γ (f x : atom) T1 T2 :
    Γ !! f = Some (T1 →ᵦ T2) ->
    Γ !! x = Some T1 ->
    Γ ⊢ₑ f @ x ⋮ T2.
  Proof.
    intros Hf Hx. basic_check.
  Qed.

  Lemma basic_infer_binop Γ (x y : atom) :
    Γ !! x = Some (ℕ : ty) ->
    Γ !! y = Some (ℕ : ty) ->
    Γ ⊢ₑ x ⟨ ≤ ⟩ y ⋮ 𝔹.
  Proof.
    intros Hx Hy. basic_check.
  Qed.

  Lemma basic_infer_tree_node Γ (n l r : atom) :
    Γ !! n = Some (ℕ : ty) ->
    Γ !! l = Some (Tree : ty) ->
    Γ !! r = Some (Tree : ty) ->
    Γ ⊢ₑ [| n, l, r |] ⋮ Tree.
  Proof.
    intros Hn Hl Hr. basic_check.
  Qed.

  Lemma basic_infer_list_cons Γ (h t : atom) :
    Γ !! h = Some (ℕ : ty) ->
    Γ !! t = Some (List : ty) ->
    Γ ⊢ₑ h ::ᵗ t ⋮ List.
  Proof.
    intros Hh Ht. basic_check.
  Qed.

End Examples.
