(** * Case-study type aliases and predicate qualifiers *)

From Stdlib Require Import List.
From ProofAutomation Require Export CaseSyntax.
From ContextTypeLanguage Require Export Syntax WF.

Import ListNotations.

Open Scope cty_scope.

Definition base_ty_as_ty (b : base_ty) : ty := TBase b.
Coercion base_ty_as_ty : base_ty >-> ty.

Notation "T1 '→ᵦ' T2" := (TArrow T1 T2)
  (at level 99, right associativity,
   format "T1  →ᵦ  T2") : core_scope.

(** ** Readable de Bruijn aliases for type qualifiers *)

Definition vnu : value := vbvar 0.
Definition arg0 : value := vbvar 1.
Definition arg1 : value := vbvar 2.
Definition arg2 : value := vbvar 3.
Definition arg3 : value := vbvar 4.

Notation "'ν'" := vnu : cty_scope.

(** ** Common basic function types used by free helper functions *)

Definition nat_unary_fun_ty : ty :=
  ℕ →ᵦ ℕ.

Definition nat_binop_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ ℕ.

Definition nat_cmp_ty : ty :=
  ℕ →ᵦ ℕ →ᵦ 𝔹.

Definition bool_binop_ty : ty :=
  𝔹 →ᵦ 𝔹 →ᵦ 𝔹.

(** ** Qualifier constructors *)

Definition q_const_pred (v : value) (P : constant -> Prop) : type_qualifier :=
  tqual (lvar_value_keys v)
    (fun σ =>
       exists c,
         denote_lvar_value (lso_store σ) v = Some (vconst c) /\
         P c).

Definition q_nat_pred (v : value) (P : nat -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with cnat n => P n | _ => False end).

Definition q_bool_pred (v : value) (P : bool -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with cbool b => P b | _ => False end).

Definition q_list_pred (v : value) (P : list nat -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with clist xs => P xs | _ => False end).

Definition q_tree_pred (v : value) (P : tree -> Prop) : type_qualifier :=
  q_const_pred v
    (fun c => match c with ctree t => P t | _ => False end).

Definition q_true : type_qualifier := bool_qual true.
Definition q_false : type_qualifier := bool_qual false.

Definition q_nonneg (v : value) : type_qualifier :=
  q_nat_pred v (fun _ => True).

(** ** Type aliases *)

Definition ONat : context_ty := over_ty TNat qual_top.
Definition UNat : context_ty := under_ty TNat qual_top.
Definition OBool : context_ty := over_ty TBool qual_top.
Definition UBool : context_ty := under_ty TBool qual_top.
Definition OTree : context_ty := over_ty TTree qual_top.
Definition UTree : context_ty := under_ty TTree qual_top.
Definition OList : context_ty := over_ty TList qual_top.
Definition UList : context_ty := under_ty TList qual_top.

Definition precise_const (c : constant) : context_ty :=
  const_precise_ty c.

Notation "'O[' b ']'" := (over_ty b qual_top)
  (at level 0, b at level 200, format "O[ b ]") : cty_scope.
Notation "'U[' b ']'" := (under_ty b qual_top)
  (at level 0, b at level 200, format "U[ b ]") : cty_scope.

(** ** Small well-formedness facts for examples *)

Ltac case_type_wf_syntax :=
  unfold basic_context_ty, ONat, UNat, OBool, UBool, OTree, UTree, OList, UList,
    precise_const, const_precise_ty, precise_ty, over_ty, under_ty,
    q_true, q_false, bool_qual, mk_q_eq, qual_top;
  cbn [wf_context_ty_at erase_ty qual_vars qual_lvars lvar_value_keys];
  repeat split; try reflexivity;
  intros [k|x] Hx; cbn [lvar_wf_at] in *; try lia; set_solver.

Lemma basic_context_ty_ONat_empty :
  basic_context_ty ∅ ONat.
Proof. case_type_wf_syntax. Qed.

Lemma basic_context_ty_UNat_empty :
  basic_context_ty ∅ UNat.
Proof. case_type_wf_syntax. Qed.

Lemma basic_context_ty_OBool_empty :
  basic_context_ty ∅ OBool.
Proof. case_type_wf_syntax. Qed.

Lemma basic_context_ty_UBool_empty :
  basic_context_ty ∅ UBool.
Proof. case_type_wf_syntax. Qed.

Lemma basic_context_ty_OList_empty :
  basic_context_ty ∅ OList.
Proof. case_type_wf_syntax. Qed.

Lemma basic_context_ty_UList_empty :
  basic_context_ty ∅ UList.
Proof. case_type_wf_syntax. Qed.
