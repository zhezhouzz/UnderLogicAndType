(** * Lightweight automation for case-study programs *)

From ProofAutomation Require Export CaseTypes.
From CoreLang Require Export BasicTyping.
From CoreLang Require Import BasicTypingProps LocallyNamelessProps.
From ContextTypeLanguage Require Import WF.

Open Scope case_scope.

(** ** Core binary-operator builders *)

Definition bin_lt (a b : value) : tm := tbinop bop_lt a b.
Definition bin_le (a b : value) : tm := tbinop bop_le a b.
Definition bin_gt (a b : value) : tm := tbinop bop_gt a b.
Definition bin_ge (a b : value) : tm := tbinop bop_ge a b.
Definition bin_plus (a b : value) : tm := tbinop bop_plus a b.
Definition bin_minus (a b : value) : tm := tbinop bop_minus a b.
Definition bin_and (a b : value) : tm := tbinop bop_and a b.
Definition bin_or (a b : value) : tm := tbinop bop_or a b.

#[global] Hint Constructors value_has_type tm_has_type : case_basic.
#[global] Hint Constructors lc_value lc_tm : case_lc.
#[global] Hint Resolve
  basic_context_ty_ONat_empty
  basic_context_ty_UNat_empty
  basic_context_ty_OBool_empty
  basic_context_ty_UBool_empty
  basic_context_ty_OList_empty
  basic_context_ty_UList_empty
  : case_wf.

Ltac case_lc :=
  cbn [avar vbool vnat leaf_value nil_value vlist Ret let_named lam_named fix_named
       fixfun_named
       match_tree_named match_list_named if_named case_app call2_tm call3_tm
       cons_tm node_tm
       nondet_tm
       bin_lt bin_le bin_gt bin_ge bin_plus bin_minus bin_and bin_or] in *;
  eauto with case_lc core.

Ltac case_basic_type :=
  cbn [avar vbool vnat leaf_value nil_value vlist Ret let_named lam_named fix_named
       fixfun_named
       match_tree_named match_list_named if_named case_app call2_tm call3_tm
       cons_tm node_tm
       nondet_tm
       bin_lt bin_le bin_gt bin_ge bin_plus bin_minus bin_and bin_or] in *;
  eauto with case_basic core.

Ltac case_wf_type :=
  cbn [ONat UNat OBool UBool OTree UTree OList UList
       precise_const const_precise_ty precise_ty over_ty under_ty] in *;
  eauto with case_wf.

Ltac case_open_norm_all :=
  case_open_norm;
  cbn [open_value open_tm open_one open_value_inst open_tm_inst
       close_value close_tm close_one close_value_inst close_tm_inst] in *.

(** ** Sanity checks for the new tree/list constructors *)

Lemma case_basic_type_nil Γ :
  Γ ⊢ᵥ nil_value ⋮ List.
Proof. unfold nil_value. constructor. Qed.

Lemma case_basic_type_cons Γ n xs :
  Γ ⊢ₑ cons_tm (vnat n) (vlist xs) ⋮ List.
Proof.
  unfold vnat, vlist, cons_tm.
  econstructor; constructor.
Qed.

Lemma case_basic_type_leaf Γ :
  Γ ⊢ᵥ leaf_value ⋮ Tree.
Proof. unfold leaf_value. constructor. Qed.

Lemma case_basic_type_node Γ n l r :
  Γ ⊢ₑ node_tm (vnat n) (vconst (ctree l)) (vconst (ctree r)) ⋮ Tree.
Proof.
  unfold vnat, node_tm.
  econstructor; constructor.
Qed.
