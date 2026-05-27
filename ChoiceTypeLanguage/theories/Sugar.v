(** * ChoiceTypeLanguage.Sugar

    Small type-level abbreviations used by the paper-facing typing layer. *)

From CoreLang Require Import Syntax.
From ChoiceTypeLanguage Require Export Interface.

Fixpoint lvar_value_keys (v : value) : lvset :=
  match v with
  | vconst _ => ∅
  | vfvar x => {[LVFree x]}
  | vbvar k => {[LVBound k]}
  | vlam _ e => tm_lvars e
  | vfix _ vf => lvar_value_keys vf
  end.

Definition denote_lvar_value (σ : LStore (V := value)) (v : value) : option value :=
  match v with
  | vbvar k => (σ : gmap logic_var value) !! LVBound k
  | vfvar x => (σ : gmap logic_var value) !! LVFree x
  | vconst c => Some (vconst c)
  | vlam T e => Some (vlam T e)
  | vfix T vf => Some (vfix T vf)
  end.

Definition mk_q_eq (v1 v2 : value) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ => denote_lvar_value (lso_store σ) v1 =
              denote_lvar_value (lso_store σ) v2).

Definition over_ty (b : base_ty) (φ : type_qualifier) : choice_ty :=
  CTOver b φ.

Definition under_ty (b : base_ty) (φ : type_qualifier) : choice_ty :=
  CTUnder b φ.

Definition precise_ty (b : base_ty) (φ : type_qualifier) : choice_ty :=
  CTInter (over_ty b φ) (under_ty b φ).

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

Notation "'b0:v=' v" := (mk_q_eq (vbvar 0) v)
  (at level 5, format "b0:v= v").
Notation "'b0:x=' x" := (mk_q_eq (vbvar 0) (vfvar x))
  (at level 5, format "b0:x= x").
Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").
Notation "'prt' b φ" := (precise_ty b φ)
  (at level 20, b at next level, φ at next level, only printing).
