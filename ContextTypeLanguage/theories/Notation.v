(** * ContextTypeLanguage.Notation

    Public syntax notation for the pure context-type language layer. *)

From CoreLang Require Export SyntaxNotation.
From ContextTypeLanguage Require Export WF.
From Stdlib Require Import Arith.Wf_nat.

Declare Scope context_scope.
Delimit Scope context_scope with ctx.
Bind Scope context_scope with context_ty.
Bind Scope context_scope with ctx.
Bind Scope context_scope with logic_var.
Bind Scope context_scope with lty_env.

Class Erase A B := erase : A -> B.
Class Lift A B := lift : A -> B.
Arguments erase {_ _ _} _.
Arguments lift {_ _ _} _.

#[global] Instance erase_context_ty : Erase context_ty ty := erase_ty.
#[global] Instance erase_ctx_inst : Erase ctx (gmap atom ty) := erase_ctx.

#[global] Instance lift_ty_inst : Lift ty context_ty := lift_ty.
#[global] Instance lift_ctx_inst : Lift (gmap atom ty) ctx := lift_ctx.

Notation "⌊ x ⌋" := (erase x)
  (at level 20, format "⌊ x ⌋").

Notation "⌈ x ⌉" := (lift x)
  (at level 20, format "⌈ x ⌉") : context_scope.

Notation "'#ₗ' k" := (LVBound k)
  (at level 5, format "#ₗ k") : context_scope.

Notation "'$ₗ' x" := (LVFree x)
  (at level 5, format "$ₗ x") : context_scope.

Notation "'↑ₗ' Σ" := (atom_env_to_lty_env Σ)
  (at level 20, format "↑ₗ Σ") : context_scope.

Module TypeLanguageNotationSmoke.
  Section Smoke.
    Variable τ : context_ty.
    Variable Γ : ctx.
    Variable T : ty.
    Variable Δ : gmap atom ty.
    Variable η : gmap nat atom.
    Variable e : tm.
    Variable Σ : lty_env.
    Variable x : atom.

    Example erase_ty_notation :
      ⌊τ⌋ = erase_ty τ := eq_refl.

    Example erase_ctx_notation :
      ⌊Γ⌋ = erase_ctx Γ := eq_refl.

    Example lift_ty_notation :
      (⌈T⌉)%ctx = lift_ty T := eq_refl.

    Example lift_ctx_notation :
      (⌈Δ⌉)%ctx = lift_ctx Δ := eq_refl.

    Example mopen_ty_notation :
      (η ⊙ τ)%ctx = open_cty_env η τ := eq_refl.

    Example mopen_lty_env_notation :
      (η ⊙ Σ)%ctx = lty_env_open η Σ := eq_refl.

    Example lvar_notation :
      (#ₗ 0, $ₗ x)%ctx = (LVBound 0, LVFree x) := eq_refl.

    Example atom_env_notation :
      (↑ₗ Δ)%ctx = atom_env_to_lty_env Δ := eq_refl.
  End Smoke.
End TypeLanguageNotationSmoke.

(** * ContextTypeLanguage.Notation

    Lightweight normalization helpers for the syntax/type-language layer. *)


Ltac mopen_norm :=
  rewrite ?mopen_insert_norm;
  type_open_env_syntax_norm.

Ltac type_lvars_norm :=
  repeat match goal with
  | |- context[into_lvars ?X] =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X
      | aset => change (into_lvars X) with (lvars_of_atoms X)
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X))
      | gmap logic_var ty => change (into_lvars X) with (dom X)
      end
  | H : context[into_lvars ?X] |- _ =>
      let T := type of X in
      lazymatch T with
      | lvset => change (into_lvars X) with X in H
      | aset => change (into_lvars X) with (lvars_of_atoms X) in H
      | gmap atom ty => change (into_lvars X) with (lvars_of_atoms (dom X)) in H
      | gmap logic_var ty => change (into_lvars X) with (dom X) in H
      end
  end.

Ltac type_env_norm :=
  type_open_env_syntax_norm;
  rewrite ?lvar_store_atom_dom_shift in *.

(** * ContextTypeLanguage.Notation

    Small context-type abbreviations used by the paper-facing typing layer. *)

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

(** Default well-founded orders used by context-type fixed points.  This is
    the HAT-style construction: each base type chooses a measure into [nat],
    and recursive calls are required to decrease under that measure. *)
Definition constant_measure_for_base (b : base_ty) (c : constant) : nat :=
  match b, c with
  | TNat, cnat n => n
  | TNat, cbool false => 0
  | TNat, cbool true => 1
  | TBool, cbool false => 0
  | TBool, cbool true => 1
  | TBool, cnat n => n
  end.

Definition constant_lt_for_base (b : base_ty) : constant -> constant -> Prop :=
  ltof _ (constant_measure_for_base b).

Notation " c1 '≺[' b ']' c2 " :=
  (constant_lt_for_base b c1 c2) (at level 20, b at next level).

Definition mk_q_lt_base (b : base_ty) (v1 v2 : value) : type_qualifier :=
  tqual (lvar_value_keys v1 ∪ lvar_value_keys v2)
    (fun σ =>
       exists c1 c2,
         denote_lvar_value (lso_store σ) v1 = Some (vconst c1) /\
         denote_lvar_value (lso_store σ) v2 = Some (vconst c2) /\
         c1 ≺[b] c2).

Definition over_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTOver b φ.

Definition under_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTUnder b φ.

Definition precise_ty (b : base_ty) (φ : type_qualifier) : context_ty :=
  CTInter (over_ty b φ) (under_ty b φ).

Definition primop_ty
    (arg_b : base_ty) (arg_φ : type_qualifier)
    (ret_b : base_ty) (ret_φ : type_qualifier) : context_ty :=
  CTArrow (over_ty arg_b arg_φ) (precise_ty ret_b ret_φ).

Definition fix_rec_call_ty
    (b : base_ty) (x : atom) (τx τ : context_ty) : context_ty :=
  CTArrow
    (CTInter τx (over_ty b (mk_q_lt_base b (vbvar 0) (vfvar x))))
    τ.

Definition bool_qual (b : bool) : type_qualifier :=
  mk_q_eq (vbvar 0) (vconst (cbool b)).

Definition bool_precise_ty (b : bool) : context_ty :=
  precise_ty TBool (bool_qual b).

Definition const_precise_ty (c : constant) : context_ty :=
  precise_ty (base_ty_of_const c) (mk_q_eq (vbvar 0) (vconst c)).

Notation "'b0:v=' v" := (mk_q_eq (vbvar 0) v)
  (at level 5, format "b0:v= v").
Notation "'b0:x=' x" := (mk_q_eq (vbvar 0) (vfvar x))
  (at level 5, format "b0:x= x").
Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").
Notation "'b0:x≺[' b ']' x" := (mk_q_lt_base b (vbvar 0) (vfvar x))
  (at level 5, b at next level, x constr, format "b0:x≺[ b ] x").
Notation "'prt' b φ" := (precise_ty b φ)
  (at level 20, b at next level, φ at next level, only printing).
