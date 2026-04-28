(** * CoreLang.BasicTyping

    Standard simple (basic) type system for the core language.
    This is the "erased" type system [⊢_basic] referenced by the
    choice-type erasure and lifting functions.

    Contexts are [gmap atom ty]; typing uses the [Typing] typeclass so
    that the notation [Γ ⊢ e ⋮ T] works for both values and terms. *)

From CoreLang Require Export Syntax.

(** ** Primitive-operation type signatures

    Each [prim_op] has a list of argument base types and a return base type.
    We postulate a total function; concrete definitions can be given later. *)

Parameter prim_op_type : prim_op → list base_ty * base_ty.

(** Well-formedness: the type signature is consistent with the paper's ops. *)
Parameter prim_op_type_wf :
  prim_op_type op_add = ([TNat; TNat], TNat) ∧
  prim_op_type op_sub = ([TNat; TNat], TNat) ∧
  prim_op_type op_mul = ([TNat; TNat], TNat) ∧
  prim_op_type op_eq  = ([TNat; TNat], TBool) ∧
  prim_op_type op_lt  = ([TNat; TNat], TBool) ∧
  prim_op_type op_le  = ([TNat; TNat], TBool) ∧
  prim_op_type op_and = ([TBool; TBool], TBool) ∧
  prim_op_type op_or  = ([TBool; TBool], TBool) ∧
  prim_op_type op_not = ([TBool], TBool) ∧
  prim_op_type op_nat_gen = ([], TNat) ∧
  prim_op_type op_int_gen = ([], TInt).

(** Constructor arities for the standard data types. *)
(** [(constructor_index, arg_base_types)].  We use a simple list;
    the [BasicTyping] rule for [tmatch] refers to this. *)
Parameter constructor_tys : base_ty → list (list base_ty).
(** Example: constructor_tys TBool = [[];[]] (false: 0 args, true: 0 args)
             constructor_tys TNat  = [[]; [TNat]]  (O: 0 args, S: 1 arg)  *)

(** ** Typing judgments *)

(** We define two mutually-inductive relations and expose them via
    the [Typing] typeclass with context type [gmap atom ty]. *)

Reserved Notation "Γ '⊢ᵥ' v '⋮' T" (at level 20, v constr, T constr).
Reserved Notation "Γ '⊢ₑ' e '⋮' T" (at level 20, e constr, T constr).

Inductive value_has_type : gmap atom ty → value → ty → Prop :=
  | VT_Const Γ c :
      Γ ⊢ᵥ (vconst c) ⋮ TBase (base_ty_of_const c)
  | VT_FVar Γ x T :
      Γ !! x = Some T →
      Γ ⊢ᵥ (vfvar x) ⋮ T
  | VT_Lam Γ s T e (L : aset) :
      (∀ x, x ∉ L → <[x := s]>Γ ⊢ₑ (e ^^ x) ⋮ T) →
      Γ ⊢ᵥ (vlam s e) ⋮ (s →ₜ T)
  | VT_Fix Γ sx T e (L : aset) :
      (** Body opened with x at bvar 0 and self (f : sx →ₜ T) at bvar 1. *)
      (∀ f x, f ∉ L → x ∉ L → f ≠ x →
        <[f := sx →ₜ T]>(<[x := sx]>Γ) ⊢ₑ ({0 ~> vfvar x} ({1 ~> vfvar f} e)) ⋮ T) →
      Γ ⊢ᵥ (vfix (sx →ₜ T) sx e) ⋮ (sx →ₜ T)

with tm_has_type : gmap atom ty → tm → ty → Prop :=
  | TT_Ret Γ v T :
      Γ ⊢ᵥ v ⋮ T →
      Γ ⊢ₑ (tret v) ⋮ T
  | TT_Let Γ T1 T2 e1 e2 (L : aset) :
      Γ ⊢ₑ e1 ⋮ T1 →
      (∀ x, x ∉ L → <[x := T1]>Γ ⊢ₑ (e2 ^^ x) ⋮ T2) →
      Γ ⊢ₑ (tlete e1 e2) ⋮ T2
  | TT_LetOp Γ op vs e_body arg_tys ret_b T (L : aset) :
      prim_op_type op = (arg_tys, ret_b) →
      Forall2 (fun v b => Γ ⊢ᵥ v ⋮ TBase b) vs arg_tys →
      (∀ x, x ∉ L → <[x := TBase ret_b]>Γ ⊢ₑ (e_body ^^ x) ⋮ T) →
      Γ ⊢ₑ (tletop op vs e_body) ⋮ T
  | TT_LetApp Γ s1 s2 T v1 v2 e (L : aset) :
      Γ ⊢ᵥ v1 ⋮ (s1 →ₜ s2) →
      Γ ⊢ᵥ v2 ⋮ s1 →
      (∀ x, x ∉ L → <[x := s2]>Γ ⊢ₑ (e ^^ x) ⋮ T) →
      Γ ⊢ₑ (tletapp v1 v2 e) ⋮ T
  | TT_Match Γ v T branches b :
      (** The discriminant [v] must have a base type. *)
      Γ ⊢ᵥ v ⋮ TBase b →
      length branches = length (constructor_tys b) →
      (** Each branch has the right number of arguments and types correctly. *)
      (∀ n body arg_tys,
         List.In ((n, body), arg_tys) (zip branches (constructor_tys b)) →
         length arg_tys = n ∧
         ∀ xs, length xs = n →
               Forall (fun x => x ∉ dom Γ) xs →
               NoDup xs →
               fold_left (fun ctx '(x, bt) => <[x := TBase bt]>ctx)
                         (zip xs arg_tys) Γ
                 ⊢ₑ fold_left (fun e x => {0 ~> vfvar x} e) xs body ⋮ T) →
      Γ ⊢ₑ (tmatch v branches) ⋮ T

where "Γ '⊢ᵥ' v '⋮' T" := (value_has_type Γ v T)
  and "Γ '⊢ₑ' e '⋮' T" := (tm_has_type Γ e T).

Scheme value_has_type_mut := Induction for value_has_type Sort Prop
  with tm_has_type_mut    := Induction for tm_has_type    Sort Prop.

#[global] Hint Constructors value_has_type tm_has_type : core.

(** Typeclass instances for uniform [⊢] notation. *)
#[global] Instance typing_value_inst : Typing (gmap atom ty) value ty :=
  value_has_type.
#[global] Instance typing_tm_inst : Typing (gmap atom ty) tm ty :=
  tm_has_type.
Arguments typing_value_inst /.
Arguments typing_tm_inst /.

(** ** Standard weakening and substitution lemmas (Admitted) *)

Lemma weakening_value Γ Γ' v T :
  Γ ⊢ᵥ v ⋮ T → Γ ⊆ Γ' → Γ' ⊢ᵥ v ⋮ T.
Proof. Admitted.

Lemma weakening_tm Γ Γ' e T :
  Γ ⊢ₑ e ⋮ T → Γ ⊆ Γ' → Γ' ⊢ₑ e ⋮ T.
Proof. Admitted.

Lemma subst_typing_value Γ x s v T vx :
  Γ ⊢ᵥ v ⋮ T → ∅ ⊢ᵥ vx ⋮ s → Γ !! x = Some s →
  delete x Γ ⊢ᵥ ({x := vx} v) ⋮ T.
Proof. Admitted.

Lemma subst_typing_tm Γ x s e T vx :
  Γ ⊢ₑ e ⋮ T → ∅ ⊢ᵥ vx ⋮ s → Γ !! x = Some s →
  delete x Γ ⊢ₑ ({x := vx} e) ⋮ T.
Proof. Admitted.

Lemma typing_value_lc Γ v T : Γ ⊢ᵥ v ⋮ T → lc_value v.
Proof. Admitted.

Lemma typing_tm_lc Γ e T : Γ ⊢ₑ e ⋮ T → lc_tm e.
Proof. Admitted.
