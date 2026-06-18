(** * CoreLang.SyntaxNotation

    Printing-oriented notation for the raw locally-nameless core language.
    These notations deliberately expose bound indices instead of inventing
    binder names. *)

From CoreLang Require Export Syntax.
From Stdlib Require Import Numbers.DecimalString.

Declare Scope core_scope.
Delimit Scope core_scope with core.
Bind Scope core_scope with base_ty.
Bind Scope core_scope with ty.
Bind Scope core_scope with constant.
Bind Scope core_scope with prim_op.
Bind Scope core_scope with value.
Bind Scope core_scope with tm.

Notation "'{' k '~>' v '}' e" := (open_value k v e)
  (at level 20, k constr, only printing,
   format "{ k ~> v } e") : core_scope.
Notation "'{' k '~>' v '}' e" := (open_tm k v e)
  (at level 20, k constr, only printing,
   format "{ k ~> v } e") : core_scope.
Notation "e '^^' x" := (open_value 0 (vfvar x) e)
  (at level 20, only printing) : core_scope.
Notation "e '^^' x" := (open_tm 0 (vfvar x) e)
  (at level 20, only printing) : core_scope.

Notation "'FV' '(' v ')'" := (fv_value v)
  (at level 10, only printing,
   format "FV ( v )") : core_scope.
Notation "'FV' '(' e ')'" := (fv_tm e)
  (at level 10, only printing,
   format "FV ( e )") : core_scope.

Notation store := (gmap atom value).
Notation tyctx := (gmap atom ty).

Notation "'𝔹'" := TBool : core_scope.
Notation "'ℕ'" := TNat : core_scope.
Notation "'𝕃'" := TList : core_scope.
Notation "T1 '→' T2" := (TArrow T1 T2)
  (at level 99, right associativity) : core_scope.
Notation "T1 ⇒ T2" := (TArrow T1 T2)
  (at level 60, right associativity, only parsing) : core_scope.

Notation "'true'" := (cbool Datatypes.true) (only printing) : core_scope.
Notation "'false'" := (cbool Datatypes.false) (only printing) : core_scope.

Definition constant_of_uint (n : Number.uint) : constant :=
  cnat (Nat.of_num_uint n).

Definition constant_to_uint (c : constant) : option Number.uint :=
  match c with
  | cnat n => Some (Nat.to_num_uint n)
  | cbool _ => None
  | clist _ => None
  end.

Number Notation constant constant_of_uint constant_to_uint : core_scope.

Notation "'#' n" := (vbvar n)
  (at level 5, format "# n") : core_scope.

Notation "'λ:' T ',' e" := (vlam T e)
  (at level 100, T at level 200, e at level 200,
   format "λ:  T ,  e") : core_scope.

Notation "'fix:' T ',' v" := (vfix T v)
  (at level 100, T at level 200, v at level 200,
   format "fix:  T ,  v") : core_scope.

Notation "'ret' v" := (tret v)
  (at level 20, v at level 20, format "ret  v") : core_scope.

Notation "'let:' e1 'in' e2" := (tlete e1 e2)
  (at level 100, e1 at level 200, e2 at level 200,
   right associativity,
   format "'[v' let:  e1  in  e2 ']'") : core_scope.

Notation "v1 · v2" := (tapp v1 v2)
  (at level 40, left associativity, format "v1  ·  v2") : core_scope.

Notation "'ifb' v 'then' et 'else' ef" := (tmatch v et ef)
  (at level 100, v at level 200, et at level 200, ef at level 200,
   format "'[v' ifb  v  then '/' et '/' else '/' ef ']'") : core_scope.

Notation "'iszero' v" := (tprim op_eq0 v)
  (at level 30, v at level 30, format "iszero  v") : core_scope.
Notation "'succ' v" := (tprim op_plus1 v)
  (at level 30, v at level 30, format "succ  v") : core_scope.
Notation "'pred' v" := (tprim op_minus1 v)
  (at level 30, v at level 30, format "pred  v") : core_scope.

Notation "'cons' v1 v2" := (tbinop op_cons v1%core v2%core) (at level 60) : core_scope.

Coercion cbool : bool >-> constant.
Coercion cnat : nat >-> constant.
Coercion clist : list >-> constant.
Coercion tret : value >-> tm.
