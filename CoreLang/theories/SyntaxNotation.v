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
Bind Scope core_scope with bin_op.
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
Notation "'Tree'" := TTree : core_scope.
Notation "'List'" := TList : core_scope.
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
  | ctree _ => None
  | clist _ => None
  end.

Number Notation constant constant_of_uint constant_to_uint : core_scope.

Notation "'#' n" := (vbvar n)
  (at level 5, format "# n") : core_scope.

Notation "'leaf'" := (ctree tr_leaf) (only printing) : core_scope.
Notation "'nil'" := (clist []) (only printing) : core_scope.

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

Notation "'if' v 'then' et 'else' ef" := (tmatch v et ef)
  (at level 100, v at level 200, et at level 200, ef at level 200,
   format "'[v' if  v  then '/' et '/' else '/' ef ']'") : core_scope.

Notation "'Leaf'" := (vconst (ctree tr_leaf))
  (at level 20, format "Leaf") : core_scope.
Notation "'Nil'" := (vconst (clist []))
  (at level 20, format "Nil") : core_scope.
Notation "'Node' r l rr" := (tnode r l rr)
  (at level 30, r at level 30, l at level 30, rr at level 30,
   format "Node  r  l  rr") : core_scope.
Notation "'Cons' hd tl" := (tcons hd tl)
  (at level 30, hd at level 30, tl at level 30,
   format "Cons  hd  tl") : core_scope.
Notation "'matchTree' v 'with' 'Leaf' '=>' el '|' 'Node' '=>' en" :=
  (tmatchtree v el en)
  (at level 100, v at level 200, el at level 200, en at level 200,
   format "'[v' matchTree  v  with '/' Leaf  =>  el '/' |  Node  =>  en ']'")
  : core_scope.
Notation "'matchList' v 'with' 'Nil' '=>' en '|' 'Cons' '=>' ec" :=
  (tmatchlist v en ec)
  (at level 100, v at level 200, en at level 200, ec at level 200,
   format "'[v' matchList  v  with '/' Nil  =>  en '/' |  Cons  =>  ec ']'")
  : core_scope.

Notation "'iszero' v" := (tprim op_eq0 v)
  (at level 30, v at level 30, format "iszero  v") : core_scope.
Notation "'succ' v" := (tprim op_plus1 v)
  (at level 30, v at level 30, format "succ  v") : core_scope.
Notation "'pred' v" := (tprim op_minus1 v)
  (at level 30, v at level 30, format "pred  v") : core_scope.
Notation "'boolGen' v" := (tprim op_boolGen v)
  (at level 30, v at level 30, format "boolGen  v") : core_scope.
Notation "'natGen' v" := (tprim op_natGen v)
  (at level 30, v at level 30, format "natGen  v") : core_scope.

Notation "v1 '<#' v2" := (tbinop bop_lt v1 v2)
  (at level 40, left associativity, format "v1  <#  v2") : core_scope.
Notation "v1 '<=#' v2" := (tbinop bop_le v1 v2)
  (at level 40, left associativity, format "v1  <=#  v2") : core_scope.
Notation "v1 '>#' v2" := (tbinop bop_gt v1 v2)
  (at level 40, left associativity, format "v1  >#  v2") : core_scope.
Notation "v1 '>=#' v2" := (tbinop bop_ge v1 v2)
  (at level 40, left associativity, format "v1  >=#  v2") : core_scope.
Notation "v1 '+#' v2" := (tbinop bop_plus v1 v2)
  (at level 50, left associativity, format "v1  +#  v2") : core_scope.
Notation "v1 '-#' v2" := (tbinop bop_minus v1 v2)
  (at level 50, left associativity, format "v1  -#  v2") : core_scope.
Notation "v1 '&&#' v2" := (tbinop bop_and v1 v2)
  (at level 40, left associativity, format "v1  &&#  v2") : core_scope.
Notation "v1 '||#' v2" := (tbinop bop_or v1 v2)
  (at level 40, left associativity, format "v1  ||#  v2") : core_scope.
