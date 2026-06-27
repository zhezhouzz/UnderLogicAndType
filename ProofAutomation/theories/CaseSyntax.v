(** * Case-study syntax builders

    The case-study files use these helpers as a paper-facing layer over the
    locally nameless core syntax.  They deliberately live outside [CoreLang]:
    the core notation stays printing-oriented, while examples can use named
    binders where readability matters. *)

From CoreLang Require Export Syntax SyntaxNotation Sugar LocallyNamelessExtra.

Declare Scope case_scope.
Delimit Scope case_scope with case.

Open Scope core_scope.

(** ** Value and term shorthands *)

Definition avar (x : atom) : value := vfvar x.
Definition vbool (b : bool) : value := vconst (cbool b).
Definition vnat (n : nat) : value := vconst (cnat n).
Definition leaf_value : value := vconst (ctree tr_leaf).
Definition nil_value : value := vconst (clist []).
Definition vlist (xs : list nat) : value := vconst (clist xs).

Coercion avar : atom >-> value.

Definition Ret (v : value) : tm := tret v.

Definition let_named (x : atom) (e1 e2 : tm) : tm :=
  tlete e1 (close_tm x 0 e2).

Definition lam_named (x : atom) (T : ty) (e : tm) : value :=
  vlam T (close_tm x 0 e).

Definition fix_named (x : atom) (T : ty) (vf : value) : value :=
  vfix T (close_value x 0 vf).

Definition fixfun_named
    (self arg : atom) (sx T : ty) (body : tm) : value :=
  let Tf := sx →ₜ T in
  vfix Tf
    (close_value arg 0
      (vlam Tf (close_tm self 0 body))).

(** Closing from the outermost binder downward matches the opening order:
    tree node_tm branches open root, then left, then right; list cons_tm branches
    open head, then tail. *)
Definition match_tree_named
    (v : value) (eleaf : tm)
    (root left right : atom) (enode : tm) : tm :=
  tmatchtree v eleaf
    (close_tm right 2 (close_tm left 1 (close_tm root 0 enode))).

Definition match_list_named
    (v : value) (enil : tm)
    (hd tl : atom) (econs : tm) : tm :=
  tmatchlist v enil
    (close_tm tl 1 (close_tm hd 0 econs)).

Definition if_named (v : value) (etrue efalse : tm) : tm :=
  tmatch v etrue efalse.

Definition case_app (f x : value) : tm := tapp f x.
Definition prim_app (op : prim_op) (v : value) : tm := tprim op v.
Definition call2_tm (f x y : value) : tm := tapp_tm (case_app f x) y.
Definition call3_tm (f x y z : value) : tm := tapp_tm (call2_tm f x y) z.
Definition cons_tm (hd tl : value) : tm := tcons hd tl.
Definition node_tm (root left right : value) : tm := tnode root left right.

Definition nondet_tm (e1 e2 : tm) : tm :=
  tlete (tprim op_boolGen (vbool false))
    (tmatch (vbvar 0) (tm_shift 0 e1) (tm_shift 0 e2)).

(** ** Case-study-only parsing notation *)

Notation "'ret' v" := (Ret v)
  (at level 20, v at level 20, format "ret  v") : case_scope.

Notation "'let' x ':=' e1 'in' e2" := (let_named x e1 e2)
  (at level 100, x constr, e1 at level 200, e2 at level 200,
   right associativity,
   format "'[v' let  x  :=  e1  in '/' e2 ']'") : case_scope.

Notation "'ƛ' x ':' T '=>' e" := (lam_named x T e)
  (at level 100, x at level 99, T at level 99, e at level 200,
   format "'[v' ƛ  x  :  T  => '/' e ']'") : case_scope.

Notation "'μ' x ':' T '=>' vf" := (fix_named x T vf)
  (at level 100, x at level 99, T at level 99, vf at level 200,
   format "'[v' μ  x  :  T  => '/' vf ']'") : case_scope.

Notation "'μ' self ',' arg ':' sx '~>' T '=>' body" :=
  (fixfun_named self arg sx T body)
  (at level 100, self at level 99, arg at level 99, sx at level 99,
   T at level 99, body at level 200,
   format "'[v' μ  self ,  arg  :  sx  ~>  T  => '/' body ']'")
  : case_scope.

Notation "f '@' x" := (case_app f x)
  (at level 40, left associativity, format "f  @  x") : case_scope.

Notation "op '·₁' v" := (prim_app op v)
  (at level 40, v at level 40,
   format "op  ·₁  v") : case_scope.

Notation "f '@@' '(' x ',' y ')'" := (call2_tm f x y)
  (at level 40, x at level 200, y at level 200) : case_scope.

Notation "f '@@@' '(' x ',' y ',' z ')'" := (call3_tm f x y z)
  (at level 40, x at level 200, y at level 200, z at level 200) : case_scope.

Notation "v1 '⟨' op '⟩' v2" := (tbinop op v1 v2)
  (at level 40, op at level 0, v2 at level 40,
   format "v1  ⟨ op ⟩  v2") : case_scope.
Notation "v1 '⟨' '<' '⟩' v2" := (tbinop bop_lt v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ < ⟩  v2") : case_scope.
Notation "v1 '⟨' '≤' '⟩' v2" := (tbinop bop_le v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ ≤ ⟩  v2") : case_scope.
Notation "v1 '⟨' '>' '⟩' v2" := (tbinop bop_gt v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ > ⟩  v2") : case_scope.
Notation "v1 '⟨' '≥' '⟩' v2" := (tbinop bop_ge v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ ≥ ⟩  v2") : case_scope.
Notation "v1 '⟨' '+' '⟩' v2" := (tbinop bop_plus v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ + ⟩  v2") : case_scope.
Notation "v1 '⟨' '-' '⟩' v2" := (tbinop bop_minus v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ - ⟩  v2") : case_scope.
Notation "v1 '⟨' '&&' '⟩' v2" := (tbinop bop_and v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ && ⟩  v2") : case_scope.
Notation "v1 '⟨' '||' '⟩' v2" := (tbinop bop_or v1 v2)
  (at level 40, v2 at level 40,
   format "v1  ⟨ || ⟩  v2") : case_scope.

Notation "hd '::ᵗ' tl" := (cons_tm hd tl)
  (at level 60, right associativity, format "hd  ::ᵗ  tl") : case_scope.

Notation "'[|' r ',' l ',' rr '|]'" := (node_tm r l rr)
  (at level 0, r at level 200, l at level 200, rr at level 200,
   format "[| r ,  l ,  rr |]") : case_scope.

Notation "'if' v 'then' et 'else' ef" := (if_named v et ef)
  (at level 100, v at level 200, et at level 200, ef at level 200,
   format "'[v' if  v  then '/' et '/' else '/' ef ']'") : case_scope.

Notation "e1 '⊕ₙ' e2" := (nondet_tm e1 e2)
  (at level 85, right associativity,
   format "'[v' e1  ⊕ₙ '/' e2 ']'") : case_scope.

Notation "'matchTree' '(' v ';' 'Leaf' '=>' el ';' 'Node' '(' root ',' left ',' right ')' '=>' en ')'" :=
  (match_tree_named v el root left right en)
  (at level 100, v at level 99, el at level 99,
   root at level 99, left at level 99, right at level 99, en at level 99)
  : case_scope.

Notation "'matchList' '(' v ';' 'Nil' '=>' en ';' 'Cons' '(' hd ',' tl ')' '=>' ec ')'" :=
  (match_list_named v en hd tl ec)
  (at level 100, v at level 99, en at level 99,
   hd at level 99, tl at level 99, ec at level 99)
  : case_scope.

Ltac case_open_norm :=
  cbn [let_named lam_named fix_named fixfun_named match_tree_named match_list_named
       if_named case_app prim_app call2_tm call3_tm cons_tm node_tm nondet_tm
       Ret avar vbool vnat leaf_value nil_value vlist
       open_tree_node_branch open_tree_node_branch_value
       open_list_cons_branch open_list_cons_branch_value].
