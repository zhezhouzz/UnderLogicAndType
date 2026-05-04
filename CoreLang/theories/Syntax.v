(** * CoreLang.Syntax

    Core language syntax (Fig. 1 of the paper): base types, basic types,
    primitive operations, values, and expressions in locally-nameless
    (LN) style.  Typeclass instances for [Open], [Close], [Stale],
    [Subst], [Lc], and [SubstM] are registered for every syntactic
    category so that all LN lemmas share a single notation. *)

From CoreLang Require Export Prelude.

(** ** Base and basic types *)

Inductive base_ty : Type :=
  | TBool | TNat.

Inductive ty : Type :=
  | TBase  (b : base_ty)
  | TArrow (s1 s2 : ty).

Coercion TBase : base_ty >-> ty.
Notation "s1 '→ₜ' s2" := (TArrow s1 s2) (at level 30, right associativity).

#[global] Instance base_ty_eqdec : EqDecision base_ty. Proof. solve_decision. Defined.
#[global] Instance ty_eqdec      : EqDecision ty.      Proof. solve_decision. Defined.

(** ** Constants and primitive operations *)

Inductive constant : Type :=
  | cbool (b : bool)
  | cnat  (n : nat).

#[global] Instance constant_eqdec : EqDecision constant. Proof. solve_decision. Defined.

Inductive prim_op : Type :=
  | op_eq0.  (** unary zero test on natural numbers *)

#[global] Instance prim_op_eqdec : EqDecision prim_op. Proof. solve_decision. Defined.

Definition base_ty_of_const (c : constant) : base_ty :=
  match c with cbool _ => TBool | cnat _ => TNat end.

(** ** Values and terms — mutual induction, locally nameless

    Binder conventions:
      [vlam s e]       : bvar 0 in e  = the λ-parameter x
      [vfix Tf vf]     : bvar 0 in vf = the ordinary argument x.
                         The opened [vf] is expected to be a function that
                         accepts the recursive self reference.  This
                         HATs-style encoding avoids giving [vfix] two
                         binders directly.
      [tlete e1 e2]    : bvar 0 in e2 = the let-bound variable
      [tmatch v et ef] : boolean case split; both branches bind no variables *)

Inductive value : Type :=
  | vconst (c : constant)
  | vfvar  (x : atom)
  | vbvar  (n : nat)
  | vlam   (s : ty)      (e : tm)
  | vfix   (Tf : ty)     (vf : value)

with tm : Type :=
  | tret    (v : value)
  | tlete   (e1 e2 : tm)
  | tprim   (op : prim_op) (arg : value)
  | tapp    (v1 v2 : value)
  | tmatch  (v : value) (etrue efalse : tm).

Scheme value_mut := Induction for value Sort Type
  with tm_mut    := Induction for tm    Sort Type.
Combined Scheme value_tm_mutind from value_mut, tm_mut.

(** EqDecision for the mutually-recursive [value]/[tm] types. *)

Fixpoint value_eqdec' (v1 v2 : value) : sumbool (v1 = v2) (v1 <> v2)
with tm_eqdec' (e1 e2 : tm) : sumbool (e1 = e2) (e1 <> e2).
Proof.
  - decide equality; try apply constant_eqdec; try apply ty_eqdec;
      try apply Nat.eq_dec; try solve_decision.
  - decide equality; try apply prim_op_eqdec; try solve_decision.
Defined.

#[global] Instance value_eqdec : EqDecision value := value_eqdec'.
#[global] Instance tm_eqdec : EqDecision tm := tm_eqdec'.

Coercion vconst : constant >-> value.
Coercion vfvar  : atom    >-> value.

(** ** Opening *)

Fixpoint open_value (k : nat) (s : value) (v : value) : value :=
  match v with
  | vconst _ => v
  | vfvar  _ => v
  | vbvar  n => if decide (k = n) then s else v
  | vlam s' e     => vlam s' (open_tm (S k) s e)
  | vfix Tf vf    => vfix Tf (open_value (S k) s vf)
  end
with open_tm (k : nat) (s : value) (e : tm) : tm :=
  match e with
  | tret v          => tret (open_value k s v)
  | tlete e1 e2     => tlete (open_tm k s e1) (open_tm (S k) s e2)
  | tprim op v      => tprim op (open_value k s v)
  | tapp v1 v2      => tapp (open_value k s v1) (open_value k s v2)
  | tmatch v et ef  =>
      tmatch (open_value k s v) (open_tm k s et) (open_tm k s ef)
  end.

#[global] Instance open_value_inst      : Open value value := open_value.
#[global] Instance open_tm_inst         : Open value tm    := open_tm.
#[global] Instance open_value_atom_inst : Open atom  value := fun k x => open_value k (vfvar x).
#[global] Instance open_tm_atom_inst    : Open atom  tm    := fun k x => open_tm    k (vfvar x).
Arguments open_value_inst /.
Arguments open_tm_inst /.
Arguments open_value_atom_inst /.
Arguments open_tm_atom_inst /.

(** [e ^^ x] works for both [value] and [tm], and for both [value] and [atom]
    second arguments via the four [Open] instances above. *)

(** ** Closing *)

Fixpoint close_value (x : atom) (k : nat) (v : value) : value :=
  match v with
  | vconst _ => v
  | vfvar  y => if decide (x = y) then vbvar k else v
  | vbvar  _ => v
  | vlam s' e     => vlam s' (close_tm x (S k) e)
  | vfix Tf vf    => vfix Tf (close_value x (S k) vf)
  end
with close_tm (x : atom) (k : nat) (e : tm) : tm :=
  match e with
  | tret v          => tret (close_value x k v)
  | tlete e1 e2     => tlete (close_tm x k e1) (close_tm x (S k) e2)
  | tprim op v      => tprim op (close_value x k v)
  | tapp v1 v2      => tapp (close_value x k v1) (close_value x k v2)
  | tmatch v et ef  =>
      tmatch (close_value x k v) (close_tm x k et) (close_tm x k ef)
  end.

#[global] Instance close_value_inst : Close value := close_value.
#[global] Instance close_tm_inst    : Close tm    := close_tm.
Arguments close_value_inst /.
Arguments close_tm_inst /.

(** ** Free variables *)

Fixpoint fv_value (v : value) : aset :=
  match v with
  | vconst _ => ∅
  | vfvar  x => {[ x ]}
  | vbvar  _ => ∅
  | vlam _ e     => fv_tm e
  | vfix _ vf    => fv_value vf
  end
with fv_tm (e : tm) : aset :=
  match e with
  | tret v          => fv_value v
  | tlete e1 e2     => fv_tm e1 ∪ fv_tm e2
  | tprim _ v       => fv_value v
  | tapp v1 v2      => fv_value v1 ∪ fv_value v2
  | tmatch v et ef  => fv_value v ∪ fv_tm et ∪ fv_tm ef
  end.

#[global] Instance stale_value_inst : Stale value := fv_value.
#[global] Instance stale_tm_inst    : Stale tm    := fv_tm.
Arguments stale_value_inst /.
Arguments stale_tm_inst /.

(** ** Single-variable substitution *)

Fixpoint value_subst (x : atom) (s : value) (v : value) : value :=
  match v with
  | vconst _ => v
  | vfvar  y => if decide (x = y) then s else v
  | vbvar  _ => v
  | vlam  ty e    => vlam ty  (tm_subst x s e)
  | vfix  Tf vf   => vfix Tf (value_subst x s vf)
  end
with tm_subst (x : atom) (s : value) (e : tm) : tm :=
  match e with
  | tret v          => tret (value_subst x s v)
  | tlete e1 e2     => tlete (tm_subst x s e1) (tm_subst x s e2)
  | tprim op v      => tprim op (value_subst x s v)
  | tapp v1 v2      => tapp (value_subst x s v1) (value_subst x s v2)
  | tmatch v et ef  =>
      tmatch (value_subst x s v) (tm_subst x s et) (tm_subst x s ef)
  end.

#[global] Instance subst_value_inst : SubstV value value := value_subst.
#[global] Instance subst_tm_inst    : SubstV value tm    := tm_subst.
Arguments subst_value_inst /.
Arguments subst_tm_inst /.

(** ** Multi-variable substitution (fold over a gmap)

    Correctness of the fold order: when [σ] maps variables to *closed*
    values, any folding order yields the same result, since no value in
    [σ] contains free variables that could be captured by another
    substitution step. *)
Definition value_subst_all (σ : gmap atom value) (v : value) : value :=
  map_fold (fun x vx acc => value_subst x vx acc) v σ.

Definition tm_subst_all (σ : gmap atom value) (e : tm) : tm :=
  map_fold (fun x vx acc => tm_subst x vx acc) e σ.

#[global] Instance substM_value_inst : SubstM (gmap atom value) value :=
  value_subst_all.
#[global] Instance substM_tm_inst : SubstM (gmap atom value) tm :=
  tm_subst_all.
Arguments substM_value_inst /.
Arguments substM_tm_inst /.

(** ** Local closure *)

Inductive lc_value : value → Prop :=
  | LC_const c : lc_value (vconst c)
  | LC_fvar  x : lc_value (vfvar x)
  | LC_lam s e (L : aset) :
      (∀ x, x ∉ L → lc_tm ({0 ~> (vfvar x)} e)) →
      lc_value (vlam s e)
  | LC_fix Tf vf (L : aset) :
      (∀ x, x ∉ L → lc_value ({0 ~> (vfvar x)} vf)) →
      lc_value (vfix Tf vf)

with lc_tm : tm → Prop :=
  | LC_ret v : lc_value v → lc_tm (tret v)
  | LC_lete e1 e2 (L : aset) :
      lc_tm e1 →
      (∀ x, x ∉ L → lc_tm ({0 ~> (vfvar x)} e2)) →
      lc_tm (tlete e1 e2)
  | LC_op op v :
      lc_value v →
      lc_tm (tprim op v)
  | LC_app v1 v2 :
      lc_value v1 → lc_value v2 →
      lc_tm (tapp v1 v2)
  | LC_match v et ef :
      lc_value v → lc_tm et → lc_tm ef →
      lc_tm (tmatch v et ef).

Scheme lc_value_mut  := Induction for lc_value  Sort Prop
  with lc_tm_mut     := Induction for lc_tm     Sort Prop.

Combined Scheme lc_mutind from lc_value_mut, lc_tm_mut.

#[global] Instance lc_value_inst : Lc value := lc_value.
#[global] Instance lc_tm_inst    : Lc tm    := lc_tm.
Arguments lc_value_inst /.
Arguments lc_tm_inst /.

#[global] Hint Constructors lc_value lc_tm : core.

(** ** Body *)

Definition body_tm (e : tm) : Prop :=
  ∃ L : aset, ∀ x : atom, x ∉ L → lc_tm ({0 ~> (vfvar x)} e).

Definition body_val (v : value) : Prop :=
  ∃ L : aset, ∀ x : atom, x ∉ L → lc_value ({0 ~> (vfvar x)} v).

(** ** Inhabited instance (required by UnderLogicAndType.Resource) *)
#[global] Instance value_inhabited : Inhabited value :=
  populate (vconst (cbool false)).

#[global] Instance corelang_value_sig : ValueSig value := {|
  valuesig_eqdec := value_eqdec;
  valuesig_inhabited := value_inhabited;
|}.
