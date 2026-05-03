(** * ChoiceType.Qualifier

    Type qualifiers are shallow Rocq predicates over stores.  Their syntax is
    shared with logic qualifiers through [ChoicePrelude.Qualifier]; this file
    specializes the generic qualifier result object to another store. *)

From ChoiceType Require Export Prelude.
From ChoicePrelude Require Import Qualifier.

(** ** Syntax *)

Definition type_qualifier_of {V : Type} `{ValueSig V} : Type :=
  qualifier (V := V) (A := gmap atom V).

Definition type_qualifier : Type := type_qualifier_of (V := value).

Definition tqual {V : Type} `{ValueSig V}
    (B : gset nat) (d : aset)
    (prop : gmap nat V → gmap atom V → gmap atom V → Prop) :
    type_qualifier_of (V := V) :=
  qual B d prop.

(** ** Locally-nameless infrastructure *)

Definition qual_open {V : Type} `{ValueSig V}
    (k : nat) (x : atom) (q : type_qualifier_of (V := V)) : type_qualifier_of (V := V) :=
  qual_open_atom k x q.

Definition qual_open_with_value (k : nat) (v : value) (q : type_qualifier) :
    type_qualifier :=
  qual_open_value k v q.

Definition qual_fv {V : Type} `{ValueSig V} (q : type_qualifier_of (V := V)) : aset :=
  qual_dom q.

Definition qual_subst_one (x : atom) (v : value) (q : type_qualifier) : type_qualifier :=
  qual_subst_value x v q.

Definition qual_subst (σ : gmap atom value) (q : type_qualifier) : type_qualifier :=
  qual_subst_map σ q.

#[global] Instance open_qual_inst      : Open value type_qualifier := qual_open_with_value.
#[global] Instance open_qual_atom_inst : Open atom type_qualifier := qual_open.
#[global] Instance stale_qual_inst     : Stale type_qualifier := qual_fv.
#[global] Instance subst_qual_inst     : SubstV value type_qualifier := qual_subst_one.
#[global] Instance substM_qual_inst    : SubstM (gmap atom value) type_qualifier := qual_subst.
Arguments open_qual_inst /.
Arguments open_qual_atom_inst /.
Arguments stale_qual_inst /.
Arguments subst_qual_inst /.
Arguments substM_qual_inst /.

Notation "q '^q^' x" := (qual_open 0 x q) (at level 20).
Notation "'{' x ':=' v '}q' q" := (qual_subst_one x v q)
  (at level 20, x constr, v constr, format "{ x := v }q  q").

(** ** Local closure *)

Definition lc_qualifier (q : type_qualifier) : Prop :=
  qual_bvars q = ∅.

#[global] Instance lc_qual_inst : Lc type_qualifier := lc_qualifier.
Arguments lc_qual_inst /.

(** ** Conjunction of two shallow qualifiers *)

Definition qualifier_and (q1 q2 : type_qualifier) : type_qualifier :=
  match q1, q2 with
  | qual B1 d1 prop1, qual B2 d2 prop2 =>
      qual (B1 ∪ B2) (d1 ∪ d2) (fun β σ ρ => prop1 β σ ρ ∧ prop2 β σ ρ)
  end.

Notation "q1 '&q' q2" := (qualifier_and q1 q2) (at level 40).

(** ** Denotation helpers *)

Definition qual_interp_full
    (β : gmap nat value) (σ ρ : gmap atom value) (q : type_qualifier) : Prop :=
  match q with
  | qual B d prop =>
      prop (map_restrict value β B) (store_restrict σ d) (store_restrict ρ d)
  end.

Definition qual_interp (σ : gmap atom value) (q : type_qualifier) : Prop :=
  qual_interp_full ∅ σ σ q.

Definition qual_interp_cl (q : type_qualifier) (σ : gmap atom value) : Prop :=
  qual_interp σ q.

#[global] Instance denot_qual_inst : Denotation type_qualifier (gmap atom value → Prop) :=
  qual_interp_cl.
Arguments denot_qual_inst /.

(** Conversion to a logic qualifier is intentionally left abstract for now. *)
Parameter type_qualifier_to_logic : type_qualifier → logic_qualifier.

(** ** Standard notations from UnderType *)

Fixpoint bv_value (v : value) : gset nat :=
  match v with
  | vconst _ => ∅
  | vfvar _ => ∅
  | vbvar k => {[k]}
  | vlam _ e => bv_tm e
  | vfix _ vf => bv_value vf
  end
with bv_tm (e : tm) : gset nat :=
  match e with
  | tret v => bv_value v
  | tlete e1 e2 => bv_tm e1 ∪ bv_tm e2
  | tprim _ v => bv_value v
  | tapp v1 v2 => bv_value v1 ∪ bv_value v2
  | tmatch v et ef => bv_value v ∪ bv_tm et ∪ bv_tm ef
  end.

Definition denote_value (β : gmap nat value) (σ : gmap atom value) (v : value) : option value :=
  match v with
  | vbvar k => β !! k
  | vfvar x => σ !! x
  | vconst c => Some (vconst c)
  | _ => Some v
  end.

Definition mk_q_eq (v1 v2 : value) : type_qualifier :=
  qual (bv_value v1 ∪ bv_value v2) (fv_value v1 ∪ fv_value v2)
    (fun β σ _ => denote_value β σ v1 = denote_value β σ v2).

Notation "'b0:v=' v" := (mk_q_eq (vbvar 0) v)
  (at level 5, format "b0:v= v").
Notation "'b0:x=' x" := (mk_q_eq (vbvar 0) (vfvar x))
  (at level 5, format "b0:x= x").
Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").

Definition qual_top : type_qualifier := qual ∅ ∅ (fun _ _ _ => True).
Definition qual_bot : type_qualifier := qual ∅ ∅ (fun _ _ _ => False).
Notation "⊤q" := qual_top.
Notation "⊥q" := qual_bot.

(** ** Key LN and substitution lemmas (Admitted) *)

Lemma qual_subst_open k s σ (q : type_qualifier) :
  subst_map σ ({k ~> s} q) = {k ~> subst_map σ s} (subst_map σ q).
Proof. Admitted.

Lemma qual_subst_fresh x v (q : type_qualifier) :
  x # q → {x := v}q q = q.
Proof. Admitted.

Lemma qual_subst_intro x v (q : type_qualifier) :
  x # q → lc_value v → {x := v}q (q ^q^ x) = {0 ~> v} q.
Proof. Admitted.

Lemma qual_interp_subst_compose (σ_X σ : gmap atom value) (q : type_qualifier) :
  store_compat σ_X σ →
  qual_interp σ (qual_subst σ_X q) ↔ qual_interp (σ_X ∪ σ) q.
Proof. Admitted.

Lemma qual_interp_and q1 q2 σ :
  qual_interp σ (q1 &q q2) ↔ qual_interp σ q1 ∧ qual_interp σ q2.
Proof. Admitted.
