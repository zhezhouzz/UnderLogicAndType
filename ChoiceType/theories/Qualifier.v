(** * ChoiceType.Qualifier

    Type qualifiers are the source-level refinement predicates used by
    choice types.  They remain shallow, locally-nameless predicates over a
    vector of values.  Logic-level atoms live separately in
    [ChoiceLogic.LogicQualifier]. *)

From ChoiceType Require Export Prelude.

(** ** Syntax *)

Inductive type_qualifier : Type :=
  (** Standard shallow-embedding qualifier (like UnderType).
      [vals] : the (possibly open) values the proposition mentions.
      [prop] : a closed Rocq proposition over the evaluated constants. *)
  | qual {n : nat} (vals : vec value n) (prop : vec constant n → Prop).

(** ** Locally-nameless infrastructure *)

Definition qual_open (k : nat) (s : value) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual vals prop => qual (vmap (open_value k s) vals) prop
  end.

Definition qual_close (x : atom) (k : nat) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual vals prop => qual (vmap (close_value x k) vals) prop
  end.

Definition qual_fv (q : type_qualifier) : aset :=
  match q with
  | qual vals _ => Vector.fold_right (fun v s => fv_value v ∪ s) vals ∅
  end.

Definition qual_subst_one (x : atom) (v : value) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual vals prop => qual (vmap (value_subst x v) vals) prop
  end.

Definition qual_subst (σ : Store) (q : type_qualifier) : type_qualifier :=
  match q with
  | qual vals prop => qual (vmap (value_subst_all σ) vals) prop
  end.

#[global] Instance open_qual_inst      : Open value type_qualifier := qual_open.
#[global] Instance close_qual_inst     : Close type_qualifier := qual_close.
#[global] Instance stale_qual_inst     : Stale type_qualifier := qual_fv.
#[global] Instance subst_qual_inst     : SubstV value type_qualifier := qual_subst_one.
#[global] Instance substM_qual_inst    : SubstM Store type_qualifier := qual_subst.
Arguments open_qual_inst /.
Arguments close_qual_inst /.
Arguments stale_qual_inst /.
Arguments subst_qual_inst /.
Arguments substM_qual_inst /.

Notation "q '^q^' x" := (qual_open 0 (vfvar x) q) (at level 20).
Notation "'{' x ':=' v '}q' q" := (qual_subst_one x v q)
  (at level 20, x constr, v constr, format "{ x := v }q  q").

(** ** Local closure *)

Inductive lc_qualifier : type_qualifier → Prop :=
  | LCQ_qual n vals prop :
      Vector.Forall lc_value vals →
      lc_qualifier (@qual n vals prop).

#[global] Instance lc_qual_inst : Lc type_qualifier := lc_qualifier.
Arguments lc_qual_inst /.
#[global] Hint Constructors lc_qualifier : core.

(** ** Conjunction of two shallow qualifiers *)

Definition qualifier_and (q1 q2 : type_qualifier) : type_qualifier :=
  match q1, q2 with
  | qual vals1 prop1, qual vals2 prop2 =>
      qual (vals1 +++ vals2) (fun v =>
        let '(v1, v2) := Vector.splitat _ v in prop1 v1 ∧ prop2 v2)
  end.

Notation "q1 '&q' q2" := (qualifier_and q1 q2) (at level 40).

(** ** Denotation helpers *)

Fixpoint eval_vals (σ : Store) {n} (vals : vec value n) : option (vec constant n) :=
  match vals with
  | [#]       => Some [#]
  | v ::: vs  =>
      match value_subst_all σ v with
      | vconst c =>
          match eval_vals σ vs with
          | Some cs => Some (c ::: cs)
          | None    => None
          end
      | _ => None
      end
  end.

Definition qual_interp (σ : Store) (q : type_qualifier) : Prop :=
  match q with
  | qual vals prop =>
      match eval_vals σ vals with
      | Some cs => prop cs
      | None    => False
      end
  end.

Definition qual_interp_cl (q : type_qualifier) (σ : Store) : Prop :=
  qual_interp σ q.

#[global] Instance denot_qual_inst : Denotation type_qualifier (Store → Prop) :=
  qual_interp_cl.
Arguments denot_qual_inst /.

(** Conversion to a logic qualifier is intentionally left abstract for now. *)
Parameter type_qualifier_to_logic : type_qualifier → logic_qualifier.

(** ** Standard notations from UnderType *)

Definition mk_q_eq (v1 v2 : value) : type_qualifier :=
  qual [# v1; v2] (fun v => v !!! 0%fin = v !!! 1%fin).

Notation "'b0:v=' v" := (mk_q_eq (vbvar 0) v)
  (at level 5, format "b0:v= v").
Notation "'b0:x=' x" := (mk_q_eq (vbvar 0) (vfvar x))
  (at level 5, format "b0:x= x").
Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").

Definition qual_top : type_qualifier := qual [#] (fun _ => True).
Definition qual_bot : type_qualifier := qual [#] (fun _ => False).
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

Lemma qual_interp_subst_compose (σ_X σ : Store) (q : type_qualifier) :
  store_compat σ_X σ →
  qual_interp σ (qual_subst σ_X q) ↔ qual_interp (σ_X ∪ σ) q.
Proof. Admitted.

Lemma qual_interp_and q1 q2 σ :
  qual_interp σ (q1 &q q2) ↔ qual_interp σ q1 ∧ qual_interp σ q2.
Proof. Admitted.
