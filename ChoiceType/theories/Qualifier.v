(** * ChoiceType.Qualifier

    Qualifiers [φ] are the atomic propositions of Choice Logic.
    We use a *shallow embedding* with length-indexed vectors (following
    UnderType/Qualifier.v), extended with two new constructors:
      [QExpr e ν] — captures the expression-denotation atom ⟦e⟧_ν
      [QProd q1 q2] — captures the resource-product compatibility atom φ×φ

    The [qualifier] type serves as the type parameter [A] in
    [ChoiceLogic.Formula A].  We provide:
      [qual_interp  : qualifier → SubstT → Prop]  ([interp]      in ChoiceLogic)
      [qual_subst   : SubstT → qualifier → qualifier] ([subst_atom] in ChoiceLogic)

    All locally-nameless operations ([open], [close], [subst_one], etc.)
    act only on the [vals] vector and the [tm] inside [QExpr]; the
    shallow [prop] and result atom [ν] in [QExpr] are left untouched. *)

From ChoiceType Require Export Prelude.

(** ** Syntax *)

Inductive qualifier : Type :=
  (** Standard shallow-embedding qualifier (like UnderType).
      [vals] : the (possibly open) values the proposition mentions.
      [prop] : a closed Rocq proposition over the evaluated constants. *)
  | qual {n : nat} (vals : vec value n) (prop : vec constant n → Prop)

  (** Expression-denotation atom.
      [interp (QExpr e ν) σ]  ≝  ∃ v, (σ(e) →* tret v) ∧ σ !! ν = Some v
      Intuitively: "e evaluates to the value bound to ν in σ". *)
  | QExpr (e : tm) (result : atom)

  (** Resource-product atom (compatibility).
      [interp (QProd q1 q2) σ]  ≝  ∃ σ1 σ2, σ1 ∪ σ2 = σ ∧ store_compat σ1 σ2
                                             ∧ interp q1 σ1 ∧ interp q2 σ2 *)
  | QProd (q1 q2 : qualifier).

(** ** Locally-nameless infrastructure *)

(** Opening acts on [vals] and the expression [e] in [QExpr]. *)
Fixpoint qual_open (k : nat) (s : value) (q : qualifier) : qualifier :=
  match q with
  | qual vals prop => qual (vmap (open_value k s) vals) prop
  | QExpr e ν     => QExpr (open_tm k s e) ν
  | QProd q1 q2   => QProd (qual_open k s q1) (qual_open k s q2)
  end.

(** Closing acts symmetrically. *)
Fixpoint qual_close (x : atom) (k : nat) (q : qualifier) : qualifier :=
  match q with
  | qual vals prop => qual (vmap (close_value x k) vals) prop
  | QExpr e ν     => QExpr (close_tm x k e) ν
  | QProd q1 q2   => QProd (qual_close x k q1) (qual_close x k q2)
  end.

(** Free variables. *)
Fixpoint qual_fv (q : qualifier) : aset :=
  match q with
  | qual vals _ => Vector.fold_right (fun v s => fv_value v ∪ s) vals ∅
  | QExpr e ν  => fv_tm e ∪ {[ ν ]}
  | QProd q1 q2 => qual_fv q1 ∪ qual_fv q2
  end.

(** Single-variable substitution. *)
Fixpoint qual_subst_one (x : atom) (v : value) (q : qualifier) : qualifier :=
  match q with
  | qual vals prop => qual (vmap (value_subst x v) vals) prop
  | QExpr e ν     => QExpr (tm_subst x v e) ν
  | QProd q1 q2   => QProd (qual_subst_one x v q1) (qual_subst_one x v q2)
  end.

(** Multi-variable substitution (the [subst_atom] parameter of ChoiceLogic). *)
Fixpoint qual_subst (σ : SubstT) (q : qualifier) : qualifier :=
  match q with
  | qual vals prop => qual (vmap (value_subst_all σ) vals) prop
  | QExpr e ν     => QExpr (tm_subst_all σ e) ν
  | QProd q1 q2   => QProd (qual_subst σ q1) (qual_subst σ q2)
  end.

(** Typeclass instances. *)
#[global] Instance open_qual_inst     : Open value qualifier  := qual_open.
#[global] Instance close_qual_inst    : Close qualifier       := qual_close.
#[global] Instance stale_qual_inst    : Stale qualifier       := qual_fv.
#[global] Instance subst_qual_inst    : SubstV value qualifier := qual_subst_one.
#[global] Instance substM_qual_inst   : SubstM SubstT qualifier := qual_subst.
Arguments open_qual_inst /.
Arguments close_qual_inst /.
Arguments stale_qual_inst /.
Arguments subst_qual_inst /.
Arguments substM_qual_inst /.

(** Notation mirrors UnderType's [^q^] and [{x:=v}q]. *)
Notation "q '^q^' x" := (qual_open 0 (vfvar x) q) (at level 20).
Notation "'{' x ':=' v '}q' q" := (qual_subst_one x v q)
  (at level 20, x constr, v constr, format "{ x := v }q  q").

(** ** Local closure *)

Inductive lc_qualifier : qualifier → Prop :=
  | LCQ_qual n vals prop :
      Vector.Forall lc_value vals →
      lc_qualifier (@qual n vals prop)
  | LCQ_expr e ν :
      lc_tm e →
      lc_qualifier (QExpr e ν)
  | LCQ_prod q1 q2 :
      lc_qualifier q1 → lc_qualifier q2 →
      lc_qualifier (QProd q1 q2).

#[global] Instance lc_qual_inst : Lc qualifier := lc_qualifier.
Arguments lc_qual_inst /.
#[global] Hint Constructors lc_qualifier : core.

(** ** Conjunction of two [qual]-style qualifiers (like UnderType). *)

Definition qualifier_and (q1 q2 : qualifier) : qualifier :=
  match q1, q2 with
  | qual vals1 prop1, qual vals2 prop2 =>
      qual (vals1 +++ vals2) (fun v =>
        let '(v1, v2) := Vector.splitat _ v in prop1 v1 ∧ prop2 v2)
  | _, _ => QProd q1 q2  (** Fallback to QProd for non-qual constructors. *)
  end.

Notation "q1 '&q' q2" := (qualifier_and q1 q2) (at level 40).

(** ** Denotation helpers *)

(** Evaluate a vector of values under substitution [σ] to constants.
    Returns [None] if any value does not reduce to a constant after
    applying [σ] (i.e., if it's a function or an unresolved free var). *)
Fixpoint eval_vals (σ : SubstT) {n} (vals : vec value n) : option (vec constant n) :=
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

(** ** Interpretation function ([interp] in ChoiceLogic)

    [qual_interp q σ] : the qualifier [q] holds when evaluated at
    substitution [σ]. *)
Fixpoint qual_interp (σ : SubstT) (q : qualifier) : Prop :=
  match q with
  | qual vals prop =>
      match eval_vals σ vals with
      | Some cs => prop cs
      | None    => False
      end
  | QExpr e ν =>
      ∃ v, (tm_subst_all σ e) →* tret v ∧ σ !! ν = Some v
  | QProd q1 q2 =>
      ∃ σ1 σ2,
        store_compat σ1 σ2 ∧ σ1 ∪ σ2 = σ ∧
        qual_interp σ1 q1 ∧ qual_interp σ2 q2
  end.

(** Flip argument order for convenience. *)
Definition qual_interp_cl (q : qualifier) (σ : SubstT) : Prop :=
  qual_interp σ q.

(** Wrap as a World for the [interp : A → WorldT] parameter of satisfies.
    The world_dom field carries no semantic weight for res_le; ∅ is a safe placeholder. *)
Definition qual_interp_world (q : qualifier) : WorldT :=
  {| world_dom := ∅; world_stores := qual_interp_cl q |}.

(** ** Denotation typeclass instance

    [⟦q⟧] : [SubstT → Prop] — the characteristic function of the
    set of substitutions satisfying [q] as a closed qualifier. *)
#[global] Instance denot_qual_inst : Denotation qualifier (SubstT → Prop) :=
  qual_interp_cl.
Arguments denot_qual_inst /.

(** ** Standard notations from UnderType *)

Definition mk_q_eq (v1 v2 : value) : qualifier :=
  qual [# v1; v2] (fun v => v !!! 0%fin = v !!! 1%fin).

Notation "'b0:v=' v" := (mk_q_eq (vbvar 0) v)
  (at level 5, format "b0:v= v").
Notation "'b0:x=' x" := (mk_q_eq (vbvar 0) (vfvar x))
  (at level 5, format "b0:x= x").
Notation "'b0:c=' c" := (mk_q_eq (vbvar 0) (vconst c))
  (at level 5, format "b0:c= c").

Definition qual_top : qualifier := qual [#] (fun _ => True).
Definition qual_bot : qualifier := qual [#] (fun _ => False).
Notation "⊤q" := qual_top.
Notation "⊥q" := qual_bot.

(** ** Key LN and substitution lemmas (Admitted) *)

Lemma qual_subst_open k s σ (q : qualifier) :
  subst_map σ ({k ~> s} q) = {k ~> subst_map σ s} (subst_map σ q).
Proof. Admitted.

Lemma qual_subst_fresh x v (q : qualifier) :
  x # q → {x := v}q q = q.
Proof. Admitted.

Lemma qual_subst_intro x v (q : qualifier) :
  x # q → lc_value v → {x := v}q (q ^q^ x) = {0 ~> v} q.
Proof. Admitted.

Lemma qual_interp_subst_compose (σ_X σ : SubstT) (q : qualifier) :
  store_compat σ_X σ →
  qual_interp σ (qual_subst σ_X q) ↔ qual_interp (σ_X ∪ σ) q.
Proof. Admitted.

Lemma qual_interp_and q1 q2 σ :
  qual_interp σ (q1 &q q2) ↔ qual_interp σ q1 ∧ qual_interp σ q2.
Proof. Admitted.
