(** * CoreLang.SmallStep

    Call-by-value small-step operational semantics for the core language.
    We define:
      - [head_step e e'] : head reduction (no context)
      - [step e e']      : one-step reduction (under let-binding context)
      - [steps e e']     : multi-step reduction (reflexive-transitive closure)
      - [is_val e]       : whether [e] is a value (i.e., [tret v]) *)

From CoreLang Require Export Syntax BasicTyping.

(** ** Evaluation of primitive operations

    Primitive evaluation is relational because generators are intentionally
    nondeterministic.  The dummy boolean inputs for generators make all
    primitives unary, matching the rest of the ANF core language. *)

Inductive prim_step : prim_op → constant → constant → Prop :=
  | Prim_eq0 n :
      prim_step op_eq0 (cnat n) (cbool (n =? 0))
  | Prim_bool_gen_true b :
      prim_step op_bool_gen (cbool b) (cbool true)
  | Prim_bool_gen_false b :
      prim_step op_bool_gen (cbool b) (cbool false)
  | Prim_nat_gen b n :
      prim_step op_nat_gen (cbool b) (cnat n)
  | Prim_plus1 n :
      prim_step op_plus1 (cnat n) (cnat (S n))
  | Prim_minus1 n :
      prim_step op_minus1 (cnat n) (cnat (Nat.pred n)).

#[global] Hint Constructors prim_step : core.

(** ** Head reduction *)

(** [head_step e e'] is the *head* (redex) reduction.
    All rules operate on closed terms; the caller must ensure [lc_tm e]. *)
Inductive head_step : tm → tm → Prop :=

  (** [tlete (tret v) e  →  e[0 ↦ v]] *)
  | HS_Ret v e :
      lc_tm (tlete (tret v) e) →
      head_step (tlete (tret v) e) ({0 ~> v} e)

  (** [tprim op c  →  c']  when [prim_step op c c'] holds. *)
  | HS_Op op c c' :
      prim_step op c c' →
      lc_tm (tprim op (vconst c)) →
      head_step (tprim op (vconst c)) (tret (vconst c'))

  (** [tapp (vlam s body) v  →  body[0 ↦ v]] *)
  | HS_Beta s body v :
      lc_tm (tapp (vlam s body) v) →
      head_step (tapp (vlam s body) v)
                ({0 ~> v} body)

  (** [tapp (vfix Tf vf) v  →  tapp (vf[0 ↦ v]) self]
      The fix body is a value.  Once opened with the ordinary argument, it is
      expected to be a function that accepts the recursive self reference. *)
  | HS_Fix Tf vf v :
      let self := vfix Tf vf in
      lc_tm (tapp self v) →
      head_step (tapp self v)
                (tapp ({0 ~> v} vf) self)

  | HS_MatchTrue et ef :
      lc_tm (tmatch (vconst (cbool true)) et ef) →
      head_step (tmatch (vconst (cbool true)) et ef) et

  | HS_MatchFalse et ef :
      lc_tm (tmatch (vconst (cbool false)) et ef) →
      head_step (tmatch (vconst (cbool false)) et ef) ef.

#[global] Hint Constructors head_step : core.

(** ** Small-step reduction (congruence under let-binding context) *)

(** The only non-trivial evaluation context for our ANF language:
    [tlete □ e2] — we reduce the first component. *)
Inductive step : tm → tm → Prop :=
  | Step_head e e' :
      head_step e e' → step e e'
  | Step_let e1 e1' e2 :
      step e1 e1' →
      lc_tm (tlete e1 e2) →
      step (tlete e1 e2) (tlete e1' e2).

#[global] Hint Constructors step : core.

(** ** Multi-step reduction *)

Inductive steps : tm → tm → Prop :=
  | Steps_refl e :
      lc_tm e →
      steps e e
  | Steps_step e1 e2 e3 :
      step e1 e2 →
      steps e2 e3 →
      steps e1 e3.

Notation "e '→*' e'" := (steps e e') (at level 40).

#[global] Hint Constructors steps : core.

(** ** Value predicate *)

Definition is_val (e : tm) : Prop := ∃ v, e = tret v.

Lemma is_val_tret v : is_val (tret v).
Proof. exists v; reflexivity. Qed.

(** Values do not step. *)
Lemma val_no_step v e : step (tret v) e → False.
Proof. inversion 1; subst. inversion H0. Qed.

Lemma val_steps_self v e : tret v →* e → e = tret v.
Proof.
  intro H. inversion H; subst; [reflexivity|].
  exfalso. eapply val_no_step; eauto.
Qed.

(** ** Preservation (BasicTyping invariant — Admitted here, proved in Properties) *)

Lemma step_preserves_type Γ e e' T :
  Γ ⊢ₑ e ⋮ T → step e e' → Γ ⊢ₑ e' ⋮ T.
Proof. Admitted.

Lemma steps_preserves_type Γ e e' T :
  Γ ⊢ₑ e ⋮ T → e →* e' → Γ ⊢ₑ e' ⋮ T.
Proof.
  intros Hty Hsteps. induction Hsteps; [exact Hty|].
  eauto using step_preserves_type.
Qed.
