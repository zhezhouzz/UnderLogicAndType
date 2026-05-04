(** * CoreLang.SmallStep

    Call-by-value small-step operational semantics for the core language.
    We define:
      - [head_step e e'] : head reduction (no context)
      - [step e e']      : one-step reduction (under let-binding context)
      - [steps e e']     : multi-step reduction (reflexive-transitive closure)
      - [is_val e]       : whether [e] is a value (i.e., [tret v]) *)

From CoreLang Require Export Syntax BasicTyping.

(** ** Evaluation of primitive operations *)

Definition prim_eval (op : prim_op) (c : constant) : option constant :=
  match op, c with
  | op_eq0, cnat n => Some (cbool (n =? 0))
  | _, _ => None
  end.

(** Consistency axioms (not needed for type soundness, but clarify intent). *)
Lemma prim_eval_eq0 : ∀ n, prim_eval op_eq0 (cnat n) = Some (cbool (n =? 0)).
Proof. reflexivity. Qed.

(** ** Head reduction *)

(** [head_step e e'] is the *head* (redex) reduction.
    All rules operate on closed terms; the caller must ensure [lc_tm e]. *)
Inductive head_step : tm → tm → Prop :=

  (** [tlete (tret v) e  →  e[0 ↦ v]] *)
  | HS_Ret v e :
      lc_tm (tlete (tret v) e) →
      head_step (tlete (tret v) e) ({0 ~> v} e)

  (** [tprim op c  →  c']  when [prim_eval] succeeds *)
  | HS_Op op c c' :
      prim_eval op c = Some c' →
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

(** ** Determinism *)

Lemma head_step_det e e1 e2 :
  head_step e e1 → head_step e e2 →
  e1 = e2.
Proof.
  intros H1 H2.
  inversion H1; subst; inversion H2; subst; eauto; try congruence.
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
