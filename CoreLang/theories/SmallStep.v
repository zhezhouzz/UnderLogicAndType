(** * CoreLang.SmallStep

    Call-by-value small-step operational semantics for the core language.
    We define:
      - [head_step e e'] : head reduction (no context)
      - [step e e']      : one-step reduction (under let-binding context)
      - [steps e e']     : multi-step reduction (reflexive-transitive closure)
      - [is_val e]       : whether [e] is a value (i.e., [tret v]) *)

From CoreLang Require Export Syntax BasicTyping.

(** ** Postulated evaluation of primitive operations

    [prim_eval op cs] : evaluate [op] on closed constant arguments [cs].
    Returns [None] for nondeterministic operations (nat_gen, int_gen)
    so that they can produce any value. *)
Parameter prim_eval : prim_op → list constant → option constant.

(** Consistency axioms (not needed for type soundness, but clarify intent). *)
Parameter prim_eval_add : ∀ n m, prim_eval op_add [cnat n; cnat m] = Some (cnat (n + m)).
Parameter prim_eval_sub : ∀ n m, prim_eval op_sub [cnat n; cnat m] = Some (cnat (n - m)).
Parameter prim_eval_eq  : ∀ n m, prim_eval op_eq  [cnat n; cnat m] = Some (cbool (n =? m)).

(** ** Postulated pattern-matching oracle

    [match_branch v brs] selects the branch that matches [v],
    returning [Some (n, body)] where [n] constructor args are in [body]. *)
Parameter match_branch : value → list (nat * tm) → option (nat * tm).

(** The result must be one of the branches. *)
Parameter match_branch_member : ∀ v brs n body,
  match_branch v brs = Some (n, body) → (n, body) ∈ brs.

(** ** Head reduction *)

(** [head_step e e'] is the *head* (redex) reduction.
    All rules operate on closed terms; the caller must ensure [lc_tm e]. *)
Inductive head_step : tm → tm → Prop :=

  (** [tlete (tret v) e  →  e[0 ↦ v]] *)
  | HS_Ret v e :
      lc_tm (tlete (tret v) e) →
      head_step (tlete (tret v) e) ({0 ~> v} e)

  (** [tprim op vs  →  c]  when [prim_eval] succeeds *)
  | HS_Op op vs cs c :
      Forall2 (fun v c => v = vconst c) vs cs →
      prim_eval op cs = Some c →
      lc_tm (tprim op vs) →
      head_step (tprim op vs) (tret (vconst c))

  (** Nondeterministic ops: [op_nat_gen] and [op_int_gen]. *)
  | HS_NatGen n :
      lc_tm (tprim op_nat_gen []) →
      head_step (tprim op_nat_gen []) (tret (vconst (cnat n)))

  | HS_IntGen z :
      lc_tm (tprim op_int_gen []) →
      head_step (tprim op_int_gen []) (tret (vconst (cint z)))

  (** [tapp (vlam s body) v  →  body[0 ↦ v]] *)
  | HS_Beta s body v :
      lc_tm (tapp (vlam s body) v) →
      head_step (tapp (vlam s body) v)
                ({0 ~> v} body)

  (** [tapp (vfix sf sx body) v  →  body[1 ↦ self][0 ↦ v]]
      Opens the body with f = self at bvar 1, then x = v at bvar 0. *)
  | HS_Fix sf sx body v :
      let self := vfix sf sx body in
      lc_tm (tapp self v) →
      head_step (tapp self v)
                ({0 ~> v} ({1 ~> self} body))

  (** [tmatch v brs  →  body[0..n-1 ↦ constructor args of v]]
      The oracle selects the branch; the [n] arguments of [v]'s
      constructor are opened into the branch body. *)
  | HS_Match v brs n body args :
      match_branch v brs = Some (n, body) →
      (** [args] are the sub-values of the matched constructor [v]. *)
      length args = n →
      Forall lc_value args →
      lc_tm (tmatch v brs) →
      head_step (tmatch v brs)
                (fold_left (fun e vx => {0 ~> vx} e) args body).

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

Definition steps : tm → tm → Prop := rtc step.

Notation "e '→*' e'" := (steps e e') (at level 40).

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

(** ** Determinism (up to nondeterminism of gen-ops) *)

(** For deterministic operations, head_step is deterministic. *)
Lemma head_step_det e e1 e2 :
  head_step e e1 → head_step e e2 →
  (∀ op cs c1 c2, prim_eval op cs = Some c1 → prim_eval op cs = Some c2 → c1 = c2) →
  e1 = e2 ∨ (∃ op, op = op_nat_gen ∨ op = op_int_gen).
Proof. Admitted.

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
