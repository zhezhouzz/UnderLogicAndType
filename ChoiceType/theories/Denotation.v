(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] over
    [qualifier] atoms:
      [⟦τ⟧ e  : Formula qualifier]  — type denotation (a predicate on expressions)
      [⟦Γ⟧    : Formula qualifier]  — context denotation

    We instantiate [satisfies] with:
      [interp     := qual_interp_world]  (qualifier → SubstT → Prop)
      [subst_atom := qual_subst]      (SubstT → qualifier → qualifier)

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From ChoiceType Require Export Syntax.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Abbreviation: a Choice Logic formula over qualifier atoms.
    [FormulaQ] is defined in ChoiceType.Prelude as
    [@Formula atom _ _ value], so [FormulaQ qualifier] fully determines
    all implicit parameters and avoids evar ambiguity. *)
Notation FQ := (FormulaQ qualifier).

(** Satisfaction: [m ⊨ φ]  ↔  [satisfies qual_interp_world qual_subst m φ] *)
Notation "m ⊨ φ" :=
  (satisfies (Var := atom) (Value := value)
     qual_interp_world qual_subst m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails (Var := atom) (Value := value)
     qual_interp_world qual_subst φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Fresh variable helpers for denotation *)

(** Pick a result variable [ν] fresh with respect to a set of atoms. *)
Definition fresh_result (avoid : aset) : atom := fresh avoid.

(** ** Type denotation

    [denot_ty τ e : FQ] encodes the proposition "expression [e] has type [τ]"
    as a Choice Logic formula.  The translation follows §1.5 verbatim.

    Naming convention: [ν] is always the *result variable* (the ν from {ν:b|φ}),
    chosen fresh with respect to [qual_fv φ] so it does not clash. *)

Fixpoint denot_ty (τ : choice_ty) (e : tm) : FQ :=
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⊸ ∀_{FV(φ)} ◁φ
      The result variable ν is chosen fresh w.r.t. φ's free variables.
      FForall {ν} quantifies over ν; inside, FImpl links execution to
      the over-approximation of φ.  FForall (fv φ) quantifies over
      the remaining free variables of φ for the fiberwise universal. *)
  | CTOver b φ =>
      let ν  := fresh_result (qual_fv φ ∪ fv_tm e) in
      FForall {[ν]}
        (FImpl (FAtom (QExpr e ν))
               (FForall (qual_fv φ) (FOver (FAtom φ))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⊸ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      let ν  := fresh_result (qual_fv φ ∪ fv_tm e) in
      FForall {[ν]}
        (FImpl (FAtom (QExpr e ν))
               (FForall (qual_fv φ) (FUnder (FAtom φ))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty τ1 e) (denot_ty τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty τ1 e) (denot_ty τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty τ1 e) (denot_ty τ2 e)

  (** x:τ_x →, τ  ≝  ⟦τ_x⟧ x ⊸ ⟦τ⟧ (e x)
      [e] is an expression (tm), so applying it to [vfvar x] requires first
      running [e] to get a function value (bound to bvar 0 by tlete), then
      applying that value.  The ANF encoding: let f = e in f x. *)
  | CTArrow x τx τ =>
      FImpl
        (denot_ty τx (tret (vfvar x)))
        (denot_ty τ  (tlete e (tletapp (vbvar 0) (vfvar x) (tret (vbvar 0)))))

  (** x:τ_x ⊸ τ  ≝  ⟦τ_x⟧ x −∗ ⟦τ⟧ (e x)  (separating implication) *)
  | CTWand x τx τ =>
      FWand
        (denot_ty τx (tret (vfvar x)))
        (denot_ty τ  (tlete e (tletapp (vbvar 0) (vfvar x) (tret (vbvar 0)))))

  (** ∗τ  ≝  □ (⟦τ⟧ e)  — persistence (the type is a persistent assertion) *)
  | CTStar τ =>
      FPers (denot_ty τ e)

  (** □τ  ≝  ∀ν. ⟦e⟧_ν ⊸ □ (⟦τ⟧ (return ν))
      For each execution result ν, the typing assertion for ν is persistent. *)
  | CTPers τ =>
      let ν := fresh_result (stale e) in
      FForall {[ν]}
        (FImpl (FAtom (QExpr e ν))
               (FPers (denot_ty τ (tret (vfvar ν)))))

  end.

(** ** Context denotation

    [denot_ctx Γ : FQ] is the formula that holds when [Γ] is "satisfied". *)
Fixpoint denot_ctx (Γ : ctx) : FQ :=
  match Γ with
  | CtxEmpty        => FTrue
  | CtxBind x τ    => denot_ty τ (tret (vfvar x))
  | CtxComma Γ1 Γ2 => FAnd  (denot_ctx Γ1) (denot_ctx Γ2)
  | CtxStar  Γ1 Γ2 => FStar (denot_ctx Γ1) (denot_ctx Γ2)
  | CtxSum   Γ1 Γ2 => FPlus (denot_ctx Γ1) (denot_ctx Γ2)
  end.

(** ** Typeclass instances for [⟦⟧] notation *)

#[global] Instance denot_cty_inst :
    Denotation choice_ty (tm → FQ) := denot_ty.
#[global] Instance denot_ctx_inst :
    Denotation ctx FQ := denot_ctx.
Arguments denot_cty_inst /.
Arguments denot_ctx_inst /.

(** With these instances:
      [⟦τ⟧ e]  unfolds to [denot_ty τ e]
      [⟦Γ⟧]    unfolds to [denot_ctx Γ]              *)

(** ** Key semantic lemmas (Admitted — to be proved in Soundness.v) *)

(** Monotonicity: if m ⊨ ⟦Γ⟧ and m ≤ m', then m' ⊨ ⟦Γ⟧ for comma contexts. *)
Lemma denot_ctx_mono_comma (Γ : ctx) m m' :
  m ⊨ ⟦Γ⟧ →
  res_le (Var := atom) (Value := value) m m' →
  m' ⊨ ⟦Γ⟧.
Proof. Admitted.

(** The context denotation of a comma-context distributes over conjunction. *)
Lemma denot_ctx_comma Γ1 Γ2 m :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** The context denotation of a star-context distributes over FStar. *)
Lemma denot_ctx_star Γ1 Γ2 m :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ m1 m2,
    res_le (Var := atom) (Value := value) (res_product m1 m2) m ∧
    world_compat (Var := atom) (Value := value) m1 m2 ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** The context denotation of a sum-context distributes over FPlus. *)
Lemma denot_ctx_sum Γ1 Γ2 m :
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ m1 m2,
    res_le (Var := atom) (Value := value) (res_sum m1 m2) m ∧
    res_sum_defined (Var := atom) (Value := value) m1 m2 ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** [⟦CtxBind x τ⟧] is [⟦τ⟧ (return x)]. *)
Lemma denot_ctx_bind x τ m :
  m ⊨ ⟦CtxBind x τ⟧ ↔ m ⊨ denot_ty τ (tret (vfvar x)).
Proof. simpl. reflexivity. Qed.

(** Substitution commutes with type denotation. *)
Lemma denot_ty_subst τ e x v m :
  lc_value v →
  m ⊨ denot_ty ({x := v} τ) ({x := v} e) ↔
  m ⊨ denot_ty τ e.
Proof. Admitted.
