(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    world predicates.  Qualifiers enter the logic through [qual_atom].

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From ChoiceType Require Export Syntax.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Abbreviation: a Choice Logic formula at the ChoiceType instantiation. *)
Notation FQ := FormulaQ.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models (Var := atom) (Value := value) m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails (Var := atom) (Value := value) φ ψ)
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
      FForall ν quantifies over the result coordinate; inside, FImpl links
      execution to the over-approximation of φ.  [FFib (fv φ)] checks the
      formula on each fiber determined by φ's free variables. *)
  | CTOver b φ =>
      let ν  := fresh_result (qual_fv φ ∪ fv_tm e) in
      FForall ν
        (FImpl (FAtom (qual_atom (QExpr e ν)))
               (FFib (qual_fv φ) (FOver (FAtom (qual_atom φ)))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⊸ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      let ν  := fresh_result (qual_fv φ ∪ fv_tm e) in
      FForall ν
        (FImpl (FAtom (qual_atom (QExpr e ν)))
               (FFib (qual_fv φ) (FUnder (FAtom (qual_atom φ)))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty τ1 e) (denot_ty τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty τ1 e) (denot_ty τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty τ1 e) (denot_ty τ2 e)

  (** x:τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.(⟦τ_x⟧ x ⇒ ⟦τ⟧ (y x)) *)
  | CTArrow x τx τ =>
      let y := fresh_result (fv_cty τx ∪ fv_cty τ ∪ fv_tm e ∪ {[x]}) in
      FForall y
        (FImpl
          (FAtom (qual_atom (QExpr e y)))
          (FFib {[y]}
            (FImpl
              (denot_ty τx (tret (vfvar x)))
              (denot_ty τ (tapp (vfvar y) (vfvar x))))))

  (** x:τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.(⟦τ_x⟧ x −∗ ⟦τ⟧ (y x)) *)
  | CTWand x τx τ =>
      let y := fresh_result (fv_cty τx ∪ fv_cty τ ∪ fv_tm e ∪ {[x]}) in
      FForall y
        (FImpl
          (FAtom (qual_atom (QExpr e y)))
          (FFib {[y]}
            (FWand
              (denot_ty τx (tret (vfvar x)))
              (denot_ty τ (tapp (vfvar y) (vfvar x))))))

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
  m ⊑ m' →
  m' ⊨ ⟦Γ⟧.
Proof. Admitted.

(** The context denotation of a comma-context distributes over conjunction. *)
Lemma denot_ctx_comma Γ1 Γ2 m :
  m ⊨ ⟦CtxComma Γ1 Γ2⟧ ↔ m ⊨ ⟦Γ1⟧ ∧ m ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** The context denotation of a star-context distributes over FStar. *)
Lemma denot_ctx_star Γ1 Γ2 m :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WorldT) (Hc : world_compat (Var := atom) (Value := value) m1 m2),
    res_product (Var := atom) (Value := value) m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. simpl. reflexivity. Qed.

(** The context denotation of a sum-context distributes over FPlus. *)
Lemma denot_ctx_sum Γ1 Γ2 m :
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WorldT) (Hdef : raw_sum_defined (Var := atom) (Value := value) m1 m2),
    res_sum (Var := atom) (Value := value) m1 m2 Hdef ⊑ m ∧
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
