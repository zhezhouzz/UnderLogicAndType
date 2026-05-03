(** * ChoiceType.Denotation

    Denotational semantics for the choice type system (§1.5 of the paper).

    The interpretation is given as formulas in [Choice Logic] whose atoms are
    logic qualifiers.  Type qualifiers are embedded through the abstract
    [lift_type_qualifier_to_logic] bridge.

    The satisfaction notation [m ⊨ φ] is the central judgment used by
    the typing rules and the fundamental theorem. *)

From ChoiceType Require Export Syntax.

(** ** ChoiceLogic satisfaction, instantiated for qualifiers *)

(** Abbreviation: a Choice Logic formula at the ChoiceType instantiation. *)
Notation FQ := FormulaQ.

(** Satisfaction: [m ⊨ φ]  ↔  [res_models m φ] *)
Notation "m ⊨ φ" :=
  (res_models m φ)
  (at level 70, format "m  ⊨  φ").

(** Entailment shorthand: [φ ⊫ ψ]  ↔  [∀ m, m ⊨ φ → m ⊨ ψ] *)
Notation "φ ⊫ ψ" :=
  (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** ** Fresh variable helpers for denotation *)

Definition fib_vars (X : aset) (p : FQ) : FQ :=
  set_fold FFib p X.

(** ** Type measure for denotation fuel

    As in HATs' denotation, the first argument of [denot_ty_fuel] is an
    over-approximation of the syntactic size of the type.  This lets the
    denotation recurse on opened locally-nameless bodies such as
    [{0 ~> x} τ], which are not syntactic subterms accepted by Rocq's
    structural termination checker. *)
Fixpoint cty_measure (τ : choice_ty) : nat :=
  match τ with
  | CTOver _ _ | CTUnder _ _ => 1
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2
  | CTArrow τ1 τ2
  | CTWand τ1 τ2 => 1 + cty_measure τ1 + cty_measure τ2
  end.

Lemma cty_measure_gt_0 τ : cty_measure τ > 0.
Proof. induction τ; simpl; lia. Qed.

Lemma cty_open_preserves_measure τ k x :
  cty_measure ({k ~> x} τ) = cty_measure τ.
Proof. induction τ in k |- *; simpl; eauto; lia. Qed.

(** ** Type denotation

    [denot_ty τ e : FQ] encodes the proposition "expression [e] has type [τ]"
    as a Choice Logic formula.  The translation follows §1.5 verbatim.

    Result variables are represented locally namelessly: the outer [FForall]
    opens the result bound variable in both the expression atom and the type
    qualifier atom. *)

Fixpoint denot_ty_fuel (gas : nat) (τ : choice_ty) (e : tm) : FQ :=
  match gas with
  | 0 => FFalse
  | S gas' =>
  match τ with

  (** {ν:b | φ}  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ◁φ
      The outer [FForall] binds the result coordinate in both [⟦e⟧] and [φ].
      [fib_vars (fv φ)] iterates the single-variable fiber modality over
      φ's free variables. *)
  | CTOver b φ =>
      FForall
        (FImpl (FBExprAtom 0 e)
               (fib_vars (qual_dom φ) (FOver (FAtom (lift_type_qualifier_to_logic φ)))))

  (** [ν:b | φ]  ≝  ∀ν. ⟦e⟧_ν ⇒ ∀_{FV(φ)} ▷φ *)
  | CTUnder b φ =>
      FForall
        (FImpl (FBExprAtom 0 e)
               (fib_vars (qual_dom φ) (FUnder (FAtom (lift_type_qualifier_to_logic φ)))))

  (** τ1 ⊓ τ2  ≝  ⟦τ1⟧ e ∧ ⟦τ2⟧ e *)
  | CTInter τ1 τ2 =>
      FAnd (denot_ty_fuel gas' τ1 e) (denot_ty_fuel gas' τ2 e)

  (** τ1 ⊔ τ2  ≝  ⟦τ1⟧ e ∨ ⟦τ2⟧ e *)
  | CTUnion τ1 τ2 =>
      FOr (denot_ty_fuel gas' τ1 e) (denot_ty_fuel gas' τ2 e)

  (** τ1 ⊕ τ2  ≝  ⟦τ1⟧ e ⊕ ⟦τ2⟧ e *)
  | CTSum τ1 τ2 =>
      FPlus (denot_ty_fuel gas' τ1 e) (denot_ty_fuel gas' τ2 e)

  (** τ_x →, τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x ⇒ ⟦τ[x]⟧ (y x)). *)
  | CTArrow τx τ =>
      FForall
        (FImpl
          (FBExprAtom 0 e)
          (FForall
            (FBFib 1
              (FImpl
                (denot_ty_fuel gas' τx (tret (vbvar 0)))
                (denot_ty_fuel gas' τ
                   (tapp (vbvar 1) (vbvar 0)))))))

  (** τ_x ⊸ τ  ≝  ∀y. ⟦e⟧_y ⇒ ∀{y}.∀x.(⟦τ_x⟧ x −∗ ⟦τ[x]⟧ (y x)). *)
  | CTWand τx τ =>
      FForall
        (FImpl
          (FBExprAtom 0 e)
          (FForall
            (FBFib 1
              (FWand
                (denot_ty_fuel gas' τx (tret (vbvar 0)))
                (denot_ty_fuel gas' τ
                   (tapp (vbvar 1) (vbvar 0)))))))

  end
  end.

Definition denot_ty (τ : choice_ty) (e : tm) : FQ :=
  denot_ty_fuel (cty_measure τ) τ e.

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
Proof. Admitted.

(** The context denotation of a star-context distributes over FStar. *)
Lemma denot_ctx_star Γ1 Γ2 m :
  m ⊨ ⟦CtxStar Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hc : world_compat m1 m2),
    res_product m1 m2 Hc ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. Admitted.

(** The context denotation of a sum-context distributes over FPlus. *)
Lemma denot_ctx_sum Γ1 Γ2 m :
  m ⊨ ⟦CtxSum Γ1 Γ2⟧ ↔
  ∃ (m1 m2 : WfWorld) (Hdef : raw_sum_defined m1 m2),
    res_sum m1 m2 Hdef ⊑ m ∧
    m1 ⊨ ⟦Γ1⟧ ∧ m2 ⊨ ⟦Γ2⟧.
Proof. Admitted.

(** [⟦CtxBind x τ⟧] is [⟦τ⟧ (return x)]. *)
Lemma denot_ctx_bind x τ m :
  m ⊨ ⟦CtxBind x τ⟧ ↔ m ⊨ denot_ty τ (tret (vfvar x)).
Proof. Admitted.

(** Substitution commutes with type denotation. *)
Lemma denot_ty_subst τ e x v m :
  lc_value v →
  m ⊨ denot_ty ({x := v} τ) ({x := v} e) ↔
  m ⊨ denot_ty τ e.
Proof. Admitted.
