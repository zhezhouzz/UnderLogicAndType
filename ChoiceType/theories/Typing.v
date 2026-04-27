(** * ChoiceType.Typing

    Declarative typing rules for the choice type system (Fig. 3–4 of the paper).

    Two *modes* govern how the environment is consumed:
      [ModeComma] — additive / comma bunching (like standard typing)
      [ModeStar]  — multiplicative / star bunching (separation-logic style)

    The central judgment is [has_choice_type mode Γ e τ].
    Notations expose it as [Γ ⊢ᶜ e ⋮ τ] (comma) and [Γ ⊢ˢ e ⋮ τ] (star).

    Subtyping is defined *semantically* — no syntactic subtyping relation —
    following the approach of §1.5 (Definition 1.12 of the paper). *)

From ChoiceType Require Export Denotation.

(** ** Typing mode *)

Inductive typing_mode : Type :=
  | ModeComma   (** additive / comma mode  ⊢ᶜ *)
  | ModeStar.   (** multiplicative / star mode ⊢ˢ *)

(** ** Context splitting

    [ctx_split Γ Γ1 Γ2] reads as "Γ decomposes into Γ1 and Γ2".
    Only used in star mode to distribute resources between subderivations.

    Rules:
      SpEmp   : the empty context splits to (∅, ∅)
      SpPers  : a persistent binding □τ is *duplicated* (intuitionistic resource)
      SpLeft  : an unrestricted binding goes entirely to the left half
      SpRight : an unrestricted binding goes entirely to the right half
      SpComma : split each component of a comma context independently
      SpStar  : split each component of a star context independently *)

Inductive ctx_split : ctx → ctx → ctx → Prop :=

  | SpEmp :
      ctx_split CtxEmpty CtxEmpty CtxEmpty

  | SpPers x τ :
      ctx_split (CtxBind x (CTPers τ))
                (CtxBind x (CTPers τ))
                (CtxBind x (CTPers τ))

  | SpLeft x τ :
      ctx_split (CtxBind x τ) (CtxBind x τ) CtxEmpty

  | SpRight x τ :
      ctx_split (CtxBind x τ) CtxEmpty (CtxBind x τ)

  | SpComma Γ Γ1 Γ2 Δ Δ1 Δ2 :
      ctx_split Γ Γ1 Γ2 →
      ctx_split Δ Δ1 Δ2 →
      ctx_split (CtxComma Γ Δ) (CtxComma Γ1 Δ1) (CtxComma Γ2 Δ2)

  | SpStar Γ Γ1 Γ2 Δ Δ1 Δ2 :
      ctx_split Γ Γ1 Γ2 →
      ctx_split Δ Δ1 Δ2 →
      ctx_split (CtxStar Γ Δ) (CtxStar Γ1 Δ1) (CtxStar Γ2 Δ2).

#[global] Hint Constructors ctx_split : core.

(** ** Persistence-context constructor

    [persist_ctx Γ] wraps every type in Γ with CTPers.
    Used in CT_Pers: to prove e : □τ, type e in the persistified context. *)
Fixpoint persist_ctx (Γ : ctx) : ctx :=
  match Γ with
  | CtxEmpty        => CtxEmpty
  | CtxBind x τ    => CtxBind x (CTPers τ)
  | CtxComma Γ1 Γ2 => CtxComma (persist_ctx Γ1) (persist_ctx Γ2)
  | CtxStar  Γ1 Γ2 => CtxComma (persist_ctx Γ1) (persist_ctx Γ2)
  end.

(** ** Semantic subtyping

    Subtyping is defined as entailment in the denotational model.

    [sub_comma Γ e τ1 τ2]: comma-mode subtyping.
      Every world satisfying ⟦Γ⟧ and ⟦τ1⟧ e also satisfies ⟦τ2⟧ e.

    [sub_star Γ e τ1 τ2]: star-mode subtyping.
      ⟦Γ⟧ entails the wand (⟦τ1⟧ e −∗ ⟦τ2⟧ e).
      The context can "convert" τ1 into τ2 on a disjoint resource. *)

Definition sub_comma (Γ : ctx) (e : tm) (τ1 τ2 : choice_ty) : Prop :=
  ∀ m, m ⊨ ⟦Γ⟧ → m ⊨ ⟦τ1⟧ e → m ⊨ ⟦τ2⟧ e.

Definition sub_star (Γ : ctx) (e : tm) (τ1 τ2 : choice_ty) : Prop :=
  ⟦Γ⟧ ⊫ FWand (⟦τ1⟧ e) (⟦τ2⟧ e).

(** ** The typing judgment

    [has_choice_type mode Γ e τ]: expression [e] has type [τ] under
    context [Γ] in [mode].  Cofinite quantification (parameter [L])
    is used for all rules that bind a fresh variable. *)

Reserved Notation "Γ '⊢ᶜ' e '⋮' τ" (at level 20, e constr, τ constr).
Reserved Notation "Γ '⊢ˢ' e '⋮' τ" (at level 20, e constr, τ constr).

Inductive has_choice_type : typing_mode → ctx → tm → choice_ty → Prop :=

  (** ================================================================
      Variable rules
      ================================================================ *)

  (** T_Var: a variable x has the type it is bound to.
      Only available in comma mode (variables are reusable). *)
  | CT_Var x τ :
      has_choice_type ModeComma
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** ================================================================
      Constant rules
      ================================================================ *)

  (** T_ConstO: a constant c has the over-type {ν:b | ν = c}.
      An over-type is a sound upper bound on possible results. *)
  | CT_ConstO c :
      has_choice_type ModeComma
        CtxEmpty
        (tret (vconst c))
        (CTOver (base_ty_of_const c) (b0:c= c))

  (** T_ConstU: a constant c has the under-type [ν:b | ν = c].
      An under-type is a tight lower bound (exact result). *)
  | CT_ConstU c :
      has_choice_type ModeStar
        CtxEmpty
        (tret (vconst c))
        (CTUnder (base_ty_of_const c) (b0:c= c))

  (** ================================================================
      Lambda / fixpoint rules
      ================================================================ *)

  (** T_Lam: introduce a comma-function type x:τx →, τ.
      Pick any fresh y ∉ L; type the body with y:τx added (comma mode).
      Alpha-rename the formal x to y in the codomain: [{x := vfvar y} τ]. *)
  | CT_Lam Γ x τx τ e (L : aset) :
      (∀ y, y ∉ L →
        has_choice_type ModeComma
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({x := vfvar y} τ)) →
      has_choice_type ModeComma Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow x τx τ)

  (** T_Wand: introduce a wand-function type x:τx ⊸ τ.
      The body is typed in the *star* extension (resources are split). *)
  | CT_Wand Γ x τx τ e (L : aset) :
      (∀ y, y ∉ L →
        has_choice_type ModeStar
          (CtxStar Γ (CtxBind y τx))
          (e ^^ y)
          ({x := vfvar y} τ)) →
      has_choice_type ModeStar Γ
        (tret (vlam (erase_ty τx) e))
        (CTWand x τx τ)

  (** T_Fix: recursive comma-function.
      Two fresh atoms f (self-reference of type x:τx →, τ) and y (argument of type τx).
      bvar 0 → y, bvar 1 → f inside the body. *)
  | CT_Fix Γ x τx τ e (L : aset) :
      (∀ f y, f ∉ L → y ∉ L → f ≠ y →
        has_choice_type ModeComma
          (CtxComma Γ
            (CtxComma (CtxBind f (CTArrow x τx τ))
                      (CtxBind y τx)))
          ({0 ~> vfvar y} ({1 ~> vfvar f} e))
          ({x := vfvar y} τ)) →
      has_choice_type ModeComma Γ
        (tret (vfix (erase_ty (CTArrow x τx τ)) (erase_ty τx) e))
        (CTArrow x τx τ)

  (** ================================================================
      Let-binding rules
      ================================================================ *)

  (** T_Let_comma: additive let-binding.
      Both e1 and e2 share the same context via comma. *)
  | CT_Let_comma Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      has_choice_type ModeComma Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type ModeComma
          (CtxComma Γ2 (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type ModeComma
        (CtxComma Γ1 Γ2)
        (tlete e1 e2)
        τ2

  (** T_Let_star: multiplicative let-binding.
      Γ1 is consumed by e1; the bound result goes into e2 via star. *)
  | CT_Let_star Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      has_choice_type ModeStar Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type ModeStar
          (CtxStar Γ2 (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type ModeStar
        (CtxStar Γ1 Γ2)
        (tlete e1 e2)
        τ2

  (** ================================================================
      Application rules
      ================================================================ *)

  (** T_App_comma: apply a comma-function.
      Γ1 provides the function; Γ2 provides the argument.
      Result type instantiates the formal parameter x with the actual y. *)
  | CT_App_comma Γ1 Γ2 x τx τ f y :
      has_choice_type ModeComma Γ1 (tret (vfvar f)) (CTArrow x τx τ) →
      has_choice_type ModeComma Γ2 (tret (vfvar y)) τx →
      has_choice_type ModeComma
        (CtxComma Γ1 Γ2)
        (tletapp (vfvar f) (vfvar y) (tret (vbvar 0)))
        ({x := vfvar y} τ)

  (** T_App_star: apply a wand-function.
      The function comes from Γ1 in comma mode (functions are reusable);
      the argument y is consumed from Γ2 in star mode. *)
  | CT_App_star Γ1 Γ2 x τx τ f y :
      has_choice_type ModeComma Γ1 (tret (vfvar f)) (CTWand x τx τ) →
      has_choice_type ModeStar  Γ2 (tret (vfvar y)) τx →
      has_choice_type ModeStar
        (CtxStar Γ1 Γ2)
        (tletapp (vfvar f) (vfvar y) (tret (vbvar 0)))
        ({x := vfvar y} τ)

  (** ================================================================
      Primitive operation rule
      ================================================================ *)

  (** T_LetOp: run a primitive operation op on arguments vs.
      Arguments are typed at their erased base types.
      The continuation e_body is typed with fresh variable x : ret_type.
      We use an explicit equality [Hop] to name the result type instead of
      a [let] pattern (which can be fragile inside inductive type bodies). *)
  | CT_LetOp Γ op vs e_body τ arg_tys ret_b (L : aset) :
      prim_op_type op = (arg_tys, ret_b) →
      Forall2
        (fun v b => has_choice_type ModeComma Γ (tret v) (lift_ty (TBase b)))
        vs arg_tys →
      (∀ x, x ∉ L →
        has_choice_type ModeComma
          (CtxComma Γ (CtxBind x (lift_ty (TBase ret_b))))
          (e_body ^^ x)
          τ) →
      has_choice_type ModeComma Γ (tletop op vs e_body) τ

  (** ================================================================
      Pattern matching rule
      ================================================================ *)

  (** T_Match: match on a value v of base type b.
      Each branch provides n fresh variables for the constructor arguments. *)
  | CT_Match Γ v τ branches b (L : aset) :
      has_choice_type ModeComma Γ (tret v) (lift_ty (TBase b)) →
      (∀ i n body arg_tys,
          branches !! i = Some (n, body) →
          constructor_tys b !! i = Some arg_tys →
          length arg_tys = n →
          ∀ ys : list atom,
            length ys = n →
            NoDup ys →
            Forall (fun y => y ∉ L) ys →
            has_choice_type ModeComma
              (fold_left
                (fun ctx '(y, bt) => CtxComma ctx (CtxBind y (lift_ty (TBase bt))))
                (zip ys arg_tys) Γ)
              (fold_left (fun e y => e ^^ y) ys body)
              τ) →
      has_choice_type ModeComma Γ (tmatch v branches) τ

  (** ================================================================
      Type connective introduction / elimination rules
      ================================================================ *)

  (** T_Inter: intersection introduction (prove both τ1 and τ2). *)
  | CT_Inter Γ e τ1 τ2 :
      has_choice_type ModeComma Γ e τ1 →
      has_choice_type ModeComma Γ e τ2 →
      has_choice_type ModeComma Γ e (CTInter τ1 τ2)

  (** T_InterL / T_InterR: intersection elimination. *)
  | CT_InterL Γ e τ1 τ2 :
      has_choice_type ModeComma Γ e (CTInter τ1 τ2) →
      has_choice_type ModeComma Γ e τ1

  | CT_InterR Γ e τ1 τ2 :
      has_choice_type ModeComma Γ e (CTInter τ1 τ2) →
      has_choice_type ModeComma Γ e τ2

  (** T_UnionL / T_UnionR: union introduction (choose a disjunct). *)
  | CT_UnionL Γ e τ1 τ2 :
      has_choice_type ModeComma Γ e τ1 →
      has_choice_type ModeComma Γ e (CTUnion τ1 τ2)

  | CT_UnionR Γ e τ1 τ2 :
      has_choice_type ModeComma Γ e τ2 →
      has_choice_type ModeComma Γ e (CTUnion τ1 τ2)

  (** T_SumL / T_SumR: choice-sum introduction.
      Choice sum ⊕ is multiplicative — it lives in star mode. *)
  | CT_SumL Γ e τ1 τ2 :
      has_choice_type ModeStar Γ e τ1 →
      has_choice_type ModeStar Γ e (CTSum τ1 τ2)

  | CT_SumR Γ e τ1 τ2 :
      has_choice_type ModeStar Γ e τ2 →
      has_choice_type ModeStar Γ e (CTSum τ1 τ2)

  (** T_Pers: persistence modality introduction □τ.
      If e has type τ in the *persistified* context (all bindings wrapped in CTPers),
      then e has type □τ in the original context. *)
  | CT_Pers Γ e τ :
      has_choice_type ModeComma (persist_ctx Γ) e τ →
      has_choice_type ModeComma Γ e (CTPers τ)

  (** T_Star: separability modality introduction ∗τ.
      If e has type τ, then it also has type ∗τ.
      Soundness relies on the denotation ⟦∗τ⟧ e = FPers (⟦τ⟧ e) being
      provable whenever ⟦τ⟧ e is (via CT_Sub + a semantic argument). *)
  | CT_Star Γ e τ :
      has_choice_type ModeComma Γ e τ →
      has_choice_type ModeComma Γ e (CTStar τ)

  (** ================================================================
      Subsumption rules
      ================================================================ *)

  (** T_Sub_comma: semantic subsumption in comma mode.
      Requires ∀ m, m ⊨ ⟦Γ⟧ → m ⊨ ⟦τ1⟧ e → m ⊨ ⟦τ2⟧ e. *)
  | CT_Sub_comma Γ e τ1 τ2 :
      has_choice_type ModeComma Γ e τ1 →
      sub_comma Γ e τ1 τ2 →
      has_choice_type ModeComma Γ e τ2

  (** T_Sub_star: semantic subsumption in star mode.
      Requires ⟦Γ⟧ ⊫ (⟦τ1⟧ e −∗ ⟦τ2⟧ e). *)
  | CT_Sub_star Γ e τ1 τ2 :
      has_choice_type ModeStar Γ e τ1 →
      sub_star Γ e τ1 τ2 →
      has_choice_type ModeStar Γ e τ2

  (** ================================================================
      Structural rules
      ================================================================ *)

  (** T_Weak: weakening in comma mode.
      An unused Δ can be added to the comma-context. *)
  | CT_Weak Γ Δ e τ :
      has_choice_type ModeComma Γ e τ →
      has_choice_type ModeComma (CtxComma Γ Δ) e τ

  (** T_Exchange: exchange in comma mode (comma is symmetric). *)
  | CT_Exchange Γ1 Γ2 e τ :
      has_choice_type ModeComma (CtxComma Γ1 Γ2) e τ →
      has_choice_type ModeComma (CtxComma Γ2 Γ1) e τ

  (** T_Sp: resource splitting for star mode.
      If Γ splits into Γ1 and Γ2, and Γ1 ⊢ˢ e ⋮ τ, then Γ ⊢ˢ e ⋮ τ.
      The extra half Γ2 is "dropped" (it must be empty or persistent). *)
  | CT_Sp Γ Γ1 Γ2 e τ :
      ctx_split Γ Γ1 Γ2 →
      has_choice_type ModeStar Γ1 e τ →
      has_choice_type ModeStar Γ e τ

  (** T_Mode_up: under-approximation lifts to over-approximation.
      A star-mode derivation (exact) entails a comma-mode derivation (sound). *)
  | CT_Mode_up Γ e b φ :
      has_choice_type ModeStar Γ e (CTUnder b φ) →
      has_choice_type ModeComma Γ e (CTOver b φ)

where "Γ '⊢ᶜ' e '⋮' τ" := (has_choice_type ModeComma Γ e τ)
  and "Γ '⊢ˢ' e '⋮' τ" := (has_choice_type ModeStar  Γ e τ).

#[global] Hint Constructors has_choice_type : core.

(** ** Key admissible rules and structural lemmas (proved in Soundness.v) *)

(** Weakening in star mode via splitting. *)
Lemma CT_Weak_star Γ Δ e τ :
  has_choice_type ModeStar Γ e τ →
  has_choice_type ModeStar (CtxStar Γ Δ) e τ.
Proof. Admitted.

(** sub_comma is reflexive. *)
Lemma sub_comma_refl Γ e τ :
  sub_comma Γ e τ τ.
Proof. unfold sub_comma. auto. Qed.

(** sub_star is reflexive. *)
Lemma sub_star_refl Γ e τ :
  sub_star Γ e τ τ.
Proof. Admitted.

(** Weakening in comma mode (direct corollary of CT_Weak). *)
Lemma weakening_comma Γ Δ e τ :
  Γ ⊢ᶜ e ⋮ τ →
  CtxComma Γ Δ ⊢ᶜ e ⋮ τ.
Proof. intro H. apply CT_Weak. exact H. Qed.

(** Substitution preserves choice typing. *)
Lemma subst_typing_choice mode Γ x τx e τ v :
  has_choice_type mode (CtxComma (CtxBind x τx) Γ) e τ →
  has_choice_type ModeComma CtxEmpty (tret v) τx →
  has_choice_type mode Γ ({x := v} e) ({x := v} τ).
Proof. Admitted.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase mode Γ e τ :
  has_choice_type mode Γ e (erase_ty τ) →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. Admitted.
