(** * ChoiceType.Typing

    Declarative typing rules for the choice type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)

From ChoiceType Require Export Denotation.

(** ** Semantic subtyping and context restriction *)

Definition sub_type (Γ : ctx) (τ1 τ2 : choice_ty) : Prop :=
  ∀ e, ⟦Γ⟧ ⊫ FImpl (⟦τ1⟧ e) (⟦τ2⟧ e).

Definition ctx_sub (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  ∀ r, r ⊨ ⟦Γ1⟧ → res_restrict r X ⊨ ⟦Γ2⟧.

(** ** The typing judgment *)

Inductive has_choice_type : ctx → tm → choice_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      has_choice_type
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const *)
  | CT_Const c :
      has_choice_type
        CtxEmpty
        (tret (vconst c))
        (CTOver (base_ty_of_const c) (b0:c= c))

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      has_choice_type Γ e τ1 →
      sub_type Γ τ1 τ2 →
      has_choice_type Γ e τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      has_choice_type Γ2 e τ →
      ctx_sub (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
      has_choice_type Γ1 e τ

  (** T-Let *)
  | CT_Let Δ Γ τ1 τ2 e1 e2 (L : aset) :
      has_choice_type Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type
          (plug_ctx Δ (CtxComma Γ (CtxBind x τ1)))
          (e2 ^^ x)
          τ2) →
      has_choice_type (plug_ctx Δ Γ) (tlete e1 e2) τ2

  (** T-LetD *)
  | CT_LetD Δ Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      has_choice_type Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type
          (plug_ctx Δ (CtxStar (CtxComma Γ1 (CtxBind x τ1)) Γ2))
          (e2 ^^ x)
          τ2) →
      has_choice_type (plug_ctx Δ (CtxStar Γ1 Γ2)) (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ x τx τ e (L : aset) :
      (∀ y, y ∉ L →
        has_choice_type
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({x := vfvar y} τ)) →
      has_choice_type Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow x τx τ)

  (** T-LamD *)
  | CT_LamD Γ x τx τ e (L : aset) :
      (∀ y, y ∉ L →
        has_choice_type
          (CtxStar Γ (CtxBind y τx))
          (e ^^ y)
          ({x := vfvar y} τ)) →
      has_choice_type Γ
        (tret (vlam (erase_ty τx) e))
        (CTWand x τx τ)

  (** T-AppFun *)
  | CT_AppFun Γ x τx τ v1 v2 :
      has_choice_type Γ (tret v1) (CTArrow x τx τ) →
      has_choice_type Γ (tret v2) τx →
      has_choice_type Γ (tapp v1 v2) ({x := v2} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 x τx τ v1 v2 :
      has_choice_type Γ1 (tret v1) (CTWand x τx τ) →
      has_choice_type Γ2 (tret v2) τx →
      has_choice_type (CtxStar Γ1 Γ2) (tapp v1 v2) ({x := v2} τ)

  (** T-Fix *)
  | CT_Fix Γ x τx τ e (L : aset) :
      (∀ f y, f ∉ L → y ∉ L → f ≠ y →
        has_choice_type
          (CtxComma Γ
            (CtxComma
              (CtxBind y τx)
              (CtxBind f (CTArrow x τx τ))))
          ({0 ~> vfvar y} ({1 ~> vfvar f} e))
          ({x := vfvar y} τ)) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTArrow x τx τ)) (erase_ty τx) e))
        (CTArrow x τx τ)

  (** T-FixD.  The paper refines the recursive argument with a decreasing
      predicate; that qualifier atom is still definitionally pending, so this
      constructor records the separating context structure. *)
  | CT_FixD Γ x τx τ e (L : aset) :
      (∀ f y, f ∉ L → y ∉ L → f ≠ y →
        has_choice_type
          (CtxStar Γ
            (CtxComma
              (CtxBind y τx)
              (CtxBind f (CTArrow x τx τ))))
          ({0 ~> vfvar y} ({1 ~> vfvar f} e))
          ({x := vfvar y} τ)) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTWand x τx τ)) (erase_ty τx) e))
        (CTWand x τx τ)

  (** T-AppOp.  Primitive operations are unary. *)
  | CT_AppOp Γ op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) →
      has_choice_type Γ (tret v) (lift_ty (TBase arg_b)) →
      has_choice_type Γ (tprim op v) (lift_ty (TBase ret_b))

  (** T-AppOpD.  Unary primitive operation in a separated argument context. *)
  | CT_AppOpD Γ1 Γ2 op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) →
      has_choice_type Γ2 (tret v) (lift_ty (TBase arg_b)) →
      has_choice_type (CtxStar Γ1 Γ2) (tprim op v) (lift_ty (TBase ret_b))

  (** T-Match.  The core match is a fixed boolean two-branch eliminator. *)
  | CT_Match Γ v τ et ef :
      has_choice_type Γ (tret v) (lift_ty (TBase TBool)) →
      has_choice_type Γ et τ →
      has_choice_type Γ ef τ →
      has_choice_type Γ (tmatch v et ef) τ.

#[global] Hint Constructors has_choice_type : core.
#[global] Instance typing_choice_inst : Typing ctx tm choice_ty := has_choice_type.
Arguments typing_choice_inst /.

(** ** Small admissible helpers kept only where they name core definitions. *)

Lemma sub_type_refl Γ τ :
  sub_type Γ τ τ.
Proof. unfold sub_type, entails. intros e m _ m' _ Hτ. exact Hτ. Qed.

Lemma ctx_sub_refl Γ :
  ctx_sub (ctx_dom Γ) Γ Γ.
Proof. Admitted.

(** Substitution preserves choice typing. *)
Lemma subst_typing_choice Γ x τx e τ v :
  has_choice_type (CtxComma (CtxBind x τx) Γ) e τ →
  has_choice_type CtxEmpty (tret v) τx →
  has_choice_type Γ ({x := v} e) ({x := v} τ).
Proof. Admitted.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Γ e τ :
  has_choice_type Γ e (erase_ty τ) →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. Admitted.
