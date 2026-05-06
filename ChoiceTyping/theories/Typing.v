(** * ChoiceTyping.Typing

    Declarative typing rules for the choice type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)

From ChoiceTyping Require Export Auxiliary PrimOpContext.

(** ** The typing judgment *)

Definition choice_typing_wf (Γ : ctx) (e : tm) (τ : choice_ty) : Prop :=
  wf_choice_ty Γ τ ∧ erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.

Definition branch_unreachable (Γ : ctx) (v : value) (b : bool) : Prop :=
  ⟦Γ⟧ ⊫ FImpl (⟦bool_precise_ty b⟧ (tret v)) FFalse.

Inductive has_choice_type : ctx → tm → choice_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      choice_typing_wf (CtxBind x τ) (tret (vfvar x)) τ →
      has_choice_type
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      choice_typing_wf CtxEmpty (tret (vconst c)) (const_precise_ty c) →
      has_choice_type
        CtxEmpty
        (tret (vconst c))
        (const_precise_ty c)

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      choice_typing_wf Γ e τ2 →
      has_choice_type Γ e τ1 →
      sub_type Γ τ1 τ2 →
      has_choice_type Γ e τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      choice_typing_wf Γ1 e τ →
      has_choice_type Γ2 e τ →
      ctx_sub (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
      has_choice_type Γ1 e τ

  (** T-Let.  Standard additive/bunched let. *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      choice_typing_wf Γ (tlete e1 e2) τ2 →
      has_choice_type Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type
          (CtxComma Γ (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type Γ (tlete e1 e2) τ2

  (** T-LetD.  Standard separating/bunched let. *)
  | CT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      choice_typing_wf (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 →
      has_choice_type Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type
          (CtxStar Γ2 (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type (CtxStar Γ1 Γ2) (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      choice_typing_wf Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_choice_type
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_choice_type Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow τx τ)

  (** T-LamD *)
  | CT_LamD Γ τx τ e (L : aset) :
      choice_typing_wf Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_choice_type
          (CtxStar Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_choice_type Γ
        (tret (vlam (erase_ty τx) e))
        (CTWand τx τ)

  (** T-AppFun *)
  | CT_AppFun Γ τx τ v1 x :
      choice_typing_wf Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      has_choice_type Γ (tret v1) (CTArrow τx τ) →
      has_choice_type Γ (tret (vfvar x)) τx →
      has_choice_type Γ (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      choice_typing_wf (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      has_choice_type Γ1 (tret v1) (CTWand τx τ) →
      has_choice_type Γ2 (tret (vfvar x)) τx →
      has_choice_type (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-Fix *)
  | CT_Fix Γ τx τ vf (L : aset) :
      choice_typing_wf Γ
        (tret (vfix (erase_ty (CTArrow τx τ)) vf))
        (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_choice_type
          (CtxComma Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (CTArrow τx τ) ({0 ~> y} τ))) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTArrow τx τ)) vf))
        (CTArrow τx τ)

  (** T-FixD.  Separating recursive function. *)
  | CT_FixD Γ τx τ vf (L : aset) :
      choice_typing_wf Γ
        (tret (vfix (erase_ty (CTWand τx τ)) vf))
        (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_choice_type
          (CtxStar Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTWand (CTWand τx τ) ({0 ~> y} τ))) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTWand τx τ)) vf))
        (CTWand τx τ)

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x sig :
      wf_primop_sig op sig →
      choice_typing_wf Γ
        (tprim op (vfvar x))
        ({0 ~> x} (primop_result_ty sig)) →
      has_choice_type Γ (tret (vfvar x)) (primop_arg_ty sig) →
      has_choice_type Γ (tprim op (vfvar x)) ({0 ~> x} (primop_result_ty sig))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf v τt τf et ef :
      choice_typing_wf (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf) →
      has_choice_type Γt (tret v) (bool_precise_ty true) →
      has_choice_type Γf (tret v) (bool_precise_ty false) →
      has_choice_type Γt et τt →
      has_choice_type Γf ef τf →
      has_choice_type (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf)

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ v τ et ef :
      choice_typing_wf Γ (tmatch v et ef) τ →
      has_choice_type Γ (tret v) (bool_precise_ty true) →
      branch_unreachable Γ v false →
      has_choice_type Γ et τ →
      erase_ctx Γ ⊢ₑ ef ⋮ erase_ty τ →
      has_choice_type Γ (tmatch v et ef) τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ v τ et ef :
      choice_typing_wf Γ (tmatch v et ef) τ →
      has_choice_type Γ (tret v) (bool_precise_ty false) →
      branch_unreachable Γ v true →
      erase_ctx Γ ⊢ₑ et ⋮ erase_ty τ →
      has_choice_type Γ ef τ →
      has_choice_type Γ (tmatch v et ef) τ.

#[global] Hint Constructors has_choice_type : core.
#[global] Instance typing_choice_inst : Typing ctx tm choice_ty := has_choice_type.
Arguments typing_choice_inst /.

(** ** Small admissible helpers kept only where they name core definitions. *)

Lemma typing_regular Γ e τ :
  has_choice_type Γ e τ →
  wf_ctx Γ ∧ wf_choice_ty Γ τ.
Proof. Admitted.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Γ e τ :
  has_choice_type Γ e (erase_ty τ) →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. Admitted.
