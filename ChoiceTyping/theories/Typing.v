(** * ChoiceTyping.Typing

    Declarative typing rules for the choice type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)

From ChoiceTyping Require Export Auxiliary.

(** ** The typing judgment *)

Inductive has_choice_type : ctx → tm → choice_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      wf_choice_ty (CtxBind x τ) τ →
      has_choice_type
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const *)
  | CT_Const c :
      wf_choice_ty CtxEmpty (CTOver (base_ty_of_const c) (b0:c= c)) →
      has_choice_type
        CtxEmpty
        (tret (vconst c))
        (CTOver (base_ty_of_const c) (b0:c= c))

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      wf_choice_ty Γ τ2 →
      has_choice_type Γ e τ1 →
      sub_type Γ τ1 τ2 →
      has_choice_type Γ e τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      wf_choice_ty Γ1 τ →
      has_choice_type Γ2 e τ →
      ctx_sub (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
      has_choice_type Γ1 e τ

  (** T-Let *)
  | CT_Let Δ Γ τ1 τ2 e1 e2 (L : aset) :
      wf_choice_ty (plug_ctx Δ Γ) τ2 →
      has_choice_type Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type
          (plug_ctx Δ (CtxComma Γ (CtxBind x τ1)))
          (e2 ^^ x)
          τ2) →
      has_choice_type (plug_ctx Δ Γ) (tlete e1 e2) τ2

  (** T-LetD *)
  | CT_LetD Δ Γ Γ' τ1 τ2 e1 e2 (L : aset) :
      wf_choice_ty (plug_ctx Δ Γ) τ2 →
      has_choice_type Γ' e1 τ1 →
      ctx_to_over Γ Γ' →
      (∀ x, x ∉ L →
        has_choice_type
          (plug_ctx Δ (CtxStar Γ (CtxBind x τ1)))
          (e2 ^^ x)
          τ2) →
      has_choice_type (plug_ctx Δ Γ) (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      wf_choice_ty Γ (CTArrow τx τ) →
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
      wf_choice_ty Γ (CTWand τx τ) →
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
      wf_choice_ty Γ ({0 ~> x} τ) →
      has_choice_type Γ (tret v1) (CTArrow τx τ) →
      has_choice_type Γ (tret (vfvar x)) τx →
      has_choice_type Γ (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      wf_choice_ty (CtxStar Γ1 Γ2) ({0 ~> x} τ) →
      has_choice_type Γ1 (tret v1) (CTWand τx τ) →
      has_choice_type Γ2 (tret (vfvar x)) τx →
      has_choice_type (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-Fix *)
  | CT_Fix Γ τx τ vf (L : aset) :
      wf_choice_ty Γ (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_choice_type
          (CtxComma Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (CTArrow τx τ) ({0 ~> y} τ))) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTArrow τx τ)) vf))
        (CTArrow τx τ)

  (** T-FixD.  The paper refines the recursive argument with a decreasing
      predicate; the corresponding logic qualifier is still left abstract, so
      this constructor records the separating context structure. *)
  | CT_FixD Γ τx τ vf (L : aset) :
      wf_choice_ty Γ (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_choice_type
          (CtxStar Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTWand (CTWand τx τ) ({0 ~> y} τ))) →
      has_choice_type Γ
        (tret (vfix (erase_ty (CTWand τx τ)) vf))
        (CTWand τx τ)

  (** T-AppOp.  Primitive operations are unary. *)
  | CT_AppOp Γ op v arg_b ret_b :
      wf_choice_ty Γ (lift_ty (TBase ret_b)) →
      prim_op_type op = (arg_b, ret_b) →
      has_choice_type Γ (tret v) (lift_ty (TBase arg_b)) →
      has_choice_type Γ (tprim op v) (lift_ty (TBase ret_b))

  (** T-AppOpD.  Unary primitive operation in a separated argument context. *)
  | CT_AppOpD Γ1 Γ2 op v arg_b ret_b :
      wf_choice_ty (CtxStar Γ1 Γ2) (lift_ty (TBase ret_b)) →
      prim_op_type op = (arg_b, ret_b) →
      has_choice_type Γ2 (tret v) (lift_ty (TBase arg_b)) →
      has_choice_type (CtxStar Γ1 Γ2) (tprim op v) (lift_ty (TBase ret_b))

  (** T-Match.  The core match is a fixed boolean two-branch eliminator. *)
  | CT_Match Γ v τ et ef :
      wf_choice_ty Γ τ →
      has_choice_type Γ (tret v) (lift_ty (TBase TBool)) →
      has_choice_type Γ et τ →
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
