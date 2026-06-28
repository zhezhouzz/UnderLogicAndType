(** * ContextTyping.Typing

    Well-formedness predicates, auxiliary semantic relations, primitive
    operation signatures, and declarative typing rules for context types. *)

From CoreLang Require Import BasicTyping BasicTypingProps Sugar.
From ContextLogic Require Import FormulaSemantics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextTypeLanguage Require Import WF.
From ContextBasicDenotation Require Import BasicTypingFormula.
From Denotation Require Import Context.
From ContextTyping Require Import PrimOpContext.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).

(** * ContextTyping.WellFormed

    Paper-level well-formedness for context contexts and context types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  Semantic nonemptiness is not part of
    well-formedness: unsatisfiable contexts make the denotational soundness
    statement vacuous rather than unsound. *)


(** ** Context and type well-formedness *)

Definition wf_ctx_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  basic_ctx (dom Σ) Γ.

Definition wf_ctx (Γ : ctx) : Prop :=
  wf_ctx_under ∅ Γ.

Definition wf_context_ty (Γ : ctx) (τ : context_ty) : Prop :=
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ.

(** ** Semantic subtyping *)

Definition sub_type_under (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) : Prop :=
  wf_ctx_under Σ Γ ∧
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ1 ∧
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ2 ∧
  erase_ty τ1 = erase_ty τ2 ∧
  ∀ e, erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ1 →
    ctx_denote_under Σ Γ ⊫
      FImpl (ty_denote (erase_ctx Γ) τ1 e)
            (ty_denote (erase_ctx Γ) τ2 e).

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2) ∧
  ∀ r, r ⊨ ctx_denote_under Σ Γ1 →
       exists r',
         res_restrict r X ⊑ r' /\
         r' ⊨ ctx_denote_under Σ Γ2.

(** ** Typing well-formedness side condition *)

Definition context_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) : Prop :=
  wf_ctx_under Σ Γ /\
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ /\
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.

Definition branch_unreachable (Σ : gmap atom ty) (Γ : ctx) (v : value) (b : bool) : Prop :=
  ctx_denote_under Σ Γ ⊫
    FImpl (ty_denote (erase_ctx Γ) (bool_precise_ty b) (tret v)) FFalse.

(** The regular lemmas for these definitions live in [TypingRegular]. *)

Inductive has_context_type (Φ : primop_ctx) (Σ : gmap atom ty) : ctx → tm → context_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ →
      has_context_type Φ Σ
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) →
      has_context_type Φ Σ
        CtxEmpty
        (tret (vconst c))
        (const_precise_ty c)

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      context_typing_wf Σ Γ e τ2 →
      has_context_type Φ Σ Γ e τ1 →
      sub_type_under Σ Γ τ1 τ2 →
      has_context_type Φ Σ Γ e τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      context_typing_wf Σ Γ1 e τ →
      has_context_type Φ Σ Γ2 e τ →
      ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
      has_context_type Φ Σ Γ1 e τ

  (** T-PersistIntro.  Persistency introduction is value-only: arbitrary
      terms may have multiple possible results, while [ret v] exposes one
      result once the visible context resource is persistent. *)
  | CT_PersistIntro Γ v τ :
      context_typing_wf Σ Γ (tret v) (CTPersist τ) →
      persistent_formula (ctx_denote_under Σ Γ) →
      has_context_type Φ Σ Γ (tret v) τ →
      has_context_type Φ Σ Γ (tret v) (CTPersist τ)

  (** T-Let.  Standard additive/bunched let. *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      context_typing_wf Σ Γ (tlete e1 e2) τ2 →
      has_context_type Φ Σ Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_context_type Φ Σ
          (CtxComma Γ (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_context_type Φ Σ Γ (tlete e1 e2) τ2

  (** T-LetD.  Standard separating/bunched let. *)
  | CT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 →
      has_context_type Φ Σ Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_context_type Φ Σ
          (CtxStar Γ2 (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_context_type Φ Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_context_type Φ Σ
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_context_type Φ Σ Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow τx τ)

  (** T-LamD *)
  | CT_LamD Γ τx τ e (L : aset) :
      context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_context_type Φ Σ
          (CtxStar Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_context_type Φ Σ Γ
        (tret (vlam (erase_ty τx) e))
        (CTWand τx τ)

  (** T-AppFun *)
  | CT_AppFun Γ τx τ v1 x :
      context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ →
      has_context_type Φ Σ Γ (tret v1) (CTArrow τx τ) →
      has_context_type Φ Σ Γ (tret (vfvar x)) τx →
      has_context_type Φ Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ →
      has_context_type Φ Σ Γ1 (tret v1) (CTWand τx τ) →
      has_context_type Φ Σ Γ2 (tret (vfvar x)) τx →
      has_context_type Φ Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-Fix *)
  | CT_Fix Γ φx τ vf b t (L : aset) :
      erase_ty τ = t →
      context_typing_wf Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow (over_ty b φx) τ) →
      (∀ y, y ∉ L →
        has_context_type Φ Σ
          (CtxComma Γ
            (CtxBind y (over_ty b φx)))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) →
      has_context_type Φ Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow (over_ty b φx) τ)

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x :
      context_typing_wf Σ Γ
        (tprim op (vfvar x))
        ({0 ~> x} (primop_result_ty (Φ op))) →
      has_context_type Φ Σ Γ (tret (vfvar x)) (primop_arg_ty (Φ op)) →
      has_context_type Φ Σ Γ (tprim op (vfvar x)) ({0 ~> x} (primop_result_ty (Φ op)))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf x τt τf et ef :
      context_typing_wf Σ (CtxSum Γt Γf) (tmatch (vfvar x) et ef) (CTSum τt τf) →
      has_context_type Φ Σ Γt (tret (vfvar x)) (bool_precise_ty true) →
      has_context_type Φ Σ Γf (tret (vfvar x)) (bool_precise_ty false) →
      has_context_type Φ Σ Γt et τt →
      has_context_type Φ Σ Γf ef τf →
      has_context_type Φ Σ (CtxSum Γt Γf) (tmatch (vfvar x) et ef) (CTSum τt τf)

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ x τ et ef :
      context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ →
      has_context_type Φ Σ Γ (tret (vfvar x)) (bool_precise_ty true) →
      has_context_type Φ Σ Γ et τ →
      has_context_type Φ Σ Γ (tmatch (vfvar x) et ef) τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ x τ et ef :
      context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ →
      has_context_type Φ Σ Γ (tret (vfvar x)) (bool_precise_ty false) →
      has_context_type Φ Σ Γ ef τ →
      has_context_type Φ Σ Γ (tmatch (vfvar x) et ef) τ.

#[global] Hint Constructors has_context_type : core.
