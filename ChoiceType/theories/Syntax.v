(** * ChoiceType.Syntax

    Choice types [τ] and type contexts [Γ] (Fig. 2 of the paper).
    Also provides type erasure [erase_ty], type lifting [lift_ty],
    and the [Stale]/[Subst]/[SubstM] typeclass instances needed for
    the LN infrastructure on qualifiers inside types. *)

From ChoiceType Require Export Qualifier.

(** ** Choice types *)

Inductive choice_ty : Type :=
  (** Overapproximation refinement type: {ν:b | φ} *)
  | CTOver  (b : base_ty) (φ : type_qualifier)
  (** Underapproximation refinement type: [ν:b | φ] *)
  | CTUnder (b : base_ty) (φ : type_qualifier)
  (** Intersection / meet *)
  | CTInter (τ1 τ2 : choice_ty)
  (** Union / join *)
  | CTUnion (τ1 τ2 : choice_ty)
  (** Choice sum (⊕) — mirrors resource sum *)
  | CTSum   (τ1 τ2 : choice_ty)
  (** Dependent function type: x:τ_x → τ *)
  | CTArrow (x : atom) (τx τ : choice_ty)
  (** Dependent separating function type: x:τ_x ⊸ τ *)
  | CTWand  (x : atom) (τx τ : choice_ty).

(** ** Type contexts *)

Inductive ctx : Type :=
  | CtxEmpty
  | CtxBind  (x : atom) (τ : choice_ty)
  | CtxComma (Γ1 Γ2 : ctx)   (** Γ,Γ  additive / comma bunching *)
  | CtxStar  (Γ1 Γ2 : ctx)   (** Γ∗Γ  multiplicative / star bunching *)
  | CtxSum   (Γ1 Γ2 : ctx).  (** Γ⊕Γ  context choice / splitting *)

(** Contexts with holes [Δ] from the paper.  [plug_ctx Δ Γ] denotes
    Δ(Γ).  The [CtxHoleCtx] case lets a raw context appear as a leaf inside
    a context-with-hole expression. *)
Inductive ctx_hole : Type :=
  | CtxHole
  | CtxHoleCtx   (Γ : ctx)
  | CtxHoleComma (Δ1 Δ2 : ctx_hole)
  | CtxHoleStar  (Δ1 Δ2 : ctx_hole)
  | CtxHoleSum   (Δ1 Δ2 : ctx_hole).

Fixpoint plug_ctx (Δ : ctx_hole) (Γ : ctx) : ctx :=
  match Δ with
  | CtxHole             => Γ
  | CtxHoleCtx Γ0       => Γ0
  | CtxHoleComma Δ1 Δ2  => CtxComma (plug_ctx Δ1 Γ) (plug_ctx Δ2 Γ)
  | CtxHoleStar  Δ1 Δ2  => CtxStar  (plug_ctx Δ1 Γ) (plug_ctx Δ2 Γ)
  | CtxHoleSum   Δ1 Δ2  => CtxSum   (plug_ctx Δ1 Γ) (plug_ctx Δ2 Γ)
  end.

(** ** Domain (free variables from binders) *)

Fixpoint ctx_dom (Γ : ctx) : aset :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x _    => {[ x ]}
  | CtxComma Γ1 Γ2 => ctx_dom Γ1 ∪ ctx_dom Γ2
  | CtxStar  Γ1 Γ2 => ctx_dom Γ1 ∪ ctx_dom Γ2
  | CtxSum   Γ1 Γ2 => ctx_dom Γ1 ∪ ctx_dom Γ2
  end.

(** ** Well-formedness

    The paper keeps well-formedness separate from raw syntax.  We mirror that
    split here: raw [choice_ty] and [ctx] remain convenient inductive syntax,
    while these predicates record the invariants needed for paper-level
    objects.  In particular, binary type constructors only combine types with
    the same erased type, and context choice [CtxSum] combines branches with
    the same erased context shape. *)

Inductive wf_choice_ty : choice_ty → Prop :=
  | Wf_CTOver b φ :
      lc_qualifier φ →
      wf_choice_ty (CTOver b φ)
  | Wf_CTUnder b φ :
      lc_qualifier φ →
      wf_choice_ty (CTUnder b φ)
  | Wf_CTInter τ1 τ2 :
      wf_choice_ty τ1 →
      wf_choice_ty τ2 →
      erase_ty τ1 = erase_ty τ2 →
      wf_choice_ty (CTInter τ1 τ2)
  | Wf_CTUnion τ1 τ2 :
      wf_choice_ty τ1 →
      wf_choice_ty τ2 →
      erase_ty τ1 = erase_ty τ2 →
      wf_choice_ty (CTUnion τ1 τ2)
  | Wf_CTSum τ1 τ2 :
      wf_choice_ty τ1 →
      wf_choice_ty τ2 →
      erase_ty τ1 = erase_ty τ2 →
      wf_choice_ty (CTSum τ1 τ2)
  | Wf_CTArrow x τx τ :
      wf_choice_ty τx →
      wf_choice_ty τ →
      wf_choice_ty (CTArrow x τx τ)
  | Wf_CTWand x τx τ :
      wf_choice_ty τx →
      wf_choice_ty τ →
      wf_choice_ty (CTWand x τx τ).

Inductive wf_ctx : ctx → Prop :=
  | Wf_CtxEmpty :
      wf_ctx CtxEmpty
  | Wf_CtxBind x τ :
      wf_choice_ty τ →
      wf_ctx (CtxBind x τ)
  | Wf_CtxComma Γ1 Γ2 :
      wf_ctx Γ1 →
      wf_ctx Γ2 →
      ctx_dom Γ1 ## ctx_dom Γ2 →
      wf_ctx (CtxComma Γ1 Γ2)
  | Wf_CtxStar Γ1 Γ2 :
      wf_ctx Γ1 →
      wf_ctx Γ2 →
      ctx_dom Γ1 ## ctx_dom Γ2 →
      wf_ctx (CtxStar Γ1 Γ2)
  | Wf_CtxSum Γ1 Γ2 :
      wf_ctx Γ1 →
      wf_ctx Γ2 →
      ctx_dom Γ1 = ctx_dom Γ2 →
      erase_ctx Γ1 = erase_ctx Γ2 →
      wf_ctx (CtxSum Γ1 Γ2).

#[global] Hint Constructors wf_choice_ty wf_ctx : core.

(** ** Substitution on types (apply single variable substitution to qualifiers) *)

Fixpoint cty_subst_one (x : atom) (v : value) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver  b φ     => CTOver  b (qual_subst_one x v φ)
  | CTUnder b φ     => CTUnder b (qual_subst_one x v φ)
  | CTInter τ1 τ2   => CTInter (cty_subst_one x v τ1) (cty_subst_one x v τ2)
  | CTUnion τ1 τ2   => CTUnion (cty_subst_one x v τ1) (cty_subst_one x v τ2)
  | CTSum   τ1 τ2   => CTSum   (cty_subst_one x v τ1) (cty_subst_one x v τ2)
  | CTArrow y τx τ  => CTArrow y (cty_subst_one x v τx)
                          (if decide (x = y) then τ else cty_subst_one x v τ)
  | CTWand y τx τ   => CTWand y (cty_subst_one x v τx)
                          (if decide (x = y) then τ else cty_subst_one x v τ)
  end.

Fixpoint cty_subst (σ : Store) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver  b φ     => CTOver  b (qual_subst σ φ)
  | CTUnder b φ     => CTUnder b (qual_subst σ φ)
  | CTInter τ1 τ2   => CTInter (cty_subst σ τ1) (cty_subst σ τ2)
  | CTUnion τ1 τ2   => CTUnion (cty_subst σ τ1) (cty_subst σ τ2)
  | CTSum   τ1 τ2   => CTSum   (cty_subst σ τ1) (cty_subst σ τ2)
  | CTArrow x τx τ  => CTArrow x (cty_subst σ τx) (cty_subst (delete x σ) τ)
  | CTWand x τx τ   => CTWand x (cty_subst σ τx) (cty_subst (delete x σ) τ)
  end.

#[global] Instance subst_cty_inst  : SubstV value choice_ty   := cty_subst_one.
#[global] Instance substM_cty_inst : SubstM Store choice_ty := cty_subst.
Arguments subst_cty_inst /.
Arguments substM_cty_inst /.

(** ** Type aliases and notation *)

Notation "x ':' τx '→,' τ" := (CTArrow x τx τ)
  (at level 30, x constr, τx constr, right associativity).
Notation "x ':' τx '⊸' τ" := (CTWand x τx τ)
  (at level 30, x constr, τx constr, right associativity).

(** Non-dependent arrow: τ1 →, τ2  when x ∉ fv_cty τ2 *)
Notation "τ1 '→,' τ2" := (CTArrow (fresh_for (fv_cty τ1 ∪ fv_cty τ2)) τ1 τ2)
  (at level 30, right associativity).

(** Affine type: τ_aff ≝ τ ⊕ lift(erase(τ))
    (adds the "discard" branch for use-once semantics) *)
Definition cty_aff (τ : choice_ty) : choice_ty :=
  CTSum τ (lift_ty (erase_ty τ)).
Notation "τ '_aff'" := (cty_aff τ) (at level 5).

(** Coercion: base type as the default over-refinement. *)
Coercion lift_ty : ty >-> choice_ty.
