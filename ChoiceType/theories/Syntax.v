(** * ChoiceType.Syntax

    Choice types [τ] and type contexts [Γ] (Fig. 2 of the paper).
    Also provides type erasure [erase_ty], type lifting [lift_ty],
    and the [Stale]/[Subst]/[SubstM] typeclass instances needed for
    the LN infrastructure on qualifiers inside types. *)

From ChoiceType Require Export Qualifier.

(** ** Choice types *)

Inductive choice_ty : Type :=
  (** Overapproximation refinement type: {ν:b | φ} *)
  | CTOver  (b : base_ty) (φ : qualifier)
  (** Underapproximation refinement type: [ν:b | φ] *)
  | CTUnder (b : base_ty) (φ : qualifier)
  (** Intersection / meet *)
  | CTInter (τ1 τ2 : choice_ty)
  (** Union / join *)
  | CTUnion (τ1 τ2 : choice_ty)
  (** Choice sum (⊕) — mirrors resource sum *)
  | CTSum   (τ1 τ2 : choice_ty)
  (** Dependent function type: x:τ_x →, τ   (additive / comma mode) *)
  | CTArrow (x : atom) (τx τ : choice_ty)
  (** Separating / wand function type: x:τ_x ⊗ τ  (star mode) *)
  | CTWand  (x : atom) (τx τ : choice_ty)
  (** Separability modality: ∗τ *)
  | CTStar  (τ : choice_ty)
  (** Persistence modality: □τ *)
  | CTPers  (τ : choice_ty).

(** ** Type contexts *)

Inductive ctx : Type :=
  | CtxEmpty
  | CtxBind  (x : atom) (τ : choice_ty)
  | CtxComma (Γ1 Γ2 : ctx)   (** Γ,Γ  additive / comma bunching *)
  | CtxStar  (Γ1 Γ2 : ctx).  (** Γ∗Γ  multiplicative / star bunching *)

(** ** Type erasure and lifting *)

(** [erase_ty τ] : the basic type underlying τ (Definition Fig. 2). *)
Fixpoint erase_ty (τ : choice_ty) : ty :=
  match τ with
  | CTOver  b _     => TBase b
  | CTUnder b _     => TBase b
  | CTInter τ1 _    => erase_ty τ1
  | CTUnion τ1 _    => erase_ty τ1
  | CTSum   τ1 _    => erase_ty τ1
  | CTArrow _ τx τ  => erase_ty τx →ₜ erase_ty τ
  | CTWand  _ τx τ  => erase_ty τx →ₜ erase_ty τ
  | CTStar  τ       => erase_ty τ
  | CTPers  τ       => erase_ty τ
  end.

(** [lift_ty s] : lift a basic type to the default over-refinement type. *)
Fixpoint lift_ty (s : ty) : choice_ty :=
  match s with
  | TBase b        => CTOver b qual_top   (** {ν:b | ⊤} *)
  | TArrow s1 s2   =>
      let x := fresh_for ∅ in
      CTArrow x (lift_ty s1) (lift_ty s2)
  end.

(** [erase_ctx Γ] : the basic context underlying Γ. *)
Fixpoint erase_ctx (Γ : ctx) : gmap atom ty :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x τ    => {[ x := erase_ty τ ]}
  | CtxComma Γ1 Γ2 => erase_ctx Γ1 ∪ erase_ctx Γ2
  | CtxStar  Γ1 Γ2 => erase_ctx Γ1 ∪ erase_ctx Γ2
  end.

(** [lift_ctx Γ_basic] : lift a basic context. *)
Definition lift_ctx (Γ : gmap atom ty) : ctx :=
  map_fold (fun x s acc => CtxComma (CtxBind x (lift_ty s)) acc) CtxEmpty Γ.

(** ** Domain (free variables from binders) *)

Fixpoint ctx_dom (Γ : ctx) : aset :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x _    => {[ x ]}
  | CtxComma Γ1 Γ2 => ctx_dom Γ1 ∪ ctx_dom Γ2
  | CtxStar  Γ1 Γ2 => ctx_dom Γ1 ∪ ctx_dom Γ2
  end.

(** ** Free variables in types and contexts *)

Fixpoint fv_cty (τ : choice_ty) : aset :=
  match τ with
  | CTOver  _ φ     => qual_fv φ
  | CTUnder _ φ     => qual_fv φ
  | CTInter τ1 τ2   => fv_cty τ1 ∪ fv_cty τ2
  | CTUnion τ1 τ2   => fv_cty τ1 ∪ fv_cty τ2
  | CTSum   τ1 τ2   => fv_cty τ1 ∪ fv_cty τ2
  | CTArrow x τx τ  => fv_cty τx ∪ (fv_cty τ ∖ {[ x ]})
  | CTWand  x τx τ  => fv_cty τx ∪ (fv_cty τ ∖ {[ x ]})
  | CTStar  τ       => fv_cty τ
  | CTPers  τ       => fv_cty τ
  end.

Fixpoint fv_ctx (Γ : ctx) : aset :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x τ    => fv_cty τ          (** x itself is a binder, not free *)
  | CtxComma Γ1 Γ2 => fv_ctx Γ1 ∪ fv_ctx Γ2
  | CtxStar  Γ1 Γ2 => fv_ctx Γ1 ∪ fv_ctx Γ2
  end.

#[global] Instance stale_cty_inst : Stale choice_ty := fv_cty.
#[global] Instance stale_ctx_inst : Stale ctx       := fv_ctx.
Arguments stale_cty_inst /.
Arguments stale_ctx_inst /.

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
  | CTWand  y τx τ  => CTWand  y (cty_subst_one x v τx)
                          (if decide (x = y) then τ else cty_subst_one x v τ)
  | CTStar  τ       => CTStar  (cty_subst_one x v τ)
  | CTPers  τ       => CTPers  (cty_subst_one x v τ)
  end.

Fixpoint cty_subst (σ : SubstT) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver  b φ     => CTOver  b (qual_subst σ φ)
  | CTUnder b φ     => CTUnder b (qual_subst σ φ)
  | CTInter τ1 τ2   => CTInter (cty_subst σ τ1) (cty_subst σ τ2)
  | CTUnion τ1 τ2   => CTUnion (cty_subst σ τ1) (cty_subst σ τ2)
  | CTSum   τ1 τ2   => CTSum   (cty_subst σ τ1) (cty_subst σ τ2)
  | CTArrow x τx τ  => CTArrow x (cty_subst σ τx) (cty_subst (delete x σ) τ)
  | CTWand  x τx τ  => CTWand  x (cty_subst σ τx) (cty_subst (delete x σ) τ)
  | CTStar  τ       => CTStar  (cty_subst σ τ)
  | CTPers  τ       => CTPers  (cty_subst σ τ)
  end.

#[global] Instance subst_cty_inst  : SubstV value choice_ty   := cty_subst_one.
#[global] Instance substM_cty_inst : SubstM SubstT choice_ty := cty_subst.
Arguments subst_cty_inst /.
Arguments substM_cty_inst /.

(** ** Type aliases and notation *)

(** Wand type is syntax sugar: x:τx ⊸ τ  ≝  x:(∗τx) →, τ *)
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
