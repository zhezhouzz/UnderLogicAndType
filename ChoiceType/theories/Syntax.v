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
  (** Dependent function type: τ_x → τ, with bvar 0 in τ bound to the argument *)
  | CTArrow (τx τ : choice_ty)
  (** Dependent separating function type: τ_x ⊸ τ, with bvar 0 in τ bound to the argument *)
  | CTWand  (τx τ : choice_ty).

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

(** ** Free variables in types and contexts *)

Fixpoint fv_cty (τ : choice_ty) : aset :=
match τ with
| CTOver  _ φ     => qual_fv φ
| CTUnder _ φ     => qual_fv φ
| CTInter τ1 τ2   => fv_cty τ1 ∪ fv_cty τ2
| CTUnion τ1 τ2   => fv_cty τ1 ∪ fv_cty τ2
| CTSum   τ1 τ2   => fv_cty τ1 ∪ fv_cty τ2
| CTArrow τx τ    => fv_cty τx ∪ fv_cty τ
| CTWand  τx τ    => fv_cty τx ∪ fv_cty τ
end.

Fixpoint ctx_fv (Γ : ctx) : aset :=
match Γ with
| CtxEmpty        => ∅
| CtxBind x τ    => {[x]} ∪ fv_cty τ
| CtxComma Γ1 Γ2 => ctx_fv Γ1 ∪ ctx_fv Γ2
| CtxStar  Γ1 Γ2 => ctx_fv Γ1 ∪ ctx_fv Γ2
| CtxSum   Γ1 Γ2 => ctx_fv Γ1 ∪ ctx_fv Γ2
end.

#[global] Instance stale_cty_inst : Stale choice_ty := fv_cty.
#[global] Instance stale_ctx_inst : Stale ctx       := ctx_fv.
Arguments stale_cty_inst /.
Arguments stale_ctx_inst /.

(** ** Locally nameless operations on choice types *)

Fixpoint cty_open (k : nat) (v : value) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver  b φ     => CTOver  b ({k ~> v} φ)
  | CTUnder b φ     => CTUnder b ({k ~> v} φ)
  | CTInter τ1 τ2   => CTInter (cty_open k v τ1) (cty_open k v τ2)
  | CTUnion τ1 τ2   => CTUnion (cty_open k v τ1) (cty_open k v τ2)
  | CTSum   τ1 τ2   => CTSum   (cty_open k v τ1) (cty_open k v τ2)
  | CTArrow τx τ    => CTArrow (cty_open k v τx) (cty_open (S k) v τ)
  | CTWand  τx τ    => CTWand  (cty_open k v τx) (cty_open (S k) v τ)
  end.

Fixpoint cty_close (x : atom) (k : nat) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver  b φ     => CTOver  b ({k <~ x} φ)
  | CTUnder b φ     => CTUnder b ({k <~ x} φ)
  | CTInter τ1 τ2   => CTInter (cty_close x k τ1) (cty_close x k τ2)
  | CTUnion τ1 τ2   => CTUnion (cty_close x k τ1) (cty_close x k τ2)
  | CTSum   τ1 τ2   => CTSum   (cty_close x k τ1) (cty_close x k τ2)
  | CTArrow τx τ    => CTArrow (cty_close x k τx) (cty_close x (S k) τ)
  | CTWand  τx τ    => CTWand  (cty_close x k τx) (cty_close x (S k) τ)
  end.

#[global] Instance open_cty_inst : Open value choice_ty := cty_open.
#[global] Instance open_cty_atom_inst : Open atom choice_ty :=
  fun k x => cty_open k (vfvar x).
#[global] Instance close_cty_inst : Close choice_ty := cty_close.
Arguments open_cty_inst /.
Arguments open_cty_atom_inst /.
Arguments close_cty_inst /.

Inductive lc_choice_ty : choice_ty → Prop :=
  | LC_CTOver b φ :
      lc_qualifier φ →
      lc_choice_ty (CTOver b φ)
  | LC_CTUnder b φ :
      lc_qualifier φ →
      lc_choice_ty (CTUnder b φ)
  | LC_CTInter τ1 τ2 :
      lc_choice_ty τ1 →
      lc_choice_ty τ2 →
      lc_choice_ty (CTInter τ1 τ2)
  | LC_CTUnion τ1 τ2 :
      lc_choice_ty τ1 →
      lc_choice_ty τ2 →
      lc_choice_ty (CTUnion τ1 τ2)
  | LC_CTSum τ1 τ2 :
      lc_choice_ty τ1 →
      lc_choice_ty τ2 →
      lc_choice_ty (CTSum τ1 τ2)
  | LC_CTArrow τx τ (L : aset) :
      lc_choice_ty τx →
      (∀ x, x ∉ L → lc_choice_ty ({0 ~> vfvar x} τ)) →
      lc_choice_ty (CTArrow τx τ)
  | LC_CTWand τx τ (L : aset) :
      lc_choice_ty τx →
      (∀ x, x ∉ L → lc_choice_ty ({0 ~> vfvar x} τ)) →
      lc_choice_ty (CTWand τx τ).

#[global] Instance lc_cty_inst : Lc choice_ty := lc_choice_ty.
Arguments lc_cty_inst /.
#[global] Hint Constructors lc_choice_ty : core.

Definition body_cty (τ : choice_ty) : Prop :=
  ∃ L : aset, ∀ x : atom, x ∉ L → lc_choice_ty ({0 ~> vfvar x} τ).

(** ** Type erasure and lifting *)

(** [erase_ty τ] : the basic type underlying τ (Definition Fig. 2). *)
Fixpoint erase_ty (τ : choice_ty) : ty :=
  match τ with
  | CTOver  b _     => TBase b
  | CTUnder b _     => TBase b
  | CTInter τ1 _    => erase_ty τ1
  | CTUnion τ1 _    => erase_ty τ1
  | CTSum   τ1 _    => erase_ty τ1
  | CTArrow τx τ    => erase_ty τx →ₜ erase_ty τ
  | CTWand  τx τ    => erase_ty τx →ₜ erase_ty τ
  end.

(** [lift_ty s] : lift a basic type to the default over-refinement type. *)
Fixpoint lift_ty (s : ty) : choice_ty :=
  match s with
  | TBase b        => CTOver b qual_top   (** {ν:b | ⊤} *)
  | TArrow s1 s2   =>
      let τ1 := lift_ty s1 in
      let τ2 := lift_ty s2 in
      CTArrow τ1 τ2
  end.

(** [erase_ctx Γ] : the basic context underlying Γ. *)
Fixpoint erase_ctx (Γ : ctx) : gmap atom ty :=
  match Γ with
  | CtxEmpty        => ∅
  | CtxBind x τ    => {[ x := erase_ty τ ]}
  | CtxComma Γ1 Γ2 => erase_ctx Γ1 ∪ erase_ctx Γ2
  | CtxStar  Γ1 Γ2 => erase_ctx Γ1 ∪ erase_ctx Γ2
  | CtxSum   Γ1 _  => erase_ctx Γ1
  end.

(** [lift_ctx Γ_basic] : lift a basic context. *)
Definition lift_ctx (Γ : gmap atom ty) : ctx :=
  map_fold (fun x s acc => CtxComma (CtxBind x (lift_ty s)) acc) CtxEmpty Γ.

(** ** Context binder domain *)

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
  | Wf_CTArrow τx τ (L : aset) :
      wf_choice_ty τx →
      (∀ x, x ∉ L → wf_choice_ty ({0 ~> vfvar x} τ)) →
      wf_choice_ty (CTArrow τx τ)
  | Wf_CTWand τx τ (L : aset) :
      wf_choice_ty τx →
      (∀ x, x ∉ L → wf_choice_ty ({0 ~> vfvar x} τ)) →
      wf_choice_ty (CTWand τx τ).

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
  | CTArrow τx τ    => CTArrow (cty_subst_one x v τx) (cty_subst_one x v τ)
  | CTWand τx τ     => CTWand  (cty_subst_one x v τx) (cty_subst_one x v τ)
  end.

Fixpoint cty_subst (σ : Store) (τ : choice_ty) : choice_ty :=
  match τ with
  | CTOver  b φ     => CTOver  b (qual_subst σ φ)
  | CTUnder b φ     => CTUnder b (qual_subst σ φ)
  | CTInter τ1 τ2   => CTInter (cty_subst σ τ1) (cty_subst σ τ2)
  | CTUnion τ1 τ2   => CTUnion (cty_subst σ τ1) (cty_subst σ τ2)
  | CTSum   τ1 τ2   => CTSum   (cty_subst σ τ1) (cty_subst σ τ2)
  | CTArrow τx τ    => CTArrow (cty_subst σ τx) (cty_subst σ τ)
  | CTWand τx τ     => CTWand  (cty_subst σ τx) (cty_subst σ τ)
  end.

#[global] Instance subst_cty_inst  : SubstV value choice_ty   := cty_subst_one.
#[global] Instance substM_cty_inst : SubstM Store choice_ty := cty_subst.
Arguments subst_cty_inst /.
Arguments substM_cty_inst /.

(** ** Type aliases and notation *)

Notation "x ':' τx '→,' τ" := (CTArrow τx ({0 <~ x} τ))
  (at level 30, x constr, τx constr, right associativity).
Notation "x ':' τx '⊸' τ" := (CTWand τx ({0 <~ x} τ))
  (at level 30, x constr, τx constr, right associativity).

(** Non-dependent arrow: τ1 →, τ2  when x ∉ fv_cty τ2 *)
Notation "τ1 '→,' τ2" := (CTArrow τ1 τ2)
  (at level 30, right associativity).

(** Affine type: τ_aff ≝ τ ⊕ lift(erase(τ))
    (adds the "discard" branch for use-once semantics) *)
Definition cty_aff (τ : choice_ty) : choice_ty :=
  CTSum τ (lift_ty (erase_ty τ)).
Notation "τ '_aff'" := (cty_aff τ) (at level 5).

(** Coercion: base type as the default over-refinement. *)
Coercion lift_ty : ty >-> choice_ty.
