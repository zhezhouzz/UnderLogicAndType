(** * ContextTyping.Typing

    Well-formedness predicates, auxiliary semantic relations, primitive
    operation signatures, and declarative typing rules for context types. *)

From CoreLang Require Import BasicTyping BasicTypingProps Sugar.
From ContextLogic Require Import FormulaSemantics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextTypeLanguage Require Import WF.
From ContextBasicDenotation Require Import BasicTypingFormula.
From Denotation Require Import Context TypeDenote.
From ContextTyping Require Import PrimOpContext.

Local Notation WorldT := (World (V := value)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := value)) (only parsing).

Open Scope ctx_scope.

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
  wf_context_ty_at 0 (dom (⌊Γ⌋)%ctx) τ.

(** ** Semantic subtyping *)

Definition sub_type_under (Σ : gmap atom ty) (Γ : ctx) (τ1 τ2 : context_ty) : Prop :=
  let Δ := (⌊Γ⌋)%ctx in
  wf_ctx_under Σ Γ ∧
  wf_context_ty_at 0 (dom Δ) τ1 ∧
  wf_context_ty_at 0 (dom Δ) τ2 ∧
  (⌊τ1⌋)%cty = (⌊τ2⌋)%cty ∧
    ∀ e, Δ ⊢ₑ e ⋮ (⌊τ1⌋)%cty ->
    ⟦ctx Γ⟧[Σ] ⊫
      (TyDenote[Δ; τ1; e] → TyDenote[Δ; τ2; e])%formula.

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (⌊Γ1⌋)%ctx (⌊Γ2⌋)%ctx ∧
  ∀ r, r ⊨ ⟦ctx Γ1⟧[Σ] ->
       exists r',
         res_restrict r X ⊑ r' /\
         r' ⊨ ⟦ctx Γ2⟧[Σ].

(** ** Typing well-formedness side condition *)

Definition context_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) : Prop :=
  wf_ctx_under Σ Γ /\
  wf_context_ty_at 0 (dom (⌊Γ⌋)%ctx) τ /\
  (⌊Γ⌋)%ctx ⊢ₑ e ⋮ (⌊τ⌋)%cty.

Definition branch_unreachable (Σ : gmap atom ty) (Γ : ctx) (v : value) (b : bool) : Prop :=
  let Δ := (⌊Γ⌋)%ctx in
  ⟦ctx Γ⟧[Σ] ⊫
    (TyDenote[Δ; bool_precise_ty b; (ret v)%core] → ⊥)%formula.

(** The regular lemmas for these definitions live in [TypingRegular]. *)

Notation "Γ '⊢wf[' Σ ']' e '⋮' τ" :=
  (context_typing_wf Σ Γ e τ)
  (at level 40, Σ at level 200,
   e at level 200, τ at level 200).

Notation "Γ '⊢ᶜ' τ1 '≤[' Σ ']' τ2" :=
  (sub_type_under Σ Γ τ1 τ2)
  (at level 40, Σ at level 200,
   τ1 at level 200, τ2 at level 200).

Notation "Γ1 '≤ᶜ[' Σ ';' X ']' Γ2" :=
  (ctx_sub_under Σ X Γ1 Γ2)
  (at level 40, Σ at level 200, X at level 200,
   Γ2 at level 200).

Notation "'unreachable[' Σ ';' Γ ']' v '@' b" :=
  (branch_unreachable Σ Γ v b)
  (at level 40, Σ at level 200, Γ at level 200,
   v at level 200, b at level 200).

Reserved Notation "Γ '⊢ᶜ' '[' Φ ';' Σ ']' e '⋮' τ"
  (at level 40, Φ at level 200, Σ at level 200,
   e at level 200, τ at level 200).

Inductive has_context_type (Φ : primop_ctx) (Σ : gmap atom ty) : ctx -> tm -> context_ty -> Prop :=

  (** T-Var *)
  | CT_Var x τ :
      ((x ∷ τ) ⊢wf[Σ] (ret (vfvar x))%core ⋮ τ) ->
      (x ∷ τ) ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      (Emp ⊢wf[Σ] (ret (vconst c))%core ⋮ (const_precise_ty c)) ->
      Emp ⊢ᶜ [Φ; Σ] (ret (vconst c))%core ⋮ const_precise_ty c

  (** T-Sub *)
  | CT_Sub Γ e (τ1 τ2 : context_ty) :
      (Γ ⊢wf[Σ] e ⋮ τ2) ->
      (Γ ⊢ᶜ [Φ; Σ] e ⋮ τ1) ->
      (Γ ⊢ᶜ τ1 ≤[Σ] τ2) ->
      Γ ⊢ᶜ [Φ; Σ] e ⋮ τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      (Γ1 ⊢wf[Σ] e ⋮ τ) ->
      (Γ2 ⊢ᶜ [Φ; Σ] e ⋮ τ) ->
      (Γ1 ≤ᶜ[Σ; (fv_tm e ∪ fv_cty τ)] Γ2) ->
      Γ1 ⊢ᶜ [Φ; Σ] e ⋮ τ

  (** T-PersistIntro.  Persistency introduction is value-only: arbitrary
      terms may have multiple possible results, while [ret v] exposes one
      result once the visible context resource is persistent. *)
  | CT_PersistIntro Γ v τ :
      (Γ ⊢wf[Σ] (ret v)%core ⋮ (□ τ)%cty) ->
      persistent_formula (ctx_denote_under Σ Γ) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret v)%core ⋮ τ) ->
      Γ ⊢ᶜ [Φ; Σ] (ret v)%core ⋮ (□ τ)%cty

  (** T-Let.  Standard additive/bunched let. *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      (Γ ⊢wf[Σ] (let: e1 in e2)%core ⋮ τ2) ->
      (Γ ⊢ᶜ [Φ; Σ] e1 ⋮ τ1) ->
      (∀ x, x ∉ L ->
        ((Γ ,, (x ∷ τ1)) ⊢ᶜ [Φ; Σ] (e2 ^^ x) ⋮ τ2)) ->
      Γ ⊢ᶜ [Φ; Σ] (let: e1 in e2)%core ⋮ τ2

  (** T-LetD.  Standard separating/bunched let. *)
  | CT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      ((Γ1 ∗ Γ2) ⊢wf[Σ] (let: e1 in e2)%core ⋮ τ2) ->
      (Γ1 ⊢ᶜ [Φ; Σ] e1 ⋮ τ1) ->
      (∀ x, x ∉ L ->
        ((Γ2 ∗ (x ∷ τ1)) ⊢ᶜ [Φ; Σ] (e2 ^^ x) ⋮ τ2)) ->
      (Γ1 ∗ Γ2) ⊢ᶜ [Φ; Σ] (let: e1 in e2)%core ⋮ τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      (Γ ⊢wf[Σ] (ret (λ: (⌊τx⌋)%cty, e))%core ⋮ (τx → τ)%cty) ->
      (∀ y, y ∉ L ->
        ((Γ ,, (y ∷ τx)) ⊢ᶜ [Φ; Σ] (e ^^ y) ⋮ ({0 ~> y} τ))) ->
      Γ ⊢ᶜ [Φ; Σ]
        (ret (λ: (⌊τx⌋)%cty, e))%core ⋮
        (τx → τ)%cty

  (** T-LamD *)
  | CT_LamD Γ τx τ e (L : aset) :
      (Γ ⊢wf[Σ] (ret (λ: (⌊τx⌋)%cty, e))%core ⋮ (τx -∗ τ)%cty) ->
      (∀ y, y ∉ L ->
        ((Γ ∗ (y ∷ τx)) ⊢ᶜ [Φ; Σ] (e ^^ y) ⋮ ({0 ~> y} τ))) ->
      Γ ⊢ᶜ [Φ; Σ]
        (ret (λ: (⌊τx⌋)%cty, e))%core ⋮
        (τx -∗ τ)%cty

  (** T-AppFun *)
  | CT_AppFun Γ τx τ v1 x :
      (Γ ⊢wf[Σ] (v1 · vfvar x)%core ⋮ ({0 ~> x} τ)) ->
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
      (Γ ⊢ᶜ [Φ; Σ] (ret v1)%core ⋮ (τx → τ)%cty) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τx) ->
      Γ ⊢ᶜ [Φ; Σ] (v1 · vfvar x)%core ⋮ {0 ~> x} τ

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      ((Γ1 ∗ Γ2) ⊢wf[Σ] (v1 · vfvar x)%core ⋮ ({0 ~> x} τ)) ->
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ ->
      (Γ1 ⊢ᶜ [Φ; Σ] (ret v1)%core ⋮ (τx -∗ τ)%cty) ->
      (Γ2 ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ τx) ->
      (Γ1 ∗ Γ2) ⊢ᶜ [Φ; Σ] (v1 · vfvar x)%core ⋮ {0 ~> x} τ

  (** T-Fix *)
  | CT_Fix Γ φx τ vf b t (L : aset) :
      (⌊τ⌋)%cty = t ->
      (Γ ⊢wf[Σ]
        (ret (fix: (TBase b →ₜ t), vf))%core
        ⋮ (over_ty b φx → τ)%cty) ->
      (∀ y, y ∉ L ->
        ((Γ ,, (y ∷ over_ty b φx)) ⊢ᶜ [Φ; Σ]
          (ret ({0 ~> vfvar y} vf))%core
          ⋮ (fix_rec_call_ty b y (over_ty b φx) τ → {0 ~> y} τ)%cty)) ->
      Γ ⊢ᶜ [Φ; Σ]
        (ret (fix: (TBase b →ₜ t), vf))%core ⋮
        (over_ty b φx → τ)%cty

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x :
      (Γ ⊢wf[Σ]
        (tprim op (vfvar x))
        ⋮ ({0 ~> x} (primop_result_ty (Φ op)))) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ primop_arg_ty (Φ op)) ->
      Γ ⊢ᶜ [Φ; Σ] (tprim op (vfvar x)) ⋮ ({0 ~> x} (primop_result_ty (Φ op)))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf x τt τf et ef :
      ((Γt ⊕ Γf) ⊢wf[Σ] (if vfvar x then et else ef)%core ⋮ (τt ⊕ τf)%cty) ->
      (Γt ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty true) ->
      (Γf ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty false) ->
      (Γt ⊢ᶜ [Φ; Σ] et ⋮ τt) ->
      (Γf ⊢ᶜ [Φ; Σ] ef ⋮ τf) ->
      (Γt ⊕ Γf) ⊢ᶜ [Φ; Σ] (if vfvar x then et else ef)%core ⋮ (τt ⊕ τf)%cty

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ x τ et ef :
      (Γ ⊢wf[Σ] (if vfvar x then et else ef)%core ⋮ τ) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty true) ->
      (Γ ⊢ᶜ [Φ; Σ] et ⋮ τ) ->
      Γ ⊢ᶜ [Φ; Σ] (if vfvar x then et else ef)%core ⋮ τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ x τ et ef :
      (Γ ⊢wf[Σ] (if vfvar x then et else ef)%core ⋮ τ) ->
      (Γ ⊢ᶜ [Φ; Σ] (ret (vfvar x))%core ⋮ bool_precise_ty false) ->
      (Γ ⊢ᶜ [Φ; Σ] ef ⋮ τ) ->
      Γ ⊢ᶜ [Φ; Σ] (if vfvar x then et else ef)%core ⋮ τ

where "Γ ⊢ᶜ [ Φ ; Σ ] e ⋮ τ" := (has_context_type Φ Σ Γ e τ).

#[global] Hint Constructors has_context_type : core.
