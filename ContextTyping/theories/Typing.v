(** * ContextTyping.Typing

    Well-formedness predicates, auxiliary semantic relations, primitive
    operation signatures, and declarative typing rules for context types. *)

From CoreLang Require Import BasicTyping BasicTypingProps Sugar.
From ContextLogic Require Import FormulaSemantics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextTypeLanguage Require Import Notation.
From Denotation Require Import Context.

(** * ContextTyping.WellFormed

    Paper-level well-formedness for context contexts and context types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  The paper's context well-formedness also
    requires semantic nonemptiness, which depends on denotation and therefore
    lives in this layer. *)


(** ** Context and type well-formedness *)

Definition ctx_nonempty_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  ∃ r : WfWorldT, r ⊨ ctx_denote_under Σ Γ.

Definition wf_ctx_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  basic_ctx (dom Σ) Γ ∧ ctx_nonempty_under Σ Γ.

Definition wf_ctx (Γ : ctx) : Prop :=
  wf_ctx_under ∅ Γ.

Definition wf_context_ty (Γ : ctx) (τ : context_ty) : Prop :=
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ.

(** ** Regularity skeletons *)

Lemma wf_ctx_basic Γ :
  wf_ctx Γ →
  basic_ctx ∅ Γ.
Proof. intros [Hbasic _]. exact Hbasic. Qed.

Lemma wf_ctx_under_basic Σ Γ :
  wf_ctx_under Σ Γ →
  basic_ctx (dom Σ) Γ.
Proof. intros [Hbasic _]. exact Hbasic. Qed.

Lemma wf_context_ty_basic Γ τ :
  wf_context_ty Γ τ →
  basic_context_ty (dom (erase_ctx Γ)) τ.
Proof. intros Hwf. exact Hwf. Qed.

Lemma wf_ctx_fv_subset Γ :
  wf_ctx Γ →
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
  intros Hwf.
  pose proof (wf_ctx_basic Γ Hwf) as Hbasic.
  apply basic_ctx_empty_fv. exact Hbasic.
Qed.

Lemma wf_context_ty_lc Γ τ :
  wf_context_ty Γ τ →
  lc_context_ty τ.
Proof.
  intros Hwf.
  eapply basic_context_ty_lc.
  exact (wf_context_ty_basic Γ τ Hwf).
Qed.

Lemma wf_context_ty_fv_subset Γ τ :
  wf_context_ty Γ τ →
  fv_cty τ ⊆ dom (erase_ctx Γ).
Proof.
  intros Hwf.
  eapply basic_context_ty_fv_subset.
  exact (wf_context_ty_basic Γ τ Hwf).
Qed.

(** * ContextTyping.Auxiliary

    Auxiliary judgments for the context typing rules. *)


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

(** * ContextTyping.PrimOpContext

    Paper-level primitive-operation signatures.  CoreLang keeps the erased
    unary type [prim_op_type]; this layer refines it with over-approximate
    argument qualifiers and precise result qualifiers. *)


Record primop_sig := mk_primop_sig {
  prim_arg_base : base_ty;
  prim_arg_qual : type_qualifier;
  prim_ret_base : base_ty;
  prim_ret_qual : type_qualifier;
}.

Definition primop_result_ty (sig : primop_sig) : context_ty :=
  precise_ty sig.(prim_ret_base) sig.(prim_ret_qual).

Definition primop_arg_ty (sig : primop_sig) : context_ty :=
  over_ty sig.(prim_arg_base) sig.(prim_arg_qual).

Definition primop_ctx : Type := prim_op → primop_sig.

Definition primop_erasure_ok (op : prim_op) (sig : primop_sig) : Prop :=
  prim_op_type op = (sig.(prim_arg_base), sig.(prim_ret_base)).

(** Paper-level semantic well-formedness for primitive operators.

    In the paper this is written as

      [Φ(op) = x : {b_x | φ_x} -> precise(b, φ)]
      and [⊨ ⟦x : {b_x | φ_x}⟧ ⇔ ⟦precise(b, φ)⟧ (op x)].

    Our CoreLang primitive operations are unary and the application rule only
    accepts atom arguments, so the specification quantifies over the atom used
    as the argument coordinate.  The two entailments record the paper's
    equivalence: the primitive result denotation is exactly characterized by
    its argument context. *)
Definition primop_semantic_ok (op : prim_op) (sig : primop_sig) : Prop :=
  ∀ x : atom,
    let Γx := CtxBind x (primop_arg_ty sig) in
    (⟦CtxBind x (primop_arg_ty sig)⟧ ⊫
      ty_denote (erase_ctx Γx) ({0 ~> x} (primop_result_ty sig))
        (tprim op (vfvar x))) ∧
    (ty_denote (erase_ctx Γx) ({0 ~> x} (primop_result_ty sig))
        (tprim op (vfvar x)) ⊫
      ⟦CtxBind x (primop_arg_ty sig)⟧).

Record wf_primop_sig (op : prim_op) (sig : primop_sig) : Prop := {
  wf_primop_erasure : primop_erasure_ok op sig;
  wf_primop_arg_basic : basic_context_ty ∅ (primop_arg_ty sig);
  wf_primop_result_basic : basic_context_ty ∅ (primop_result_ty sig);
  wf_primop_semantic : primop_semantic_ok op sig;
}.

Definition wf_primop_ctx (Φ : primop_ctx) : Prop :=
  ∀ op, wf_primop_sig op (Φ op).

(** Default shallow signatures for the current unary CoreLang primitives.
    These are intentionally conservative: arguments and results are typed by
    top qualifiers except where examples can later refine them. *)
Definition default_primop_ctx : primop_ctx :=
  λ op,
    match prim_op_type op with
    | (arg_b, ret_b) => mk_primop_sig arg_b qual_top ret_b qual_top
    end.

(** * ContextTyping.Typing

    Declarative typing rules for the context type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)


(** ** The typing judgment *)

Definition context_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) : Prop :=
  wf_ctx_under Σ Γ /\
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ /\
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.

Lemma context_typing_wf_basic_typing Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. intros [_ [_ Hbasic]]. exact Hbasic. Qed.

Lemma context_typing_wf_lc_tm Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  lc_tm e.
Proof.
  intros Hwf.
  eapply typing_tm_lc.
  exact (context_typing_wf_basic_typing Σ Γ e τ Hwf).
Qed.

Lemma context_typing_wf_ret_lc_value Σ Γ v τ :
  context_typing_wf Σ Γ (tret v) τ ->
  lc_value v.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_lc_tm Σ Γ (tret v) τ Hwf) as Hlc.
  inversion Hlc; subst.
  assumption.
Qed.

Lemma context_typing_wf_app_fun_lc_value Σ Γ v1 v2 τ :
  context_typing_wf Σ Γ (tapp v1 v2) τ ->
  lc_value v1.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_lc_tm Σ Γ (tapp v1 v2) τ Hwf) as Hlc.
  inversion Hlc; subst.
  assumption.
Qed.

Lemma context_typing_wf_lam_body Σ Γ T e τ :
  context_typing_wf Σ Γ (tret (vlam T e)) τ ->
  body_tm e.
Proof.
  intros Hwf.
  apply (proj1 (lc_lam_iff_body T e)).
  exact (context_typing_wf_ret_lc_value Σ Γ (vlam T e) τ Hwf).
Qed.

Lemma context_typing_wf_ctx Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  wf_ctx_under Σ Γ.
Proof. intros [Hctx _]. exact Hctx. Qed.

Lemma context_typing_wf_context_ty Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ.
Proof. intros [_ [Hτ _]]. exact Hτ. Qed.

Lemma context_typing_wf_bind_context_ty Σ x τ e :
  context_typing_wf Σ (CtxBind x τ) e τ ->
  basic_context_ty {[x]} τ.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ (CtxBind x τ) e τ Hwf)
    as Hτ.
  rewrite erase_ctx_bind_dom in Hτ.
  exact Hτ.
Qed.

Definition branch_unreachable (Σ : gmap atom ty) (Γ : ctx) (v : value) (b : bool) : Prop :=
  ctx_denote_under Σ Γ ⊫
    FImpl (ty_denote (erase_ctx Γ) (bool_precise_ty b) (tret v)) FFalse.

Lemma context_typing_wf_fv_tm_subset Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  fv_tm e ⊆ dom (erase_ctx Γ).
Proof.
  intros Hct.
  apply basic_typing_contains_fv_tm with (T := erase_ty τ).
  exact (context_typing_wf_basic_typing Σ Γ e τ Hct).
Qed.

Lemma context_typing_wf_erase_dom Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof.
  intros Hct.
  pose proof (context_typing_wf_ctx Σ Γ e τ Hct) as Hctx.
  pose proof (wf_ctx_under_basic Σ Γ Hctx) as Hbasic.
  apply (basic_ctx_erase_dom (dom Σ)). exact Hbasic.
Qed.

Lemma context_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  fv_cty τ ⊆ dom (erase_ctx Γ).
Proof.
  intros Hct.
  eapply wf_context_ty_at_fv_subset.
  exact (context_typing_wf_context_ty Σ Γ e τ Hct).
Qed.

Lemma context_typing_wf_wand_arg_global Σ Γ e τx τr :
  context_typing_wf Σ Γ e (CTWand τx τr) ->
  basic_context_ty ∅ τx.
Proof.
  intros Hwf.
  pose proof (context_typing_wf_context_ty Σ Γ e (CTWand τx τr) Hwf)
    as Hτ.
  cbn [wf_context_ty_at] in Hτ.
  exact (proj1 Hτ).
Qed.

Section HasContextType.

Context (Φ : primop_ctx).

Inductive has_context_type (Σ : gmap atom ty) : ctx → tm → context_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ →
      has_context_type
        Σ
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) →
      has_context_type
        Σ
        CtxEmpty
        (tret (vconst c))
        (const_precise_ty c)

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      context_typing_wf Σ Γ e τ2 →
      has_context_type Σ Γ e τ1 →
      sub_type_under Σ Γ τ1 τ2 →
      has_context_type Σ Γ e τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      context_typing_wf Σ Γ1 e τ →
      has_context_type Σ Γ2 e τ →
      ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
      has_context_type Σ Γ1 e τ

  (** T-Let.  Standard additive/bunched let. *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      context_typing_wf Σ Γ (tlete e1 e2) τ2 →
      has_context_type Σ Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_context_type Σ
          (CtxComma Γ (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_context_type Σ Γ (tlete e1 e2) τ2

  (** T-LetD.  Standard separating/bunched let. *)
  | CT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      context_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 →
      has_context_type Σ Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_context_type Σ
          (CtxStar Γ2 (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_context_type Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_context_type Σ
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_context_type Σ Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow τx τ)

  (** T-LamD *)
  | CT_LamD Γ τx τ e (L : aset) :
      context_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_context_type Σ
          (CtxStar Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_context_type Σ Γ
        (tret (vlam (erase_ty τx) e))
        (CTWand τx τ)

  (** T-AppFun *)
  | CT_AppFun Γ τx τ v1 x :
      context_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ →
      has_context_type Σ Γ (tret v1) (CTArrow τx τ) →
      has_context_type Σ Γ (tret (vfvar x)) τx →
      has_context_type Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      x ∉ fv_value v1 ∪ fv_cty τx ∪ fv_cty τ →
      has_context_type Σ Γ1 (tret v1) (CTWand τx τ) →
      has_context_type Σ Γ2 (tret (vfvar x)) τx →
      has_context_type Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-Fix *)
  | CT_Fix Γ φx τ vf b t (L : aset) :
      erase_ty τ = t →
      context_typing_wf Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow (over_ty b φx) τ) →
      (∀ y, y ∉ L →
        has_context_type Σ
          (CtxComma Γ
            (CtxBind y (over_ty b φx)))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) →
      has_context_type Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow (over_ty b φx) τ)

  (** T-FixD.  Separating recursive function. *)
  | CT_FixD Γ φx τ vf b t (L : aset) :
      erase_ty τ = t →
      context_typing_wf Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTWand (over_ty b φx) τ) →
      (∀ y, y ∉ L →
        has_context_type Σ
          (CtxStar Γ
            (CtxBind y (over_ty b φx)))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (fix_rec_call_ty b y (over_ty b φx) τ) ({0 ~> y} τ))) →
      has_context_type Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTWand (over_ty b φx) τ)

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x :
      wf_primop_sig op (Φ op) →
      context_typing_wf Σ Γ
        (tprim op (vfvar x))
        ({0 ~> x} (primop_result_ty (Φ op))) →
      has_context_type Σ Γ (tret (vfvar x)) (primop_arg_ty (Φ op)) →
      has_context_type Σ Γ (tprim op (vfvar x)) ({0 ~> x} (primop_result_ty (Φ op)))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf x τt τf et ef :
      context_typing_wf Σ (CtxSum Γt Γf) (tmatch (vfvar x) et ef) (CTSum τt τf) →
      has_context_type Σ Γt (tret (vfvar x)) (bool_precise_ty true) →
      has_context_type Σ Γf (tret (vfvar x)) (bool_precise_ty false) →
      has_context_type Σ Γt et τt →
      has_context_type Σ Γf ef τf →
      has_context_type Σ (CtxSum Γt Γf) (tmatch (vfvar x) et ef) (CTSum τt τf)

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ x τ et ef :
      context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ →
      has_context_type Σ Γ (tret (vfvar x)) (bool_precise_ty true) →
      has_context_type Σ Γ et τ →
      has_context_type Σ Γ (tmatch (vfvar x) et ef) τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ x τ et ef :
      context_typing_wf Σ Γ (tmatch (vfvar x) et ef) τ →
      has_context_type Σ Γ (tret (vfvar x)) (bool_precise_ty false) →
      has_context_type Σ Γ ef τ →
      has_context_type Σ Γ (tmatch (vfvar x) et ef) τ.

End HasContextType.

#[global] Hint Constructors has_context_type : core.
#[global] Instance typing_context_inst : Typing ctx tm context_ty :=
  has_context_type default_primop_ctx ∅.
Arguments typing_context_inst /.

(** ** Small admissible helpers kept only where they name core definitions. *)

Section TypingRegularity.

Context (Φ : primop_ctx).

Lemma typing_wf Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  context_typing_wf ∅ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma typing_wf_under Σ Γ e τ :
  has_context_type Φ Σ Γ e τ →
  context_typing_wf Σ Γ e τ.
Proof. induction 1; assumption. Qed.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hty.
  exact (context_typing_wf_basic_typing ∅ Γ e τ
    (typing_wf Γ e τ Hty)).
Qed.

End TypingRegularity.
