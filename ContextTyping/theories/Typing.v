(** * ContextTyping.Typing

    Well-formedness predicates, auxiliary semantic relations, primitive
    operation signatures, and declarative typing rules for context types. *)

From CoreLang Require Import BasicTyping BasicTypingProps Sugar.
From ContextLogic Require Import FormulaSemantics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceInterface.
From ContextTypeLanguage Require Export Notation.
From Denotation Require Export Context.

(** * ContextTyping.WellFormed

    Paper-level well-formedness for context contexts and context types.

    [BasicTyping] checks the syntactic formation side: referenced atoms are in
    scope, locally-nameless binders are well scoped, and tree-shaped contexts
    bind each atom at most once.  The paper's context well-formedness also
    requires semantic nonemptiness, which depends on denotation and therefore
    lives in this layer. *)


(** ** Context and type well-formedness *)

Definition ctx_nonempty_under (Σ : gmap atom ty) (Γ : ctx) : Prop :=
  ∃ r : WfWorldT, r ⊨ denot_ctx_under Σ Γ.

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
    denot_ctx_under Σ Γ ⊫
      FImpl (denot_ty (erase_ctx Γ) τ1 e)
            (denot_ty (erase_ctx Γ) τ2 e).

Definition ctx_sub_under
    (Σ : gmap atom ty) (X : aset) (Γ1 Γ2 : ctx) : Prop :=
  wf_ctx_under Σ Γ1 ∧
  wf_ctx_under Σ Γ2 ∧
  ty_env_agree_on X (erase_ctx Γ1) (erase_ctx Γ2) ∧
  ∀ r, r ⊨ denot_ctx_under Σ Γ1 →
       exists r',
         res_restrict r X ⊑ r' /\
         r' ⊨ denot_ctx_under Σ Γ2.

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

Definition primop_sig_ty (sig : primop_sig) : context_ty :=
  primop_ty
    sig.(prim_arg_base) sig.(prim_arg_qual)
    sig.(prim_ret_base) sig.(prim_ret_qual).

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
      denot_ty_in_ctx Γx ({0 ~> x} (primop_result_ty sig)) (tprim op (vfvar x))) ∧
    (denot_ty_in_ctx Γx ({0 ~> x} (primop_result_ty sig)) (tprim op (vfvar x)) ⊫
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

Lemma default_primop_ctx_erasure_ok op :
  primop_erasure_ok op (default_primop_ctx op).
Proof.
  unfold primop_erasure_ok, default_primop_ctx.
  destruct (prim_op_type op) as [arg_b ret_b]. reflexivity.
Qed.

Lemma default_primop_ctx_arg_basic op :
  basic_context_ty ∅ (primop_arg_ty (default_primop_ctx op)).
Proof.
  unfold default_primop_ctx, primop_arg_ty, over_ty.
  destruct (prim_op_type op) as [arg_b ret_b].
  apply basic_context_ty_over.
  apply basic_qualifier_body_top.
Qed.

Lemma default_primop_ctx_result_basic op :
  basic_context_ty ∅ (primop_result_ty (default_primop_ctx op)).
Proof.
  unfold default_primop_ctx, primop_result_ty, precise_ty, over_ty, under_ty.
  destruct (prim_op_type op) as [arg_b ret_b].
  apply basic_context_ty_inter.
  - apply basic_context_ty_over. apply basic_qualifier_body_top.
  - apply basic_context_ty_under. apply basic_qualifier_body_top.
  - reflexivity.
Qed.

(** * ContextTyping.Typing

    Declarative typing rules for the context type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)


(** ** The typing judgment *)

Definition context_typing_regular
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) : Prop :=
  wf_ctx_under Σ Γ /\
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ /\
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.

Definition context_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : context_ty) : Prop :=
  wf_ctx_under Σ Γ /\
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ /\
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.

Lemma context_typing_wf_regular Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  context_typing_regular Σ Γ e τ.
Proof.
  intros Hwf. exact Hwf.
Qed.

Lemma context_typing_wf_basic_typing Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. intros [_ [_ Hbasic]]. exact Hbasic. Qed.

Lemma context_typing_wf_ctx Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  wf_ctx_under Σ Γ.
Proof. intros [Hctx _]. exact Hctx. Qed.

Lemma context_typing_wf_context_ty Σ Γ e τ :
  context_typing_wf Σ Γ e τ ->
  wf_context_ty_at 0 (dom (erase_ctx Γ)) τ.
Proof. intros [_ [Hτ _]]. exact Hτ. Qed.

Definition branch_unreachable (Σ : gmap atom ty) (Γ : ctx) (v : value) (b : bool) : Prop :=
  denot_ctx_under Σ Γ ⊫
    FImpl (denot_ty (erase_ctx Γ) (bool_precise_ty b) (tret v)) FFalse.

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

Lemma context_typing_wf_basic_context_ty_erased Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  basic_context_ty (dom (erase_ctx Γ)) τ.
Proof.
  apply context_typing_wf_context_ty.
Qed.

Lemma context_typing_wf_fv_tm_subset_erase_dom Σ Γ e τ :
  context_typing_wf Σ Γ e τ →
  fv_tm e ⊆ dom (erase_ctx Γ).
Proof.
  apply context_typing_wf_fv_tm_subset.
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

Inductive has_context_type (Φ : primop_ctx) (Σ : gmap atom ty) : ctx → tm → context_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      context_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ →
      has_context_type Φ
        Σ
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      context_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) →
      has_context_type Φ
        Σ
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
      has_context_type Φ Σ Γ (tret v1) (CTArrow τx τ) →
      has_context_type Φ Σ Γ (tret (vfvar x)) τx →
      has_context_type Φ Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      context_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      has_context_type Φ Σ Γ1 (tret v1) (CTWand τx τ) →
      has_context_type Φ Σ Γ2 (tret (vfvar x)) τx →
      has_context_type Φ Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-Fix *)
  | CT_Fix Γ τx τ vf b t (L : aset) :
      erase_ty τx = TBase b →
      erase_ty τ = t →
      context_typing_wf Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_context_type Φ Σ
          (CtxComma Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))) →
      has_context_type Φ Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTArrow τx τ)

  (** T-FixD.  Separating recursive function. *)
  | CT_FixD Γ τx τ vf b t (L : aset) :
      erase_ty τx = TBase b →
      erase_ty τ = t →
      context_typing_wf Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_context_type Φ Σ
          (CtxStar Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (fix_rec_call_ty b y τx τ) ({0 ~> y} τ))) →
      has_context_type Φ Σ Γ
        (tret (vfix (TBase b →ₜ t) vf))
        (CTWand τx τ)

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x :
      wf_primop_sig op (Φ op) →
      context_typing_wf Σ Γ
        (tprim op (vfvar x))
        ({0 ~> x} (primop_result_ty (Φ op))) →
      has_context_type Φ Σ Γ (tret (vfvar x)) (primop_arg_ty (Φ op)) →
      has_context_type Φ Σ Γ (tprim op (vfvar x)) ({0 ~> x} (primop_result_ty (Φ op)))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf v τt τf et ef :
      context_typing_wf Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf) →
      has_context_type Φ Σ Γt (tret v) (bool_precise_ty true) →
      has_context_type Φ Σ Γf (tret v) (bool_precise_ty false) →
      has_context_type Φ Σ Γt et τt →
      has_context_type Φ Σ Γf ef τf →
      has_context_type Φ Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf)

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ v τ et ef :
      context_typing_wf Σ Γ (tmatch v et ef) τ →
      has_context_type Φ Σ Γ (tret v) (bool_precise_ty true) →
      branch_unreachable Σ Γ v false →
      has_context_type Φ Σ Γ et τ →
      erase_ctx Γ ⊢ₑ ef ⋮ erase_ty τ →
      has_context_type Φ Σ Γ (tmatch v et ef) τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ v τ et ef :
      context_typing_wf Σ Γ (tmatch v et ef) τ →
      has_context_type Φ Σ Γ (tret v) (bool_precise_ty false) →
      branch_unreachable Σ Γ v true →
      erase_ctx Γ ⊢ₑ et ⋮ erase_ty τ →
      has_context_type Φ Σ Γ ef τ →
      has_context_type Φ Σ Γ (tmatch v et ef) τ.

#[global] Hint Constructors has_context_type : core.
#[global] Instance typing_context_inst : Typing ctx tm context_ty :=
  has_context_type default_primop_ctx ∅.
Arguments typing_context_inst /.

(** ** Small admissible helpers kept only where they name core definitions. *)

Lemma typing_wf Φ Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  context_typing_wf ∅ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma typing_wf_under Φ Σ Γ e τ :
  has_context_type Φ Σ Γ e τ →
  context_typing_wf Σ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma typing_regular Φ Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  wf_ctx Γ ∧ wf_context_ty Γ τ.
Proof.
  intros Hty.
  pose proof (context_typing_wf_regular ∅ Γ e τ
    (typing_wf Φ Γ e τ Hty)) as [Hctx [Hτ _]].
  split; assumption.
Qed.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Φ Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  erase_ctx Γ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros Hty.
  exact (context_typing_wf_basic_typing ∅ Γ e τ
    (typing_wf Φ Γ e τ Hty)).
Qed.

Lemma typing_lc Φ Γ e τ :
  has_context_type Φ ∅ Γ e τ →
  lc_tm e.
Proof.
  intros Hty.
  eapply typing_tm_lc. exact (typing_erase Φ Γ e τ Hty).
Qed.
