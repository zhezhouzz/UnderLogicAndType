(** * ChoiceTyping.Typing

    Declarative typing rules for the choice type system.

    The current paper presentation has a single judgment [Γ ⊢ e ⋮ τ].
    Star, sum, intersection, and union remain type/context syntax with
    denotational meaning; their direct proof rules are derived/optional and
    are deliberately not part of this core definition. *)

From CoreLang Require Import BasicTypingProps.
From ChoiceTyping Require Export Auxiliary PrimOpContext.

(** ** The typing judgment *)

Definition choice_typing_wf
    (Σ : gmap atom ty) (Γ : ctx) (e : tm) (τ : choice_ty) : Prop :=
  wf_choice_ty_under Σ Γ τ ∧ erase_ctx_under Σ Γ ⊢ₑ e ⋮ erase_ty τ.

Definition branch_unreachable (Σ : gmap atom ty) (Γ : ctx) (v : value) (b : bool) : Prop :=
  denot_ctx_in_env Σ Γ ⊫
    FImpl (denot_ty_in_ctx_under Σ Γ (bool_precise_ty b) (tret v)) FFalse.

Lemma choice_typing_wf_fv_tm_subset Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  fv_tm e ⊆ dom Σ ∪ ctx_dom Γ.
Proof.
  intros [Hwf Herase].
  pose proof (basic_typing_contains_fv_tm (erase_ctx_under Σ Γ) e (erase_ty τ) Herase)
    as Hfv.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ
    (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwf))) as Hdom.
  unfold erase_ctx_under in Hfv.
  rewrite dom_union_L, Hdom in Hfv. exact Hfv.
Qed.

Lemma choice_typing_wf_footprint_subset Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  fv_tm e ∪ fv_cty τ ⊆ dom Σ ∪ ctx_dom Γ.
Proof.
  intros Hwf.
  destruct Hwf as [Hty Herase].
  pose proof (choice_typing_wf_fv_tm_subset Σ Γ e τ
    (conj Hty Herase)) as He.
  pose proof (wf_choice_ty_under_fv_subset Σ Γ τ Hty) as Hτ.
  set_solver.
Qed.

Lemma choice_typing_wf_erase_dom Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ.
Proof.
  intros [Hwf _].
  unfold erase_ctx_under.
  rewrite dom_union_L.
  rewrite (basic_ctx_erase_dom (dom Σ) Γ
    (wf_ctx_under_basic Σ Γ (wf_choice_ty_under_ctx Σ Γ τ Hwf))).
  reflexivity.
Qed.

Lemma choice_typing_wf_basic_choice_ty_erased Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  basic_choice_ty (dom (erase_ctx_under Σ Γ)) τ.
Proof.
  intros Hwf.
  destruct Hwf as [Hwfτ Herase].
  pose proof (wf_choice_ty_under_basic Σ Γ τ Hwfτ) as Hbasic.
  rewrite (choice_typing_wf_erase_dom Σ Γ e τ (conj Hwfτ Herase)).
  exact Hbasic.
Qed.

Lemma choice_typing_wf_fv_tm_subset_erase_dom Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  fv_tm e ⊆ dom (erase_ctx_under Σ Γ).
Proof.
  intros Hwf.
  rewrite (choice_typing_wf_erase_dom Σ Γ e τ Hwf).
  exact (choice_typing_wf_fv_tm_subset Σ Γ e τ Hwf).
Qed.

Lemma choice_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  fv_cty τ ⊆ dom (erase_ctx_under Σ Γ).
Proof.
  intros Hwf.
  destruct Hwf as [Hwfτ Herase].
  rewrite (choice_typing_wf_erase_dom Σ Γ e τ (conj Hwfτ Herase)).
  exact (wf_choice_ty_under_fv_subset Σ Γ τ Hwfτ).
Qed.

Lemma choice_typing_wf_footprint_subset_erase_dom Σ Γ e τ :
  choice_typing_wf Σ Γ e τ →
  fv_tm e ∪ fv_cty τ ⊆ dom (erase_ctx_under Σ Γ).
Proof.
  intros Hwf.
  pose proof (choice_typing_wf_fv_tm_subset_erase_dom Σ Γ e τ Hwf) as He.
  pose proof (choice_typing_wf_fv_cty_subset_erase_dom Σ Γ e τ Hwf) as Hτ.
  set_solver.
Qed.

Inductive has_choice_type (Φ : primop_ctx) (Σ : gmap atom ty) : ctx → tm → choice_ty → Prop :=

  (** T-Var *)
  | CT_Var x τ :
      choice_typing_wf Σ (CtxBind x τ) (tret (vfvar x)) τ →
      has_choice_type Φ
        Σ
        (CtxBind x τ)
        (tret (vfvar x))
        τ

  (** T-Const.  Constants are precise: over and under at the same qualifier. *)
  | CT_Const c :
      choice_typing_wf Σ CtxEmpty (tret (vconst c)) (const_precise_ty c) →
      has_choice_type Φ
        Σ
        CtxEmpty
        (tret (vconst c))
        (const_precise_ty c)

  (** T-Sub *)
  | CT_Sub Γ e τ1 τ2 :
      choice_typing_wf Σ Γ e τ2 →
      has_choice_type Φ Σ Γ e τ1 →
      sub_type_under Σ Γ τ1 τ2 →
      has_choice_type Φ Σ Γ e τ2

  (** T-CtxSub *)
  | CT_CtxSub Γ1 Γ2 e τ :
      choice_typing_wf Σ Γ1 e τ →
      has_choice_type Φ Σ Γ2 e τ →
      ctx_sub_under Σ (fv_tm e ∪ fv_cty τ) Γ1 Γ2 →
      has_choice_type Φ Σ Γ1 e τ

  (** T-Let.  Standard additive/bunched let. *)
  | CT_Let Γ τ1 τ2 e1 e2 (L : aset) :
      choice_typing_wf Σ Γ (tlete e1 e2) τ2 →
      has_choice_type Φ Σ Γ e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type Φ Σ
          (CtxComma Γ (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type Φ Σ Γ (tlete e1 e2) τ2

  (** T-LetD.  Standard separating/bunched let. *)
  | CT_LetD Γ1 Γ2 τ1 τ2 e1 e2 (L : aset) :
      choice_typing_wf Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2 →
      has_choice_type Φ Σ Γ1 e1 τ1 →
      (∀ x, x ∉ L →
        has_choice_type Φ Σ
          (CtxStar Γ2 (CtxBind x τ1))
          (e2 ^^ x)
          τ2) →
      has_choice_type Φ Σ (CtxStar Γ1 Γ2) (tlete e1 e2) τ2

  (** T-Lam *)
  | CT_Lam Γ τx τ e (L : aset) :
      choice_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_choice_type Φ Σ
          (CtxComma Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_choice_type Φ Σ Γ
        (tret (vlam (erase_ty τx) e))
        (CTArrow τx τ)

  (** T-LamD *)
  | CT_LamD Γ τx τ e (L : aset) :
      choice_typing_wf Σ Γ (tret (vlam (erase_ty τx) e)) (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_choice_type Φ Σ
          (CtxStar Γ (CtxBind y τx))
          (e ^^ y)
          ({0 ~> y} τ)) →
      has_choice_type Φ Σ Γ
        (tret (vlam (erase_ty τx) e))
        (CTWand τx τ)

  (** T-AppFun *)
  | CT_AppFun Γ τx τ v1 x :
      choice_typing_wf Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      has_choice_type Φ Σ Γ (tret v1) (CTArrow τx τ) →
      has_choice_type Φ Σ Γ (tret (vfvar x)) τx →
      has_choice_type Φ Σ Γ (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-AppFunD *)
  | CT_AppFunD Γ1 Γ2 τx τ v1 x :
      choice_typing_wf Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ) →
      has_choice_type Φ Σ Γ1 (tret v1) (CTWand τx τ) →
      has_choice_type Φ Σ Γ2 (tret (vfvar x)) τx →
      has_choice_type Φ Σ (CtxStar Γ1 Γ2) (tapp v1 (vfvar x)) ({0 ~> x} τ)

  (** T-Fix *)
  | CT_Fix Γ τx τ vf (L : aset) :
      choice_typing_wf Σ Γ
        (tret (vfix (erase_ty (CTArrow τx τ)) vf))
        (CTArrow τx τ) →
      (∀ y, y ∉ L →
        has_choice_type Φ Σ
          (CtxComma Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTArrow (CTArrow τx τ) ({0 ~> y} τ))) →
      has_choice_type Φ Σ Γ
        (tret (vfix (erase_ty (CTArrow τx τ)) vf))
        (CTArrow τx τ)

  (** T-FixD.  Separating recursive function. *)
  | CT_FixD Γ τx τ vf (L : aset) :
      choice_typing_wf Σ Γ
        (tret (vfix (erase_ty (CTWand τx τ)) vf))
        (CTWand τx τ) →
      (∀ y, y ∉ L →
        has_choice_type Φ Σ
          (CtxStar Γ
            (CtxBind y τx))
          (tret ({0 ~> vfvar y} vf))
          (CTWand (CTWand τx τ) ({0 ~> y} τ))) →
      has_choice_type Φ Σ Γ
        (tret (vfix (erase_ty (CTWand τx τ)) vf))
        (CTWand τx τ)

  (** T-AppOp.  Primitive operations are unary; the argument must be an atom.
      Arguments are over-approximate and results are precise. *)
  | CT_AppOp Γ op x :
      wf_primop_sig op (Φ op) →
      choice_typing_wf Σ Γ
        (tprim op (vfvar x))
        ({0 ~> x} (primop_result_ty (Φ op))) →
      has_choice_type Φ Σ Γ (tret (vfvar x)) (primop_arg_ty (Φ op)) →
      has_choice_type Φ Σ Γ (tprim op (vfvar x)) ({0 ~> x} (primop_result_ty (Φ op)))

  (** T-MatchBoth.  Both boolean branches are reachable and contribute a
      context/type sum. *)
  | CT_MatchBoth Γt Γf v τt τf et ef :
      choice_typing_wf Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf) →
      has_choice_type Φ Σ Γt (tret v) (bool_precise_ty true) →
      has_choice_type Φ Σ Γf (tret v) (bool_precise_ty false) →
      has_choice_type Φ Σ Γt et τt →
      has_choice_type Φ Σ Γf ef τf →
      has_choice_type Φ Σ (CtxSum Γt Γf) (tmatch v et ef) (CTSum τt τf)

  (** T-MatchTrueOnly.  The false branch is unreachable but must remain
      well typed after erasure because it is still present in Core syntax. *)
  | CT_MatchTrueOnly Γ v τ et ef :
      choice_typing_wf Σ Γ (tmatch v et ef) τ →
      has_choice_type Φ Σ Γ (tret v) (bool_precise_ty true) →
      branch_unreachable Σ Γ v false →
      has_choice_type Φ Σ Γ et τ →
      erase_ctx_under Σ Γ ⊢ₑ ef ⋮ erase_ty τ →
      has_choice_type Φ Σ Γ (tmatch v et ef) τ

  (** T-MatchFalseOnly. *)
  | CT_MatchFalseOnly Γ v τ et ef :
      choice_typing_wf Σ Γ (tmatch v et ef) τ →
      has_choice_type Φ Σ Γ (tret v) (bool_precise_ty false) →
      branch_unreachable Σ Γ v true →
      erase_ctx_under Σ Γ ⊢ₑ et ⋮ erase_ty τ →
      has_choice_type Φ Σ Γ ef τ →
      has_choice_type Φ Σ Γ (tmatch v et ef) τ.

#[global] Hint Constructors has_choice_type : core.
Definition default_has_choice_type : ctx → tm → choice_ty → Prop :=
  has_choice_type default_primop_ctx ∅.

#[global] Instance typing_choice_inst : Typing ctx tm choice_ty := default_has_choice_type.
Arguments typing_choice_inst /.

(** ** Small admissible helpers kept only where they name core definitions. *)

Lemma typing_wf Φ Γ e τ :
  has_choice_type Φ ∅ Γ e τ →
  choice_typing_wf ∅ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma typing_wf_under Φ Σ Γ e τ :
  has_choice_type Φ Σ Γ e τ →
  choice_typing_wf Σ Γ e τ.
Proof. induction 1; assumption. Qed.

Lemma typing_regular Φ Γ e τ :
  has_choice_type Φ ∅ Γ e τ →
  wf_ctx Γ ∧ wf_choice_ty Γ τ.
Proof.
  intros Hty.
  pose proof (typing_wf Φ Γ e τ Hty) as [Hwf _].
  split; [exact (wf_choice_ty_ctx Γ τ Hwf) | exact Hwf].
Qed.

(** Typing implies basic typing (erasure correctness). *)
Lemma typing_erase Φ Γ e τ :
  has_choice_type Φ ∅ Γ e τ →
  erase_ctx_under ∅ Γ ⊢ₑ e ⋮ erase_ty τ.
Proof. intros Hty. exact (proj2 (typing_wf Φ Γ e τ Hty)). Qed.

Lemma typing_lc Φ Γ e τ :
  has_choice_type Φ ∅ Γ e τ →
  lc_tm e.
Proof.
  intros Hty.
  apply typing_tm_lc with (Γ := erase_ctx_under ∅ Γ) (T := erase_ty τ).
  apply typing_erase with (Φ := Φ). exact Hty.
Qed.
