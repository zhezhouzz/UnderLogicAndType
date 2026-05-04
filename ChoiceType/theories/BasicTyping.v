(** * ChoiceType.BasicTyping

    Paper-level basic formation checks for choice qualifiers, refinement
    types, and tree-shaped choice contexts.

    Type qualifiers are shallow Rocq predicates over untyped stores.  Their
    basic checking therefore records only the syntactic information that the
    embedding exposes: referenced free atoms must be available in the ambient
    domain, and locally-nameless bound variables must be opened in the usual
    cofinite style. *)

From ChoiceType Require Export Syntax.

(** ** Basic qualifier formation *)

Definition basic_qualifier (D : aset) (q : type_qualifier) : Prop :=
  qual_dom q ⊆ D ∧ qual_bvars q = ∅.

Definition basic_qualifier_body (D : aset) (q : type_qualifier) : Prop :=
  ∃ L : aset, ∀ x : atom, x ∉ L → basic_qualifier (D ∪ {[x]}) (qual_open_atom 0 x q).

(** ** Basic type and context formation *)

Inductive basic_choice_ty : aset → choice_ty → Prop :=
  | Basic_CTOver D b φ :
      basic_qualifier_body D φ →
      basic_choice_ty D (CTOver b φ)
  | Basic_CTUnder D b φ :
      basic_qualifier_body D φ →
      basic_choice_ty D (CTUnder b φ)
  | Basic_CTInter D τ1 τ2 :
      basic_choice_ty D τ1 →
      basic_choice_ty D τ2 →
      erase_ty τ1 = erase_ty τ2 →
      basic_choice_ty D (CTInter τ1 τ2)
  | Basic_CTUnion D τ1 τ2 :
      basic_choice_ty D τ1 →
      basic_choice_ty D τ2 →
      erase_ty τ1 = erase_ty τ2 →
      basic_choice_ty D (CTUnion τ1 τ2)
  | Basic_CTSum D τ1 τ2 :
      basic_choice_ty D τ1 →
      basic_choice_ty D τ2 →
      erase_ty τ1 = erase_ty τ2 →
      basic_choice_ty D (CTSum τ1 τ2)
  | Basic_CTArrow D τx τ (L : aset) :
      basic_choice_ty D τx →
      (∀ x, x ∉ L → basic_choice_ty (D ∪ {[x]}) ({0 ~> x} τ)) →
      basic_choice_ty D (CTArrow τx τ)
  | Basic_CTWand D τx τ (L : aset) :
      basic_choice_ty D τx →
      (∀ x, x ∉ L → basic_choice_ty (D ∪ {[x]}) ({0 ~> x} τ)) →
      basic_choice_ty D (CTWand τx τ).

Inductive basic_ctx : aset → ctx → Prop :=
  | Basic_CtxEmpty D :
      basic_ctx D CtxEmpty
  | Basic_CtxBind D x τ :
      x ∉ D →
      basic_choice_ty D τ →
      basic_ctx D (CtxBind x τ)
  | Basic_CtxComma D Γ1 Γ2 :
      basic_ctx D Γ1 →
      basic_ctx (D ∪ ctx_dom Γ1) Γ2 →
      ctx_dom Γ1 ## ctx_dom Γ2 →
      basic_ctx D (CtxComma Γ1 Γ2)
  | Basic_CtxStar D Γ1 Γ2 :
      basic_ctx D Γ1 →
      basic_ctx D Γ2 →
      ctx_dom Γ1 ## ctx_dom Γ2 →
      basic_ctx D (CtxStar Γ1 Γ2)
  | Basic_CtxSum D Γ1 Γ2 :
      basic_ctx D Γ1 →
      basic_ctx D Γ2 →
      ctx_dom Γ1 = ctx_dom Γ2 →
      erase_ctx Γ1 = erase_ctx Γ2 →
      basic_ctx D (CtxSum Γ1 Γ2).

#[global] Hint Constructors basic_choice_ty basic_ctx : core.

(** ** Top-level well-formedness wrappers *)

Definition basic_choice_ty_closed (τ : choice_ty) : Prop :=
  basic_choice_ty ∅ τ.

Definition basic_ctx_closed (Γ : ctx) : Prop :=
  basic_ctx ∅ Γ.

(** ** Regularity and domain facts

    These statements are the small facts expected from the paper-level
    formation checks.  Proofs are intentionally left for the proof pass. *)

Lemma basic_qualifier_open_lc D q x :
  basic_qualifier (D ∪ {[x]}) (qual_open_atom 0 x q) →
  lc_qualifier (qual_open_atom 0 x q).
Proof. Admitted.

Lemma basic_qualifier_body_lc D q :
  basic_qualifier_body D q →
  body_qualifier q.
Proof. Admitted.

Lemma basic_choice_ty_lc D τ :
  basic_choice_ty D τ →
  lc_choice_ty τ.
Proof. Admitted.

Lemma basic_choice_ty_fv_subset D τ :
  basic_choice_ty D τ →
  fv_cty τ ⊆ D.
Proof. Admitted.

Lemma basic_ctx_dom_fresh D Γ :
  basic_ctx D Γ →
  ctx_dom Γ ## D.
Proof. Admitted.

Lemma basic_ctx_comma_dom_disjoint D Γ1 Γ2 :
  basic_ctx D (CtxComma Γ1 Γ2) →
  ctx_dom Γ1 ## ctx_dom Γ2.
Proof. Admitted.

Lemma basic_ctx_fv_subset D Γ :
  basic_ctx D Γ →
  ctx_fv Γ ⊆ D ∪ ctx_dom Γ.
Proof. Admitted.

Lemma basic_ctx_erase_dom D Γ :
  basic_ctx D Γ →
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof. Admitted.

Lemma basic_ctx_closed_fv Γ :
  basic_ctx_closed Γ →
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof. Admitted.
