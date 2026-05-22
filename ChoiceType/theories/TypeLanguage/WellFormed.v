(** * ChoiceType.TypeLanguage.WellFormed

    Formation/scoping for the type-language fragment.

    The old constructor-heavy [basic_choice_ty] judgment is replaced by a
    depth-indexed local-nameless predicate.  A bound lvar is accepted exactly
    when it is under enough binders; a free lvar is accepted exactly when its
    atom lies in the ambient domain. *)

From ChoiceType.TypeLanguage Require Export Syntax.

Definition lvar_wf_at (d : nat) (D : aset) (v : logic_var) : Prop :=
  match v with
  | LVFree x => x ∈ D
  | LVBound k => k < d
  end.

Definition lvars_wf_at (d : nat) (D : aset) (L : lvset) : Prop :=
  forall v, v ∈ L -> lvar_wf_at d D v.

Definition lvars_lc_at (d : nat) (L : lvset) : Prop :=
  forall k, k ∈ lvars_bv L -> k < d.

Fixpoint cty_lc_at (d : nat) (τ : choice_ty) : Prop :=
  match τ with
  | CTOver _ φ | CTUnder _ φ =>
      lvars_lc_at (S d) (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 =>
      cty_lc_at d τ1 /\ cty_lc_at d τ2
  | CTArrow τx τ
  | CTWand τx τ =>
      cty_lc_at d τx /\ cty_lc_at (S d) τ
  end.

Definition lc_choice_ty (τ : choice_ty) : Prop :=
  cty_lc_at 0 τ.

Fixpoint wf_choice_ty_at (d : nat) (D : aset) (τ : choice_ty) : Prop :=
  match τ with
  | CTOver _ φ | CTUnder _ φ =>
      lvars_wf_at (S d) D (qual_vars φ)
  | CTInter τ1 τ2
  | CTUnion τ1 τ2
  | CTSum τ1 τ2 =>
      wf_choice_ty_at d D τ1 /\
      wf_choice_ty_at d D τ2 /\
      erase_ty τ1 = erase_ty τ2
  | CTArrow τx τ
  | CTWand τx τ =>
      wf_choice_ty_at d D τx /\
      wf_choice_ty_at (S d) D τ
  end.

Definition basic_choice_ty (D : aset) (τ : choice_ty) : Prop :=
  wf_choice_ty_at 0 D τ.

Fixpoint basic_ctx (D : aset) (Γ : ctx) : Prop :=
  match Γ with
  | CtxEmpty => True
  | CtxBind x τ =>
      x ∉ D /\ basic_choice_ty D τ
  | CtxComma Γ1 Γ2 =>
      basic_ctx D Γ1 /\
      basic_ctx (D ∪ ctx_dom Γ1) Γ2 /\
      ctx_dom Γ1 ## ctx_dom Γ2
  | CtxStar Γ1 Γ2 =>
      basic_ctx D Γ1 /\
      basic_ctx D Γ2 /\
      ctx_dom Γ1 ## ctx_dom Γ2
  | CtxSum Γ1 Γ2 =>
      basic_ctx D Γ1 /\
      basic_ctx D Γ2 /\
      ctx_dom Γ1 = ctx_dom Γ2 /\
      erase_ctx Γ1 = erase_ctx Γ2
  end.

#[global] Instance lc_cty_inst : Lc choice_ty := lc_choice_ty.
Arguments lc_cty_inst /.

Class ScopedIn A := scoped_in : aset -> A -> Prop.

#[global] Instance scoped_choice_ty : ScopedIn choice_ty := basic_choice_ty.
#[global] Instance scoped_ctx : ScopedIn ctx := basic_ctx.

Notation "D '⊢s' x" := (scoped_in D x)
  (at level 40, x at level 40).
Notation "D '⊢sτ' τ" := (basic_choice_ty D τ)
  (at level 40, τ at level 40, only printing).
Notation "D '⊢sΓ' Γ" := (basic_ctx D Γ)
  (at level 40, Γ at level 40, only printing).

Lemma scoped_choice_ty_iff D τ :
  D ⊢s τ <-> basic_choice_ty D τ.
Proof. reflexivity. Qed.

Lemma scoped_ctx_iff D Γ :
  D ⊢s Γ <-> basic_ctx D Γ.
Proof. reflexivity. Qed.

Lemma lvars_wf_at_mono d D E L :
  D ⊆ E ->
  lvars_wf_at d D L ->
  lvars_wf_at d E L.
Proof.
Admitted.

Lemma lvars_wf_at_lc d D L :
  lvars_wf_at d D L ->
  lvars_lc_at d L.
Proof.
Admitted.

Lemma lvars_wf_at_fv_subset d D L :
  lvars_wf_at d D L ->
  lvars_fv L ⊆ D.
Proof.
Admitted.

Lemma lvars_wf_at_drop_fresh d D x L :
  x ∉ lvars_fv L ->
  lvars_wf_at d (D ∪ {[x]}) L ->
  lvars_wf_at d D L.
Proof.
Admitted.

Lemma lvars_wf_at_open_body D L x :
  x ∉ D ->
  lvars_wf_at 1 D L ->
  lvars_wf_at 0 (D ∪ {[x]}) (lvars_open 0 x L).
Proof.
Admitted.

Lemma lvars_wf_at_shift d D L k :
  d <= k ->
  lvars_wf_at d D L ->
  lvars_wf_at d D (lvars_shift_from k L).
Proof.
Admitted.

Lemma wf_choice_ty_at_shift d D τ k :
  d <= k ->
  wf_choice_ty_at d D τ ->
  wf_choice_ty_at d D (cty_shift k τ).
Proof.
Admitted.

Lemma wf_choice_ty_at_mono d D E τ :
  D ⊆ E ->
  wf_choice_ty_at d D τ ->
  wf_choice_ty_at d E τ.
Proof.
Admitted.

Lemma basic_choice_ty_mono D E τ :
  D ⊆ E ->
  basic_choice_ty D τ ->
  basic_choice_ty E τ.
Proof.
Admitted.

Lemma wf_choice_ty_at_lc d D τ :
  wf_choice_ty_at d D τ ->
  cty_lc_at d τ.
Proof.
Admitted.

Lemma basic_choice_ty_lc D τ :
  basic_choice_ty D τ ->
  lc_choice_ty τ.
Proof.
Admitted.

Lemma lc_choice_ty_lvars_bv_empty τ :
  lc_choice_ty τ ->
  lvars_bv (choice_ty_lvars τ) = ∅.
Proof.
Admitted.

Lemma lc_choice_ty_lvars_subset_atoms τ :
  lc_choice_ty τ ->
  choice_ty_lvars τ ⊆ lvars_of_atoms (fv_cty τ).
Proof.
Admitted.

Lemma wf_choice_ty_at_fv_subset d D τ :
  wf_choice_ty_at d D τ ->
  fv_cty τ ⊆ D.
Proof.
Admitted.

Lemma basic_choice_ty_fv_subset D τ :
  basic_choice_ty D τ ->
  fv_cty τ ⊆ D.
Proof.
Admitted.

Lemma basic_choice_ty_lvar_cty_vars_equiv D τ1 τ2 :
  τ1 ≡τv τ2 ->
  basic_choice_ty D τ1 ->
  basic_choice_ty D τ2.
Proof.
Admitted.

Lemma basic_choice_ty_drop_fresh D x τ :
  x ∉ fv_cty τ ->
  basic_choice_ty (D ∪ {[x]}) τ ->
  basic_choice_ty D τ.
Proof.
Admitted.

Lemma basic_choice_ty_drop_insert_fresh
    (Σ : gmap atom ty) x T τ :
  x ∉ dom Σ ->
  x ∉ fv_cty τ ->
  basic_choice_ty (dom (<[x := T]> Σ)) τ ->
  basic_choice_ty (dom Σ) τ.
Proof.
Admitted.

Lemma lc_choice_ty_open_fresh k x τ :
  lc_choice_ty τ ->
  x ∉ fv_cty τ ->
  {k ~> x} τ = τ.
Proof.
Admitted.

Lemma basic_choice_ty_open_body D τ x :
  x ∉ D ->
  wf_choice_ty_at 1 D τ ->
  basic_choice_ty (D ∪ {[x]}) ({0 ~> x} τ).
Proof.
Admitted.

Lemma basic_choice_ty_open_body_cofinite D τ (L0 : aset) :
  wf_choice_ty_at 1 D τ ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_choice_ty (D ∪ {[y]}) ({0 ~> y} τ).
Proof.
Admitted.

Lemma basic_choice_ty_arrow_inv D τx τ :
  basic_choice_ty D (CTArrow τx τ) ->
  basic_choice_ty D τx /\ wf_choice_ty_at 1 D τ.
Proof.
Admitted.

Lemma basic_choice_ty_wand_inv D τx τ :
  basic_choice_ty D (CTWand τx τ) ->
  basic_choice_ty D τx /\ wf_choice_ty_at 1 D τ.
Proof.
Admitted.

Lemma basic_choice_ty_open_arrow_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_choice_ty (dom Δ) (CTArrow τx τ) ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_choice_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
Admitted.

Lemma basic_choice_ty_open_wand_body_cofinite
    (Δ : gmap atom ty) τx τ (L0 : gset atom) :
  basic_choice_ty (dom Δ) (CTWand τx τ) ->
  exists L,
    L0 ⊆ L /\
    forall y,
      y ∉ L ->
      basic_choice_ty (dom (<[y := erase_ty τx]> Δ)) ({0 ~> y} τ).
Proof.
Admitted.

Lemma basic_choice_ty_shift D τ k :
  basic_choice_ty D τ ->
  basic_choice_ty D (cty_shift k τ).
Proof.
Admitted.

Lemma basic_ctx_weaken_fresh D E Γ :
  D ⊆ E ->
  ctx_dom Γ ## E ->
  basic_ctx D Γ ->
  basic_ctx E Γ.
Proof.
Admitted.

Lemma basic_ctx_fv_subset D Γ :
  basic_ctx D Γ ->
  ctx_fv Γ ⊆ D.
Proof.
Admitted.

Lemma basic_ctx_fv_subset_weak D Γ :
  basic_ctx D Γ ->
  ctx_fv Γ ⊆ D ∪ ctx_dom Γ.
Proof.
Admitted.

Lemma basic_ctx_dom_fresh D Γ :
  basic_ctx D Γ ->
  ctx_dom Γ ## D.
Proof.
Admitted.

Lemma basic_ctx_dom_fv_disjoint D Γ :
  basic_ctx D Γ ->
  ctx_dom Γ ## ctx_fv Γ.
Proof.
Admitted.

Lemma basic_ctx_bind_lc D x τ :
  basic_ctx D (CtxBind x τ) ->
  lc_choice_ty τ.
Proof.
Admitted.

Lemma basic_ctx_lc D Γ :
  basic_ctx D Γ ->
  forall x τ, Γ = CtxBind x τ -> lc_choice_ty τ.
Proof.
Admitted.

Lemma basic_ctx_erase_dom D Γ :
  basic_ctx D Γ ->
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof.
Admitted.

Lemma basic_ctx_empty_fv Γ :
  basic_ctx ∅ Γ ->
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
Admitted.
