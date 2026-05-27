(** * ContextTypeLanguage.WFContext

    Formation/scoping predicates for type contexts. *)

From ContextTypeLanguage Require Export WFContextTy.

Fixpoint basic_ctx (D : aset) (Γ : ctx) : Prop :=
  match Γ with
  | CtxEmpty => True
  | CtxBind x τ =>
      x ∉ D /\ basic_context_ty D τ
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

#[global] Instance scoped_ctx : ScopedIn ctx := basic_ctx.

Notation "D '⊢sΓ' Γ" := (basic_ctx D Γ)
  (at level 40, Γ at level 40, only printing).

Lemma scoped_ctx_iff D Γ :
  D ⊢s Γ <-> basic_ctx D Γ.
Proof. reflexivity. Qed.

Lemma basic_ctx_weaken_fresh D E Γ :
  D ⊆ E ->
  ctx_dom Γ ## E ->
  basic_ctx D Γ ->
  basic_ctx E Γ.
Proof.
  induction Γ in D, E |- *; cbn [basic_ctx ctx_dom]; intros HDE Hdom Hbasic.
  - exact I.
  - destruct Hbasic as [Hx Hτ]. split.
    + set_solver.
    + eapply basic_context_ty_mono; [exact HDE|exact Hτ].
  - destruct Hbasic as [H1 [H2 Hdisj]]. repeat split.
    + eapply IHΓ1; [exact HDE|set_solver|exact H1].
    + eapply (IHΓ2 (D ∪ ctx_dom Γ1) (E ∪ ctx_dom Γ1)).
      * set_solver.
      * set_solver.
      * exact H2.
    + exact Hdisj.
  - destruct Hbasic as [H1 [H2 Hdisj]]. repeat split.
    + eapply IHΓ1; [exact HDE|set_solver|exact H1].
    + eapply IHΓ2; [exact HDE|set_solver|exact H2].
    + exact Hdisj.
  - destruct Hbasic as [H1 [H2 [Hdom12 Herase]]]. repeat split.
    + eapply IHΓ1; [exact HDE|set_solver|exact H1].
    + eapply IHΓ2; [exact HDE|set_solver|exact H2].
    + exact Hdom12.
    + exact Herase.
Qed.

Lemma basic_ctx_fv_subset D Γ :
  basic_ctx D Γ ->
  ctx_fv Γ ⊆ D.
Proof.
  induction Γ in D |- *; cbn [basic_ctx ctx_fv ctx_dom]; intros Hbasic.
  - set_solver.
  - destruct Hbasic as [_ Hτ].
    apply basic_context_ty_fv_subset. exact Hτ.
  - destruct Hbasic as [H1 [H2 _]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 (D ∪ ctx_dom Γ1) H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 _]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 [_ _]]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
Qed.

Lemma basic_ctx_fv_subset_weak D Γ :
  basic_ctx D Γ ->
  ctx_fv Γ ⊆ D ∪ ctx_dom Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_fv_subset D Γ Hbasic). set_solver.
Qed.

Lemma basic_ctx_dom_fresh D Γ :
  basic_ctx D Γ ->
  ctx_dom Γ ## D.
Proof.
  induction Γ in D |- *; cbn [basic_ctx ctx_dom]; intros Hbasic.
  - set_solver.
  - destruct Hbasic as [Hx _]. set_solver.
  - destruct Hbasic as [H1 [H2 Hdisj]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 (D ∪ ctx_dom Γ1) H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 _]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
  - destruct Hbasic as [H1 [H2 [_ _]]].
    specialize (IHΓ1 D H1).
    specialize (IHΓ2 D H2).
    set_solver.
Qed.

Lemma basic_ctx_dom_fv_disjoint D Γ :
  basic_ctx D Γ ->
  ctx_dom Γ ## ctx_fv Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_dom_fresh D Γ Hbasic).
  pose proof (basic_ctx_fv_subset D Γ Hbasic).
  set_solver.
Qed.

Lemma basic_ctx_bind_lc D x τ :
  basic_ctx D (CtxBind x τ) ->
  lc_context_ty τ.
Proof.
  intros [_ Hτ]. apply (basic_context_ty_lc D). exact Hτ.
Qed.

Lemma basic_ctx_lc D Γ :
  basic_ctx D Γ ->
  forall x τ, Γ = CtxBind x τ -> lc_context_ty τ.
Proof.
  intros Hbasic x τ ->.
  apply (basic_ctx_bind_lc D x τ). exact Hbasic.
Qed.

Lemma basic_ctx_erase_dom D Γ :
  basic_ctx D Γ ->
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof.
  induction Γ in D |- *; cbn [basic_ctx erase_ctx ctx_dom]; intros Hbasic.
  - rewrite dom_empty_L. reflexivity.
  - apply (dom_singleton_L (M := gmap atom) (D := gset atom)).
  - destruct Hbasic as [H1 [H2 _]].
    change (dom (erase_ctx Γ1 ∪ erase_ctx Γ2) = ctx_dom Γ1 ∪ ctx_dom Γ2).
    transitivity (dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2)).
    + apply (dom_union_L (M := gmap atom) (D := gset atom)).
    + rewrite (IHΓ1 D) by exact H1.
      rewrite (IHΓ2 (D ∪ ctx_dom Γ1)) by exact H2.
      reflexivity.
  - destruct Hbasic as [H1 [H2 _]].
    change (dom (erase_ctx Γ1 ∪ erase_ctx Γ2) = ctx_dom Γ1 ∪ ctx_dom Γ2).
    transitivity (dom (erase_ctx Γ1) ∪ dom (erase_ctx Γ2)).
    + apply (dom_union_L (M := gmap atom) (D := gset atom)).
    + rewrite (IHΓ1 D) by exact H1.
      rewrite (IHΓ2 D) by exact H2.
      reflexivity.
  - destruct Hbasic as [H1 [_ [Hdom _]]].
    rewrite (IHΓ1 D) by exact H1.
    set_solver.
Qed.

Lemma basic_ctx_empty_fv Γ :
  basic_ctx ∅ Γ ->
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_fv_subset ∅ Γ Hbasic).
  set_solver.
Qed.
