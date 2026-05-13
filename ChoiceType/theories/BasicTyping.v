(** * ChoiceType.BasicTyping

    Paper-level basic formation checks for choice qualifiers, refinement
    types, and tree-shaped choice contexts.

    Type qualifiers are shallow Rocq predicates over untyped stores.  Their
    basic checking therefore records only the syntactic information that the
    embedding exposes: referenced free atoms must be available in the ambient
    domain, and locally-nameless bound variables must be opened in the usual
    cofinite style. *)

From LocallyNameless Require Import Classes.
From ChoiceType Require Export Syntax.
From ChoiceType Require Import QualifierInstances QualifierProps
  LocallyNamelessInstances LocallyNamelessProps.

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

(** ** Paper-judgment notations

    These notations are for printed goals and statements.  Proof scripts should
    keep using the explicit names [basic_choice_ty] and [basic_ctx]. *)

Notation "D '⊢sτ' τ" := (basic_choice_ty D τ)
  (at level 40, τ at level 40, only printing).
Notation "D '⊢sΓ' Γ" := (basic_ctx D Γ)
  (at level 40, Γ at level 40, only printing).

(** ** Regularity and domain facts

    These statements are the small facts expected from the paper-level
    formation checks.  Proofs are intentionally left for the proof pass. *)

Lemma basic_qualifier_open_lc D q x :
  basic_qualifier (D ∪ {[x]}) (qual_open_atom 0 x q) →
  lc_qualifier (qual_open_atom 0 x q).
Proof. intros [_ Hlc]. exact Hlc. Qed.

Lemma basic_qualifier_body_lc D q :
  basic_qualifier_body D q →
  body_qualifier q.
Proof.
  intros [L Hbody]. exists L. intros x Hx.
  eapply basic_qualifier_open_lc. exact (Hbody x Hx).
Qed.

Lemma basic_qualifier_body_fv_subset D q :
  basic_qualifier_body D q →
  qual_dom q ⊆ D.
Proof.
  intros [L Hbody] z Hz.
  set (x := fresh_for (L ∪ {[z]})).
  assert (HxL : x ∉ L) by (subst x; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
  assert (Hzx : z ≠ x) by (subst x; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
  destruct (Hbody x HxL) as [Hdom _].
  pose proof (open_fv' q x 0 z Hz) as Hzopen.
  simpl in Hzopen. pose proof (Hdom z Hzopen) as HzDx. set_solver.
Qed.

Lemma basic_qualifier_body_top D :
  basic_qualifier_body D qual_top.
Proof.
  exists ∅. intros x _.
  unfold basic_qualifier, qual_open_atom, qual_top, qual_dom, qual_bvars.
  simpl. split; set_solver.
Qed.

Lemma basic_choice_ty_lc D τ :
  basic_choice_ty D τ →
  lc_choice_ty τ.
Proof.
  induction 1; eauto using basic_qualifier_body_lc.
Qed.

Lemma basic_qualifier_mono D E q :
  D ⊆ E →
  basic_qualifier D q →
  basic_qualifier E q.
Proof.
  unfold basic_qualifier. set_solver.
Qed.

Lemma basic_qualifier_body_mono D E q :
  D ⊆ E →
  basic_qualifier_body D q →
  basic_qualifier_body E q.
Proof.
  intros HDE [L Hbody].
  exists L. intros x Hx.
  eapply basic_qualifier_mono; [| apply Hbody; exact Hx].
  set_solver.
Qed.

Lemma basic_qualifier_swap x y D q :
  basic_qualifier D q →
  basic_qualifier (aset_swap x y D) (qual_swap_atom x y q).
Proof.
  unfold basic_qualifier.
  rewrite qual_dom_swap, qual_bvars_swap.
  intros [Hdom Hbvars]. split; [| exact Hbvars].
  intros z Hz. rewrite elem_of_aset_swap in Hz.
  rewrite elem_of_aset_swap.
  apply Hdom. exact Hz.
Qed.

Lemma basic_qualifier_body_swap x y D q :
  basic_qualifier_body D q →
  basic_qualifier_body (aset_swap x y D) (qual_swap_atom x y q).
Proof.
  intros [L Hbody].
  exists (aset_swap x y L).
  intros z Hz.
  rewrite qual_open_atom_swap.
  replace (aset_swap x y D ∪ {[z]})
    with (aset_swap x y (D ∪ {[atom_swap x y z]})).
  - apply basic_qualifier_swap.
    apply Hbody.
    intros Hin. apply Hz.
    rewrite elem_of_aset_swap. exact Hin.
  - rewrite aset_swap_union, aset_swap_singleton, atom_swap_involutive.
    reflexivity.
Qed.

Lemma basic_choice_ty_mono D E τ :
  D ⊆ E →
  basic_choice_ty D τ →
  basic_choice_ty E τ.
Proof.
  intros HDE Hbasic.
  revert E HDE.
  induction Hbasic; intros E HDE.
  - constructor. eapply basic_qualifier_body_mono; eauto.
  - constructor. eapply basic_qualifier_body_mono; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply Basic_CTArrow.
    + eauto.
    + intros x Hx.
      match goal with
      | IH : ∀ y, y ∉ _ → ∀ E, _ ⊆ E → basic_choice_ty E _ |- _ =>
          eapply IH; [exact Hx | set_solver]
      end.
  - eapply Basic_CTWand.
    + eauto.
    + intros x Hx.
      match goal with
      | IH : ∀ y, y ∉ _ → ∀ E, _ ⊆ E → basic_choice_ty E _ |- _ =>
          eapply IH; [exact Hx | set_solver]
      end.
Qed.

Lemma basic_choice_ty_swap x y D τ :
  basic_choice_ty D τ →
  basic_choice_ty (aset_swap x y D) (cty_swap_atom x y τ).
Proof.
  induction 1; simpl.
  - constructor. apply basic_qualifier_body_swap. exact H.
  - constructor. apply basic_qualifier_body_swap. exact H.
  - econstructor; eauto.
    rewrite !cty_swap_preserves_erasure. exact H1.
  - econstructor; eauto.
    rewrite !cty_swap_preserves_erasure. exact H1.
  - econstructor; eauto.
    rewrite !cty_swap_preserves_erasure. exact H1.
  - eapply Basic_CTArrow with (L := aset_swap x y L).
    + exact IHbasic_choice_ty.
    + intros z Hz.
      replace (aset_swap x y D ∪ {[z]})
        with (aset_swap x y (D ∪ {[atom_swap x y z]})).
      * rewrite cty_open_swap_atom.
        apply H1.
        intros Hin. apply Hz.
        rewrite elem_of_aset_swap. exact Hin.
      * rewrite aset_swap_union, aset_swap_singleton, atom_swap_involutive.
        reflexivity.
  - eapply Basic_CTWand with (L := aset_swap x y L).
    + exact IHbasic_choice_ty.
    + intros z Hz.
      replace (aset_swap x y D ∪ {[z]})
        with (aset_swap x y (D ∪ {[atom_swap x y z]})).
      * rewrite cty_open_swap_atom.
        apply H1.
        intros Hin. apply Hz.
        rewrite elem_of_aset_swap. exact Hin.
      * rewrite aset_swap_union, aset_swap_singleton, atom_swap_involutive.
        reflexivity.
Qed.

Lemma basic_choice_ty_swap_iff x y D τ :
  basic_choice_ty (aset_swap x y D) (cty_swap_atom x y τ) ↔
  basic_choice_ty D τ.
Proof.
  split.
  - intros Hswap.
    pose proof (basic_choice_ty_swap x y _ _ Hswap) as Hback.
    rewrite aset_swap_involutive in Hback.
    rewrite cty_swap_atom_involutive in Hback.
    exact Hback.
  - apply basic_choice_ty_swap.
Qed.

Lemma basic_choice_ty_drop_fresh D x τ :
  x ∉ fv_cty τ →
  basic_choice_ty (D ∪ {[x]}) τ →
  basic_choice_ty D τ.
Proof.
  intros Hfresh Hbasic.
  remember (D ∪ {[x]}) as E.
  revert D x Hfresh HeqE.
  induction Hbasic as
    [E b φ Hbody
    |E b φ Hbody
    |E τ1 τ2 Hτ1 Hτ2 Herase IHτ1 IHτ2
    |E τ1 τ2 Hτ1 Hτ2 Herase IHτ1 IHτ2
    |E τ1 τ2 Hτ1 Hτ2 Herase IHτ1 IHτ2
    |E τx τ L Hτx Hbody IHτx IHbody
    |E τx τ L Hτx Hbody IHτx IHbody];
    intros D0 x0 Hfresh HeqE; subst; simpl in Hfresh.
  - constructor.
    destruct Hbody as [L Hbody].
    exists (L ∪ {[x0]}). intros y Hy.
    eapply basic_qualifier_mono.
    + set_solver.
    + specialize (Hbody y ltac:(set_solver)).
      unfold basic_qualifier in *.
      destruct Hbody as [Hdom Hbvars]. split; [| exact Hbvars].
      destruct φ as [B d p].
      unfold qual_open_atom, qual_dom in *. simpl in *.
      destruct (decide (0 ∈ B)); simpl in *; set_solver.
  - constructor.
    destruct Hbody as [L Hbody].
    exists (L ∪ {[x0]}). intros y Hy.
    eapply basic_qualifier_mono.
    + set_solver.
    + specialize (Hbody y ltac:(set_solver)).
      unfold basic_qualifier in *.
      destruct Hbody as [Hdom Hbvars]. split; [| exact Hbvars].
      destruct φ as [B d p].
      unfold qual_open_atom, qual_dom in *. simpl in *.
      destruct (decide (0 ∈ B)); simpl in *; set_solver.
  - econstructor; eauto; set_solver.
  - econstructor; eauto; set_solver.
  - econstructor; eauto; set_solver.
  - eapply (Basic_CTArrow _ _ _ (L ∪ {[x0]})).
    + eapply Hbody; eauto; set_solver.
    + intros y Hy.
      assert (HyL : y ∉ L).
      { intros HyL. apply Hy. apply elem_of_union. left. exact HyL. }
      eapply (IHbody y HyL (D0 ∪ {[y]}) x0).
      * pose proof (open_fv τ y 0) as Hopen.
        simpl in Hopen. intros Hxopen.
        pose proof (Hopen x0 Hxopen) as Hxuy.
        apply elem_of_union in Hxuy as [Hxy | Hxτ].
        -- change (x0 ∈ ({[y]} : aset)) in Hxy.
           apply elem_of_singleton in Hxy. subst.
           apply Hy. apply elem_of_union. right. apply elem_of_singleton. reflexivity.
        -- apply Hfresh. apply elem_of_union. right. exact Hxτ.
      * apply set_eq. intros z. split.
        -- intros Hz. apply elem_of_union in Hz as [Hz | Hz].
           ++ apply elem_of_union in Hz as [Hz | Hz].
              ** apply elem_of_union. left. apply elem_of_union. left. exact Hz.
              ** apply elem_of_union. right. exact Hz.
           ++ apply elem_of_union. left. apply elem_of_union. right. exact Hz.
        -- intros Hz. apply elem_of_union in Hz as [Hz | Hz].
           ++ apply elem_of_union in Hz as [Hz | Hz].
              ** apply elem_of_union. left. apply elem_of_union. left. exact Hz.
              ** apply elem_of_union. right. exact Hz.
           ++ apply elem_of_union. left. apply elem_of_union. right. exact Hz.
  - eapply (Basic_CTWand _ _ _ (L ∪ {[x0]})).
    + eapply Hbody; eauto; set_solver.
    + intros y Hy.
      assert (HyL : y ∉ L).
      { intros HyL. apply Hy. apply elem_of_union. left. exact HyL. }
      eapply (IHbody y HyL (D0 ∪ {[y]}) x0).
      * pose proof (open_fv τ y 0) as Hopen.
        simpl in Hopen. intros Hxopen.
        pose proof (Hopen x0 Hxopen) as Hxuy.
        apply elem_of_union in Hxuy as [Hxy | Hxτ].
        -- change (x0 ∈ ({[y]} : aset)) in Hxy.
           apply elem_of_singleton in Hxy. subst.
           apply Hy. apply elem_of_union. right. apply elem_of_singleton. reflexivity.
        -- apply Hfresh. apply elem_of_union. right. exact Hxτ.
      * apply set_eq. intros z. split.
        -- intros Hz. apply elem_of_union in Hz as [Hz | Hz].
           ++ apply elem_of_union in Hz as [Hz | Hz].
              ** apply elem_of_union. left. apply elem_of_union. left. exact Hz.
              ** apply elem_of_union. right. exact Hz.
           ++ apply elem_of_union. left. apply elem_of_union. right. exact Hz.
        -- intros Hz. apply elem_of_union in Hz as [Hz | Hz].
           ++ apply elem_of_union in Hz as [Hz | Hz].
              ** apply elem_of_union. left. apply elem_of_union. left. exact Hz.
              ** apply elem_of_union. right. exact Hz.
           ++ apply elem_of_union. left. apply elem_of_union. right. exact Hz.
Qed.

Lemma basic_choice_ty_drop_insert_fresh
    (Σ : gmap atom ty) x T τ :
  x ∉ dom Σ →
  x ∉ fv_cty τ →
  basic_choice_ty (dom (<[x := T]> Σ)) τ →
  basic_choice_ty (dom Σ) τ.
Proof.
  intros HxΣ Hxτ Hbasic.
  rewrite dom_insert_L in Hbasic.
  replace ({[x]} ∪ dom Σ) with (dom Σ ∪ {[x]}) in Hbasic by set_solver.
  eapply basic_choice_ty_drop_fresh; eauto.
Qed.

Lemma basic_choice_ty_fv_subset D τ :
  basic_choice_ty D τ →
  fv_cty τ ⊆ D.
Proof.
  induction 1; simpl; try set_solver.
  - eapply basic_qualifier_body_fv_subset. exact H.
  - eapply basic_qualifier_body_fv_subset. exact H.
  - intros z Hz.
    apply elem_of_union in Hz as [Hzτx | Hz].
    { set_solver. }
    set (x := fresh_for (L ∪ {[z]})).
    assert (HxL : x ∉ L) by (subst x; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hzx : z ≠ x) by (subst x; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    match goal with
    | IHopen : ∀ x, x ∉ L → fv_cty ({0 ~> x} τ) ⊆ D ∪ {[x]} |- _ =>
        pose proof (IHopen x HxL) as Hfv_open
    end.
    pose proof (open_fv' τ x 0 z Hz) as Hzopen.
    simpl in Hzopen. pose proof (Hfv_open z Hzopen) as HzDx. set_solver.
  - intros z Hz.
    apply elem_of_union in Hz as [Hzτx | Hz].
    { set_solver. }
    set (x := fresh_for (L ∪ {[z]})).
    assert (HxL : x ∉ L) by (subst x; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    assert (Hzx : z ≠ x) by (subst x; pose proof (fresh_for_not_in (L ∪ {[z]})); set_solver).
    match goal with
    | IHopen : ∀ x, x ∉ L → fv_cty ({0 ~> x} τ) ⊆ D ∪ {[x]} |- _ =>
        pose proof (IHopen x HxL) as Hfv_open
    end.
    pose proof (open_fv' τ x 0 z Hz) as Hzopen.
    simpl in Hzopen. pose proof (Hfv_open z Hzopen) as HzDx. set_solver.
Qed.

Lemma basic_ctx_dom_fresh D Γ :
  basic_ctx D Γ →
  ctx_dom Γ ## D.
Proof.
  induction 1; simpl; try set_solver.
Qed.

Lemma basic_ctx_comma_dom_disjoint D Γ1 Γ2 :
  basic_ctx D (CtxComma Γ1 Γ2) →
  ctx_dom Γ1 ## ctx_dom Γ2.
Proof. intros H. inversion H; subst; assumption. Qed.

Lemma basic_ctx_fv_subset D Γ :
  basic_ctx D Γ →
  ctx_fv Γ ⊆ D ∪ ctx_dom Γ.
Proof.
  induction 1; simpl; try set_solver.
  - pose proof (basic_choice_ty_fv_subset D τ H0). set_solver.
Qed.

Lemma basic_ctx_erase_dom D Γ :
  basic_ctx D Γ →
  dom (erase_ctx Γ) = ctx_dom Γ.
Proof.
  induction 1; simpl.
  - rewrite dom_empty_L. reflexivity.
  - rewrite dom_singleton_L. reflexivity.
  - rewrite dom_union_L. set_solver.
  - rewrite dom_union_L. set_solver.
  - rewrite IHbasic_ctx1. set_solver.
Qed.

Lemma basic_ctx_empty_fv Γ :
  basic_ctx ∅ Γ →
  ctx_fv Γ ⊆ ctx_dom Γ.
Proof.
  intros Hbasic.
  pose proof (basic_ctx_fv_subset ∅ Γ Hbasic). set_solver.
Qed.
