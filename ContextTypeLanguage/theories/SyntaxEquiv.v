(** * ContextTypeLanguage.SyntaxEquiv

    Variables-equivalence and context support lemmas. *)

From Stdlib Require Import Classes.RelationClasses.
From ContextTypeLanguage Require Export SyntaxOpen.

Fixpoint cty_vars_equiv (τ1 τ2 : context_ty) : Prop :=
  match τ1, τ2 with
  | CTOver b1 φ1, CTOver b2 φ2 =>
      b1 = b2 /\ qual_vars φ1 = qual_vars φ2
  | CTUnder b1 φ1, CTUnder b2 φ2 =>
      b1 = b2 /\ qual_vars φ1 = qual_vars φ2
  | CTInter τ11 τ12, CTInter τ21 τ22
  | CTUnion τ11 τ12, CTUnion τ21 τ22
  | CTSum τ11 τ12, CTSum τ21 τ22
  | CTArrow τ11 τ12, CTArrow τ21 τ22
  | CTWand τ11 τ12, CTWand τ21 τ22 =>
      cty_vars_equiv τ11 τ21 /\ cty_vars_equiv τ12 τ22
  | _, _ => False
  end.

Notation "τ1 ≡τv τ2" := (cty_vars_equiv τ1 τ2)
  (at level 70, no associativity).

Class VarsEquiv (A : Type) := vars_equiv : relation A.

Notation "x ≈v y" := (vars_equiv x y)
  (at level 70, no associativity).

#[global] Instance vars_equiv_context_ty : VarsEquiv context_ty :=
  cty_vars_equiv.

#[global] Instance cty_vars_equiv_equivalence : Equivalence cty_vars_equiv.
Proof.
  split.
  - intro τ. induction τ; cbn [cty_vars_equiv]; try split; eauto.
  - intros τ1 τ2. induction τ1 in τ2 |- *.
    all: destruct τ2; cbn [cty_vars_equiv]; try tauto;
      intros H; destruct H as [H1 H2]; split; try congruence;
      try symmetry; eauto.
  - intros τ1 τ2 τ3. induction τ1 in τ2, τ3 |- *.
    all: destruct τ2, τ3; cbn [cty_vars_equiv]; try tauto;
      intros Hxy Hyz; destruct Hxy as [Hxy1 Hxy2];
      destruct Hyz as [Hyz1 Hyz2]; split; try congruence;
      try etransitivity; eauto.
Qed.

#[global] Instance cty_vars_equiv_preorder : PreOrder cty_vars_equiv.
Proof.
  split.
  - intro τ. reflexivity.
  - intros τ1 τ2 τ3 H12 H23. transitivity τ2; assumption.
Qed.

#[global] Instance vars_equiv_context_ty_equivalence :
  Equivalence (@vars_equiv context_ty vars_equiv_context_ty).
Proof.
  apply cty_vars_equiv_equivalence.
Qed.

#[global] Instance vars_equiv_context_ty_preorder :
  PreOrder (@vars_equiv context_ty vars_equiv_context_ty).
Proof.
  apply cty_vars_equiv_preorder.
Qed.

Lemma cty_vars_equiv_erase τ1 τ2 :
  τ1 ≡τv τ2 ->
  erase_ty τ1 = erase_ty τ2.
Proof.
  induction τ1 in τ2 |- *; destruct τ2; cbn [cty_vars_equiv erase_ty];
    try tauto; intros H; destruct H as [H1 H2]; subst; eauto;
    rewrite ?(IHτ1_1 _ H1), ?(IHτ1_2 _ H2); reflexivity.
Qed.

Lemma cty_vars_equiv_open k x τ1 τ2 :
  τ1 ≡τv τ2 ->
  {k ~> x} τ1 ≡τv {k ~> x} τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_open open_one open_cty_atom_inst];
    try tauto; intros H; destruct H as [H1 H2]; split; try congruence;
    try (rewrite !qual_open_atom_vars, H2; reflexivity);
    try (apply IHτ1_1; exact H1);
    try (apply IHτ1_2; exact H2).
Qed.

Lemma cty_vars_equiv_shift_from k τ1 τ2 :
  τ1 ≡τv τ2 ->
  cty_shift k τ1 ≡τv cty_shift k τ2.
Proof.
  induction τ1 in k, τ2 |- *; destruct τ2;
    cbn [cty_vars_equiv cty_shift]; try tauto; intros H;
    destruct H as [H1 H2].
  - split; [congruence |].
    rewrite !qual_shift_from_vars, H2. reflexivity.
  - split; [congruence |].
    rewrite !qual_shift_from_vars, H2. reflexivity.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
  - split; [apply IHτ1_1 | apply IHτ1_2]; assumption.
Qed.

Lemma ctx_stale_eq_fv_dom Γ :
  ctx_stale Γ = ctx_fv Γ ∪ ctx_dom Γ.
Proof.
  induction Γ; simpl.
  - set_solver.
  - set_solver.
  - apply set_eq. intros z.
    rewrite IHΓ1, IHΓ2.
    rewrite !elem_of_union, elem_of_difference.
    split.
    + intros [[Hzfv1 | Hzdom1] | [Hzfv2 | Hzdom2]].
      * left. left. exact Hzfv1.
      * right. left. exact Hzdom1.
      * destruct (decide (z ∈ ctx_dom Γ1)) as [Hzdom1 | Hznotdom1].
        -- right. left. exact Hzdom1.
        -- left. right. split; [exact Hzfv2 | exact Hznotdom1].
      * right. right. exact Hzdom2.
    + intros [[Hzfv1 | [Hzfv2 Hznotdom1]] | [Hzdom1 | Hzdom2]].
      * left. left. exact Hzfv1.
      * right. left. exact Hzfv2.
      * left. right. exact Hzdom1.
      * right. right. exact Hzdom2.
  - rewrite IHΓ1, IHΓ2. set_solver.
  - rewrite IHΓ1, IHΓ2. set_solver.
Qed.

Lemma erase_ctx_dom_subset Γ :
  dom (erase_ctx Γ) ⊆ ctx_dom Γ.
Proof.
  induction Γ as [|x τ|Γ1 IH1 Γ2 IH2|Γ1 IH1 Γ2 IH2|Γ1 IH1 Γ2 IH2]; simpl.
  - rewrite dom_empty_L. set_solver.
  - intros y Hy. set_unfold.
    rewrite elem_of_dom in Hy. destruct Hy as [v Hy].
    destruct (decide (x = y)) as [-> | Hneq]; [reflexivity |].
    unfold store_singleton, Store, StoreA in Hy.
    pose proof (lookup_singleton_ne (M:=gmap atom) x y (erase_ty τ) Hneq) as Hnone.
    rewrite Hnone in Hy. discriminate.
  - intros y Hy. set_unfold.
    destruct Hy as [Hy | Hy].
    + pose proof (IH1 y Hy). set_solver.
    + pose proof (IH2 y Hy). set_solver.
  - intros y Hy. set_unfold.
    destruct Hy as [Hy | Hy].
    + pose proof (IH1 y Hy). set_solver.
    + pose proof (IH2 y Hy). set_solver.
  - intros y Hy. pose proof (IH1 y Hy). set_solver.
Qed.

Lemma ctx_dom_subset_stale Γ :
  ctx_dom Γ ⊆ ctx_stale Γ.
Proof.
  induction Γ; simpl; set_solver.
Qed.
