(** * ChoiceTyping.Naming

    Small proof-layer helpers for binder representatives.  These definitions
    keep the tlet proofs from repeatedly rebuilding the same freshness,
    context-domain, and open/substitution side conditions. *)

From CoreLang Require Import Instantiation InstantiationProps.
From ChoiceTyping Require Export Typing.
From ChoicePrelude Require Import Store.
From ChoiceAlgebra Require Import ResourceInterface.
From ChoiceTypeLanguage Require Import SyntaxOpen.

(** ** Fresh representatives for tlet body binders *)

Definition tlet_fresh_avoid
    (L X : aset) (τ : choice_ty) (e : tm) (m : WfWorldT) : aset :=
  L ∪ world_dom (m : WorldT) ∪ X ∪ fv_cty τ ∪ fv_tm e.

Record tlet_fresh_name
    (L X : aset) (τ : choice_ty) (e : tm) (m : WfWorldT) (x : atom) : Prop := {
  tlet_fresh_notin_L : x ∉ L;
  tlet_fresh_notin_world : x ∉ world_dom (m : WorldT);
  tlet_fresh_notin_body : x ∉ X ∪ fv_cty τ ∪ fv_tm e;
}.

Lemma tlet_fresh_name_for
    L X τ e (m : WfWorldT) :
  tlet_fresh_name L X τ e m
    (fresh_for (tlet_fresh_avoid L X τ e m)).
Proof.
  pose proof (fresh_for_not_in (tlet_fresh_avoid L X τ e m)) as Hfresh.
  constructor; unfold tlet_fresh_avoid in Hfresh; set_solver.
Qed.

(** A lighter variant for totality lemmas that only mention a body term, not a
    result refinement type. *)

Definition body_fresh_avoid
    (L X : aset) (e : tm) (m : WfWorldT) : aset :=
  L ∪ world_dom (m : WorldT) ∪ X ∪ fv_tm e.

Record body_fresh_name
    (L X : aset) (e : tm) (m : WfWorldT) (x : atom) : Prop := {
  body_fresh_notin_L : x ∉ L;
  body_fresh_notin_world : x ∉ world_dom (m : WorldT);
  body_fresh_notin_X : x ∉ X;
  body_fresh_notin_fv_tm : x ∉ fv_tm e;
}.

Lemma body_fresh_name_for
    L X e (m : WfWorldT) :
  body_fresh_name L X e m
    (fresh_for (body_fresh_avoid L X e m)).
Proof.
  pose proof (fresh_for_not_in (body_fresh_avoid L X e m)) as Hfresh.
  constructor; unfold body_fresh_avoid in Hfresh; set_solver.
Qed.

Ltac pick_tlet_fresh x L X τ e m :=
  let Hfresh := fresh "Hfresh" in
  set (x := fresh_for (tlet_fresh_avoid L X τ e m));
  pose proof (tlet_fresh_name_for L X τ e m) as Hfresh;
  change (tlet_fresh_name L X τ e m x) in Hfresh.

Ltac pick_body_fresh x L X e m :=
  let Hfresh := fresh "Hfresh" in
  set (x := fresh_for (body_fresh_avoid L X e m));
  pose proof (body_fresh_name_for L X e m) as Hfresh;
  change (body_fresh_name L X e m x) in Hfresh.

(** ** Context binder normal forms *)

Lemma erase_ctx_under_comma_bind_dom_nf Σ Γ x τ :
  dom (erase_ctx_under Σ (CtxComma Γ (CtxBind x τ))) =
  dom (erase_ctx_under Σ Γ) ∪ {[x]}.
Proof.
  unfold erase_ctx_under.
  cbn [erase_ctx].
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hz].
    apply store_lookup_union_Some_raw in Hz as [HzΣ|[HΣ Hzrest]].
    + apply elem_of_union_l. apply elem_of_dom. exists T.
      apply store_lookup_union_Some_raw. left. exact HzΣ.
    + apply store_lookup_union_Some_raw in Hzrest as [HzΓ|[_ Hzx]].
      * apply elem_of_union_l. apply elem_of_dom. exists T.
        apply store_lookup_union_Some_raw. right. eauto.
      * cbv [ChoicePrelude.StoreInterfaceCore.store_singleton map_singleton
          singleton singletonM insert ChoicePrelude.StoreInterfaceCore.store_insert
          map_insert] in Hzx.
        destruct (decide (z = x)) as [->|Hzx_ne]; [set_solver|].
        change ((partial_alter (λ _ : option ty, Some (erase_ty τ))
          x (∅ : gmap atom ty)) !! z = Some T) in Hzx.
        rewrite (lookup_partial_alter_ne (K := atom) (M := gmap atom)) in Hzx
          by congruence.
        rewrite lookup_empty in Hzx. discriminate.
  - intros Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_dom in Hz as [T Hz].
      apply elem_of_dom.
      apply store_lookup_union_Some_raw in Hz as [HzΣ|[HΣ HzΓ]].
      * exists T. apply store_lookup_union_Some_raw. left. exact HzΣ.
      * exists T. apply store_lookup_union_Some_raw. right.
        split; [exact HΣ|]. apply store_lookup_union_Some_raw. left. exact HzΓ.
    + apply elem_of_singleton in Hz. subst z.
      destruct (Σ !! x) as [TΣ|] eqn:HΣ.
      * apply elem_of_dom. exists TΣ.
        apply store_lookup_union_Some_raw. left. exact HΣ.
      * destruct (erase_ctx Γ !! x) as [TΓ|] eqn:HΓ.
        -- apply elem_of_dom. exists TΓ.
           apply store_lookup_union_Some_raw. right. split; [exact HΣ|].
           apply store_lookup_union_Some_raw. left. exact HΓ.
        -- apply elem_of_dom. exists (erase_ty τ).
           apply store_lookup_union_Some_raw. right. split; [exact HΣ|].
           apply store_lookup_union_Some_raw. right.
           split.
           ++ exact HΓ.
           ++ cbv [ChoicePrelude.StoreInterfaceCore.store_singleton map_singleton
                singleton singletonM insert ChoicePrelude.StoreInterfaceCore.store_insert
                map_insert].
              change ((partial_alter (λ _ : option ty, Some (erase_ty τ))
                x (∅ : gmap atom ty)) !! x = Some (erase_ty τ)).
              rewrite (lookup_partial_alter_eq (K := atom) (M := gmap atom)).
              reflexivity.
Qed.

Lemma erase_ctx_under_comma_bind_env_fresh Σ Γ x τ :
  x ∉ dom (erase_ctx_under Σ Γ) →
  erase_ctx_under Σ (CtxComma Γ (CtxBind x τ)) =
  <[x := erase_ty τ]> (erase_ctx_under Σ Γ).
Proof.
  intros Hfresh.
  unfold erase_ctx_under in *.
  cbn [erase_ctx] in *.
  assert (HxΣ : x ∉ dom Σ).
  { intros HxΣ. apply Hfresh.
    apply elem_of_dom in HxΣ as [T HxΣ].
    apply elem_of_dom. exists T.
    apply store_lookup_union_Some_raw. left. exact HxΣ. }
  assert (HxΓ : x ∉ dom (erase_ctx Γ)).
  { intros HxΓ. apply Hfresh.
    apply elem_of_dom in HxΓ as [T HxΓ].
    apply elem_of_dom. exists T.
    apply store_lookup_union_Some_raw. right.
    split.
    - apply store_lookup_none_of_not_elem_dom. exact HxΣ.
    - exact HxΓ. }
  change (Σ ∪ ((erase_ctx Γ : @StoreA ty atom _ _) ∪
      ({[x := erase_ty τ]} : @StoreA ty atom _ _)) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  replace ((erase_ctx Γ : @StoreA ty atom _ _) ∪
      ({[x := erase_ty τ]} : @StoreA ty atom _ _))
    with (<[x := erase_ty τ]> (erase_ctx Γ : @StoreA ty atom _ _)).
  2:{
    symmetry.
    apply (storeA_union_singleton_insert_fresh
      (V := ty) (K := atom) (erase_ctx Γ : @StoreA ty atom _ _)
      x (erase_ty τ)).
    exact HxΓ.
  }
  change (Σ ∪ (<[x := erase_ty τ]> (erase_ctx Γ : gmap atom ty) :
      gmap atom ty) =
    <[x := erase_ty τ]> (Σ ∪ erase_ctx Γ)).
  apply (storeA_insert_union_r_fresh (V := ty) (K := atom)
    (Σ : @StoreA ty atom _ _) (erase_ctx Γ : @StoreA ty atom _ _)
    x (erase_ty τ)).
  exact HxΣ.
Qed.

Lemma erase_ctx_under_dom_basic Σ Γ :
  basic_ctx (dom Σ) Γ →
  dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ.
Proof.
  intros Hbasic.
  unfold erase_ctx_under.
  pose proof (basic_ctx_erase_dom (dom Σ) Γ Hbasic) as HdomΓ.
  apply set_eq. intros z. split.
  - intros Hz.
    apply elem_of_dom in Hz as [T Hz].
    apply store_lookup_union_Some_raw in Hz as [HzΣ|[_ HzΓ]].
    + apply elem_of_union_l. apply elem_of_dom. eauto.
    + apply elem_of_union_r. rewrite <- HdomΓ. apply elem_of_dom. eauto.
  - intros Hz.
    apply elem_of_union in Hz as [HzΣ|HzΓ].
    + apply elem_of_dom in HzΣ as [T HzΣ].
      apply elem_of_dom. exists T.
      apply store_lookup_union_Some_raw. left. exact HzΣ.
    + rewrite <- HdomΓ in HzΓ.
      apply elem_of_dom in HzΓ as [T HzΓ].
      apply elem_of_dom.
      destruct (Σ !! z) as [TΣ|] eqn:HΣ.
      * exists TΣ. apply store_lookup_union_Some_raw. left. exact HΣ.
      * exists T. apply store_lookup_union_Some_raw. right. eauto.
Qed.

Ltac ctx_name_norm :=
  repeat match goal with
  | H : context[dom (erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ)))] |- _ =>
      rewrite (erase_ctx_under_comma_bind_dom_nf Σ Γ x τ) in H
  | |- context[dom (erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ)))] =>
      rewrite (erase_ctx_under_comma_bind_dom_nf Σ Γ x τ)
  | Hfresh : ?x ∉ dom (erase_ctx_under ?Σ ?Γ),
    H : context[erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ))] |- _ =>
      rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ Hfresh) in H
  | Hfresh : ?x ∉ dom (erase_ctx_under ?Σ ?Γ)
      |- context[erase_ctx_under ?Σ (CtxComma ?Γ (CtxBind ?x ?τ))] =>
      rewrite (erase_ctx_under_comma_bind_env_fresh Σ Γ x τ Hfresh)
  end.
