(** * BasicDenotation.BasicTypingFormula

    Encoding CoreLang basic type well-formedness side conditions as
    ContextLogic formulas.  We keep only the component formulas; obligation
    wrapper sugar is intentionally avoided on the new route. *)

From CoreLang Require Import LocallyNamelessExtra.
From ContextBasicDenotation Require Import Notation StoreTyping TermSyntax TermEval
  TermOpen TermTLet.
From ContextBase Require Import BaseTactics.

Section BasicTypingFormula.

Lemma basic_world_formula_empty (m : WfWorldT) :
  res_models m (basic_world_formula (∅ : lty_env)).
Proof.
  apply basic_world_formula_models_iff.
  split.
  - rewrite dom_empty_L. unfold lc_lvars. set_solver.
  - split.
    + rewrite dom_empty_L, lvars_fv_empty. set_solver.
    + unfold lworld_has_type, worldA_has_type, storeA_has_type.
      split; [rewrite dom_empty_L; set_solver|].
      intros σ _ v T val Hlookup _.
      rewrite lookup_empty in Hlookup. discriminate.
Qed.

Definition basic_tm_has_ltype_by_open_env
    (Σ : lty_env) (e : tm) (T : ty) : Prop :=
  tm_lvars e ⊆ dom Σ /\
  forall η,
    open_env_fresh_for_lvars η (dom Σ) ->
    lvars_bv (dom Σ) ⊆ dom η ->
    lty_env_to_atom_env (lty_env_open_lvars η Σ) ⊢ₑ
      open_tm_env η e ⋮ T.

Inductive basic_value_has_ltype : lty_env -> value -> ty -> Prop :=
  | BVT_Const Σ c :
      basic_value_has_ltype Σ (vconst c) (TBase (base_ty_of_const c))
  | BVT_FVar Σ x T :
      Σ !! LVFree x = Some T ->
      basic_value_has_ltype Σ (vfvar x) T
  | BVT_BVar Σ k T :
      Σ !! LVBound k = Some T ->
      basic_value_has_ltype Σ (vbvar k) T
  | BVT_Lam Σ s T e (L : aset) :
      (forall x, x ∉ L ->
        basic_tm_has_ltype (<[LVFree x := s]> Σ) (e ^^ x) T) ->
      basic_value_has_ltype Σ (vlam s e) (s →ₜ T)
  | BVT_Fix Σ sx T vf (L : aset) :
      (forall x, x ∉ L ->
        basic_value_has_ltype (<[LVFree x := sx]> Σ) (vf ^^ x)
          ((sx →ₜ T) →ₜ T)) ->
      basic_value_has_ltype Σ (vfix (sx →ₜ T) vf) (sx →ₜ T)

with basic_tm_has_ltype : lty_env -> tm -> ty -> Prop :=
  | BTT_Ret Σ v T :
      basic_value_has_ltype Σ v T ->
      basic_tm_has_ltype Σ (tret v) T
  | BTT_Let Σ T1 T2 e1 e2 (L : aset) :
      basic_tm_has_ltype Σ e1 T1 ->
      (forall x, x ∉ L ->
        basic_tm_has_ltype (<[LVFree x := T1]> Σ) (e2 ^^ x) T2) ->
      basic_tm_has_ltype Σ (tlete e1 e2) T2
  | BTT_Op Σ op v arg_b ret_b :
      prim_op_type op = (arg_b, ret_b) ->
      basic_value_has_ltype Σ v (TBase arg_b) ->
      basic_tm_has_ltype Σ (tprim op v) (TBase ret_b)
  | BTT_App Σ s1 s2 v1 v2 :
      basic_value_has_ltype Σ v1 (s1 →ₜ s2) ->
      basic_value_has_ltype Σ v2 s1 ->
      basic_tm_has_ltype Σ (tapp v1 v2) s2
  | BTT_Match Σ v T et ef :
      basic_value_has_ltype Σ v (TBase TBool) ->
      basic_tm_has_ltype Σ et T ->
      basic_tm_has_ltype Σ ef T ->
      basic_tm_has_ltype Σ (tmatch v et ef) T.

Scheme basic_value_has_ltype_ind' := Induction for basic_value_has_ltype Sort Prop
  with basic_tm_has_ltype_ind' := Induction for basic_tm_has_ltype Sort Prop.
Combined Scheme basic_has_ltype_mutind
  from basic_value_has_ltype_ind', basic_tm_has_ltype_ind'.

Hint Constructors basic_value_has_ltype basic_tm_has_ltype : core.

Lemma basic_tm_has_ltype_lvars Σ e T :
  basic_tm_has_ltype Σ e T ->
  lvars_of_atoms (fv_tm e) ⊆ dom Σ.
Proof.
  induction 1 using basic_tm_has_ltype_ind'
    with (P := fun Σ v T _ => lvars_of_atoms (fv_value v) ⊆ dom Σ);
    cbn [fv_value fv_tm]; try set_solver.
  - match goal with
    | Hlook : _ !! _ = Some _ |- _ =>
        apply elem_of_dom_2 in Hlook; set_solver
    end.
  - set (y := fresh_for (L ∪ fv_tm e ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_tm' e (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
  - set (y := fresh_for (L ∪ fv_value vf ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_value vf ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_value _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_value' vf (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
  - set (y := fresh_for (L ∪ fv_tm e2 ∪ lvars_fv (dom Σ))).
    assert (Hy : y ∉ L ∪ fv_tm e2 ∪ lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    match goal with
    | Hopen_typed : forall z, z ∉ _ ->
        lvars_of_atoms (fv_tm _) ⊆ _ |- _ =>
        pose proof (Hopen_typed y ltac:(set_solver)) as Hopened;
        rewrite dom_insert in Hopened
    end.
    pose proof (open_fv_tm' e2 (vfvar y) 0) as Hopen.
    cbn [fv_value] in Hopen.
    set_solver.
Qed.

Lemma basic_has_ltype_weaken_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    forall Σ',
      Σ ⊆ Σ' ->
      basic_value_has_ltype Σ' v T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    forall Σ',
      Σ ⊆ Σ' ->
      basic_tm_has_ltype Σ' e T).
Proof.
  apply basic_has_ltype_mutind; intros; eauto.
  - econstructor. eapply lookup_weaken; eassumption.
  - econstructor. eapply lookup_weaken; eassumption.
  - eapply BVT_Lam with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    apply insert_mono. exact H0.
  - eapply BVT_Fix with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    apply insert_mono. exact H0.
  - eapply BTT_Let with (L := L).
    + eapply H; exact H1.
    + intros x Hx. eapply H0; [exact Hx|].
      apply insert_mono. exact H1.
Qed.

Lemma basic_value_has_ltype_weaken Σ Σ' v T :
  basic_value_has_ltype Σ v T ->
  Σ ⊆ Σ' ->
  basic_value_has_ltype Σ' v T.
Proof.
  intros Hty Hsub.
  exact (proj1 basic_has_ltype_weaken_mutual Σ v T Hty Σ' Hsub).
Qed.

Lemma basic_tm_has_ltype_weaken Σ Σ' e T :
  basic_tm_has_ltype Σ e T ->
  Σ ⊆ Σ' ->
  basic_tm_has_ltype Σ' e T.
Proof.
  intros Hty Hsub.
  exact (proj2 basic_has_ltype_weaken_mutual Σ e T Hty Σ' Hsub).
Qed.

Lemma basic_has_ltype_lc_mutual :
  (forall Σ v T,
    lc_lvars (dom Σ) ->
    basic_value_has_ltype Σ v T ->
    lc_value v) /\
  (forall Σ e T,
    lc_lvars (dom Σ) ->
    basic_tm_has_ltype Σ e T ->
    lc_tm e).
Proof.
  enough (
    (forall Σ v T (Hty : basic_value_has_ltype Σ v T),
      lc_lvars (dom Σ) -> lc_value v) /\
    (forall Σ e T (Hty : basic_tm_has_ltype Σ e T),
      lc_lvars (dom Σ) -> lc_tm e)) as Hreg.
  {
    split; intros; eapply Hreg; eauto.
  }
  apply basic_has_ltype_mutind
    with (P := fun Σ v T _ => lc_lvars (dom Σ) -> lc_value v)
         (P0 := fun Σ e T _ => lc_lvars (dom Σ) -> lc_tm e);
    intros; eauto.
  - exfalso.
    match goal with
    | Hlc : lc_lvars (dom ?Σ),
      Hlook : ?Σ !! LVBound ?k = Some ?T |- _ =>
        apply (Hlc (LVBound k));
        eapply elem_of_dom_2; exact Hlook
    end.
  - eapply LC_lam with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    + intros v Hv.
      rewrite dom_insert in Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      * rewrite elem_of_singleton in Hv. subst v. exact I.
      * exact (H0 v Hv).
  - eapply LC_fix with (L := L). intros x Hx.
    eapply H; [exact Hx|].
    + intros v Hv.
      rewrite dom_insert in Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      * rewrite elem_of_singleton in Hv. subst v. exact I.
      * exact (H0 v Hv).
  - eapply LC_lete with (L := L).
    + eauto.
    + intros x Hx. eapply H0; [exact Hx|].
      * intros v Hv.
        rewrite dom_insert in Hv.
        apply elem_of_union in Hv as [Hv|Hv].
        -- rewrite elem_of_singleton in Hv. subst v. exact I.
        -- exact (H1 v Hv).
Qed.

Lemma basic_value_has_ltype_lc Σ v T :
  lc_lvars (dom Σ) ->
  basic_value_has_ltype Σ v T ->
  lc_value v.
Proof.
  exact (proj1 basic_has_ltype_lc_mutual Σ v T).
Qed.

Lemma basic_tm_has_ltype_lc Σ e T :
  lc_lvars (dom Σ) ->
  basic_tm_has_ltype Σ e T ->
  lc_tm e.
Proof.
  exact (proj2 basic_has_ltype_lc_mutual Σ e T).
Qed.

Lemma basic_has_ltype_restrict_lvars_lc_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    lc_value v ->
    forall D,
      value_lvars v ⊆ D ->
      basic_value_has_ltype (storeA_restrict Σ D) v T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    lc_tm e ->
    forall D,
      tm_lvars e ⊆ D ->
      basic_tm_has_ltype (storeA_restrict Σ D) e T).
Proof.
  apply basic_has_ltype_mutind; intros; eauto.
  - constructor.
    match goal with
    | Hlook : ?Σ !! LVFree ?x = Some ?T |- _ =>
        apply storeA_restrict_lookup_some_2; [exact Hlook|]
    end.
    match goal with
    | Hsub : value_lvars (vfvar _) ⊆ _ |- _ =>
        cbn [value_lvars value_lvars_at] in Hsub; set_solver
    end.
  - exfalso. eapply lc_bvar_absurd; eassumption.
  - apply lc_lam_iff_body in H0 as Hbody_lc.
    eapply BVT_Lam with
      (L := L ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_tm e).
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as IHbody.
    specialize (IHbody (body_open_tm _ _ Hbody_lc (LC_fvar x))
      (D ∪ {[LVFree x]})).
    rewrite storeA_restrict_insert_fresh_union in IHbody.
    + apply IHbody.
      eapply tm_lvars_open_body_subset_lc; [exact Hbody_lc|].
      cbn [value_lvars value_lvars_at] in H1. exact H1.
    + apply not_elem_of_dom. intros Hdom.
      apply Hx. apply elem_of_union_l. apply elem_of_union_r.
      apply lvars_fv_elem. exact Hdom.
    + intros Hbad. apply Hx.
      apply lvars_fv_elem in Hbad. set_solver.
  - apply lc_fix_iff_body in H0 as Hbody_lc.
    eapply BVT_Fix with
      (L := L ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_value vf).
    intros x Hx.
    pose proof (H x ltac:(set_solver)) as IHbody.
    specialize (IHbody (body_open_value _ _ Hbody_lc (LC_fvar x))
      (D ∪ {[LVFree x]})).
    rewrite storeA_restrict_insert_fresh_union in IHbody.
    + apply IHbody.
      eapply value_lvars_open_body_subset_lc; [exact Hbody_lc|].
      cbn [value_lvars value_lvars_at] in H1. exact H1.
    + apply not_elem_of_dom. intros Hdom.
      apply Hx. apply elem_of_union_l. apply elem_of_union_r.
      apply lvars_fv_elem. exact Hdom.
    + intros Hbad. apply Hx.
      apply lvars_fv_elem in Hbad. set_solver.
  - apply lc_ret_iff_value in H0.
    constructor. eapply H; eauto.
  - apply lc_lete_iff_body in H1 as [Hlc1 Hbody2].
    eapply BTT_Let with
      (L := L ∪ lvars_fv D ∪ lvars_fv (dom Σ) ∪ fv_tm e2).
    + eapply H; eauto. cbn [tm_lvars tm_lvars_at] in H2. set_solver.
    + intros x Hx.
      pose proof (H0 x ltac:(set_solver)) as IHbody.
      specialize (IHbody (body_open_tm _ _ Hbody2 (LC_fvar x))
        (D ∪ {[LVFree x]})).
      rewrite storeA_restrict_insert_fresh_union in IHbody.
      * apply IHbody.
        eapply tm_lvars_open_body_subset_lc; [exact Hbody2|].
        cbn [tm_lvars tm_lvars_at] in H2. set_solver.
      * apply not_elem_of_dom. intros Hdom.
        apply Hx. apply elem_of_union_l. apply elem_of_union_r.
        apply lvars_fv_elem. exact Hdom.
      * intros Hbad. apply Hx.
        apply lvars_fv_elem in Hbad. set_solver.
  - match goal with
    | Hlc : lc_tm (tprim _ _) |- _ => apply lc_prim_iff_value in Hlc
    end.
    eapply BTT_Op.
    + match goal with
      | Hop : prim_op_type _ = _ |- _ => exact Hop
      end.
    +
    eapply H; eauto.
  - match goal with
    | Hlc : lc_tm (tapp _ _) |- _ =>
        apply lc_app_iff_values in Hlc as [Hlc1 Hlc2]
    end.
    eapply BTT_App.
    + eapply H; eauto.
      match goal with
      | Hsub : tm_lvars (tapp _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H0; eauto.
      match goal with
      | Hsub : tm_lvars (tapp _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
  - match goal with
    | Hlc : lc_tm (tmatch _ _ _) |- _ =>
        apply lc_match_iff_parts in Hlc as [Hlcv [Hlcet Hlcef]]
    end.
    eapply BTT_Match.
    + eapply H; eauto.
      match goal with
      | Hsub : tm_lvars (tmatch _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H0; eauto.
      match goal with
      | Hsub : tm_lvars (tmatch _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
    + eapply H1; eauto.
      match goal with
      | Hsub : tm_lvars (tmatch _ _ _) ⊆ _ |- _ =>
          cbn [tm_lvars tm_lvars_at] in Hsub; set_solver
      end.
Qed.

Lemma basic_tm_has_ltype_restrict_lvars_lc Σ e T D :
  basic_tm_has_ltype Σ e T ->
  lc_tm e ->
  tm_lvars e ⊆ D ->
  basic_tm_has_ltype (storeA_restrict Σ D) e T.
Proof.
  intros Hty Hlc Hsub.
  exact (proj2 basic_has_ltype_restrict_lvars_lc_mutual
    Σ e T Hty Hlc D Hsub).
Qed.

Lemma basic_has_ltype_of_atom_typing_mutual :
  (forall Δ v T,
    Δ ⊢ᵥ v ⋮ T ->
    basic_value_has_ltype (atom_env_to_lty_env Δ) v T) /\
  (forall Δ e T,
    Δ ⊢ₑ e ⋮ T ->
    basic_tm_has_ltype (atom_env_to_lty_env Δ) e T).
Proof.
  apply has_type_mutind; intros; eauto.
  - econstructor. rewrite atom_store_to_lvar_store_lookup_free. exact e.
  - eapply BVT_Lam with (L := L). intros x Hx.
    pose proof (H x Hx) as Hbody.
    rewrite atom_store_to_lvar_store_insert in Hbody.
    exact Hbody.
  - eapply BVT_Fix with (L := L). intros x Hx.
    pose proof (H x Hx) as Hbody.
    rewrite atom_store_to_lvar_store_insert in Hbody.
    exact Hbody.
  - eapply BTT_Let with (L := L); eauto.
    intros x Hx.
    pose proof (H0 x Hx) as Hbody.
    rewrite atom_store_to_lvar_store_insert in Hbody.
    exact Hbody.
Qed.

Lemma basic_value_has_ltype_of_atom_env_typing Δ v T :
  Δ ⊢ᵥ v ⋮ T ->
  basic_value_has_ltype (atom_env_to_lty_env Δ) v T.
Proof. exact (proj1 basic_has_ltype_of_atom_typing_mutual Δ v T). Qed.

Lemma basic_tm_has_ltype_of_atom_env_typing Δ e T :
  Δ ⊢ₑ e ⋮ T ->
  basic_tm_has_ltype (atom_env_to_lty_env Δ) e T.
Proof. exact (proj2 basic_has_ltype_of_atom_typing_mutual Δ e T). Qed.

Lemma basic_has_ltype_to_atom_typing_mutual :
  (forall Σ v T,
    basic_value_has_ltype Σ v T ->
    forall Δ,
      Σ = atom_env_to_lty_env Δ ->
      Δ ⊢ᵥ v ⋮ T) /\
  (forall Σ e T,
    basic_tm_has_ltype Σ e T ->
    forall Δ,
      Σ = atom_env_to_lty_env Δ ->
      Δ ⊢ₑ e ⋮ T).
Proof.
  apply basic_has_ltype_mutind; intros; subst.
  - constructor.
  - constructor.
    match goal with
    | Hlook : (atom_env_to_lty_env Δ : gmap logic_var ty) !! LVFree x =
        Some T |- _ =>
        rewrite atom_store_to_lvar_store_lookup_free in Hlook;
        exact Hlook
    end.
  - match goal with
    | Hlook : (atom_env_to_lty_env Δ : gmap logic_var ty) !! LVBound k =
        Some T |- _ =>
        rewrite atom_store_to_lvar_store_lookup_bound_none in Hlook;
        discriminate
    end.
  - eapply VT_Lam with (L := L).
    intros x Hx.
    specialize (H x Hx (<[x := s]> Δ)).
    exact (H (eq_sym (atom_store_to_lvar_store_insert x s Δ))).
  - eapply VT_Fix with (L := L).
    intros x Hx.
    specialize (H x Hx (<[x := sx]> Δ)).
    exact (H (eq_sym (atom_store_to_lvar_store_insert x sx Δ))).
  - eapply TT_Ret. eauto.
  - eapply TT_Let with (L := L).
    + eauto.
    + intros x Hx.
      specialize (H0 x Hx (<[x := T1]> Δ)).
      exact (H0 (eq_sym (atom_store_to_lvar_store_insert x T1 Δ))).
  - eapply TT_Op; eauto.
  - eapply TT_App; eauto.
  - eapply TT_Match; eauto.
Qed.

Lemma basic_tm_has_ltype_to_atom_env_typing Δ e T :
  basic_tm_has_ltype (atom_env_to_lty_env Δ) e T ->
  Δ ⊢ₑ e ⋮ T.
Proof.
  intros Hty.
  exact (proj2 basic_has_ltype_to_atom_typing_mutual
    (atom_env_to_lty_env Δ) e T Hty Δ eq_refl).
Qed.

Lemma atom_store_has_ltype_env_has_type Σ σ :
  atom_store_has_ltype Σ σ ->
  env_has_type (lty_env_to_atom_env Σ) σ.
Proof.
  intros Hσ x T v HΣx Hσx.
  destruct (Hσ x v Hσx) as [U [HΣU Hv]].
  change ((lvar_store_to_atom_store Σ : gmap atom ty) !! x = Some T)
    in HΣx.
  apply lvar_store_to_atom_store_lookup_some in HΣx as HΣT.
  change (((Σ : gmap logic_var ty) !! LVFree x) = Some U) in HΣU.
  change (((Σ : gmap logic_var ty) !! LVFree x) = Some T) in HΣT.
  rewrite HΣU in HΣT.
  inversion HΣT. subst U. exact Hv.
Qed.

Lemma basic_value_has_ltype_of_empty_atom_typing Σ v T :
  ∅ ⊢ᵥ v ⋮ T ->
  basic_value_has_ltype Σ v T.
Proof.
  intros Hty.
  eapply basic_value_has_ltype_weaken.
  - exact (basic_value_has_ltype_of_atom_env_typing ∅ v T Hty).
  - apply map_empty_subseteq.
Qed.

Lemma basic_has_ltype_unique_mutual :
  (forall Σ v T1,
    basic_value_has_ltype Σ v T1 ->
    forall T2, basic_value_has_ltype Σ v T2 -> T1 = T2) /\
  (forall Σ e T1,
    basic_tm_has_ltype Σ e T1 ->
    forall T2, basic_tm_has_ltype Σ e T2 -> T1 = T2).
Proof.
  apply basic_has_ltype_mutind; intros;
    match goal with
    | |- _ = ?T2 =>
        match goal with
        | H : basic_value_has_ltype _ _ T2 |- _ => inversion H; subst
        | H : basic_tm_has_ltype _ _ T2 |- _ => inversion H; subst
        end
    end.
  - reflexivity.
  - match goal with
    | H1 : ?Σ !! LVFree ?x = Some ?T1,
      H2 : ?Σ !! LVFree ?x = Some ?T2 |- _ =>
        rewrite H1 in H2; inversion H2; reflexivity
    end.
  - match goal with
    | H1 : ?Σ !! LVBound ?k = Some ?T1,
      H2 : ?Σ !! LVBound ?k = Some ?T2 |- _ =>
        rewrite H1 in H2; inversion H2; reflexivity
    end.
  -
    match goal with
    | IH : forall x, x ∉ ?L1 -> forall T2,
        basic_tm_has_ltype (<[LVFree x := _]> _) (_ ^^ x) T2 -> _,
      Hbody : forall x, x ∉ ?L2 ->
        basic_tm_has_ltype (<[LVFree x := _]> _) (_ ^^ x) _ |- _ =>
        set (y := fresh_for (L1 ∪ L2));
        assert (Hy : y ∉ L1 ∪ L2) by (subst y; apply fresh_for_not_in);
        pose proof (IH y ltac:(set_solver) _ (Hbody y ltac:(set_solver))) as Heq
    end.
    subst. reflexivity.
  -
    match goal with
    | IH : forall x, x ∉ ?L1 -> forall T2,
        basic_value_has_ltype (<[LVFree x := _]> _) (_ ^^ x) T2 -> _,
      Hbody : forall x, x ∉ ?L2 ->
        basic_value_has_ltype (<[LVFree x := _]> _) (_ ^^ x) _ |- _ =>
        set (y := fresh_for (L1 ∪ L2));
        assert (Hy : y ∉ L1 ∪ L2) by (subst y; apply fresh_for_not_in);
        pose proof (IH y ltac:(set_solver) _ (Hbody y ltac:(set_solver))) as Heq
    end.
    inversion Heq. reflexivity.
  - eauto.
  - match goal with
    | IH1 : forall T2, basic_tm_has_ltype _ _ T2 -> ?T1 = T2,
      Hty1 : basic_tm_has_ltype _ _ ?T1' |- _ =>
        pose proof (IH1 _ Hty1) as Heq1
    end.
    subst.
    match goal with
    | IH2 : forall x, x ∉ ?L1 -> forall T2,
        basic_tm_has_ltype (<[LVFree x := _]> _) (_ ^^ x) T2 -> _,
      Hbody : forall x, x ∉ ?L2 ->
        basic_tm_has_ltype (<[LVFree x := _]> _) (_ ^^ x) _ |- _ =>
        set (y := fresh_for (L1 ∪ L2));
        assert (Hy : y ∉ L1 ∪ L2) by (subst y; apply fresh_for_not_in);
        exact (IH2 y ltac:(set_solver) _ (Hbody y ltac:(set_solver)))
    end.
  - match goal with
    | Hop1 : prim_op_type ?op = (?a1, ?r1),
      Hop2 : prim_op_type ?op = (?a2, ?r2) |- _ =>
        rewrite Hop1 in Hop2; inversion Hop2; reflexivity
    end.
  - match goal with
    | IH : forall T2, basic_value_has_ltype _ _ T2 -> _,
      Hfun : basic_value_has_ltype _ _ (_ →ₜ _) |- _ =>
        pose proof (IH _ Hfun) as Heq
    end.
    inversion Heq. reflexivity.
  - match goal with
    | IH : forall T2, basic_tm_has_ltype _ _ T2 -> _,
      Hthen : basic_tm_has_ltype _ _ _ |- _ =>
        exact (IH _ Hthen)
    end.
Qed.

Lemma basic_value_has_ltype_unique Σ v T1 T2 :
  basic_value_has_ltype Σ v T1 ->
  basic_value_has_ltype Σ v T2 ->
  T1 = T2.
Proof.
  intros H1 H2.
  exact (proj1 basic_has_ltype_unique_mutual Σ v T1 H1 T2 H2).
Qed.

Lemma atom_store_has_ltype_lookup_from_basic_ltype Σ σ x vx T :
  atom_store_has_ltype Σ σ ->
  σ !! x = Some vx ->
  basic_value_has_ltype (lty_env_msubst_store σ Σ) vx T ->
  Σ !! LVFree x = Some T.
Proof.
  intros Hσtyped Hσx HvxT.
  destruct (Hσtyped x vx Hσx) as [U [HΣU HvxU]].
  assert (HvxU_basic :
    basic_value_has_ltype (lty_env_msubst_store σ Σ) vx U).
  { apply basic_value_has_ltype_of_empty_atom_typing. exact HvxU. }
  pose proof (basic_value_has_ltype_unique _ _ _ _ HvxU_basic HvxT)
    as ->.
  exact HΣU.
Qed.

Lemma basic_value_has_ltype_msubst_store_back_fvar
    Σ σ x vx T :
  atom_store_has_ltype Σ σ ->
  σ !! x = Some vx ->
  basic_value_has_ltype (lty_env_msubst_store σ Σ) vx T ->
  basic_value_has_ltype Σ (vfvar x) T.
Proof.
  intros Hσ Hlook Hty.
  constructor.
  eapply atom_store_has_ltype_lookup_from_basic_ltype; eauto.
Qed.

Lemma lstore_instantiate_value_at_lift_free_bvar d σ n :
  lstore_instantiate_value_at d (lstore_lift_free σ) (vbvar n) = vbvar n.
Proof.
  cbn [lstore_instantiate_value_at lstore_instantiate_value_split_at].
  destruct (decide (d <= n)); [|reflexivity].
  rewrite StoreInterface.lstore_bound_part_lookup.
  rewrite lstore_lift_free_lookup_bound.
  reflexivity.
Qed.

Ltac rewrite_lift_free_bvar_in H :=
  match type of H with
  | context [match decide (?d <= ?n) with
             | left _ =>
                 match StoreInterface.lstore_bound_part (V:=value)
                         (lstore_lift_free ?σ : LStoreT) !! (?n - ?d) with
                 | Some u => u | None => vbvar ?n end
             | right _ => vbvar ?n
             end] =>
      change (match decide (d <= n) with
              | left _ =>
                  match StoreInterface.lstore_bound_part (V:=value)
                          (lstore_lift_free σ : LStoreT) !! (n - d) with
                  | Some u => u | None => vbvar n end
              | right _ => vbvar n
              end) with
        (lstore_instantiate_value_at d (lstore_lift_free σ) (vbvar n)) in H;
	      rewrite lstore_instantiate_value_at_lift_free_bvar in H
  end.

Ltac invert_instantiated_tm_shape :=
  cbn [lstore_instantiate_tm_at lstore_instantiate_tm_split_at] in *;
  try discriminate;
  match goal with
  | Heq : _ = lstore_instantiate_tm_at _ _ _ |- _ =>
      unfold lstore_instantiate_tm_at in Heq;
      cbn [lstore_instantiate_tm_split_at] in Heq;
      inversion Heq; subst
  | Heq : ret _ = ret _ |- _ =>
      inversion Heq; subst
  | Heq : (let: _ in _) = (let: _ in _) |- _ =>
      inversion Heq; subst
  | Heq : tprim _ _ = tprim _ _ |- _ =>
      inversion Heq; subst
  | Heq : tapp _ _ = tapp _ _ |- _ =>
      inversion Heq; subst
  | Heq : tmatch _ _ _ = tmatch _ _ _ |- _ =>
      inversion Heq; subst
  end.

Ltac solve_instantiated_fvar_case Heq :=
  cbn [lstore_instantiate_value_at lstore_instantiate_value_split_at] in Heq;
  rewrite ?lstore_free_part_lift_free in Heq;
  match type of Heq with
  | context [match (?σ : gmap atom value) !! ?x with
             | Some u => u
             | None => vfvar ?x
             end] =>
      let Hlookup := fresh "Hlookup" in
      destruct ((σ : gmap atom value) !! x) as [vx|] eqn:Hlookup;
      [ replace (match (σ : gmap atom value) !! x with
                 | Some u => u | None => vfvar x end) with vx in Heq
          by (rewrite Hlookup; reflexivity);
        destruct vx; inversion Heq; subst;
        eapply basic_value_has_ltype_msubst_store_back_fvar; eauto
      | replace (match (σ : gmap atom value) !! x with
                 | Some u => u | None => vfvar x end) with (vfvar x) in Heq
          by (rewrite Hlookup; reflexivity);
        first
          [ discriminate
          | inversion Heq; subst; constructor; subst;
            match goal with
            | Hlook : lty_env_msubst_store _ _ !! _ = Some _ |- _ =>
                apply lty_env_msubst_store_lookup_some in Hlook as [Hlook' _];
                exact Hlook'
            end ] ]
  end.

(** The syntactic well-formedness of [τ] is not a runtime property of the
    world, but we still package it as a world-independent logic qualifier.
    Unlike [basic_context_ty], this version is scoped by the lvar-domain of [Σ]
    directly, so bound lvars in a type body are preserved until the surrounding
    formula open swaps them to atoms. *)
Definition context_ty_wf_lqual
    (Σ : lty_env) (τ : context_ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_context_ty_lvars (dom Σ) τ).
Definition context_ty_wf_formula
    (Σ : lty_env) (τ : context_ty) : Formula :=
  FAtom (context_ty_wf_lqual Σ τ).
Lemma formula_fv_context_ty_wf_formula Σ τ :
  formula_fv (context_ty_wf_formula Σ τ) = lvars_fv (dom Σ).
Proof. reflexivity. Qed.
Definition expr_basic_typing_lqual
    (Σ : lty_env) (e : tm) (T : ty) : LogicQualifierT :=
  lqual (dom Σ)
    (fun _ => basic_tm_has_ltype Σ e T).
Definition expr_basic_typing_formula
    (Σ : lty_env) (e : tm) (T : ty) : Formula :=
  FAtom (expr_basic_typing_lqual Σ e T).
Lemma formula_fv_expr_basic_typing_formula Σ e T :
  formula_fv (expr_basic_typing_formula Σ e T) = lvars_fv (dom Σ).
Proof. reflexivity. Qed.
Lemma formula_open_context_ty_wf_formula k y Σ τ :
  formula_open k y (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_one k y Σ) (cty_open k y τ).
Proof.
  unfold context_ty_wf_formula, context_ty_wf_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 _. cbn [lqual_prop].
    rewrite lty_env_open_one_dom.
    rewrite basic_context_ty_lvars_open.
    reflexivity.
Qed.

Lemma formula_open_env_context_ty_wf_formula η Σ τ :
  open_env_fresh_for_lvars η (dom Σ ∪ context_ty_lvars τ) ->
  open_env_values_inj η ->
  formula_open_env η (context_ty_wf_formula Σ τ) =
  context_ty_wf_formula (lty_env_open_lvars η Σ) (open_cty_env η τ).
Proof.
  revert Σ τ.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ τ _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty,
      open_cty_env_empty. reflexivity.
  - intros Σ τ Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ context_ty_lvars τ) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_context_ty_wf_formula.
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv | exact Hfresh]. }
    rewrite open_cty_env_insert_fresh by assumption.
    reflexivity.
Qed.

Lemma basic_tm_has_ltype_open_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Admitted.

Lemma atom_env_lty_env_roundtrip_closed (Σ : lty_env) :
  lty_env_closed Σ ->
  atom_env_to_lty_env (lty_env_to_atom_env Σ) = Σ.
Proof.
  intros Hclosed.
  apply map_eq. intros [k|x].
  - rewrite atom_store_to_lvar_store_lookup_bound_none.
    symmetry. apply lty_env_closed_lookup_bound_none. exact Hclosed.
  - rewrite atom_store_to_lvar_store_lookup_free.
    apply lvar_store_to_atom_store_lookup.
Qed.

Lemma basic_tm_has_ltype_of_atom_typing Σ e T :
  lty_env_closed Σ ->
  lty_env_to_atom_env Σ ⊢ₑ e ⋮ T ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hclosed Hty.
  pose proof (basic_tm_has_ltype_of_atom_env_typing
    (lty_env_to_atom_env Σ) e T Hty) as Hbasic.
  rewrite atom_env_lty_env_roundtrip_closed in Hbasic by exact Hclosed.
  exact Hbasic.
Qed.

Lemma basic_tm_has_ltype_eval_in_atom_store_value_type
    Σ σ e T v :
  lty_env_closed Σ ->
  atom_store_has_ltype Σ σ ->
  basic_tm_has_ltype Σ e T ->
  tm_eval_in_store σ e v ->
  fv_tm e ⊆ dom (σ : StoreT) ->
  ∅ ⊢ᵥ v ⋮ T.
Proof.
  intros HΣclosed Hσtyped Hty Heval Hfvcover.
  pose proof (atom_store_has_ltype_closed _ _ Hσtyped) as Hσclosed.
  destruct Hσclosed as [Hclosed Hlcenv].
  pose proof (basic_tm_has_ltype_to_atom_env_typing
    (lty_env_to_atom_env Σ) e T) as Hto_atom.
  rewrite atom_env_lty_env_roundtrip_closed in Hto_atom by exact HΣclosed.
  specialize (Hto_atom Hty) as Hty_atom.
  pose proof (atom_store_has_ltype_env_has_type Σ σ Hσtyped) as Henvty.
  pose proof (msubst_basic_typing_tm
    (lty_env_to_atom_env Σ) σ e T Hclosed Henvty Hty_atom)
    as Hsubst_ty.
  assert (Hsubst_ty_empty : ∅ ⊢ₑ m{σ} e ⋮ T).
  {
    eapply basic_typing_env_agree_tm; [exact Hsubst_ty|].
    intros y Hy.
    exfalso.
    pose proof (msubst_fv_delete_tm σ e Hclosed) as Hfv.
    set_solver.
  }
  unfold tm_eval_in_store, expr_eval_in_store in Heval.
  rewrite lstore_instantiate_tm_no_bvars in Heval.
  - rewrite lstore_free_part_lift_free in Heval.
    pose proof (basic_steps_preservation ∅ (m{σ} e) (tret v) T
      Hsubst_ty_empty Heval) as Hret.
    inversion Hret; subst.
    match goal with
    | H : ∅ ⊢ᵥ v ⋮ _ |- _ => exact H
    end.
  - apply lc_lstore_lift_free.
  - rewrite lstore_free_part_lift_free. exact Hclosed.
Qed.

Lemma basic_tm_has_ltype_close_one_fresh k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T ->
  basic_tm_has_ltype Σ e T.
Admitted.

Lemma basic_tm_has_ltype_open_one_fresh_iff k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  basic_tm_has_ltype Σ e T <->
  basic_tm_has_ltype (lty_env_open_one k y Σ)
    (open_tm k (vfvar y) e) T.
Proof.
  intros Hy. split.
  - apply basic_tm_has_ltype_open_one_fresh. exact Hy.
  - apply basic_tm_has_ltype_close_one_fresh. exact Hy.
Qed.

Lemma formula_open_expr_basic_typing_formula k y Σ e T :
  y ∉ lvars_fv (dom Σ) ∪ fv_tm e ->
  formula_open k y (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_one k y Σ) (open_tm k (vfvar y) e) T.
Proof.
  intros Hy.
  unfold expr_basic_typing_formula, expr_basic_typing_lqual.
  cbn [formula_open lqual_open].
  f_equal.
  apply logic_qualifier_ext.
  - rewrite lty_env_open_one_dom. reflexivity.
  - intros w1 w2 Hlw. cbn [lqual_prop].
    apply basic_tm_has_ltype_open_one_fresh_iff. exact Hy.
Qed.

Lemma formula_open_env_expr_basic_typing_formula η Σ e T :
  open_env_fresh_for_lvars η (dom Σ ∪ tm_lvars e) ->
  open_env_values_inj η ->
  formula_open_env η (expr_basic_typing_formula Σ e T) =
  expr_basic_typing_formula
    (lty_env_open_lvars η Σ) (open_tm_env η e) T.
Proof.
  revert Σ e.
  induction η as [|k x η Hnone Hfold IH] using fin_maps.map_fold_ind.
  - intros Σ e _ _.
    rewrite formula_open_env_empty, lty_env_open_lvars_empty.
    rewrite map_fold_empty. reflexivity.
  - intros Σ e Hfresh Hinj.
    pose proof (open_env_values_inj_insert_inv η k x Hnone Hinj)
      as [Hinjη Havoid].
    pose proof (open_env_fresh_for_lvars_insert_tail η k x
      (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hfreshη.
    rewrite formula_open_env_insert_fresh by assumption.
    rewrite IH by (exact Hfreshη || exact Hinjη).
    rewrite formula_open_expr_basic_typing_formula.
    2:{
      pose proof (open_env_fresh_for_lvars_insert_head η k x
        (dom Σ ∪ tm_lvars e) Hnone Hfresh) as Hhead.
      rewrite <- tm_lvars_fv.
      rewrite tm_lvars_open_tm_env.
      2:{ eapply open_env_fresh_for_lvars_mono.
          - intros v Hv. apply elem_of_union_r. exact Hv.
          - exact Hfreshη. }
      assert (HΣfv : lvars_fv (dom (lty_env_open_lvars η Σ)) ⊆
                     lvars_fv (lvars_open_env η (dom Σ))).
      {
        rewrite lty_env_open_lvars_dom.
        - unfold lvars_open_env. set_solver.
        - eapply open_env_fresh_for_lvars_mono;
            [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfreshη].
      }
      intros Hbad. apply Hhead.
      rewrite lvars_open_env_union, lvars_fv_union.
      apply elem_of_union.
      apply elem_of_union in Hbad as [Hbad|Hbad].
      - left. apply HΣfv. exact Hbad.
      - right. exact Hbad.
    }
    rewrite lty_env_open_lvars_insert_fresh.
    2: exact Hnone.
    2: exact Havoid.
    2:{ eapply open_env_fresh_for_lvars_mono;
          [intros v Hv; apply elem_of_union_l; exact Hv|exact Hfresh]. }
    rewrite open_tm_env_insert_fresh_plain by exact Hnone.
    reflexivity.
Qed.

Lemma context_ty_wf_lqual_denote_iff Σ τ (m : WfWorldT) :
  logic_qualifier_denote (context_ty_wf_lqual Σ τ) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  unfold context_ty_wf_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma context_ty_wf_formula_models_iff Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  unfold res_models, context_ty_wf_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply context_ty_wf_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply context_ty_wf_lqual_denote_iff. exact Hden.
Qed.

Lemma context_ty_wf_formula_basic_lvars Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  basic_context_ty_lvars (dom Σ) τ.
Proof.
  intros Hmodels.
  apply context_ty_wf_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

Lemma context_ty_wf_formula_fv_cty_subset Σ τ (m : WfWorldT) :
  res_models m (context_ty_wf_formula Σ τ) ->
  fv_cty τ ⊆ lvars_fv (dom Σ).
Proof.
  intros Hmodels.
  pose proof (context_ty_wf_formula_basic_lvars Σ τ m Hmodels)
    as [Hvars _].
  rewrite <- context_ty_lvars_fv.
  apply lvars_fv_mono. exact Hvars.
Qed.

Lemma expr_basic_typing_lqual_denote_iff Σ e T (m : WfWorldT) :
  logic_qualifier_denote (expr_basic_typing_lqual Σ e T) m <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  unfold expr_basic_typing_lqual, logic_qualifier_denote.
  split.
  - intros [Hlc [Hsub Hbasic]]. tauto.
  - intros [Hlc [Hsub Hbasic]]. exists Hlc, Hsub. exact Hbasic.
Qed.

Lemma expr_basic_typing_formula_models_iff Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) <->
  lc_lvars (dom Σ) /\
  lvars_fv (dom Σ) ⊆ world_dom (m : WorldT) /\
  basic_tm_has_ltype Σ e T.
Proof.
  unfold res_models, expr_basic_typing_formula.
  cbn [formula_measure res_models_fuel].
  split.
  - intros [_ Hden].
    apply expr_basic_typing_lqual_denote_iff. exact Hden.
  - intros Hden. split.
    + destruct Hden as [_ [Hsub _]]. exact Hsub.
    + apply expr_basic_typing_lqual_denote_iff. exact Hden.
Qed.

Lemma expr_basic_typing_formula_basic_ltype Σ e T (m : WfWorldT) :
  res_models m (expr_basic_typing_formula Σ e T) ->
  basic_tm_has_ltype Σ e T.
Proof.
  intros Hmodels.
  apply expr_basic_typing_formula_models_iff in Hmodels as [_ [_ Hbasic]].
  exact Hbasic.
Qed.

End BasicTypingFormula.
