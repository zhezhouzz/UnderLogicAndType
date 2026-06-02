(** * BasicDenotation.MsubstTransport

    Transport lemmas for freezing ordinary atom stores into formulas.  These
    are the BasicDenotation-facing bridge between [formula_msubst_store] and
    the TypeLanguage-level substitution operations on contexts, qualifiers,
    and terms. *)

From ContextBasicDenotation Require Import Notation StoreTyping TermEval TermOpen Qualifier
  BasicTypingFormula RelevantEnv.
From ContextLogic Require Import FormulaConnectives.
From ContextAlgebra Require Import ResourceAlgebra.

Section MsubstTransport.

Local Notation LWorldOnT := (LWorldOn (V := value)) (only parsing).

Definition wf_erased_ctx_under
    (Σbase Δ : gmap atom ty) : Prop :=
  forall x T, Σbase !! x = Some T -> Δ !! x = Some T.

Fixpoint context_ty_wf_for_erased
    (Σbase Δ : gmap atom ty) (τ : context_ty) : Prop :=
  match τ with
  | CTOver _ _ | CTUnder _ _ =>
      basic_context_ty (dom Δ) τ
  | CTInter τ1 τ2 | CTUnion τ1 τ2 | CTSum τ1 τ2 =>
      context_ty_wf_for_erased Σbase Δ τ1 /\
      context_ty_wf_for_erased Σbase Δ τ2 /\
      erase_ty τ1 = erase_ty τ2
  | CTArrow τx τr =>
      basic_context_ty (dom Δ) τx /\
      wf_context_ty_at 1 (dom Δ) τr
  | CTWand τx τr =>
      basic_context_ty (dom Σbase) τx /\
      wf_context_ty_at 1 (dom Δ) τr
  end.

Definition context_typing_wf_erased
    (Σbase Δ : gmap atom ty) (e : tm) (τ : context_ty) : Prop :=
  wf_erased_ctx_under Σbase Δ /\
  context_ty_wf_for_erased Σbase Δ τ /\
  Δ ⊢ₑ e ⋮ erase_ty τ.

Lemma wf_erased_ctx_under_dom_subset Σbase Δ :
  wf_erased_ctx_under Σbase Δ ->
  dom Σbase ⊆ dom Δ.
Proof.
  intros Hwf x Hx.
  apply elem_of_dom in Hx as [T HΣ].
  apply elem_of_dom. exists T. eapply Hwf. exact HΣ.
Qed.

Lemma context_ty_wf_for_erased_regular Σbase Δ τ :
  wf_erased_ctx_under Σbase Δ ->
  context_ty_wf_for_erased Σbase Δ τ ->
  basic_context_ty (dom Δ) τ.
Proof.
  intros Henv.
  induction τ as [b φ|b φ|τ1 IH1 τ2 IH2|τ1 IH1 τ2 IH2
                 |τ1 IH1 τ2 IH2|τx IHx τr IHr|τx IHx τr IHr];
    cbn [context_ty_wf_for_erased]; intros Hwf; try exact Hwf.
  - destruct Hwf as [H1 [H2 Herase]].
    apply basic_context_ty_inter; [apply IH1|apply IH2|]; assumption.
  - destruct Hwf as [H1 [H2 Herase]].
    apply basic_context_ty_iff_wf_context_ty_at.
    cbn [wf_context_ty_at]. repeat split.
    + apply basic_context_ty_iff_wf_context_ty_at. apply IH1. exact H1.
    + apply basic_context_ty_iff_wf_context_ty_at. apply IH2. exact H2.
    + exact Herase.
  - destruct Hwf as [H1 [H2 Herase]].
    apply basic_context_ty_iff_wf_context_ty_at.
    cbn [wf_context_ty_at]. repeat split.
    + apply basic_context_ty_iff_wf_context_ty_at. apply IH1. exact H1.
    + apply basic_context_ty_iff_wf_context_ty_at. apply IH2. exact H2.
    + exact Herase.
  - destruct Hwf as [Harg Hbody].
    apply basic_context_ty_iff_wf_context_ty_at.
    cbn [wf_context_ty_at]. split.
    + apply basic_context_ty_iff_wf_context_ty_at. exact Harg.
    + exact Hbody.
  - destruct Hwf as [Harg Hbody].
    apply basic_context_ty_iff_wf_context_ty_at.
    cbn [wf_context_ty_at]. split.
    + apply basic_context_ty_iff_wf_context_ty_at.
      eapply basic_context_ty_mono; [|exact Harg].
      apply wf_erased_ctx_under_dom_subset. exact Henv.
    + exact Hbody.
Qed.

Lemma context_typing_wf_erased_regular Σbase Δ e τ :
  context_typing_wf_erased Σbase Δ e τ ->
  basic_context_ty (dom Δ) τ /\ Δ ⊢ₑ e ⋮ erase_ty τ.
Proof.
  intros [Henv [Hτ Hbasic]]. split; [|exact Hbasic].
  eapply context_ty_wf_for_erased_regular; eauto.
Qed.

Lemma context_typing_wf_erased_basic_typing Σbase Δ e τ :
  context_typing_wf_erased Σbase Δ e τ ->
  Δ ⊢ₑ e ⋮ erase_ty τ.
Proof. intros Hwf. exact (proj2 (context_typing_wf_erased_regular _ _ _ _ Hwf)). Qed.

Lemma context_typing_wf_erased_context_ty_wf Σbase Δ e τ :
  context_typing_wf_erased Σbase Δ e τ ->
  basic_context_ty (dom Δ) τ.
Proof. intros Hwf. exact (proj1 (context_typing_wf_erased_regular _ _ _ _ Hwf)). Qed.

Lemma context_typing_wf_erased_wand_arg_global Σbase Δ e τx τr :
  context_typing_wf_erased Σbase Δ e (CTWand τx τr) ->
  basic_context_ty (dom Σbase) τx.
Proof.
  intros [_ [Hτ _]].
  cbn [context_ty_wf_for_erased] in Hτ.
  exact (proj1 Hτ).
Qed.

Lemma lworld_has_type_msubst_store_from_back
    σ Σ (w : LWorldOnT (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))) :
  atom_store_has_ltype Σ σ ->
  lworld_has_type Σ
    (@lw value _ (lworld_on_mlsubst_back (dom Σ) (lstore_lift_free σ) w)
      : LWorldT) ->
  lworld_has_type
    (storeA_restrict Σ (dom Σ ∖ dom (lstore_lift_free σ : LStoreT)))
    (@lw value _ w : LWorldT).
Proof.
  intros _ [Hdom Hstores]. split.
  - intros v Hv.
    rewrite storeA_restrict_dom in Hv.
    assert (Hv' : v ∈ dom Σ ∖ dom (lstore_lift_free σ : LStoreT)) by set_solver.
    change (v ∈ lworld_dom (@lw value _ w : LWorldT)).
    rewrite (@lw_dom value _ w). exact Hv'.
  - intros τ Hτ.
    intros v T u HΣv Hτv.
    apply storeA_restrict_lookup_some in HΣv as [HvD HΣv].
    apply elem_of_difference in HvD as [_ Hvfresh].
    assert (Hτdom : dom (τ : LStoreT) =
      dom Σ ∖ dom (lstore_lift_free σ : LStoreT)).
    {
      pose proof (wfworldA_store_dom (@lw value _ w : LWfWorld) τ Hτ) as Hdomτ.
      change (dom (τ : LStoreT) = lworld_dom (@lw value _ w : LWorldT)) in Hdomτ.
      rewrite (@lw_dom value _ w) in Hdomτ. exact Hdomτ.
    }
    set (ρD := storeA_restrict (lstore_lift_free σ : LStoreT) (dom Σ)).
    assert (HρDdom : dom (ρD : LStoreT) =
      dom (lstore_lift_free σ : LStoreT) ∩ dom Σ).
    {
      unfold ρD.
      apply (@storeA_restrict_dom value logic_var _ _
        (lstore_lift_free σ : LStoreT) (dom Σ)).
    }
    assert (Hcompat : storeA_compat τ ρD).
    {
      unfold storeA_compat, map_compat.
      intros z a b Hzτ Hzρ.
      apply elem_of_dom_2 in Hzτ.
      apply elem_of_dom_2 in Hzρ.
      change (z ∈ dom (τ : LStoreT)) in Hzτ.
      change (z ∈ dom (ρD : LStoreT)) in Hzρ.
      rewrite Hτdom in Hzτ.
      rewrite HρDdom in Hzρ.
      set_solver.
    }
    assert (Hback_store :
      worldA_stores
        (@lw value _ (lworld_on_mlsubst_back (dom Σ)
          (lstore_lift_free σ) w) : LWorldT)
        (τ ∪ ρD)).
    {
      unfold lworld_on_mlsubst_back.
      cbn [lw resA_product rawA_product singleton_worldA worldA_stores].
      exists τ, ρD.
      repeat split; try exact Hτ; try exact Hcompat; try reflexivity.
      all: unfold ρD; reflexivity.
    }
    specialize (Hstores _ Hback_store v T u HΣv).
    apply Hstores.
    apply map_lookup_union_Some_raw. left. exact Hτv.
Qed.

Lemma context_ty_wf_formula_msubst_store_models
    σ Σ τ (m : WfWorldT) :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ dom Σ ->
  res_models m (formula_msubst_store σ (context_ty_wf_formula Σ τ)) ->
  res_models m (context_ty_wf_formula
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)).
Proof.
  intros HσΣ Hm.
  change (formula_msubst_store σ (context_ty_wf_formula Σ τ))
    with (FAtom (lqual_msubst_store σ (context_ty_wf_lqual Σ τ))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, context_ty_wf_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hbasic]].
  rewrite dom_lstore_lift_free in Hlc, Hsub.
  apply context_ty_wf_formula_models_iff.
  split.
  - rewrite lty_env_msubst_store_dom. exact Hlc.
  - split.
    + rewrite lty_env_msubst_store_dom. exact Hsub.
    + rewrite lty_env_msubst_store_dom.
      apply basic_context_ty_lvars_msubst_store.
      exact Hbasic.
Qed.

Lemma context_ty_wf_formula_msubst_store_models_back
    σ Σ τ (m : WfWorldT) :
  context_ty_lvars τ ⊆ dom Σ ->
  res_models m (context_ty_wf_formula
    (lty_env_msubst_store σ Σ)
    (context_ty_msubst_store σ τ)) ->
  res_models m (formula_msubst_store σ (context_ty_wf_formula Σ τ)).
Proof.
  intros HτΣ Hm.
  apply context_ty_wf_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  destruct Hbasic as [_ Hshape].
  apply res_models_atom_intro.
  unfold context_ty_wf_formula, context_ty_wf_lqual,
    lqual_msubst_store, lqual_mlsubst, logic_qualifier_denote.
  cbn [lqual_dom lqual_prop].
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  rewrite dom_lstore_lift_free.
  rewrite lty_env_msubst_store_dom in Hlc, Hsub.
  exists Hlc, Hsub.
  split; [exact HτΣ|].
  apply (proj1 (context_ty_shape_ok_msubst_store σ τ)). exact Hshape.
Qed.

Lemma basic_world_formula_msubst_store_models
    σ Σ (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (basic_world_formula Σ)) ->
  res_models m (basic_world_formula (lty_env_msubst_store σ Σ)).
Proof.
  intros Hσtyped Hm.
  change (formula_msubst_store σ (basic_world_formula Σ))
    with (FAtom (lqual_msubst_store σ (basic_world_lqual Σ))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, basic_world_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Htyped]].
  apply res_models_atom_intro.
  unfold basic_world_lqual, logic_qualifier_denote.
  rewrite lty_env_msubst_store_dom.
  rewrite <- dom_lstore_lift_free.
  exists Hlc, Hsub.
  change (lworld_has_type (lty_env_msubst_store σ Σ)
    (@lw value _
      (lworld_on_lift
        (dom Σ ∖ dom (lstore_lift_free σ : LStoreT)) m Hlc Hsub) : LWorldT)).
  assert (Henv :
    lty_env_msubst_store σ Σ =
    storeA_restrict Σ (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))).
  {
    unfold lty_env_msubst_store.
    rewrite dom_lstore_lift_free.
    reflexivity.
  }
  rewrite Henv.
  eapply lworld_has_type_msubst_store_from_back; [exact Hσtyped|].
  exact Htyped.
Qed.

Lemma lworld_has_type_msubst_store_to_back
    σ Σ (w : LWorldOnT (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))) :
  atom_store_has_ltype Σ σ ->
  lworld_has_type
    (storeA_restrict Σ (dom Σ ∖ dom (lstore_lift_free σ : LStoreT)))
    (@lw value _ w : LWorldT) ->
  lworld_has_type Σ
    (@lw value _ (lworld_on_mlsubst_back (dom Σ) (lstore_lift_free σ) w)
      : LWorldT).
Proof.
  intros Hσtyped [Hdom_res Hstores_res]. split.
  - intros v Hv.
    change (v ∈ lworld_dom
      (@lw value _ (lworld_on_mlsubst_back (dom Σ)
        (lstore_lift_free σ) w) : LWorldT)).
    rewrite (@lw_dom value _ (lworld_on_mlsubst_back (dom Σ)
      (lstore_lift_free σ) w)).
    exact Hv.
  - intros τ Hτ v T u HΣv Hτv.
    unfold lworld_on_mlsubst_back in Hτ.
    cbn [lw resA_product rawA_product singleton_worldA worldA_stores] in Hτ.
    destruct Hτ as [τw [ρD [Hτw [HρD [Hcompat Hτeq]]]]].
    change (ρD = storeA_restrict (lstore_lift_free σ : LStoreT) (dom Σ)) in HρD.
    subst ρD.
    subst τ.
    change ((((τw : gmap logic_var value) ∪
      storeA_restrict (lstore_lift_free σ : LStoreT) (dom Σ))
      : gmap logic_var value) !! v = Some u) in Hτv.
    apply (proj1 (map_lookup_union_Some_raw
      (τw : gmap logic_var value)
      (storeA_restrict (lstore_lift_free σ : LStoreT) (dom Σ)) v u)) in Hτv.
    destruct Hτv as [Hτw_v | [Hτw_none HρD_v]].
    + eapply Hstores_res.
      * exact Hτw.
      * apply storeA_restrict_lookup_some_2; [exact HΣv|].
        pose proof (wfworldA_store_dom (@lw value _ w : LWfWorld)
          τw Hτw) as Hdomτw.
        change (dom (τw : LStoreT) =
          lworld_dom (@lw value _ w : LWorldT)) in Hdomτw.
        apply elem_of_dom_2 in Hτw_v.
        change (v ∈ dom (τw : LStoreT)) in Hτw_v.
        rewrite Hdomτw in Hτw_v.
        rewrite (@lw_dom value _ w) in Hτw_v.
        exact Hτw_v.
      * exact Hτw_v.
    + apply storeA_restrict_lookup_some in HρD_v as [HvΣ Hρv].
      destruct v as [k|x].
      * rewrite lstore_lift_free_lookup_bound in Hρv. discriminate.
      * rewrite lstore_lift_free_lookup_free in Hρv.
        destruct (Hσtyped x u Hρv) as [U [HΣU Hu]].
        change (Σ !! LVFree x = Some T) in HΣv.
        rewrite HΣv in HΣU. inversion HΣU. subst U.
        exact Hu.
Qed.

Lemma lworld_has_type_lift_from_res_lift_free_same_dom
    (Σ : lty_env) (D : lvset) (m : WfWorldT)
    (Hlc : lc_lvars D) (Hsub : lvars_fv D ⊆ world_dom (m : WorldT)) :
  dom Σ = D ->
  lworld_has_type Σ (res_lift_free m : LWorldT) ->
  lworld_has_type Σ
    (@lw value _ (lworld_on_lift D m Hlc Hsub) : LWorldT).
Proof.
  intros Hdom_eq [Hdom Hstores]. split.
  - intros v Hv.
    change (v ∈ lworld_dom
      (@lw value _ (lworld_on_lift D m Hlc Hsub) : LWorldT)).
    rewrite (@lw_dom value _ (lworld_on_lift D m Hlc Hsub)).
    rewrite <- Hdom_eq. exact Hv.
  - intros τ Hτ v T u HΣv Hτv.
    unfold lworld_on_lift in Hτ.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hτ.
    destruct Hτ as [τ0 [Hτ0 Hrestrict]]. subst τ.
    unfold res_lift_free in Hτ0.
    cbn [worldA_stores] in Hτ0.
    destruct Hτ0 as [σr [Hσr ->]].
    unfold res_restrict, resA_restrict, rawA_restrict in Hσr.
    cbn [worldA_stores] in Hσr.
    destruct Hσr as [σ0 [Hσ0 Hσr]]. subst σr.
    apply storeA_restrict_lookup_some in Hτv as [HvD Hτv].
    destruct v as [k|x].
    + exfalso.
      exact (Hlc (LVBound k) ltac:(
        rewrite <- Hdom_eq; eapply elem_of_dom_2; exact HΣv)).
    + rewrite lstore_lift_free_lookup_free in Hτv.
      apply storeA_restrict_lookup_some in Hτv as [_ Hσ0x].
      eapply Hstores.
      * exists σ0. split; [exact Hσ0|reflexivity].
      * exact HΣv.
      * rewrite lstore_lift_free_lookup_free. exact Hσ0x.
Qed.

Lemma basic_world_formula_msubst_store_models_back
    σ Σ (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (basic_world_formula (lty_env_msubst_store σ Σ)) ->
  res_models m (formula_msubst_store σ (basic_world_formula Σ)).
Proof.
  intros Hσtyped Hm.
  apply basic_world_formula_models_iff in Hm as [Hlc [Hsub Htyped]].
  apply res_models_atom_intro.
  unfold basic_world_lqual, lqual_msubst_store, lqual_mlsubst,
    logic_qualifier_denote.
  cbn [lqual_dom lqual_prop].
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  assert (HdomD : dom (lty_env_msubst_store σ Σ) =
    dom Σ ∖ dom (lstore_lift_free σ : LStoreT)).
  {
    rewrite lty_env_msubst_store_dom, dom_lstore_lift_free.
    reflexivity.
  }
  rewrite HdomD in Hlc, Hsub.
  exists Hlc, Hsub.
  change (lworld_has_type Σ
    (@lw value _
      (lworld_on_mlsubst_back (dom Σ) (lstore_lift_free σ)
        (lworld_on_lift (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))
          m Hlc Hsub)) : LWorldT)).
  eapply lworld_has_type_msubst_store_to_back; [exact Hσtyped|].
  assert (Henv :
    lty_env_msubst_store σ Σ =
    storeA_restrict Σ (dom Σ ∖ dom (lstore_lift_free σ : LStoreT))).
  {
    unfold lty_env_msubst_store.
    rewrite dom_lstore_lift_free.
    reflexivity.
  }
  rewrite <- Henv.
  eapply lworld_has_type_lift_from_res_lift_free_same_dom;
    [exact HdomD|exact Htyped].
Qed.

Lemma basic_world_formula_fibvars_intro
    (D : lvset) (Σ : lty_env) (m : WfWorld) :
  lc_lvars D ->
  lvars_fv D ⊆ lvars_fv (dom Σ) ->
  res_models m (basic_world_formula Σ) ->
  res_models m (FFibVars D (basic_world_formula Σ)).
Proof.
  intros HDlc HDsub Hworld.
  pose proof (res_models_scoped _ _ Hworld) as Hworld_scope.
  apply basic_world_formula_models_iff in Hworld as
    [HΣlc [HΣscope HΣtyped]].
  destruct HΣtyped as [HΣdom HΣstores].
  eapply res_models_FFibVars_intro.
  - apply (proj2 (formula_scoped_fibvars_iff m D (basic_world_formula Σ))).
    split.
    + intros x Hx. apply HΣscope. exact (HDsub x Hx).
    + exact Hworld_scope.
  - exact HDlc.
  - intros σD mfib Hproj.
    assert (HDscope : lvars_fv D ⊆ world_dom (m : World)).
    {
      intros x Hx. apply HΣscope. exact (HDsub x Hx).
    }
    assert (HdomσD : dom (σD : StoreT) = lvars_fv D).
    {
      eapply res_fiber_from_projection_store_dom_of_subset; eauto.
    }
    assert (HσDtyped : atom_store_has_ltype Σ σD).
    {
      intros x v HσDx.
      assert (HxD : x ∈ lvars_fv D).
      {
        rewrite <- HdomσD.
        change (x ∈ dom (σD : gmap atom value)).
        rewrite elem_of_dom. eauto.
      }
      assert (HxΣfv : x ∈ lvars_fv (dom Σ)).
      { exact (HDsub x HxD). }
      assert (HxΣ : LVFree x ∈ dom Σ).
      { apply lvars_fv_elem. exact HxΣfv. }
      apply elem_of_dom in HxΣ as [T HΣx].
      exists T. split; [exact HΣx|].
      destruct Hproj as [Hproj_store _].
      destruct Hproj_store as [σm [Hσm Hrestrict]].
      assert (Hσmx : σm !! x = Some v).
      {
        assert ((storeA_restrict σm (lvars_fv D) : StoreT) !! x = Some v).
        { rewrite Hrestrict. exact HσDx. }
        apply storeA_restrict_lookup_some in H as [_ Hlookup].
        exact Hlookup.
      }
      eapply HΣstores.
      - unfold res_lift_free. exists σm. split; [exact Hσm|reflexivity].
      - exact HΣx.
      - rewrite lstore_lift_free_lookup_free. exact Hσmx.
    }
    assert (Hmfib_world : res_models mfib (basic_world_formula Σ)).
    {
      apply basic_world_formula_models_iff.
      split; [exact HΣlc|].
      split.
      - rewrite (res_fiber_from_projection_world_dom m mfib (lvars_fv D) σD Hproj).
        exact HΣscope.
      - split.
        + intros v Hv.
          pose proof (HΣdom v Hv) as Hvm.
          change (v ∈ lvars_of_atoms (world_dom (mfib : World))).
          change (v ∈ lvars_of_atoms (world_dom (m : World))) in Hvm.
          rewrite (res_fiber_from_projection_world_dom m mfib (lvars_fv D) σD Hproj).
          exact Hvm.
        + intros τ Hτ v T u HΣv Hτv.
          unfold res_lift_free in Hτ.
          cbn [worldA_stores] in Hτ.
          destruct Hτ as [σm [Hσmfib ->]].
          eapply HΣstores.
          * unfold res_lift_free. exists σm. split; [|reflexivity].
            eapply res_fiber_from_projection_store_source; eauto.
          * exact HΣv.
          * exact Hτv.
    }
    assert (Hres_world :
      res_models mfib (basic_world_formula (lty_env_msubst_store σD Σ))).
    {
      eapply basic_world_formula_subenv; [|exact Hmfib_world].
      intros v T Hlook.
      apply lty_env_msubst_store_lookup_some in Hlook as [HΣv _].
      exact HΣv.
    }
    eapply basic_world_formula_msubst_store_models_back; eauto.
Qed.

Lemma expr_basic_typing_formula_msubst_store_models
    σ Σ e T (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (expr_basic_typing_formula Σ e T)) ->
  res_models m (expr_basic_typing_formula
    (lty_env_msubst_store σ Σ)
    (lstore_instantiate_tm (lstore_lift_free σ) e) T).
Proof.
  intros Hσtyped Hm.
  change (formula_msubst_store σ (expr_basic_typing_formula Σ e T))
    with (FAtom (lqual_msubst_store σ (expr_basic_typing_lqual Σ e T))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, expr_basic_typing_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hbasic]].
  apply expr_basic_typing_formula_models_iff.
  split.
  - rewrite lty_env_msubst_store_dom.
    rewrite <- dom_lstore_lift_free.
    exact Hlc.
  - split.
    + rewrite lty_env_msubst_store_dom.
      rewrite <- dom_lstore_lift_free. exact Hsub.
    + apply basic_tm_has_ltype_msubst_store; assumption.
Qed.

Lemma expr_basic_typing_formula_msubst_store_models_back
    σ Σ e T (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (expr_basic_typing_formula
    (lty_env_msubst_store σ Σ)
    (lstore_instantiate_tm (lstore_lift_free σ) e) T) ->
  res_models m (formula_msubst_store σ (expr_basic_typing_formula Σ e T)).
Proof.
  intros Hσtyped Hm.
  apply expr_basic_typing_formula_models_iff in Hm as [Hlc [Hsub Hbasic]].
  apply res_models_atom_intro.
  unfold expr_basic_typing_lqual, lqual_msubst_store, lqual_mlsubst,
    logic_qualifier_denote.
  cbn [lqual_dom lqual_prop].
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  assert (HdomD : dom (lty_env_msubst_store σ Σ) =
    dom Σ ∖ dom (lstore_lift_free σ : LStoreT)).
  {
    rewrite lty_env_msubst_store_dom, dom_lstore_lift_free.
    reflexivity.
  }
  rewrite HdomD in Hlc, Hsub.
  exists Hlc, Hsub.
  eapply basic_tm_has_ltype_msubst_store_back; eauto.
Qed.

Lemma expr_total_formula_msubst_store_models
    σ Σ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (formula_msubst_store σ (expr_total_formula e)) ->
  res_models m (expr_total_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e)).
Proof.
  intros Hσtyped Hm.
  change (formula_msubst_store σ (expr_total_formula e))
    with (FAtom (lqual_msubst_store σ (expr_total_lqual e))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, expr_total_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Htotal]].
  pose proof (atom_store_has_ltype_closed _ _ Hσtyped) as Hclosed.
  pose proof (expr_total_on_msubst_store_from_back σ e
    (lworld_on_lift (tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT))
      m Hlc Hsub) Hclosed Htotal) as Htotal'.
  apply res_models_atom_intro.
  unfold expr_total_lqual, logic_qualifier_denote.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  exists Hlc, Hsub. exact Htotal'.
Qed.

Lemma expr_total_formula_msubst_store_models_back
    σ Σ e (m : WfWorldT) :
  atom_store_has_ltype Σ σ ->
  res_models m (expr_total_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
  res_models m (formula_msubst_store σ (expr_total_formula e)).
Proof.
  intros Hσtyped Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold expr_total_lqual, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  pose proof (atom_store_has_ltype_closed _ _ Hσtyped) as Hclosed.
  destruct Hden as [Hlc [Hsub Htotal]].
  apply res_models_atom_intro.
  unfold expr_total_lqual, lqual_msubst_store, lqual_mlsubst,
    logic_qualifier_denote.
  cbn [lqual_dom lqual_prop].
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  assert (HDeq :
    tm_lvars (lstore_instantiate_tm (lstore_lift_free σ) e) =
    tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT)).
  { apply tm_lvars_lstore_instantiate_lift_free_closed. exact Hclosed. }
  symmetry in HDeq.
  destruct HDeq.
  exists Hlc, Hsub.
  eapply expr_total_on_msubst_store_to_back; eauto.
Qed.

Lemma type_qualifier_formula_msubst_store_models
    σ q (m : WfWorldT) :
  res_models m (formula_msubst_store σ (type_qualifier_formula q)) ->
  res_models m (type_qualifier_formula (qual_msubst_store σ q)).
Proof.
  intros Hm.
  destruct q as [D P].
  change (formula_msubst_store σ
    (type_qualifier_formula {| qual_lvars := D; qual_prop := P |}))
    with (FAtom (lqual_msubst_store σ
      (type_qualifier_lqual {| qual_lvars := D; qual_prop := P |}))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, type_qualifier_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop] in Hden.
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  destruct Hden as [Hlc [Hsub Hholds]].
  apply res_models_atom_intro.
  unfold type_qualifier_formula, type_qualifier_lqual,
    qual_msubst_store, qual_mlsubst, logic_qualifier_denote.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop].
  change (atom_store_to_lvar_store σ) with (lstore_lift_free σ).
  exists Hlc, Hsub.
  intros s.
  specialize (Hholds (lstore_on_mlsubst_back D (lstore_lift_free σ) s)).
  split; intros HP.
  - apply (proj1 (lstore_in_lworld_on_mlsubst_back D
      (lstore_lift_free σ) s
      (lworld_on_lift (D ∖ dom (lstore_lift_free σ : LStoreT))
        m Hlc Hsub))).
    apply Hholds. exact HP.
  - apply Hholds.
    apply (proj2 (lstore_in_lworld_on_mlsubst_back D
      (lstore_lift_free σ) s
      (lworld_on_lift (D ∖ dom (lstore_lift_free σ : LStoreT))
        m Hlc Hsub))).
    exact HP.
Qed.

Lemma type_qualifier_formula_msubst_store2_models
    σ1 σ2 q (m : WfWorldT) :
  res_models m
    (formula_msubst_store σ2
      (formula_msubst_store σ1 (type_qualifier_formula q))) ->
  res_models m
    (type_qualifier_formula
      (qual_msubst_store σ2 (qual_msubst_store σ1 q))).
Proof.
  intros Hm.
  destruct q as [D P].
  change (formula_msubst_store σ2
    (formula_msubst_store σ1
      (type_qualifier_formula {| qual_lvars := D; qual_prop := P |})))
    with (FAtom (lqual_msubst_store σ2
      (lqual_msubst_store σ1
        (type_qualifier_lqual {| qual_lvars := D; qual_prop := P |}))))
    in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, type_qualifier_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop] in Hden.
  change (atom_store_to_lvar_store σ1) with (lstore_lift_free σ1) in Hden.
  change (atom_store_to_lvar_store σ2) with (lstore_lift_free σ2) in Hden.
  destruct Hden as [Hlc [Hsub Hholds]].
  apply res_models_atom_intro.
  unfold type_qualifier_formula, type_qualifier_lqual,
    qual_msubst_store, qual_mlsubst, logic_qualifier_denote.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop].
  change (atom_store_to_lvar_store σ1) with (lstore_lift_free σ1).
  change (atom_store_to_lvar_store σ2) with (lstore_lift_free σ2).
  exists Hlc, Hsub.
  intros s.
  specialize (Hholds
    (lstore_on_mlsubst_back D (lstore_lift_free σ1)
      (lstore_on_mlsubst_back (D ∖ dom (lstore_lift_free σ1 : LStoreT))
        (lstore_lift_free σ2) s))).
  rewrite lstore_in_lworld_on_mlsubst_back in Hholds.
  rewrite lstore_in_lworld_on_mlsubst_back in Hholds.
  exact Hholds.
Qed.

Lemma type_qualifier_formula_msubst_store_assoc_models
    σ1 σ2 q (m : WfWorldT) :
  res_models m
    (formula_msubst_store σ2
      (formula_msubst_store σ1 (type_qualifier_formula q))) ->
  res_models m
    (formula_msubst_store σ2
      (type_qualifier_formula (qual_msubst_store σ1 q))).
Proof.
  intros Hm.
  destruct q as [D P].
  change (formula_msubst_store σ2
    (formula_msubst_store σ1
      (type_qualifier_formula {| qual_lvars := D; qual_prop := P |})))
    with (FAtom (lqual_msubst_store σ2
      (lqual_msubst_store σ1
        (type_qualifier_lqual {| qual_lvars := D; qual_prop := P |}))))
    in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, type_qualifier_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop] in Hden.
  change (atom_store_to_lvar_store σ1) with (lstore_lift_free σ1) in Hden.
  change (atom_store_to_lvar_store σ2) with (lstore_lift_free σ2) in Hden.
  destruct Hden as [Hlc [Hsub Hholds]].
  apply res_models_atom_intro.
  unfold type_qualifier_formula, type_qualifier_lqual,
    qual_msubst_store, qual_mlsubst, logic_qualifier_denote.
  cbn [lqual_dom lqual_prop type_qualifier_holds_lworld
    qual_vars qual_lvars qual_prop].
  change (atom_store_to_lvar_store σ1) with (lstore_lift_free σ1).
  change (atom_store_to_lvar_store σ2) with (lstore_lift_free σ2).
  exists Hlc, Hsub.
  intros s.
  specialize (Hholds (lstore_on_mlsubst_back D (lstore_lift_free σ1) s)).
  rewrite lstore_in_lworld_on_mlsubst_back in Hholds.
  exact Hholds.
Qed.

Lemma expr_result_formula_msubst_store_models
    σ e x (m : WfWorldT) :
  store_closed σ ->
  x ∉ dom (lstore_lift_free σ : LStoreT) ->
  res_models m (formula_msubst_store σ (expr_result_formula e x)) ->
  res_models m (expr_result_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e) x).
Proof.
  intros Hclosed Hxρ Hm.
  change (formula_msubst_store σ (expr_result_formula e x))
    with (FAtom (lqual_msubst_store σ (expr_result_lqual e x))) in Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold lqual_msubst_store, expr_result_lqual,
    lqual_mlsubst, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  destruct Hden as [Hlc [Hsub Hresult]].
  pose proof (expr_result_at_world_msubst_store_from_back σ e x
    (lworld_on_lift ((tm_lvars e ∪ {[x]})
      ∖ dom (lstore_lift_free σ : LStoreT)) m Hlc Hsub)
    Hclosed Hxρ Hresult) as Hresult'.
  apply res_models_atom_intro.
  unfold expr_result_lqual, logic_qualifier_denote.
  rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
  replace ((tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT)) ∪ {[x]})
    with ((tm_lvars e ∪ {[x]}) ∖ dom (lstore_lift_free σ : LStoreT))
    by set_solver.
  exists Hlc, Hsub. exact Hresult'.
Qed.

Lemma expr_result_formula_msubst_store_models_back
    σ e x (m : WfWorldT) :
  store_closed σ ->
  x ∉ dom (lstore_lift_free σ : LStoreT) ->
  res_models m (expr_result_formula
    (lstore_instantiate_tm (lstore_lift_free σ) e) x) ->
  res_models m (formula_msubst_store σ (expr_result_formula e x)).
Proof.
  intros Hclosed Hxρ Hm.
  unfold res_models in Hm.
  cbn [formula_measure res_models_fuel] in Hm.
  destruct Hm as [_ Hden].
  unfold expr_result_lqual, logic_qualifier_denote in Hden.
  cbn [lqual_dom lqual_prop] in Hden.
  replace (tm_lvars (lstore_instantiate_tm (lstore_lift_free σ) e) ∪ {[x]})
    with ((tm_lvars e ∪ {[x]}) ∖ dom (lstore_lift_free σ : LStoreT))
    in Hden
    by (rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed);
      set_solver).
  destruct Hden as [Hlc [Hsub Hresult]].
  apply res_models_atom_intro.
  unfold lqual_msubst_store, expr_result_lqual,
    lqual_mlsubst, logic_qualifier_denote.
  cbn [lqual_dom lqual_prop].
  set (Dsrc := (tm_lvars e ∪ {[x]})
    ∖ dom (lstore_lift_free σ : LStoreT)).
  set (Ddst := tm_lvars (lstore_instantiate_tm (lstore_lift_free σ) e)
    ∪ {[x]}).
  assert (HD : Dsrc = Ddst).
  {
    unfold Dsrc, Ddst.
    rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
    set_solver.
  }
  assert (Hlc_src : lc_lvars Dsrc) by (rewrite HD; exact Hlc).
  assert (Hsub_src : lvars_fv Dsrc ⊆ world_dom (m : WorldT))
    by (rewrite HD; exact Hsub).
  assert (Hlift_eq :
      @lw value _ (lworld_on_lift Dsrc m Hlc_src Hsub_src) =
      @lw value _ (lworld_on_lift Ddst m Hlc Hsub)).
  {
    apply wfworldA_ext.
    unfold lworld_on_lift. simpl.
    subst Dsrc Ddst.
    rewrite (tm_lvars_lstore_instantiate_lift_free_closed σ e Hclosed).
    replace ((tm_lvars e ∪ {[x]})
        ∖ dom (lstore_lift_free σ : LStoreT))
      with ((tm_lvars e ∖ dom (lstore_lift_free σ : LStoreT))
        ∪ {[x]}) by set_solver.
    reflexivity.
  }
  exists Hlc_src, Hsub_src.
  eapply expr_result_at_world_msubst_store_to_back; eauto.
  change (expr_result_at_world
    (lstore_instantiate_tm (lstore_lift_free σ) e) x
    (@lw value _ (lworld_on_lift Dsrc m Hlc_src Hsub_src) : LWorldT)).
  rewrite Hlift_eq. exact Hresult.
Qed.

Lemma logic_var_open_bound0_fresh_lift_free k y (σ : StoreT) :
  y ∉ dom (σ : gmap atom value) ->
  swap (LVBound k) (LVFree y) (LVBound 0) ∉
    dom (lstore_lift_free σ : LStoreT).
Proof.
  intros Hy.
  rewrite dom_lstore_lift_free.
  destruct k as [|k].
  - rewrite swap_l.
    unfold lvars_of_atoms. intros Hbad.
    apply elem_of_map in Hbad as [z [Hz Hzdom]].
    inversion Hz. subst z. exact (Hy Hzdom).
  - rewrite swap_fresh by discriminate.
    unfold lvars_of_atoms. intros Hbad.
    apply elem_of_map in Hbad as [z [Hz _]].
    discriminate Hz.
Qed.

Lemma expr_result_formula_msubst_store_open_shift_models
    σ e k y (m : WfWorldT) :
  store_closed σ ->
  y ∉ dom (σ : gmap atom value) ∪ fv_tm e ->
  res_models m
    (formula_msubst_store σ
      (formula_open k y
        (expr_result_formula (tm_shift 0 e) (LVBound 0)))) ->
  res_models m
    (formula_open k y
      (expr_result_formula
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (LVBound 0))).
Proof.
  intros Hclosed Hfresh Hmodel.
  rewrite formula_open_expr_result_formula in Hmodel.
  2:{ rewrite tm_shift_fv. set_solver. }
  rewrite formula_open_expr_result_formula.
  2:{
    rewrite tm_shift_fv.
    assert (Hfvinst :
      fv_tm (lstore_instantiate_tm (lstore_lift_free σ) e) ⊆ fv_tm e).
    {
      rewrite lstore_instantiate_tm_no_bvars.
      - change (lstore_to_store (lstore_lift_free σ))
          with (lstore_free_part (lstore_lift_free σ)).
        rewrite lstore_free_part_lift_free.
        pose proof (msubst_fv_delete_tm σ e (proj1 Hclosed)).
        set_solver.
      - apply lc_lstore_lift_free.
      - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
    }
    set_solver.
  }
  eapply expr_result_formula_msubst_store_models in Hmodel.
  2:{ exact Hclosed. }
  2:{
    apply logic_var_open_bound0_fresh_lift_free.
    set_solver.
  }
  - rewrite lstore_instantiate_tm_open_fresh_lift_free in Hmodel
      by (exact Hclosed || (rewrite tm_shift_fv; exact Hfresh)).
    rewrite lstore_instantiate_tm_shift_lift_free in Hmodel
      by exact Hclosed.
    exact Hmodel.
Qed.

Lemma expr_result_formula_msubst_store_open_shift_models_back
    σ e k y (m : WfWorldT) :
  store_closed σ ->
  y ∉ dom (σ : gmap atom value) ∪ fv_tm e ->
  res_models m
    (formula_open k y
      (expr_result_formula
        (tm_shift 0 (lstore_instantiate_tm (lstore_lift_free σ) e))
        (LVBound 0))) ->
  res_models m
    (formula_msubst_store σ
      (formula_open k y
        (expr_result_formula (tm_shift 0 e) (LVBound 0)))).
Proof.
  intros Hclosed Hfresh Hmodel.
  rewrite formula_open_expr_result_formula in Hmodel.
  2:{
    rewrite tm_shift_fv.
    assert (Hfvinst :
      fv_tm (lstore_instantiate_tm (lstore_lift_free σ) e) ⊆ fv_tm e).
    {
      rewrite lstore_instantiate_tm_no_bvars.
      - change (lstore_to_store (lstore_lift_free σ))
          with (lstore_free_part (lstore_lift_free σ)).
        rewrite lstore_free_part_lift_free.
        pose proof (msubst_fv_delete_tm σ e (proj1 Hclosed)).
        set_solver.
      - apply lc_lstore_lift_free.
      - rewrite lstore_free_part_lift_free. exact (proj1 Hclosed).
    }
    set_solver.
  }
  rewrite formula_open_expr_result_formula.
  2:{ rewrite tm_shift_fv. set_solver. }
  eapply expr_result_formula_msubst_store_models_back.
  - exact Hclosed.
  - apply logic_var_open_bound0_fresh_lift_free. set_solver.
  - rewrite lstore_instantiate_tm_open_fresh_lift_free
      by (exact Hclosed || (rewrite tm_shift_fv; exact Hfresh)).
    rewrite lstore_instantiate_tm_shift_lift_free
      by exact Hclosed.
    exact Hmodel.
Qed.

End MsubstTransport.
