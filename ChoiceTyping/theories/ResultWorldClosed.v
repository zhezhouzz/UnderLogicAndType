(** * ChoiceTyping.ResultWorldClosed

    Store-closedness and regularity facts for result worlds.  These lemmas are
    independent of the later expression-result bridges, so keeping them here
    makes the tlet proof support files less tangled. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  BasicTypingProps LocallyNamelessProps StrongNormalization.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma denot_ctx_in_env_world_closed_on_erased Σ Γ m :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  world_closed_on (dom (erase_ctx_under Σ Γ)) m.
Proof.
  intros Hbasic Hctx σ Hσ.
  assert (Hdom_erase :
    dom (erase_ctx_under Σ Γ) = dom Σ ∪ ctx_dom Γ).
  { apply erase_ctx_under_dom_basic. exact Hbasic. }
  rewrite Hdom_erase.
  split.
  - exact (proj1 (denot_ctx_in_env_store_erased_typed
      Σ Γ m σ Hbasic Hctx Hσ)).
  - exact (denot_ctx_in_env_store_erased_lc
      Σ Γ m σ Hbasic Hctx Hσ).
Qed.

Lemma world_closed_on_restrict_store_closed X (m : WfWorld) σ :
  world_closed_on X m →
  (res_restrict m X : World) σ →
  store_closed σ.
Proof.
  intros Hclosed [σ0 [Hσ0 <-]].
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma world_closed_on_store_restrict_closed X Y (m : WfWorld) σ :
  Y ⊆ X →
  world_closed_on X m →
  (m : World) σ →
  store_closed (store_restrict σ Y).
Proof.
  intros HYX Hclosed Hσ.
  replace (store_restrict σ Y) with
    (store_restrict (store_restrict σ X) Y).
  - apply store_closed_restrict. exact (Hclosed σ Hσ).
  - rewrite store_restrict_twice_subset by exact HYX. reflexivity.
Qed.

Lemma world_closed_on_mono (X Y : aset) (m : WfWorld) :
  X ⊆ Y →
  world_closed_on Y m →
  world_closed_on X m.
Proof.
  intros HXY Hclosed σ Hσ.
  specialize (Hclosed σ Hσ) as [Hclosed_env Hlc_env].
  split.
  - replace (store_restrict σ X) with
      (store_restrict (store_restrict σ Y) X).
    + apply closed_env_restrict. exact Hclosed_env.
    + rewrite store_restrict_twice_subset by exact HXY. reflexivity.
  - replace (store_restrict σ X) with
      (store_restrict (store_restrict σ Y) X).
    + apply lc_env_restrict. exact Hlc_env.
    + rewrite store_restrict_twice_subset by exact HXY. reflexivity.
Qed.

Lemma expr_total_on_to_fv_result X e (m : WfWorld) :
  world_closed_on X m →
  expr_total_on X e m →
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hclosed [Hfv Htotal] σ Hσ.
  destruct (Htotal σ Hσ) as [vx Hsteps].
  exists vx.
  pose proof (subst_map_eq_on_fv e
    (store_restrict σ X)
    (store_restrict σ (fv_tm e))) as Heq.
  assert (Hclosed_fv :
    closed_env (store_restrict (store_restrict σ X) (fv_tm e))).
  {
    replace (store_restrict (store_restrict σ X) (fv_tm e)) with
      (store_restrict σ (fv_tm e)).
    - exact (proj1 (world_closed_on_store_restrict_closed
        X (fv_tm e) m σ Hfv Hclosed Hσ)).
    - rewrite store_restrict_twice_subset by exact Hfv. reflexivity.
  }
  specialize (Heq Hclosed_fv).
  assert (Hagree :
    store_restrict (store_restrict σ (fv_tm e)) (fv_tm e) =
    store_restrict (store_restrict σ X) (fv_tm e)).
  {
    rewrite store_restrict_twice_same.
    rewrite store_restrict_twice_subset by exact Hfv.
    reflexivity.
  }
  specialize (Heq Hagree).
  change (subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
  replace (subst_map (store_restrict σ (fv_tm e)) e)
    with (subst_map (store_restrict σ X) e) by (symmetry; exact Heq).
  exact Hsteps.
Qed.

Lemma msubst_closed_tm_of_restrict_world X e (m : WfWorld) σ :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  lc_tm e →
  world_closed_on X m →
  (res_restrict m X : World) σ →
  closed_tm (subst_map (store_restrict σ X) e).
Proof.
  intros HXm Hfv Hlc Hclosed Hσ.
  assert (Hdomσ : dom σ ⊆ X).
  {
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
    simpl in Hdom. set_solver.
  }
  replace (store_restrict σ X) with σ.
  - apply msubst_closed_tm.
    + eapply world_closed_on_restrict_store_closed; eauto.
    + eauto 6.
    + change (fv_tm e ⊆ dom σ).
      pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
      simpl in Hdom. rewrite Hdom. set_solver.
  - symmetry. apply store_restrict_idemp. exact Hdomσ.
Qed.

Lemma steps_closed_result_of_restrict_world X e (m : WfWorld) σ v :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  lc_tm e →
  world_closed_on X m →
  (res_restrict m X : World) σ →
  subst_map (store_restrict σ X) e →* tret v →
  stale v = ∅ ∧ is_lc v.
Proof.
  intros HXm Hfv Hlc Hclosed Hσ Hsteps.
  eapply steps_closed_result.
  - eapply msubst_closed_tm_of_restrict_world; eauto.
  - eauto 6.
Qed.

Lemma body_tm_msubst_restrict_world X e (m : WfWorld) σ :
  body_tm e →
  world_closed_on X m →
  (res_restrict m X : World) σ →
  body_tm (subst_map (store_restrict σ X) e).
Proof.
  intros Hbody Hclosed Hσ.
  assert (Hdomσ : dom σ ⊆ X).
  {
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
    simpl in Hdom. set_solver.
  }
  replace (store_restrict σ X) with σ.
  - apply body_tm_msubst.
    + exact (proj1 (world_closed_on_restrict_store_closed X m σ
        Hclosed Hσ)).
    + exact (proj2 (world_closed_on_restrict_store_closed X m σ
        Hclosed Hσ)).
    + eauto 6.
  - symmetry. apply store_restrict_idemp. exact Hdomσ.
Qed.

Lemma world_closed_on_restrict X Y (m : WfWorld) :
  X ⊆ Y →
  world_closed_on X m →
  world_closed_on X (res_restrict m Y).
Proof.
  intros HXY Hclosed σ Hσ.
  destruct Hσ as [σ0 [Hσ0 Hrestrict]].
  rewrite <- Hrestrict.
  store_norm.
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma let_result_world_on_store_closed_on
    X e ν (n : WfWorld) Hfresh Hresult :
  ν ∉ X →
  world_closed_on X n →
  world_closed_on X (let_result_world_on e ν n Hfresh Hresult).
Proof.
  intros HνX Hclosed σx Hσx.
  destruct (let_result_world_on_elim e ν n Hfresh Hresult σx Hσx)
    as [σ [vx [Hσ [Hsteps ->]]]].
  rewrite store_restrict_insert_notin by exact HνX.
  exact (Hclosed σ Hσ).
Qed.

Lemma let_result_world_on_store_closed_on_insert
    X e ν (n : WfWorld) Hfresh Hresult :
  ν ∉ X →
  world_closed_on X n →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ (fv_tm e)) e →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  world_closed_on (X ∪ {[ν]})
    (let_result_world_on e ν n Hfresh Hresult).
Proof.
  intros HνX Hclosed Hres σν Hσν.
  destruct (let_result_world_on_elim e ν n Hfresh Hresult σν Hσν)
    as [σ [vx [Hσ [Hsteps ->]]]].
  rewrite store_restrict_insert_fresh_union.
  2:{
    eapply store_lookup_none_of_dom.
    - apply wfworld_store_dom; eauto 6.
    - eauto 6.
  }
  2:{ eauto 6. }
  destruct (Hclosed σ Hσ) as [Hclosedσ Hlcσ].
  destruct (Hres σ vx Hσ Hsteps) as [Hvx_closed Hvx_lc].
  split.
  - unfold closed_env in *.
    apply map_Forall_insert_2; eauto 6.
  - unfold lc_env in *.
    apply map_Forall_insert_2; eauto 6.
Qed.

Lemma let_result_world_on_closed_insert_from_basic_subset
    (Δ : gmap atom ty) T e x (m : WfWorld) Hfresh Hresult :
  Δ ⊢ₑ e ⋮ T →
  dom Δ ⊆ world_dom (m : World) →
  world_closed_on (dom Δ) m →
  x ∉ dom Δ →
  world_closed_on (dom (<[x := T]> Δ))
    (let_result_world_on e x m Hfresh Hresult).
Proof.
  intros Htyped Hdom Hclosed Hx.
  rewrite dom_insert_L.
  replace ({[x]} ∪ dom Δ) with (dom Δ ∪ {[x]}) by set_solver.
  eapply let_result_world_on_store_closed_on_insert.
  - eauto 6.
  - eauto 6.
  - intros σ vx Hσ Hsteps.
    pose proof (basic_typing_contains_fv_tm Δ e T Htyped) as Hfv.
    pose proof (typing_tm_lc Δ e T Htyped) as Hlc.
    assert (Hclosed_fv : world_closed_on (fv_tm e) m).
    { eapply world_closed_on_mono; [exact Hfv | exact Hclosed]. }
    eapply (steps_closed_result_of_restrict_world
      (fv_tm e) e m (store_restrict σ (fv_tm e)) vx).
    + intros z Hz. apply Hdom. apply Hfv. exact Hz.
    + set_solver.
    + eauto 6.
    + eauto 6.
    + exists σ. split; eauto 6.
    + replace (store_restrict (store_restrict σ (fv_tm e)) (fv_tm e))
        with (store_restrict σ (fv_tm e)).
      * eauto 6.
      * store_norm. reflexivity.
Qed.

Lemma let_result_world_on_closed_insert_from_basic
    (Δ : gmap atom ty) T e x (m : WfWorld) Hfresh Hresult :
  Δ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Δ →
  world_closed_on (dom Δ) m →
  x ∉ dom Δ →
  world_closed_on (dom (<[x := T]> Δ))
    (let_result_world_on e x m Hfresh Hresult).
Proof.
  intros Htyped Hdom Hclosed Hx.
  eapply let_result_world_on_closed_insert_from_basic_subset; eauto.
  rewrite Hdom. set_solver.
Qed.
