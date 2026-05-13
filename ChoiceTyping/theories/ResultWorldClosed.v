(** * ChoiceTyping.ResultWorldClosed

    Store-closedness and regularity facts for result worlds.  These lemmas are
    independent of the later fiber/fresh-forall bridges, so keeping them here
    makes the tlet proof support files less tangled. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps StrongNormalization.
From ChoiceTyping Require Export SoundnessCommon.
From ChoiceTyping Require Export LetResultWorld.
From ChoiceTyping Require Import Naming.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Definition world_store_closed_on (X : aset) (m : WfWorld) : Prop :=
  ∀ σ, (m : World) σ → store_closed (store_restrict σ X).

Lemma world_store_closed_on_world_closed_on X (m : WfWorld) :
  world_store_closed_on X m →
  world_closed_on X m.
Proof.
  intros Hclosed σ Hσ.
  exact (proj1 (Hclosed σ Hσ)).
Qed.

Lemma world_store_closed_on_swap x y X (m : WfWorld) :
  world_store_closed_on X m →
  world_store_closed_on (aset_swap x y X) (res_swap x y m).
Proof.
  intros Hclosed σ Hσ.
  simpl in Hσ.
  destruct Hσ as [σ0 [Hσ0 Hswap]]. subst σ.
  rewrite store_restrict_swap.
  apply store_closed_store_swap.
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma denot_ctx_in_env_world_store_closed_on_erased Σ Γ m :
  basic_ctx (dom Σ) Γ →
  m ⊨ denot_ctx_in_env Σ Γ →
  world_store_closed_on (dom (erase_ctx_under Σ Γ)) m.
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

Lemma world_store_closed_on_restrict_store_closed X (m : WfWorld) σ :
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  store_closed σ.
Proof.
  intros Hclosed [σ0 [Hσ0 <-]].
  exact (Hclosed σ0 Hσ0).
Qed.

Lemma world_store_closed_on_restrict_closed_env X (m : WfWorld) σ :
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  closed_env σ.
Proof.
  intros Hclosed Hσ.
  exact (proj1 (world_store_closed_on_restrict_store_closed X m σ Hclosed Hσ)).
Qed.

Lemma world_store_closed_on_restrict_lc_env X (m : WfWorld) σ :
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  lc_env σ.
Proof.
  intros Hclosed Hσ.
  exact (proj2 (world_store_closed_on_restrict_store_closed X m σ Hclosed Hσ)).
Qed.

Lemma world_store_closed_on_restrict_store_restrict_closed X (m : WfWorld) σ :
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  store_closed (store_restrict σ X).
Proof.
  intros Hclosed Hσ.
  apply store_closed_restrict.
  eapply world_store_closed_on_restrict_store_closed; eauto.
Qed.

Lemma world_store_closed_on_restrict_store_restrict_closed_env X (m : WfWorld) σ :
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  closed_env (store_restrict σ X).
Proof.
  intros Hclosed Hσ.
  exact (proj1 (world_store_closed_on_restrict_store_restrict_closed X m σ Hclosed Hσ)).
Qed.

Lemma world_store_closed_on_restrict_store_restrict_lc_env X (m : WfWorld) σ :
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  lc_env (store_restrict σ X).
Proof.
  intros Hclosed Hσ.
  exact (proj2 (world_store_closed_on_restrict_store_restrict_closed X m σ Hclosed Hσ)).
Qed.

Lemma world_store_closed_on_mono (X Y : aset) (m : WfWorld) :
  X ⊆ Y →
  world_store_closed_on Y m →
  world_store_closed_on X m.
Proof.
  intros HXY Hclosed σ Hσ.
  specialize (Hclosed σ Hσ) as [Hclosed_env Hlc_env].
  split.
  - replace (store_restrict σ X) with
      (store_restrict (store_restrict σ Y) X).
    + apply closed_env_restrict. exact Hclosed_env.
    + store_norm. replace (Y ∩ X) with X by set_solver. reflexivity.
  - replace (store_restrict σ X) with
      (store_restrict (store_restrict σ Y) X).
    + apply lc_env_restrict. exact Hlc_env.
    + store_norm. replace (Y ∩ X) with X by set_solver. reflexivity.
Qed.

Lemma expr_total_on_to_fv_result X e (m : WfWorld) :
  world_store_closed_on X m →
  expr_total_on X e m →
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hclosed [Hfv Htotal] σ Hσ.
  destruct (strongly_normalizing_reaches_result _ (Htotal σ Hσ)) as [vx Hsteps].
  exists vx.
  pose proof (subst_map_eq_on_fv e
    (store_restrict σ X)
    (store_restrict σ (fv_tm e))) as Heq.
  assert (Hclosed_fv :
    closed_env (store_restrict (store_restrict σ X) (fv_tm e))).
  {
    apply closed_env_restrict.
    exact (proj1 (Hclosed σ Hσ)).
  }
  specialize (Heq Hclosed_fv).
  assert (Hagree :
    store_restrict (store_restrict σ (fv_tm e)) (fv_tm e) =
    store_restrict (store_restrict σ X) (fv_tm e)).
  {
    store_norm.
    replace (X ∩ fv_tm e) with (fv_tm e) by set_solver.
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
  world_store_closed_on X m →
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
    + eapply world_store_closed_on_restrict_store_closed; eauto.
    + exact Hlc.
    + change (fv_tm e ⊆ dom σ).
      pose proof (wfworld_store_dom (res_restrict m X) σ Hσ) as Hdom.
      simpl in Hdom. rewrite Hdom. set_solver.
  - symmetry. apply store_restrict_idemp. exact Hdomσ.
Qed.

Lemma steps_closed_result_of_restrict_world X e (m : WfWorld) σ v :
  X ⊆ world_dom (m : World) →
  fv_tm e ⊆ X →
  lc_tm e →
  world_store_closed_on X m →
  (res_restrict m X : World) σ →
  subst_map (store_restrict σ X) e →* tret v →
  stale v = ∅ ∧ is_lc v.
Proof.
  intros HXm Hfv Hlc Hclosed Hσ Hsteps.
  eapply steps_closed_result.
  - eapply msubst_closed_tm_of_restrict_world; eauto.
  - exact Hsteps.
Qed.

Lemma body_tm_msubst_restrict_world X e (m : WfWorld) σ :
  body_tm e →
  world_store_closed_on X m →
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
    + eapply world_store_closed_on_restrict_closed_env; eauto.
    + eapply world_store_closed_on_restrict_lc_env; eauto.
    + exact Hbody.
  - symmetry. apply store_restrict_idemp. exact Hdomσ.
Qed.

Lemma world_store_closed_on_le X (m n : WfWorld) :
  X ⊆ world_dom (m : World) →
  m ⊑ n →
  world_store_closed_on X m →
  world_store_closed_on X n.
Proof.
  intros HXm Hle Hclosed σ Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert ((res_restrict n (world_dom (m : World)) : World)
    (store_restrict σ (world_dom (m : World)))) as Hσm.
  { exists σ. split; [exact Hσ | reflexivity]. }
  rewrite Hrestrict in Hσm.
  replace (store_restrict σ X) with
    (store_restrict (store_restrict σ (world_dom (m : World))) X).
  - exact (Hclosed _ Hσm).
  - store_norm. reflexivity.
Qed.

Lemma world_store_closed_on_restrict X Y (m : WfWorld) :
  X ⊆ Y →
  world_store_closed_on X m →
  world_store_closed_on X (res_restrict m Y).
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
  world_store_closed_on X n →
  world_store_closed_on X (let_result_world_on e ν n Hfresh Hresult).
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
  world_store_closed_on X n →
  (∀ σ vx,
    (n : World) σ →
    subst_map (store_restrict σ (fv_tm e)) e →* tret vx →
    stale vx = ∅ ∧ is_lc vx) →
  world_store_closed_on (X ∪ {[ν]})
    (let_result_world_on e ν n Hfresh Hresult).
Proof.
  intros HνX Hclosed Hres σν Hσν.
  destruct (let_result_world_on_elim e ν n Hfresh Hresult σν Hσν)
    as [σ [vx [Hσ [Hsteps ->]]]].
  rewrite store_restrict_insert_fresh_union.
  2:{
    eapply store_lookup_none_of_dom.
    - apply wfworld_store_dom. exact Hσ.
    - exact Hfresh.
  }
  2:{ exact HνX. }
  destruct (Hclosed σ Hσ) as [Hclosedσ Hlcσ].
  destruct (Hres σ vx Hσ Hsteps) as [Hvx_closed Hvx_lc].
  split.
  - unfold closed_env in *.
    apply map_Forall_insert_2; [exact Hvx_closed | exact Hclosedσ].
  - unfold lc_env in *.
    apply map_Forall_insert_2; [exact Hvx_lc | exact Hlcσ].
Qed.
