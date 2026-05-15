(** * ChoiceTyping.ResultWorldExtension

    Result-world facts phrased through explicit world extensions. *)

From CoreLang Require Import BasicTypingProps OperationalProps.
From ChoiceAlgebra Require Import WorldExtension.
From ChoiceTyping Require Import LetResultWorld ResultWorldExprCont.

Lemma let_result_world_on_total_as_extend_by
    X e x (m : WfWorld)
    (Hfresh : x ∉ world_dom (m : World))
    (Htotal : expr_total_result_on X e m) :
  ∃ F,
    forall_extension_shape (world_dom (m : World)) x F ∧
    m #> F ~~> let_result_world_on_total X e x m Hfresh Htotal.
Proof.
  unfold let_result_world_on_total.
  eapply forall_world_as_extend_by.
  - exact Hfresh.
  - apply let_result_world_on_dom.
  - apply let_result_world_on_restrict.
Qed.

Lemma FExprResultAt_base_result_witness
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  res_restrict n (dom Σ) = m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∀ σ, (m : World) σ →
    ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx.
Proof.
  intros Hty Hdom_m Hclosed Hrestrict Hdom_n Hmodel σ Hσm.
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as Hfv.
  pose proof (typing_tm_lc Σ e T Hty) as Hlc.
  assert (Hproj : (res_restrict n (dom Σ) : World) σ).
  { rewrite Hrestrict. exact Hσm. }
  destruct Hproj as [σn [Hσn HσnΣ]].
  assert (Hproj' : (res_restrict n (dom Σ) : World) σ).
  { exists σn. split; eauto. }
  pose proof (FExprResultAt_fiber_expr_result_in_world
    (dom Σ) e ν n σ Hproj' Hlc Hdom_n Hmodel) as Hexpr.
  assert (Hfiber :
    (res_fiber_from_projection n (dom Σ) σ Hproj' : World) σn).
  { apply res_fiber_from_projection_member; eauto. }
  assert (Hνproj :
    (res_restrict
      (res_fiber_from_projection n (dom Σ) σ Hproj') {[ν]} : World)
      (store_restrict σn {[ν]})).
  { exists σn. split; eauto. }
  pose proof (expr_result_in_world_sound
    (store_restrict σ (dom Σ)) e ν
    (res_fiber_from_projection n (dom Σ) σ Hproj')
    (store_restrict σn {[ν]}) Hexpr Hνproj) as Hstore.
  destruct (expr_result_store_elim ν
    (subst_map (store_restrict σ (dom Σ)) e)
    (store_restrict σn {[ν]}) Hstore)
    as [vx [_ [_ [_ HstepsX]]]].
  exists vx.
  rewrite (subst_map_restrict_to_fv_from_superset e
    (dom Σ) σ Hfv (proj1 (Hclosed σ Hσm))).
  exact HstepsX.
Qed.

Lemma FExprResultAt_as_extend_by
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World)) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  res_restrict n (dom Σ) = m →
  n ⊨ FExprResultAt (dom Σ) e ν →
  ∃ F,
    forall_extension_shape (world_dom (m : World)) ν F ∧
    m #> F ~~> n.
Proof.
  intros Hty Hdom_m Hclosed Hdom_n Hrestrict Hmodel.
  pose proof (FExprResultAt_base_result_witness
    Σ T e ν m n Hty Hdom_m Hclosed Hrestrict Hdom_n Hmodel) as Hresult.
  pose proof (FExprResultAt_unique_let_result_world
    Σ T e ν m n Hfresh Hresult Hty Hdom_m Hclosed Hdom_n Hrestrict Hmodel)
    as ->.
  apply forall_world_as_extend_by.
  - exact Hfresh.
  - apply let_result_world_on_dom.
  - apply let_result_world_on_restrict.
Qed.

Lemma FExprContIn_iff_result_extension
    (Σ : gmap atom ty) (T : ty) e
    (Q : FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  formula_fv Q ⊆ dom Σ →
  m ⊨ FExprContIn Σ e Q ↔
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν F n,
      ν ∉ L →
      forall_extension_shape (world_dom (m : World)) ν F →
      m #> F ~~> n →
      n ⊨ FExprResultAt (dom Σ) e ν →
      n ⊨ formula_open 0 ν Q.
Proof.
  intros Hty Hdom Hclosed Htotal HQfv.
  split.
  - intros Hcont.
    destruct (proj1 (FExprContIn_iff_let_result_world
      Σ T e Q m Hty Hdom Hclosed Htotal HQfv) Hcont)
      as [L [HLdom Hbody]].
    exists (L ∪ dom Σ ∪ fv_tm e ∪ formula_fv Q).
    split; [set_solver |].
    intros ν F n Hν HFshape Hext Hresult_model.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[[HνL HνΣ] Hνe] HνQ].
    assert (Hfresh : ν ∉ world_dom (m : World)).
    { rewrite Hdom. exact HνΣ. }
    pose proof (res_extend_by_dom _ _ _ Hext) as Hdom_n_ext.
    destruct HFshape as [HFin HFout].
    assert (Hdom_n : world_dom (n : World) = dom Σ ∪ {[ν]}).
    { rewrite Hdom_n_ext, Hdom, HFout. reflexivity. }
    assert (Hrestrict : res_restrict n (dom Σ) = m).
    { rewrite <- Hdom. apply res_extend_by_restrict_base with (F := F). exact Hext. }
    pose proof (FExprResultAt_base_result_witness
      Σ T e ν m n Hty Hdom Hclosed Hrestrict Hdom_n Hresult_model)
      as Hresult.
    pose proof (FExprResultAt_unique_let_result_world
      Σ T e ν m n Hfresh Hresult Hty Hdom Hclosed Hdom_n Hrestrict
      Hresult_model) as ->.
    eauto.
  - intros [L [HLdom Hbody]].
    apply (proj2 (FExprContIn_iff_let_result_world
      Σ T e Q m Hty Hdom Hclosed Htotal HQfv)).
    exists (L ∪ dom Σ ∪ fv_tm e).
    split; [set_solver |].
    intros ν Hν Hfresh Hresult.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[HνL HνΣ] Hνe].
    set (mν := let_result_world_on e ν m Hfresh Hresult).
    destruct (forall_world_as_extend_by m ν mν Hfresh
      ltac:(subst mν; apply let_result_world_on_dom)
      ltac:(subst mν; apply let_result_world_on_restrict))
      as [F [HFshape Hext]].
    apply (Hbody ν F mν HνL HFshape Hext).
    subst mν.
    eapply let_result_world_on_models_FExprResultAt.
    + eapply basic_typing_contains_fv_tm. exact Hty.
    + eapply typing_tm_lc. exact Hty.
    + exact HνΣ.
    + rewrite Hdom. reflexivity.
    + exact Hclosed.
Qed.
