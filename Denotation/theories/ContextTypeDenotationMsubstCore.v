(** * Denotation.ContextTypeDenotationMsubstCore

    Split from ContextTypeDenotationMsubst for incremental compilation. *)

From Denotation Require Import Notation ContextTypeDenotationDefinition ContextTypeDenotationLvars.

Section ContextTypeDenotationMsubst.

Definition denot_msubst_relevant_store
    (σ : StoreT) (τ : context_ty) (e : tm) : StoreT :=
  store_restrict σ (lvars_fv (denot_relevant_lvars τ e)).

Definition base_store_projection
    (Σbase : gmap atom ty) (σ : StoreT) (m : WfWorldT) : Prop :=
  dom (σ : StoreT) = dom Σbase /\
  (res_restrict m (dom Σbase) : WorldT) = singleton_world σ.

Definition store_singleton_projection
    (σ : StoreT) (m : WfWorldT) : Prop :=
  (res_restrict m (dom (σ : StoreT)) : WorldT) = singleton_world σ.

Lemma res_fiber_from_projection_store_dom
    (m mfib : WfWorldT) (X : aset) (σ : StoreT) :
  X ⊆ world_dom (m : WorldT) ->
  res_fiber_from_projection m X σ mfib ->
  dom (σ : StoreT) = X.
Proof.
  intros HX [Hproj _].
  pose proof (wfworld_store_dom (res_restrict m X) σ Hproj) as Hdom.
  change (dom (σ : StoreT) = world_dom (res_restrict m X : WorldT)) in Hdom.
  cbn [res_restrict resA_restrict rawA_restrict worldA_dom] in Hdom.
  set_solver.
Qed.

Lemma base_store_projection_from_fiber
    (Σbase : gmap atom ty) (m mfib : WfWorldT) (σ : StoreT) :
  dom Σbase ⊆ world_dom (m : WorldT) ->
  res_fiber_from_projection m (dom Σbase) σ mfib ->
  base_store_projection Σbase σ mfib.
Proof.
  intros HΣm Hfib.
  split.
  - eapply res_fiber_from_projection_store_dom; eauto.
  - eapply res_restrict_fiber_from_projection_eq_singleton.
    + exact Hfib.
    + eapply res_fiber_from_projection_store_dom; eauto.
Qed.

Lemma base_store_projection_restrict
    (Σbase : gmap atom ty) (σ : StoreT) (m : WfWorldT) X :
  X ⊆ dom Σbase ->
  base_store_projection Σbase σ m ->
  (res_restrict m X : WorldT) = singleton_world (store_restrict σ X).
Proof.
  intros HX [_ Hsingle].
  eapply res_restrict_singleton_subset; eauto.
Qed.

Lemma base_store_projection_to_store_singleton_projection
    (Σbase : gmap atom ty) (σ : StoreT) (m : WfWorldT) :
  base_store_projection Σbase σ m ->
  store_singleton_projection σ m.
Proof.
  intros [Hdom Hsingle].
  unfold store_singleton_projection.
  rewrite Hdom. exact Hsingle.
Qed.

Lemma store_singleton_projection_restrict
    (σ : StoreT) (m : WfWorldT) X :
  X ⊆ dom (σ : StoreT) ->
  store_singleton_projection σ m ->
  (res_restrict m X : WorldT) = singleton_world (store_restrict σ X).
Proof.
  intros HX Hproj.
  unfold store_singleton_projection in Hproj.
  eapply res_restrict_singleton_subset; eauto.
Qed.

Lemma store_singleton_projection_restrict_current
    (σ : StoreT) (m : WfWorldT) X :
  X ⊆ dom (σ : StoreT) ->
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) m.
Proof.
  intros HX Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  replace (dom (σ : StoreT) ∩ X) with X by set_solver.
  eapply store_singleton_projection_restrict; eauto.
Qed.

Lemma store_singleton_projection_restrict_any
    (σ : StoreT) (m : WfWorldT) X :
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) m.
Proof.
  intros Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  transitivity (singleton_world (store_restrict σ (dom (σ : StoreT) ∩ X))).
  - eapply store_singleton_projection_restrict; [set_solver|exact Hproj].
  - f_equal.
    transitivity
      (store_restrict (store_restrict σ X) (dom (σ : StoreT) ∩ X)).
    + symmetry.
      rewrite storeA_restrict_restrict.
      replace (X ∩ (dom (σ : StoreT) ∩ X)) with
        (dom (σ : StoreT) ∩ X) by set_solver.
      reflexivity.
    + apply storeA_restrict_idemp_eq.
      rewrite storeA_restrict_dom. set_solver.
Qed.

Lemma store_singleton_projection_dom_subset_world
    (σ : StoreT) (m : WfWorldT) :
  store_singleton_projection σ m ->
  dom (σ : StoreT) ⊆ world_dom (m : WorldT).
Proof.
  intros Hsingle x Hx.
  pose proof (f_equal world_dom Hsingle) as Hdom.
  simpl in Hdom.
  set_solver.
Qed.

Lemma store_singleton_projection_extend_base
    (σ : StoreT) (m my : WfWorldT) (F : fiber_extension) :
  res_extend_by m F my ->
  store_singleton_projection σ m ->
  store_singleton_projection σ my.
Proof.
  intros Hext Hproj.
  unfold store_singleton_projection in *.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hdomσ.
  pose proof (res_extend_by_restrict_base m F my Hext) as Hbase.
  assert (Hself : res_restrict m (world_dom (m : WorldT)) = m).
  {
    apply res_restrict_eq_of_le.
    reflexivity.
  }
  pose proof (res_restrict_eq_subset my m (world_dom (m : WorldT))
    (dom (σ : StoreT)) Hdomσ ltac:(rewrite Hbase, Hself; reflexivity))
    as Hrestrict.
  rewrite Hrestrict. exact Hproj.
Qed.

Lemma store_singleton_projection_of_restrict_base
    (σ : StoreT) (m my : WfWorldT) :
  res_restrict my (world_dom (m : WorldT)) = m ->
  store_singleton_projection σ m ->
  store_singleton_projection σ my.
Proof.
  intros Hbase Hproj.
  unfold store_singleton_projection in *.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hdomσ.
  assert (Hself : res_restrict m (world_dom (m : WorldT)) = m).
  {
    apply res_restrict_eq_of_le.
    reflexivity.
  }
  pose proof (res_restrict_eq_subset my m (world_dom (m : WorldT))
    (dom (σ : StoreT)) Hdomσ ltac:(rewrite Hbase, Hself; reflexivity))
    as Hrestrict.
  rewrite Hrestrict. exact Hproj.
Qed.

Lemma store_singleton_projection_subset_world
    (σ : StoreT) (p m : WfWorldT) X :
  res_subset p m ->
  X ⊆ dom (σ : StoreT) ->
  X ⊆ world_dom (p : WorldT) ->
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) p.
Proof.
  intros Hsub HX HpX Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  replace (dom (σ : StoreT) ∩ X) with X by set_solver.
  eapply res_subset_singleton_restrict; [exact Hsub|exact HpX|].
  eapply store_singleton_projection_restrict; eauto.
Qed.

Lemma store_singleton_projection_product_le_l
    (σ : StoreT) (m m1 m2 : WfWorldT) (Hc : world_compat m1 m2) X :
  res_product m1 m2 Hc ⊑ m ->
  X ⊆ dom (σ : StoreT) ->
  X ⊆ world_dom (m1 : WorldT) ->
  X ⊆ world_dom (m2 : WorldT) ->
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) m1.
Proof.
  intros Hle HX Hm1X Hm2X Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  replace (dom (σ : StoreT) ∩ X) with X by set_solver.
  destruct (res_product_le_singleton_restrict_inv
    m m1 m2 Hc X (store_restrict σ X) Hle Hm1X Hm2X) as [H1 _].
  - eapply store_singleton_projection_restrict; eauto.
  - exact H1.
Qed.

Lemma store_singleton_projection_product_le_r
    (σ : StoreT) (m m1 m2 : WfWorldT) (Hc : world_compat m1 m2) X :
  res_product m1 m2 Hc ⊑ m ->
  X ⊆ dom (σ : StoreT) ->
  X ⊆ world_dom (m1 : WorldT) ->
  X ⊆ world_dom (m2 : WorldT) ->
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) m2.
Proof.
  intros Hle HX Hm1X Hm2X Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  replace (dom (σ : StoreT) ∩ X) with X by set_solver.
  destruct (res_product_le_singleton_restrict_inv
    m m1 m2 Hc X (store_restrict σ X) Hle Hm1X Hm2X) as [_ H2].
  - eapply store_singleton_projection_restrict; eauto.
  - exact H2.
Qed.

Lemma store_singleton_projection_compat_restrict_of_scope
    (σ : StoreT) (m n : WfWorldT) (φ : FormulaT) :
  world_compat n m ->
  store_singleton_projection σ m ->
  formula_scoped_in_world n φ ->
  store_singleton_projection (store_restrict σ (formula_fv φ)) n.
Proof.
  intros Hc Hproj Hscope.
  unfold store_singleton_projection.
  change (dom (store_restrict σ (formula_fv φ) : StoreT)) with
    (dom (store_restrict σ (formula_fv φ) : gmap atom value)).
  rewrite storeA_restrict_dom.
  eapply res_restrict_to_singleton_if_projection_constant.
  intros σn Hσn.
  pose proof (wfworld_store_dom n σn Hσn) as Hdomn.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hdomσm.
  destruct (world_wf m) as [[σm Hσm] _].
  pose proof (wfworld_store_dom m σm Hσm) as Hdomm.
  assert (Hoverlap_sub :
    dom (σ : StoreT) ∩ formula_fv φ ⊆
    dom (σn : StoreT) ∩ dom (σm : StoreT)).
  {
    intros z Hz.
    apply elem_of_intersection in Hz as [Hzσ Hzφ].
    apply elem_of_intersection. split.
    - assert (HzN : z ∈ world_dom (n : WorldT)).
      { unfold formula_scoped_in_world in Hscope. set_solver. }
      rewrite <- Hdomn in HzN. exact HzN.
    - assert (HzM : z ∈ world_dom (m : WorldT)).
      { set_solver. }
      rewrite <- Hdomm in HzM. exact HzM.
  }
  pose proof (Hc σn σm Hσn Hσm) as Hcompat.
  pose proof (proj1 (storeA_compat_spec σn σm) Hcompat) as Hoverlap.
  pose proof (storeA_restrict_eq_mono σn σm
    (dom (σ : StoreT) ∩ formula_fv φ)
    (dom (σn : StoreT) ∩ dom (σm : StoreT))
    Hoverlap_sub Hoverlap) as Hnm.
  pose proof (store_singleton_projection_restrict σ m
    (dom (σ : StoreT) ∩ formula_fv φ) ltac:(set_solver) Hproj)
    as HmX.
  assert (HσmX : storeA_restrict σm (dom (σ : StoreT) ∩ formula_fv φ) =
                 storeA_restrict σ (dom (σ : StoreT) ∩ formula_fv φ)).
  {
    assert (Hraw :
      (res_restrict m (dom (σ : StoreT) ∩ formula_fv φ) : WorldT)
        (storeA_restrict σm (dom (σ : StoreT) ∩ formula_fv φ))).
    { exists σm. split; [exact Hσm|reflexivity]. }
    rewrite HmX in Hraw. simpl in Hraw. exact Hraw.
  }
  transitivity (storeA_restrict σm (dom (σ : StoreT) ∩ formula_fv φ)).
  - exact Hnm.
  - rewrite HσmX.
    apply storeA_map_eq. intros z.
    rewrite !storeA_restrict_lookup.
    destruct (decide (z ∈ formula_fv φ)) as [Hzφ|Hzφ].
    + destruct ((σ : StoreT) !! z) as [v|] eqn:Hzσ.
      * assert (Hzdom : z ∈ dom (σ : gmap atom value)).
        { apply elem_of_dom. exists v. exact Hzσ. }
        rewrite !decide_True by set_solver. reflexivity.
      * assert (Hzσnone : (σ : gmap atom value) !! z = None) by exact Hzσ.
        rewrite decide_False by
          (intros Hz; apply elem_of_intersection in Hz as [Hzdom _];
           change (z ∈ dom (σ : gmap atom value)) in Hzdom;
           apply elem_of_dom in Hzdom as [v Hv]; rewrite Hzσnone in Hv; discriminate).
        change (None = (σ : gmap atom value) !! z).
        symmetry. exact Hzσnone.
    + rewrite !decide_False by set_solver. reflexivity.
Qed.

Lemma world_compat_singleton_restrict_from_projection
    (σ : StoreT) (m n : WfWorldT) X :
  world_compat n m ->
  store_singleton_projection σ m ->
  world_compat n (singleton_world (store_restrict σ X)).
Proof.
  intros Hc Hproj σn σfix Hσn Hσfix.
  change (σfix = store_restrict σ X) in Hσfix.
  subst σfix.
  apply (proj2 (storeA_compat_spec σn (store_restrict σ X))).
  destruct (world_wf m) as [[σm Hσm] _].
  pose proof (wfworld_store_dom n σn Hσn) as Hdomn.
  pose proof (wfworld_store_dom m σm Hσm) as Hdomm.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hdomσm.
  pose proof (Hc σn σm Hσn Hσm) as Hcompat.
  pose proof (proj1 (storeA_compat_spec σn σm) Hcompat) as Hoverlap.
  set (O := dom (σn : StoreT) ∩ dom (store_restrict σ X : StoreT)).
  assert (HOsub : O ⊆ dom (σn : StoreT) ∩ dom (σm : StoreT)).
  {
    subst O.
    change (dom (store_restrict σ X : StoreT)) with
      (dom (store_restrict σ X : gmap atom value)).
    rewrite storeA_restrict_dom.
    set_solver.
  }
  pose proof (storeA_restrict_eq_mono σn σm O
    (dom (σn : StoreT) ∩ dom (σm : StoreT))
    HOsub Hoverlap) as Hnm.
  pose proof (store_singleton_projection_restrict σ m
    (dom (σ : StoreT) ∩ X) ltac:(set_solver) Hproj) as HmX.
  assert (HσmX : storeA_restrict σm (dom (σ : StoreT) ∩ X) =
                 storeA_restrict σ (dom (σ : StoreT) ∩ X)).
  {
    assert (Hraw :
      (res_restrict m (dom (σ : StoreT) ∩ X) : WorldT)
        (storeA_restrict σm (dom (σ : StoreT) ∩ X))).
    { exists σm. split; [exact Hσm|reflexivity]. }
    rewrite HmX in Hraw. simpl in Hraw. exact Hraw.
  }
  transitivity (storeA_restrict σm O).
  - exact Hnm.
  - subst O.
    change (dom (store_restrict σ X : StoreT)) with
      (dom (store_restrict σ X : gmap atom value)).
    rewrite storeA_restrict_dom.
    pose proof (storeA_restrict_eq_mono σm σ
      (dom (σn : StoreT) ∩ (dom (σ : StoreT) ∩ X))
      (dom (σ : StoreT) ∩ X)
      ltac:(set_solver) HσmX) as HmO.
    transitivity (storeA_restrict σ
      (dom (σn : StoreT) ∩ (dom (σ : StoreT) ∩ X))).
    + exact HmO.
    + rewrite storeA_restrict_restrict.
      replace (X ∩ (dom (σn : StoreT) ∩ (dom (σ : StoreT) ∩ X)))
        with (dom (σn : StoreT) ∩ (dom (σ : StoreT) ∩ X)) by set_solver.
      reflexivity.
Qed.

Lemma world_compat_product_singleton_restrict_from_projection
    (σ : StoreT) (m n : WfWorldT) X
    (Hcfix : world_compat n (singleton_world (store_restrict σ X))) :
  world_compat n m ->
  store_singleton_projection σ m ->
  world_compat
    (res_product n
      (exist _ (singleton_world (store_restrict σ X))
        (wf_singleton_world (store_restrict σ X))) Hcfix) m.
Proof.
  intros Hc Hproj σp σm Hσp Hσm.
  cbn [res_product raw_product raw_world world_stores] in Hσp.
  destruct Hσp as [σn [σfix [Hσn [Hσfix [Hnfix ->]]]]].
  change (σfix = store_restrict σ X) in Hσfix.
  subst σfix.
  apply storeA_compat_union_intro_l.
  - exact (Hc σn σm Hσn Hσm).
  - apply (proj2 (storeA_compat_spec (store_restrict σ X) σm)).
    pose proof (wfworld_store_dom m σm Hσm) as Hdomm.
    pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
      as Hdomσm.
    set (O := dom (store_restrict σ X : StoreT) ∩ dom (σm : StoreT)).
    pose proof (store_singleton_projection_restrict σ m
      (dom (σ : StoreT) ∩ X) ltac:(set_solver) Hproj) as HmX.
    assert (HσmX : storeA_restrict σm (dom (σ : StoreT) ∩ X) =
                   storeA_restrict σ (dom (σ : StoreT) ∩ X)).
    {
      assert (Hraw :
        (res_restrict m (dom (σ : StoreT) ∩ X) : WorldT)
          (storeA_restrict σm (dom (σ : StoreT) ∩ X))).
      { exists σm. split; [exact Hσm|reflexivity]. }
      rewrite HmX in Hraw. simpl in Hraw. exact Hraw.
    }
    subst O.
    change (dom (store_restrict σ X : StoreT)) with
      (dom (store_restrict σ X : gmap atom value)).
    rewrite storeA_restrict_dom.
    pose proof (storeA_restrict_eq_mono σ σm
      (dom (σ : StoreT) ∩ X ∩ dom (σm : StoreT))
      (dom (σ : StoreT) ∩ X)
      ltac:(set_solver) (eq_sym HσmX)) as HσO.
    transitivity (storeA_restrict σ
      (dom (σ : StoreT) ∩ X ∩ dom (σm : StoreT))).
    + rewrite storeA_restrict_restrict.
      replace (X ∩ (dom (σ : StoreT) ∩ X ∩ dom (σm : StoreT)))
        with (dom (σ : StoreT) ∩ X ∩ dom (σm : StoreT)) by set_solver.
      reflexivity.
    + exact HσO.
Qed.

Lemma store_singleton_projection_product_singleton_frame
    (σ : StoreT) (n : WfWorldT) X Y
    (Hcfix : world_compat n (singleton_world (store_restrict σ X))) :
  Y ⊆ X ->
  store_singleton_projection (store_restrict σ Y)
    (res_product n
      (exist _ (singleton_world (store_restrict σ X))
        (wf_singleton_world (store_restrict σ X))) Hcfix).
Proof.
  intros HYX.
  unfold store_singleton_projection.
  change (dom (store_restrict σ Y : StoreT)) with
    (dom (store_restrict σ Y : gmap atom value)).
  rewrite storeA_restrict_dom.
  eapply res_restrict_to_singleton_if_projection_constant.
  intros σp Hσp.
  cbn [res_product raw_product raw_world world_stores] in Hσp.
  destruct Hσp as [σn [σfix [Hσn [Hσfix [Hcompat ->]]]]].
  change (σfix = store_restrict σ X) in Hσfix.
  subst σfix.
  rewrite (storeA_restrict_union_absorb_r σn (store_restrict σ X)
    (dom (σ : StoreT) ∩ Y)).
  - apply storeA_map_eq. intros z.
    rewrite !storeA_restrict_lookup.
    destruct (decide (z ∈ Y)) as [HzY|HzY].
    + destruct ((σ : StoreT) !! z) as [v|] eqn:Hzσ.
      * assert (Hzdom : z ∈ dom (σ : gmap atom value)).
        { apply elem_of_dom. exists v. exact Hzσ. }
        rewrite !decide_True by set_solver. reflexivity.
      * assert (Hzσnone : (σ : gmap atom value) !! z = None) by exact Hzσ.
        rewrite decide_False by
          (intros Hz; apply elem_of_intersection in Hz as [Hzdom _];
           change (z ∈ dom (σ : gmap atom value)) in Hzdom;
           apply elem_of_dom in Hzdom as [v Hv]; rewrite Hzσnone in Hv; discriminate).
        change (None = (σ : gmap atom value) !! z).
        symmetry. exact Hzσnone.
    + rewrite !decide_False by set_solver. reflexivity.
  - exact Hcompat.
  - change (dom (store_restrict σ X : StoreT)) with
      (dom (store_restrict σ X : gmap atom value)).
    rewrite storeA_restrict_dom. set_solver.
Qed.

Lemma store_singleton_projection_product_restrict_of_scope
    (σ : StoreT) (m n : WfWorldT) (Hc : world_compat n m) (φ : FormulaT) :
  store_singleton_projection σ m ->
  formula_scoped_in_world (res_product n m Hc) φ ->
  store_singleton_projection
    (store_restrict σ (formula_fv φ)) (res_product n m Hc).
Proof.
  intros Hproj Hscope.
  unfold store_singleton_projection.
  change (dom (store_restrict σ (formula_fv φ) : StoreT)) with
    (dom (store_restrict σ (formula_fv φ) : gmap atom value)).
  rewrite storeA_restrict_dom.
  eapply res_restrict_to_singleton_if_projection_constant.
  intros σp Hσp.
  cbn [res_product raw_world world_stores world_dom] in Hσp.
  destruct Hσp as [σn [σm [Hσn [Hσm [Hcompat ->]]]]].
  pose proof (wfworld_store_dom m σm Hσm) as Hdomm.
  pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
    as Hdomσm.
  assert (Hsub_m :
    dom (σ : StoreT) ∩ formula_fv φ ⊆ dom (σm : StoreT)).
  {
    intros z Hz.
    apply elem_of_intersection in Hz as [Hzσ _].
    assert (HzM : z ∈ world_dom (m : WorldT)) by set_solver.
    rewrite <- Hdomm in HzM. exact HzM.
  }
  assert (HσmX : storeA_restrict σm (dom (σ : StoreT) ∩ formula_fv φ) =
                 storeA_restrict σ (dom (σ : StoreT) ∩ formula_fv φ)).
  {
    pose proof (store_singleton_projection_restrict σ m
      (dom (σ : StoreT) ∩ formula_fv φ) ltac:(set_solver) Hproj)
      as HmX.
    assert (Hraw :
      (res_restrict m (dom (σ : StoreT) ∩ formula_fv φ) : WorldT)
        (storeA_restrict σm (dom (σ : StoreT) ∩ formula_fv φ))).
    { exists σm. split; [exact Hσm|reflexivity]. }
    rewrite HmX in Hraw. simpl in Hraw. exact Hraw.
  }
  rewrite (storeA_restrict_union_absorb_r σn σm
    (dom (σ : StoreT) ∩ formula_fv φ)); [|exact Hcompat|exact Hsub_m].
  rewrite HσmX.
  apply storeA_map_eq. intros z.
  rewrite !storeA_restrict_lookup.
  destruct (decide (z ∈ formula_fv φ)) as [Hzφ|Hzφ].
  - destruct ((σ : StoreT) !! z) as [v|] eqn:Hzσ.
    + assert (Hzdom : z ∈ dom (σ : gmap atom value)).
      { apply elem_of_dom. exists v. exact Hzσ. }
      rewrite !decide_True by set_solver. reflexivity.
    + assert (Hzσnone : (σ : gmap atom value) !! z = None) by exact Hzσ.
      rewrite decide_False by
        (intros Hz; apply elem_of_intersection in Hz as [Hzdom _];
         change (z ∈ dom (σ : gmap atom value)) in Hzdom;
         apply elem_of_dom in Hzdom as [v Hv]; rewrite Hzσnone in Hv; discriminate).
      change (None = (σ : gmap atom value) !! z).
      symmetry. exact Hzσnone.
	  - rewrite !decide_False by set_solver. reflexivity.
Qed.

Lemma store_singleton_projection_forall_restrict_of_scope
    (σ : StoreT) (m my : WfWorldT) y (φ : FormulaT) :
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ dom (σ : StoreT) ->
  store_singleton_projection σ m ->
  formula_scoped_in_world my φ ->
  store_singleton_projection (store_restrict σ (formula_fv φ)) my.
Proof.
  intros Hdom Hrestrict Hy Hproj Hscope.
  unfold store_singleton_projection.
  change (dom (store_restrict σ (formula_fv φ) : StoreT)) with
    (dom (store_restrict σ (formula_fv φ) : gmap atom value)).
  rewrite storeA_restrict_dom.
  eapply res_restrict_to_singleton_if_projection_constant.
  intros σmy Hσmy.
  set (X := dom (σ : StoreT) ∩ formula_fv φ).
  assert (HXm : X ⊆ world_dom (m : WorldT)).
  {
    subst X.
    pose proof (store_singleton_projection_dom_subset_world σ m Hproj)
      as Hσm.
    set_solver.
  }
  assert (Hmy_to_m :
    (m : WorldT) (store_restrict σmy (world_dom (m : WorldT)))).
  {
    assert (Hraw :
      (res_restrict my (world_dom (m : WorldT)) : WorldT)
        (store_restrict σmy (world_dom (m : WorldT)))).
    { exists σmy. split; [exact Hσmy|reflexivity]. }
    rewrite Hrestrict in Hraw. exact Hraw.
  }
  pose proof (store_singleton_projection_restrict σ m X ltac:(set_solver) Hproj)
    as HmX.
  assert (HrawX :
    (res_restrict m X : WorldT) (store_restrict σmy X)).
  {
    exists (store_restrict σmy (world_dom (m : WorldT))).
    split; [exact Hmy_to_m|].
    unfold X.
    rewrite storeA_restrict_restrict.
    replace (world_dom (m : WorldT) ∩ (dom (σ : StoreT) ∩ formula_fv φ))
      with (dom (σ : StoreT) ∩ formula_fv φ) by set_solver.
    reflexivity.
  }
  rewrite HmX in HrawX. simpl in HrawX.
  transitivity (store_restrict σ X).
  - exact HrawX.
  - subst X. apply storeA_map_eq. intros z.
    rewrite !storeA_restrict_lookup.
    destruct (decide (z ∈ formula_fv φ)) as [Hzφ|Hzφ].
    + destruct ((σ : StoreT) !! z) as [v|] eqn:Hzσ.
      * assert (Hzdom : z ∈ dom (σ : gmap atom value)).
        { apply elem_of_dom. exists v. exact Hzσ. }
        rewrite !decide_True by set_solver. reflexivity.
      * assert (Hzσnone : (σ : gmap atom value) !! z = None) by exact Hzσ.
        rewrite decide_False by
          (intros Hz; apply elem_of_intersection in Hz as [Hzdom _];
           change (z ∈ dom (σ : gmap atom value)) in Hzdom;
           apply elem_of_dom in Hzdom as [v Hv]; rewrite Hzσnone in Hv; discriminate).
        change (None = (σ : gmap atom value) !! z).
        symmetry. exact Hzσnone.
    + rewrite !decide_False by set_solver. reflexivity.
Qed.

Lemma store_singleton_projection_sum_le_l
    (σ : StoreT) (m m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2) X :
  res_sum m1 m2 Hdef ⊑ m ->
  X ⊆ dom (σ : StoreT) ->
  X ⊆ world_dom (m1 : WorldT) ->
  X ⊆ world_dom (m2 : WorldT) ->
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) m1.
Proof.
  intros Hle HX Hm1X Hm2X Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  replace (dom (σ : StoreT) ∩ X) with X by set_solver.
  destruct (res_sum_le_singleton_restrict_inv
    m m1 m2 Hdef X (store_restrict σ X) Hle Hm1X Hm2X) as [H1 _].
  - eapply store_singleton_projection_restrict; eauto.
  - exact H1.
Qed.

Lemma store_singleton_projection_sum_le_r
    (σ : StoreT) (m m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2) X :
  res_sum m1 m2 Hdef ⊑ m ->
  X ⊆ dom (σ : StoreT) ->
  X ⊆ world_dom (m1 : WorldT) ->
  X ⊆ world_dom (m2 : WorldT) ->
  store_singleton_projection σ m ->
  store_singleton_projection (store_restrict σ X) m2.
Proof.
  intros Hle HX Hm1X Hm2X Hproj.
  unfold store_singleton_projection.
  change (dom (store_restrict σ X : StoreT)) with
    (dom (store_restrict σ X : gmap atom value)).
  rewrite storeA_restrict_dom.
  replace (dom (σ : StoreT) ∩ X) with X by set_solver.
  destruct (res_sum_le_singleton_restrict_inv
    m m1 m2 Hdef X (store_restrict σ X) Hle Hm1X Hm2X) as [_ H2].
  - eapply store_singleton_projection_restrict; eauto.
  - exact H2.
Qed.

Lemma base_store_projection_restrict_overlap
    (Σbase : gmap atom ty) (σ : StoreT) (m : WfWorldT) X :
  base_store_projection Σbase σ m ->
  (res_restrict m (X ∩ dom Σbase) : WorldT) =
    singleton_world (store_restrict σ (X ∩ dom Σbase)).
Proof.
  intros Hproj.
  eapply base_store_projection_restrict; [|exact Hproj].
  intros x Hx. apply elem_of_intersection in Hx as [_ Hx]. exact Hx.
Qed.

Lemma base_store_projection_dom_subset_world
    (Σbase : gmap atom ty) (σ : StoreT) (m : WfWorldT) :
  base_store_projection Σbase σ m ->
  dom (σ : StoreT) ⊆ world_dom (m : WorldT).
Proof.
  intros [Hdom Hsingle] x Hx.
  pose proof (f_equal world_dom Hsingle) as Hworld.
  simpl in Hworld.
  rewrite <- Hdom in Hworld.
  set_solver.
Qed.

Lemma base_store_projection_atom_store_has_ltype
    (Σbase : gmap atom ty) (σ : StoreT) (m : WfWorldT) :
  storeA_has_type Σbase σ ->
  base_store_projection Σbase σ m ->
  atom_store_has_ltype (atom_env_to_lty_env Σbase) σ.
Proof.
  intros Hty [Hdom _].
  eapply storeA_has_type_atom_store_has_ltype; eauto.
Qed.

Lemma base_store_projection_atom_store_has_ltype_under
    (Σbase Δ : gmap atom ty) (σ : StoreT) (m : WfWorldT) :
  wf_erased_ctx_under Σbase Δ ->
  storeA_has_type Σbase σ ->
  base_store_projection Σbase σ m ->
  atom_store_has_ltype (atom_env_to_lty_env Δ) σ.
Proof.
  intros Henv Hty Hproj x v Hσx.
  destruct Hproj as [Hdom _].
  assert (HxΣ : x ∈ dom Σbase).
  {
    rewrite <- Hdom.
    change (x ∈ dom (σ : gmap atom value)).
    rewrite elem_of_dom. eauto.
  }
  apply elem_of_dom in HxΣ as [T HΣx].
  exists T. split.
  - rewrite atom_store_to_lvar_store_lookup_free.
    eapply Henv. exact HΣx.
  - exact (Hty x T v HΣx Hσx).
Qed.

Definition denot_msubst_induction_hyp (gas : nat) : Prop :=
  forall σ0 Σ0 τ0 e0 (m0 : WfWorldT),
    denot_relevant_lvars τ0 e0 ⊆ dom Σ0 ->
    atom_store_has_ltype Σ0 σ0 ->
    m0 ⊨ formula_msubst_store σ0 (denot_ty_lvar_gas gas Σ0 τ0 e0) <->
    m0 ⊨ denot_ty_lvar_gas gas
      (lty_env_msubst_store σ0 Σ0)
      (context_ty_msubst_store σ0 τ0)
      (lstore_instantiate_tm (lstore_lift_free σ0) e0).

Definition denot_msubst_local_induction_hyp (gas : nat) : Prop :=
  forall σ Σ τ e (m : WfWorldT),
    basic_context_ty_lvars (dom Σ) τ ->
    tm_lvars e ⊆ dom Σ ->
    lc_tm e ->
    atom_store_has_ltype Σ σ ->
    store_singleton_projection σ m ->
    m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e) <->
    m ⊨ denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e).

Definition denot_msubst_local_scoped_induction_hyp (gas : nat) : Prop :=
  forall σ Σ τ e (m : WfWorldT),
    dom (σ : StoreT) ⊆ formula_fv (denot_ty_lvar_gas gas Σ τ e) ->
    basic_context_ty_lvars (dom Σ) τ ->
    tm_lvars e ⊆ dom Σ ->
    lc_tm e ->
    atom_store_has_ltype Σ σ ->
    store_singleton_projection σ m ->
    formula_scoped_in_world m
      (formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e)) ->
    formula_scoped_in_world m
      (denot_ty_lvar_gas gas Σ τ
        (lstore_instantiate_tm (lstore_lift_free σ) e)) ->
    m ⊨ formula_msubst_store σ (denot_ty_lvar_gas gas Σ τ e) <->
    m ⊨ denot_ty_lvar_gas gas Σ τ
      (lstore_instantiate_tm (lstore_lift_free σ) e).

Lemma formula_open_denot_ty_lvar_gas_singleton
    k y gas Σ τ e :
  y ∉ lvars_fv (dom Σ) ->
  y ∉ fv_tm e ->
  y ∉ fv_cty τ ->
  formula_open k y (denot_ty_lvar_gas gas Σ τ e) =
  denot_ty_lvar_gas gas
    (lty_env_open_one k y Σ)
    (cty_open k y τ)
    (open_tm k (vfvar y) e).
Proof.
  intros HΣ He Hτ.
  assert (HΣfree : LVFree y ∉ dom Σ).
  {
    intros Hbad. apply HΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hfresh :
    open_env_fresh_for_lvars (<[k := y]> ∅)
      (dom Σ ∪ denot_relevant_lvars τ e)).
  {
    apply open_env_fresh_for_lvars_singleton.
    rewrite lvars_fv_union.
    unfold denot_relevant_lvars.
    rewrite lvars_fv_union, context_ty_lvars_fv, tm_lvars_fv.
    set_solver.
  }
  pose proof (formula_open_env_denot_ty_lvar_gas
    (<[k := y]> ∅) gas Σ τ e Hfresh
    (open_env_values_inj_singleton k y)) as Heq.
  rewrite formula_open_env_singleton in Heq.
  rewrite lty_env_open_lvars_singleton in Heq by exact HΣfree.
  rewrite open_cty_env_singleton in Heq.
  rewrite open_tm_env_singleton in Heq.
  exact Heq.
Qed.

Lemma atom_store_has_ltype_denot_relevant_env Σ σ τ e :
  lvars_of_atoms (dom (σ : gmap atom value)) ⊆ denot_relevant_lvars τ e ->
  atom_store_has_ltype Σ σ ->
  atom_store_has_ltype (denot_relevant_env Σ τ e) σ.
Proof.
  intros Hrel Hty.
  unfold denot_relevant_env, lty_env_restrict_lvars.
  apply atom_store_has_ltype_restrict_lvars; assumption.
Qed.

Lemma atom_store_has_ltype_restrict_store Σ σ X :
  atom_store_has_ltype Σ σ ->
  atom_store_has_ltype Σ (store_restrict σ X).
Proof.
  intros Hty x v Hlook.
  apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
  exact (Hty x v Hlook).
Qed.
End ContextTypeDenotationMsubst.
