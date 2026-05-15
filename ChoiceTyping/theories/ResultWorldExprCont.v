(** * ChoiceTyping.ResultWorldExprCont

    Bridges from LN expression-result continuations to the concrete result
    world used by the [tlet] proof. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  BasicTypingProps LocallyNamelessProps.
From ChoiceTyping Require Import SoundnessCommon LetResultWorld ResultWorldClosed.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma store_eq_insert_of_restrict_singleton
    X (σx σ : Store) ν vx :
  dom σx = X ∪ {[ν]} →
  ν ∉ X →
  store_restrict σx X = σ →
  store_restrict σx {[ν]} = {[ν := vx]} →
  σx = <[ν := vx]> σ.
Proof.
  intros Hdom HνX HσX Hσν.
  assert (Hdomσ : dom σ ⊆ X).
  {
    rewrite <- HσX, store_restrict_dom. set_solver.
  }
  transitivity (store_restrict σx (X ∪ {[ν]})).
  - symmetry. apply store_restrict_idemp_eq. exact Hdom.
  - rewrite (store_restrict_union_from_parts σx σ ({[ν := vx]}) X ν);
      try assumption.
    change ({[ν := vx]} : Store) with (<[ν := vx]> (∅ : Store)).
    rewrite store_insert_union_r_fresh by set_solver.
    rewrite (map_union_empty σ). reflexivity.
Qed.

Local Lemma inter_self (X : aset) :
  X ∩ X = X.
Proof.
  set_solver.
Qed.

Local Lemma inter_union_singleton_l (X : aset) (ν : atom) :
  (X ∪ {[ν]}) ∩ X = X.
Proof.
  set_solver.
Qed.

Local Lemma inter_union_singleton_r_fresh (X : aset) (ν : atom) :
  ν ∉ X →
  (X ∪ {[ν]}) ∩ ({[ν]} : aset) = {[ν]}.
Proof.
  set_solver.
Qed.

Lemma FExprResultAt_fiber_expr_result_in_world
    X e ν (n : WfWorld) σX Hproj :
  lc_tm e →
  world_dom (n : World) = X ∪ {[ν]} →
  n ⊨ FExprResultAt X e ν →
  expr_result_in_world (store_restrict σX X) e ν
    (res_fiber_from_projection n X σX Hproj).
Proof.
  intros Hlc Hdom Hmodel.
  unfold FExprResultAt, FExprResultOn in Hmodel.
  cbn [formula_open] in Hmodel.
  rewrite lvars_open_of_atoms in Hmodel.
  destruct (FFibVars_models_elim _ _ _ _ Hmodel) as [_ Hfib].
  rewrite lvars_fv_of_atoms in Hfib.
  specialize (Hfib σX Hproj).
  unfold res_models_with_store, FStoreResourceAtom in Hfib.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv formula_open lqual_dom logic_qualifier_denote lqual_prop
    lqual_open stale stale_logic_qualifier into_lvars into_lvars_aset
    into_lvars_lvset] in Hfib.
  denot_lvars_norm.
  rewrite lvars_fv_open_atoms_with_bound in Hfib.
  rewrite lookup_insert_eq in Hfib.
  rewrite map_empty_union in Hfib.
  destruct Hfib as [_ [m0 [Hscope [Hresult Hle]]]].
  assert (Hm0_eq :
    m0 = res_fiber_from_projection n X σX Hproj).
  {
    apply res_le_same_dom_eq; [exact Hle |].
    unfold formula_scoped_in_world in Hscope.
    cbn [formula_fv stale stale_logic_qualifier lqual_dom] in Hscope.
    denot_lvars_norm.
    rewrite lvars_fv_open_atoms_with_bound in Hscope.
    pose proof (raw_le_dom m0
      (res_fiber_from_projection n X σX Hproj) Hle) as Hle_dom.
    simpl in *.
    set_solver.
  }
  subst m0.
  rewrite open_tm_env_singleton_lc in Hresult by exact Hlc.
  rewrite lvars_fv_of_atoms in Hresult.
  rewrite map_empty_union in Hresult.
  store_norm.
  rewrite (inter_union_singleton_l X ν) in Hresult.
  replace (X ∪ {[ν]})
    with (world_dom (res_fiber_from_projection n X σX Hproj : World))
    in Hresult by (simpl; exact Hdom).
  rewrite res_restrict_self in Hresult.
  exact Hresult.
Qed.

Lemma FExprResultAt_unique_let_result_world
    (Σ : gmap atom ty) (T : ty) e ν (m n : WfWorld)
    (Hfresh : ν ∉ world_dom (m : World))
    (Hresult : ∀ σ, (m : World) σ →
      ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  world_dom (n : World) = dom Σ ∪ {[ν]} →
  res_restrict n (dom Σ) = m →
  n ⊨ FExprResultAt (dom Σ) e ν →
  n = let_result_world_on e ν m Hfresh Hresult.
Proof.
  intros Hty Hdom_m Hclosed Hdom_n Hrestrict Hmodel.
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as Hfv.
  pose proof (typing_tm_lc Σ e T Hty) as Hlc.
  assert (HνΣ : ν ∉ dom Σ) by (rewrite <- Hdom_m; exact Hfresh).
  apply wfworld_ext. apply world_ext.
  - rewrite Hdom_n, let_result_world_on_dom, Hdom_m. reflexivity.
  - intros σν. split.
    + intros Hσν_n.
      set (σ := store_restrict σν (dom Σ)).
      assert (Hproj : (res_restrict n (dom Σ) : World) σ).
      { exists σν. split; [exact Hσν_n | reflexivity]. }
      assert (Hσm : (m : World) σ).
      { rewrite <- Hrestrict. exact Hproj. }
      pose proof (FExprResultAt_fiber_expr_result_in_world
        (dom Σ) e ν n σ Hproj Hlc Hdom_n Hmodel) as Hexpr.
      assert (Hfiber :
        (res_fiber_from_projection n (dom Σ) σ Hproj : World) σν).
      { apply res_fiber_from_projection_member; [exact Hσν_n | reflexivity]. }
      assert (Hνproj :
        (res_restrict (res_fiber_from_projection n (dom Σ) σ Hproj) {[ν]} : World)
          (store_restrict σν {[ν]})).
      { exists σν. split; [exact Hfiber | reflexivity]. }
      pose proof (expr_result_in_world_sound
        (store_restrict σ (dom Σ)) e ν
        (res_fiber_from_projection n (dom Σ) σ Hproj)
        (store_restrict σν {[ν]}) Hexpr Hνproj) as Hstore.
      destruct (expr_result_store_elim ν
        (subst_map (store_restrict σ (dom Σ)) e)
        (store_restrict σν {[ν]}) Hstore)
        as [vx [Hσν_single [_ [_ HstepsX]]]].
      assert (Hsteps_fv :
        subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
      {
        rewrite (subst_map_restrict_to_fv_from_superset e
          (dom Σ) σ Hfv (proj1 (Hclosed σ Hσm))).
        exact HstepsX.
      }
      assert (Hσν_dom : dom σν = dom Σ ∪ {[ν]}).
      { rewrite (wfworld_store_dom n σν Hσν_n). exact Hdom_n. }
      rewrite (store_eq_insert_of_restrict_singleton
        (dom Σ) σν σ ν vx Hσν_dom HνΣ ltac:(reflexivity) Hσν_single).
      apply let_result_world_on_member; eauto.
    + intros Hσν_let.
      destruct (let_result_world_on_elim e ν m Hfresh Hresult σν Hσν_let)
        as [σ [vx [Hσm [Hsteps_fv ->]]]].
      assert (Hproj : (res_restrict n (dom Σ) : World) σ).
      { rewrite Hrestrict. exact Hσm. }
      destruct Hproj as [σn [Hσn HσnX]].
      assert (Hproj' : (res_restrict n (dom Σ) : World) σ).
      { exists σn. split; [exact Hσn | exact HσnX]. }
      pose proof (FExprResultAt_fiber_expr_result_in_world
        (dom Σ) e ν n σ Hproj' Hlc Hdom_n Hmodel) as Hexpr.
      assert (Hfiber :
        (res_fiber_from_projection n (dom Σ) σ Hproj' : World) σn).
      { apply res_fiber_from_projection_member; [exact Hσn | exact HσnX]. }
      assert (Hνproj :
        (res_restrict (res_fiber_from_projection n (dom Σ) σ Hproj') {[ν]} : World)
          (store_restrict σn {[ν]})).
      { exists σn. split; [exact Hfiber | reflexivity]. }
      pose proof (expr_result_in_world_sound
        (store_restrict σ (dom Σ)) e ν
        (res_fiber_from_projection n (dom Σ) σ Hproj')
        (store_restrict σn {[ν]}) Hexpr Hνproj) as Hstore.
      destruct (expr_result_store_elim ν
        (subst_map (store_restrict σ (dom Σ)) e)
        (store_restrict σn {[ν]}) Hstore)
        as [vy [Hσn_single [_ [_ HstepsX]]]].
      assert (HstepsX_vx :
        subst_map (store_restrict σ (dom Σ)) e →* tret vx).
      {
        rewrite <- (subst_map_restrict_to_fv_from_superset e
          (dom Σ) σ Hfv (proj1 (Hclosed σ Hσm))).
        exact Hsteps_fv.
      }
      assert (vy = vx) by (eapply steps_result_unique; eauto).
      subst vy.
      assert (Hσn_dom : dom σn = dom Σ ∪ {[ν]}).
      { rewrite (wfworld_store_dom n σn Hσn). exact Hdom_n. }
      rewrite <- (store_eq_insert_of_restrict_singleton
        (dom Σ) σn σ ν vx Hσn_dom HνΣ HσnX Hσn_single).
      exact Hσn.
Qed.

Lemma set_difference_pull_singleton (X Y : aset) x :
  x ∈ X →
  x ∉ Y →
  X ∖ Y = (X ∖ ({[x]} ∪ Y)) ∪ {[x]}.
Proof.
  intros HxX HxY.
  apply set_eq. intros z.
  rewrite elem_of_difference, elem_of_union, elem_of_difference,
    elem_of_union, !elem_of_singleton.
  split.
  - intros [HzX HzY].
    destruct (decide (z = x)) as [->|Hzx].
    + right. reflexivity.
    + left. split; [exact HzX |].
      intros [Hzx'|HzY']; [congruence | contradiction].
  - intros [[HzX Hnot] | Hzx].
    + split; [exact HzX |].
      intros HzY. apply Hnot. right. exact HzY.
    + subst z. split; [exact HxX | exact HxY].
Qed.

Lemma let_result_world_on_fiber_expr_result_in_world
    X e ν (n : WfWorld) Hfresh Hresult σX Hproj :
  fv_tm e ⊆ X →
  lc_tm e →
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  world_closed_on X n →
  expr_result_in_world (store_restrict σX X) e ν
    (res_fiber_from_projection
      (let_result_world_on e ν n Hfresh Hresult) X σX Hproj).
Proof.
  intros Hfv Hlc HνX HX Hclosed.
  assert (HdomσX : dom σX = X).
  {
    pose proof (wfworld_store_dom
      (res_restrict (let_result_world_on e ν n Hfresh Hresult) X)
      σX Hproj) as Hdom.
    simpl in Hdom. set_solver.
  }
  intros σν. split.
  - intros Hσν.
    destruct Hσν as [σall [Hσfiber Hσν_eq]].
    destruct Hσfiber as [Hσlet HσX].
    destruct (let_result_world_on_elim e ν n Hfresh Hresult σall Hσlet)
      as [σ [vx [Hσn [Hsteps ->]]]].
    assert (HσX_base : store_restrict σ X = σX).
    {
      replace (dom σX) with X in HσX by (symmetry; exact HdomσX).
      rewrite <- HσX.
      rewrite store_restrict_insert_notin.
      - reflexivity.
      - exact HνX.
    }
    assert (HstepsX :
      subst_map (store_restrict σX X) e →* tret vx).
    {
      assert (HσX_id : store_restrict σX X = store_restrict σ X).
	    {
	      rewrite <- HσX_base.
	      rewrite store_restrict_twice_same.
	      reflexivity.
	    }
      rewrite HσX_id.
      rewrite <- (subst_map_restrict_to_fv_from_superset e X σ).
      - exact Hsteps.
      - exact Hfv.
      - exact (proj1 (Hclosed σ Hσn)).
    }
    assert (Hσν_single : σν = {[ν := vx]}).
    {
      rewrite <- Hσν_eq.
      rewrite store_restrict_insert_singleton.
      reflexivity.
    }
    pose proof (steps_closed_result_of_restrict_world X e n σX vx
      HX Hfv Hlc Hclosed ltac:(exists σ; split; [exact Hσn | exact HσX_base])
      HstepsX) as [Hv_stale Hv_lc].
    exists vx. repeat split; eauto.
  - intros Hstore.
    destruct (expr_result_store_elim ν
      (subst_map (store_restrict σX X) e) σν Hstore)
      as [vx [-> [Hv_closed [Hv_lc HstepsX]]]].
    destruct Hproj as [σall [Hσlet HσX]].
    destruct (let_result_world_on_elim e ν n Hfresh Hresult σall Hσlet)
      as [σ [vy [Hσn [_ ->]]]].
    assert (HσX_base : store_restrict σ X = σX).
    {
      replace (dom σX) with X in HσX by (symmetry; exact HdomσX).
      rewrite <- HσX.
      rewrite store_restrict_insert_notin.
      - reflexivity.
      - exact HνX.
    }
    assert (Hsteps_fv :
      subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
    {
      rewrite (subst_map_restrict_to_fv_from_superset e X σ Hfv
        (proj1 (Hclosed σ Hσn))).
      rewrite HσX_base.
      rewrite (store_restrict_idemp_eq σX X HdomσX) in HstepsX.
      exact HstepsX.
    }
    exists (<[ν := vx]> σ). split.
    + split.
      * apply let_result_world_on_member; [exact Hσn | exact Hsteps_fv].
      * replace (dom σX) with X by (symmetry; exact HdomσX).
        rewrite store_restrict_insert_notin by exact HνX.
        exact HσX_base.
    + rewrite store_restrict_insert_singleton.
      reflexivity.
Qed.

Lemma FExprResultAt_scoped_let_result_world X e ν (n : WfWorld) Hfresh Hresult :
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  formula_scoped_in_world ∅
    (let_result_world_on e ν n Hfresh Hresult)
    (FExprResultAt X e ν).
Proof.
  intros HνX HX.
  unfold formula_scoped_in_world.
  rewrite dom_empty_L.
  rewrite FExprResultAt_fv.
  rewrite let_result_world_on_dom.
  set_solver.
Qed.

Lemma FExprResultAt_body_scoped_in_fiber
    X e ν (n : WfWorld) Hfresh Hresult σX Hproj :
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  formula_scoped_in_world σX
    (res_fiber_from_projection
      (let_result_world_on e ν n Hfresh Hresult) X σX Hproj)
    (FStoreResourceAtom (lvars_of_atoms X ∪ {[LVBound 0]})
      (fun η σ w =>
        match η !! 0 with
        | Some ν => expr_result_in_world (store_restrict σ X) e ν w
        | None => False
        end)).
Proof.
  intros HνX HX.
  unfold formula_scoped_in_world.
  unfold FStoreResourceAtom.
  cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
    into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound.
  pose proof (wfworld_store_dom
    (res_restrict (let_result_world_on e ν n Hfresh Hresult) X)
    σX Hproj) as HdomσX.
  simpl in HdomσX.
  simpl.
  set_solver.
Qed.

Lemma FExprResultAt_body_opened_scoped_in_fiber
    X e ν (n : WfWorld) Hfresh Hresult σX Hproj :
  ν ∉ X →
  X ⊆ world_dom (n : World) →
  formula_scoped_in_world σX
    (res_fiber_from_projection
      (let_result_world_on e ν n Hfresh Hresult) X σX Hproj)
    (formula_open 0 ν
      (FStoreResourceAtom (lvars_of_atoms X ∪ {[LVBound 0]})
        (fun η σ w =>
          match η !! 0 with
          | Some ν => expr_result_in_world (store_restrict σ X) e ν w
          | None => False
          end))).
Proof.
  intros HνX HX.
  unfold formula_scoped_in_world, FStoreResourceAtom.
  cbn [formula_open formula_fv stale stale_logic_qualifier lqual_dom
    lqual_open into_lvars into_lvars_lvset].
  denot_lvars_norm.
  rewrite lvars_fv_open_atoms_with_bound.
  pose proof (wfworld_store_dom
    (res_restrict (let_result_world_on e ν n Hfresh Hresult) X)
    σX Hproj) as HdomσX.
  simpl in HdomσX.
  simpl.
  set_solver.
Qed.

Lemma let_result_world_on_models_FExprResultAt :
  ∀ X e ν (n : WfWorld) Hfresh Hresult,
    fv_tm e ⊆ X →
    lc_tm e →
    ν ∉ X →
    X ⊆ world_dom (n : World) →
    world_closed_on X n →
    let_result_world_on e ν n Hfresh Hresult ⊨ FExprResultAt X e ν.
Proof.
  intros X e ν n Hfresh Hresult Hfv Hlc HνX HX Hclosed.
  unfold FExprResultAt, FExprResultOn.
  cbn [formula_open].
  rewrite lvars_open_of_atoms.
  apply FFibVars_models_intro.
  - unfold formula_scoped_in_world.
    rewrite dom_empty_L.
    assert (Hopen_fv :
      formula_fv
        (formula_open 0 ν
          (FStoreResourceAtom (into_lvars X ∪ {[LVBound 0]})
            (fun η σ w =>
              match η !! 0 with
              | Some ν =>
                  expr_result_in_world
                    (store_restrict σ (lvars_fv (into_lvars X)))
                    (open_tm_env η e) ν w
              | None => False
              end))) ⊆ X ∪ {[ν]}).
    {
      apply formula_open_fv_subset_env.
      unfold FStoreResourceAtom.
      cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
        into_lvars_aset into_lvars_lvset].
      denot_lvars_norm.
      rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound.
      set_solver.
    }
    cbn [formula_fv].
    rewrite lvars_fv_of_atoms.
    rewrite let_result_world_on_dom.
    set_solver.
  - unfold FFibVars_obligation.
    rewrite lvars_fv_of_atoms.
    split; [set_solver |].
    intros σX Hproj.
    unfold res_models_with_store.
    unfold FStoreResourceAtom.
    cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
      formula_fv formula_open lqual_dom logic_qualifier_denote lqual_prop
      lqual_open stale stale_logic_qualifier into_lvars into_lvars_aset
      into_lvars_lvset].
    denot_lvars_norm.
    rewrite lvars_fv_open_atoms_with_bound.
    rewrite lookup_insert_eq.
    rewrite map_empty_union.
    split.
    + eapply FExprResultAt_body_opened_scoped_in_fiber; eauto.
    + exists (res_fiber_from_projection
        (let_result_world_on e ν n Hfresh Hresult) X σX Hproj).
      split.
      * rewrite map_empty_union.
        eapply FExprResultAt_body_opened_scoped_in_fiber; eauto.
      * split.
        -- rewrite open_tm_env_singleton_lc by exact Hlc.
           assert (Hexact :
             expr_result_in_world (store_restrict σX X) e ν
               (res_fiber_from_projection
                 (let_result_world_on e ν n Hfresh Hresult) X σX Hproj)).
           {
             eapply let_result_world_on_fiber_expr_result_in_world; eauto.
           }
	     intros σν.
	     rewrite map_empty_union.
	     rewrite lvars_fv_of_atoms.
	     replace ((X ∪ {[ν]}) ∩ X) with X
	       by (symmetry; apply inter_union_singleton_l).
	     rewrite store_restrict_twice_subset by set_solver.
	           rewrite res_restrict_restrict_eq.
	           rewrite (inter_union_singleton_r_fresh X ν HνX).
	           exact (Hexact σν).
        -- reflexivity.
Qed.

Lemma FExprContIn_elim_let_result_world
    (Σ : gmap atom ty) (T : ty) e
    (Q : FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  formula_fv Q ⊆ dom Σ →
  m ⊨ FExprContIn Σ e Q →
  ∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ formula_open 0 ν Q.
Proof.
  intros Hty Hdom Hclosed Htotal HQfv Hcont.
  unfold FExprContIn, res_models, res_models_with_store in Hcont.
  cbn [formula_measure res_models_with_store_fuel formula_scoped_in_world
    formula_fv formula_open] in Hcont.
  destruct Hcont as [_ [L [HLdom Hforall]]].
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as Hfv.
  pose proof (typing_tm_lc Σ e T Hty) as Hlc.
  exists (L ∪ dom Σ ∪ fv_tm e).
  split.
  {
    intros z Hz. apply elem_of_union_l. apply elem_of_union_r. exact Hz.
  }
  intros ν Hν Hfresh Hresult.
  rewrite !not_elem_of_union in Hν.
  destruct Hν as [[HνL HνΣ] Hνe].
  set (mν := let_result_world_on e ν m Hfresh Hresult).
  assert (Himpl : mν ⊨ formula_open 0 ν
      (FImpl (FExprResultOn (into_lvars Σ) e) Q)).
  {
    unfold res_models, res_models_with_store.
    specialize (Hforall ν HνL mν).
    eapply res_models_with_store_fuel_irrel; [| | eapply Hforall].
    - rewrite formula_open_preserves_measure. simpl. lia.
    - rewrite formula_open_preserves_measure. simpl. lia.
    - subst mν. rewrite let_result_world_on_dom. reflexivity.
    - subst mν. rewrite let_result_world_on_restrict. reflexivity.
  }
  eapply res_models_impl_elim.
  - exact Himpl.
  - subst mν.
    change (let_result_world_on e ν m Hfresh Hresult
      ⊨ FExprResultAt (dom Σ) e ν).
    eapply let_result_world_on_models_FExprResultAt; eauto.
    rewrite Hdom. set_solver.
Qed.

Lemma FExprContIn_intro_let_result_world
    (Σ : gmap atom ty) (T : ty) e
    (Q : FormulaQ) (m : WfWorld) :
  Σ ⊢ₑ e ⋮ T →
  world_dom (m : World) = dom Σ →
  world_closed_on (dom Σ) m →
  expr_total_on (dom Σ) e m →
  formula_fv Q ⊆ dom Σ →
  (∃ L : aset,
    dom Σ ⊆ L ∧
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ formula_open 0 ν Q) →
  m ⊨ FExprContIn Σ e Q.
Proof.
  intros Hty Hdom Hclosed Htotal HQfv [L [HLdom Hbody]].
  pose proof (basic_typing_contains_fv_tm Σ e T Hty) as Hfv.
  pose proof (typing_tm_lc Σ e T Hty) as Hlc.
  unfold FExprContIn.
  eapply res_models_forall_intro.
  - unfold formula_scoped_in_world.
    rewrite dom_empty_L.
    cbn [formula_fv].
    unfold FExprResultOn, FStoreResourceAtom.
    cbn [formula_fv stale stale_logic_qualifier lqual_dom into_lvars
      into_lvars_aset into_lvars_lvset].
    denot_lvars_norm.
    rewrite lvars_fv_union, lvars_fv_of_atoms, lvars_fv_singleton_bound.
    rewrite Hdom. set_solver.
  - exists (L ∪ dom Σ ∪ fv_tm e ∪ formula_fv Q).
    split.
    {
      rewrite Hdom.
      intros z Hz.
      apply elem_of_union_l. apply elem_of_union_l.
      apply elem_of_union_r. exact Hz.
    }
    intros ν Hν n Hdom_n Hrestrict.
    rewrite !not_elem_of_union in Hν.
    destruct Hν as [[[HνL HνΣ] Hνe] HνQ].
    assert (Hfresh : ν ∉ world_dom (m : World)).
    { rewrite Hdom. exact HνΣ. }
    assert (Hresult :
      ∀ σ, (m : World) σ →
        ∃ vx, subst_map (store_restrict σ (fv_tm e)) e →* tret vx).
    {
      eapply expr_total_on_to_fv_result; eauto.
    }
    eapply res_models_impl_intro.
    + unfold formula_scoped_in_world.
      rewrite dom_empty_L.
      intros z Hz.
      apply elem_of_union in Hz as [Hz_empty | Hz].
      { set_solver. }
      pose proof (formula_open_fv_subset 0 ν
        (FImpl (FExprResultOn (into_lvars Σ) e) Q) z Hz) as Hzopen.
      pose proof (FExprContIn_formula_fv_subset
        Σ e (dom Σ) Q ltac:(set_solver) HQfv) as Hfv_cont.
      unfold FExprContIn in Hfv_cont.
      cbn [formula_fv] in Hfv_cont.
      rewrite Hdom_n, Hdom.
      clear -Hzopen Hfv_cont HνΣ HνQ.
      set_solver.
    + intros Hexpr.
      pose proof (FExprResultOn_scoped_dom (dom Σ) e ν n
        (res_models_with_store_fuel_scoped _ _ _ _ Hexpr)) as Hscope_expr.
      set (nr := res_restrict n (dom Σ ∪ {[ν]})).
      assert (Hnr_dom : world_dom (nr : World) = dom Σ ∪ {[ν]}).
      { subst nr. simpl. set_solver. }
      assert (Hnr_restrict : res_restrict nr (dom Σ) = m).
	{
	  subst nr.
	  rewrite res_restrict_restrict_eq.
	  rewrite (inter_union_singleton_l (dom Σ) ν).
	  exact Hrestrict.
	}
      assert (Hexpr_nr : nr ⊨ FExprResultAt (dom Σ) e ν).
      {
        subst nr.
        pose proof (res_models_minimal_on (dom Σ ∪ {[ν]}) n
          (FExprResultAt (dom Σ) e ν)
          ltac:(rewrite FExprResultAt_fv; reflexivity)) as Hmin.
        apply (proj1 Hmin).
        change (n ⊨ FExprResultAt (dom Σ) e ν).
        exact Hexpr.
      }
      pose proof (FExprResultAt_unique_let_result_world
        Σ T e ν m nr Hfresh Hresult Hty Hdom Hclosed
        Hnr_dom Hnr_restrict Hexpr_nr) as Hnr_eq.
      assert (HQopen_fv : formula_fv (formula_open 0 ν Q) ⊆ dom Σ ∪ {[ν]}).
      {
        apply formula_open_fv_subset_env.
        exact HQfv.
      }
      apply (proj2 (res_models_minimal_on (dom Σ ∪ {[ν]}) n
        (formula_open 0 ν Q) HQopen_fv)).
      change (nr ⊨ formula_open 0 ν Q).
      rewrite Hnr_eq.
      exact (Hbody ν HνL Hfresh Hresult).
Qed.

Lemma FExprContIn_iff_let_result_world
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
    ∀ ν,
      ν ∉ L →
      ∀ Hfresh Hresult,
        let_result_world_on e ν m Hfresh Hresult ⊨ formula_open 0 ν Q.
Proof.
  intros Hty Hdom Hclosed Htotal HQfv.
  split.
  - eapply FExprContIn_elim_let_result_world; eauto.
  - eapply FExprContIn_intro_let_result_world; eauto.
Qed.
