(** * Denotation.TypeEquivBody

    Body cases for term-result-equivalence transport. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import TypeEquivCore TypeEquivTerm TypeEquivFiberTransport.

Section TypeDenote.

Lemma sum_branch_bind_env_fresh
    (Σ : lty_env) τ1 τ2 e y :
  y ∉ lvars_fv (dom Σ) ∪ fv_cty τ1 ∪ fv_cty τ2 ∪ fv_tm e ->
  y ∉ lvars_fv
    (dom (typed_lty_env_bind
      (relevant_env Σ (CTSum τ1 τ2) e) (erase_ty τ1))).
Proof.
  intros Hy Hbad.
  rewrite typed_lty_env_bind_lvars_fv_dom in Hbad.
  apply lvars_fv_elem in Hbad.
  apply (relevant_env_dom_subset_direct
    Σ (CTSum τ1 τ2) e) in Hbad as HΣ.
  assert (HyΣ : y ∈ lvars_fv (dom Σ)).
  {
    apply (proj2 (lvars_fv_elem (dom Σ) y)). exact HΣ.
  }
  apply Hy. set_solver.
Qed.

Lemma context_ty_lvars_at_lc_from_lc_support d D τ :
  lc_lvars D ->
  context_ty_lvars_at d τ ⊆ D ->
  cty_lc_at d τ.
Proof.
  intros HlcD Hsub.
  induction τ in d, Hsub |- *; cbn [cty_lc_at context_ty_lvars_at] in *.
  - intros k Hk.
    destruct (decide (k < S d)) as [Hlt|Hnlt]; [exact Hlt|].
    exfalso.
    assert (Hdeep : LVBound (k - S d) ∈ lvars_at_depth (S d) (qual_vars φ)).
    {
      rewrite lvars_at_depth_elem.
      exists (LVBound k). split.
      - apply lvars_bv_elem. exact Hk.
      - cbn [logic_var_at_depth].
        destruct (decide (S d <= k)); [reflexivity|lia].
    }
    specialize (HlcD (LVBound (k - S d))).
    assert (Hbd : LVBound (k - S d) ∈ D).
    {
      apply Hsub. exact Hdeep.
    }
    specialize (HlcD Hbd). cbn [lc_logic_var_key] in HlcD. exact HlcD.
  - intros k Hk.
    destruct (decide (k < S d)) as [Hlt|Hnlt]; [exact Hlt|].
    exfalso.
    assert (Hdeep : LVBound (k - S d) ∈ lvars_at_depth (S d) (qual_vars φ)).
    {
      rewrite lvars_at_depth_elem.
      exists (LVBound k). split.
      - apply lvars_bv_elem. exact Hk.
      - cbn [logic_var_at_depth].
        destruct (decide (S d <= k)); [reflexivity|lia].
    }
    specialize (HlcD (LVBound (k - S d))).
    assert (Hbd : LVBound (k - S d) ∈ D).
    {
      apply Hsub. exact Hdeep.
    }
    specialize (HlcD Hbd). cbn [lc_logic_var_key] in HlcD. exact HlcD.
  - split.
    + eapply IHτ1; [intros v Hv; apply Hsub; set_solver].
    + eapply IHτ2; [intros v Hv; apply Hsub; set_solver].
  - split.
    + eapply IHτ1; [intros v Hv; apply Hsub; set_solver].
    + eapply IHτ2; [intros v Hv; apply Hsub; set_solver].
  - split.
    + eapply IHτ1; [intros v Hv; apply Hsub; set_solver].
    + eapply IHτ2; [intros v Hv; apply Hsub; set_solver].
  - split.
    + eapply IHτ1; [intros v Hv; apply Hsub; set_solver].
    + eapply IHτ2; [intros v Hv; apply Hsub; set_solver].
  - split.
    + eapply IHτ1; [intros v Hv; apply Hsub; set_solver].
    + eapply IHτ2; [intros v Hv; apply Hsub; set_solver].
Qed.

Lemma ty_denote_gas_zero_sum_lc
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  lc_context_ty τ1 /\ lc_context_ty τ2.
Proof.
  intros Hzero.
  apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [Hwf _].
  apply context_ty_wf_formula_models_iff in Hwf as [HlcΣ [_ Hbasic]].
  destruct Hbasic as [Hvars _].
  split.
  - eapply context_ty_lvars_at_lc_from_lc_support.
    + exact HlcΣ.
    + intros v Hv. apply Hvars. cbn. set_solver.
  - eapply context_ty_lvars_at_lc_from_lc_support.
    + exact HlcΣ.
    + intros v Hv. apply Hvars. cbn. set_solver.
Qed.

Lemma relevant_env_lookup_of_relevant
    (Σ : lty_env) τ e v :
  v ∈ relevant_lvars τ e ->
  relevant_env Σ τ e !! v = Σ !! v.
Proof.
  intros Hv.
  unfold relevant_env, lty_env_restrict_lvars.
  change ((storeA_restrict Σ (relevant_lvars τ e)
      : gmap logic_var ty) !! v = (Σ : gmap logic_var ty) !! v).
  destruct ((Σ : gmap logic_var ty) !! v) as [T|] eqn:Hlookup.
  - apply storeA_restrict_lookup_some_2; [exact Hlookup|exact Hv].
  - apply storeA_restrict_lookup_none_l. exact Hlookup.
Qed.

Lemma sum_branch_open_bind_relevant_env_agree
    (Σ : lty_env) τ1 τ2 τ e1 e2 y :
  lc_context_ty τ ->
  τ = τ1 \/ τ = τ2 ->
  y ∉ fv_cty τ1 ∪ fv_cty τ2 ->
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTSum τ1 τ2) e1) (erase_ty τ1)))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τ))
      (tret (vfvar y))) =
  lty_env_restrict_lvars
    (lty_env_open_one 0 y
      (typed_lty_env_bind
        (relevant_env Σ (CTSum τ1 τ2) e2) (erase_ty τ1)))
    (relevant_lvars (cty_open 0 y (cty_shift 0 τ))
      (tret (vfvar y))).
Proof.
  intros Hlcτ Hτ Hyτ.
  apply lty_env_restrict_open_one_bind_agree_on.
  - assert (Hyτcur : y ∉ fv_cty τ).
    {
      destruct Hτ as [Hτeq|Hτeq]; subst; set_solver.
    }
    rewrite (cty_open_shift_from_lc_fresh 0 y τ Hlcτ Hyτcur).
    apply lc_lvars_relevant_lvars; [exact Hlcτ|constructor; constructor].
  - intros z HzD Hzy.
    assert (Hyτcur : y ∉ fv_cty τ).
    {
      destruct Hτ as [Hτeq|Hτeq]; subst; set_solver.
    }
    rewrite (cty_open_shift_from_lc_fresh 0 y τ Hlcτ Hyτcur) in HzD.
    destruct Hτ as [Hτeq|Hτeq]; subst.
    + assert (HzRel1 : LVFree z ∈ relevant_lvars (CTSum τ1 τ2) e1).
      { relevant_lvars_norm_in HzD. relevant_lvars_norm. better_set_solver. }
      assert (HzRel2 : LVFree z ∈ relevant_lvars (CTSum τ1 τ2) e2).
      { relevant_lvars_norm_in HzD. relevant_lvars_norm. better_set_solver. }
      rewrite (relevant_env_lookup_of_relevant
        Σ (CTSum τ1 τ2) e1 (LVFree z) HzRel1).
      rewrite (relevant_env_lookup_of_relevant
        Σ (CTSum τ1 τ2) e2 (LVFree z) HzRel2).
      reflexivity.
    + assert (HzRel1 : LVFree z ∈ relevant_lvars (CTSum τ1 τ2) e1).
      { relevant_lvars_norm_in HzD. relevant_lvars_norm. better_set_solver. }
      assert (HzRel2 : LVFree z ∈ relevant_lvars (CTSum τ1 τ2) e2).
      { relevant_lvars_norm_in HzD. relevant_lvars_norm. better_set_solver. }
      rewrite (relevant_env_lookup_of_relevant
        Σ (CTSum τ1 τ2) e1 (LVFree z) HzRel1).
      rewrite (relevant_env_lookup_of_relevant
        Σ (CTSum τ1 τ2) e2 (LVFree z) HzRel2).
      reflexivity.
Qed.

Local Lemma lvars_open_removed_bound0_fv_fresh y D :
  y ∉ lvars_fv D ->
  y ∉ lvars_fv (lvars_open 0 y (D ∖ {[LVBound 0]})).
Proof.
  intros Hy Hbad.
  rewrite lvars_fv_open in Hbad.
  assert (HyD : y ∉ lvars_fv (D ∖ {[LVBound 0]})).
  {
    intros HyD.
    apply Hy.
    rewrite !lvars_fv_elem in HyD |- *.
    set_solver.
  }
  destruct (decide (0 ∈ lvars_bv (D ∖ {[LVBound 0]}))) as [Hb|Hb].
  - rewrite lvars_bv_elem in Hb. set_solver.
  - set_solver.
Qed.

Local Lemma res_fiber_projection_store_fresh_of_open_removed_bound0
    (my mfib : WfWorldT) y D σ :
  y ∉ lvars_fv D ->
  res_fiber_from_projection my
    (lvars_fv (lvars_open 0 y (D ∖ {[LVBound 0]}))) σ mfib ->
  y ∉ dom (σ : StoreT).
Proof.
  intros Hy Hproj Hyσ.
  pose proof (res_fiber_from_projection_store_dom_subset
    my mfib
    (lvars_fv (lvars_open 0 y (D ∖ {[LVBound 0]}))) σ Hproj)
    as Hσsub.
  apply Hσsub in Hyσ.
  eapply lvars_open_removed_bound0_fv_fresh; eauto.
Qed.

Lemma res_models_forall_fibvars_impl_map
    (m : WfWorldT) (D : lvset)
    (A1 A2 B1 B2 : FormulaT) :
  formula_scoped_in_world m (FForall (FFibVars D (FImpl A2 B2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
      forall σ mfib,
        res_fiber_from_projection my
          (lvars_fv (lvars_open 0 y D)) σ mfib ->
        (mfib ⊨ formula_msubst_store σ (formula_open 0 y A2) ->
         mfib ⊨ formula_msubst_store σ (formula_open 0 y A1)) /\
        (mfib ⊨ formula_msubst_store σ (formula_open 0 y B1) ->
         mfib ⊨ formula_msubst_store σ (formula_open 0 y B2))) ->
  m ⊨ FForall (FFibVars D (FImpl A1 B1)) ->
  m ⊨ FForall (FFibVars D (FImpl A2 B2)).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FFibVars D (FImpl A2 B2)))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_fibvars in Hopened, Htarget_scope |- *.
  rewrite !formula_open_impl in Hopened, Htarget_scope |- *.
  apply res_models_FFibVars_iff in Hopened as [_ [Hlc Hfib]].
  eapply res_models_FFibVars_intro; [exact Htarget_scope|exact Hlc|].
  intros σ mfib Hproj.
  specialize (Hfib σ mfib Hproj).
  change (formula_msubst_store σ
    (FImpl (formula_open 0 y A1) (formula_open 0 y B1)))
    with (FImpl
      (formula_msubst_store σ (formula_open 0 y A1))
      (formula_msubst_store σ (formula_open 0 y B1))) in Hfib.
  change (formula_msubst_store σ
    (FImpl (formula_open 0 y A2) (formula_open 0 y B2)))
    with (FImpl
      (formula_msubst_store σ (formula_open 0 y A2))
      (formula_msubst_store σ (formula_open 0 y B2))).
  assert (Himpl_scope :
      formula_scoped_in_world mfib
        (FImpl
          (formula_msubst_store σ (formula_open 0 y A2))
          (formula_msubst_store σ (formula_open 0 y B2)))).
  {
    pose proof (formula_scoped_fibvars_r _ _ _ Htarget_scope)
      as Htarget_impl_scope.
    unfold formula_scoped_in_world in *.
    intros a Ha.
    assert (Ha_open : a ∈ formula_fv (FImpl
        (formula_open 0 y A2) (formula_open 0 y B2))).
    {
      pose proof (formula_msubst_store_fv_subset σ (formula_open 0 y A2))
        as HfvA.
      pose proof (formula_msubst_store_fv_subset σ (formula_open 0 y B2))
        as HfvB.
      rewrite formula_fv_impl in Ha |- *.
      apply elem_of_union in Ha as [Ha|Ha].
      - apply elem_of_union_l. exact (HfvA _ Ha).
      - apply elem_of_union_r. exact (HfvB _ Ha).
    }
    specialize (Htarget_impl_scope a Ha_open).
    destruct Hproj as [_ Hfib_eq].
    change ((mfib : WorldT) = raw_fiber (my : WorldT) σ) in Hfib_eq.
    pose proof (f_equal world_dom Hfib_eq) as Hdom_eq.
    change (world_dom (mfib : WorldT) = world_dom (my : WorldT))
      in Hdom_eq.
    rewrite Hdom_eq. exact Htarget_impl_scope.
  }
  destruct (Hmap y Hy my Hdom Hrestrict σ mfib Hproj) as [HA HB].
  eapply res_models_impl_map; [exact Himpl_scope|exact HA|exact HB|exact Hfib].
Qed.

Lemma ty_denote_gas_tm_equiv_over_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTOver b φ) m e1 e2 ->
  m ⊨
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
          (expr_result_formula (tm_shift 0 e1) (LVBound 0))
          (FOver (FAtom φ)))) ->
  m ⊨
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
          (expr_result_formula (tm_shift 0 e2) (LVBound 0))
          (FOver (FAtom φ)))).
Proof.
Admitted.

Lemma ty_denote_gas_tm_equiv_under_body
    (gas : nat) (Σ : lty_env) b φ e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTUnder b φ) m e1 e2 ->
  m ⊨
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
          (expr_result_formula (tm_shift 0 e1) (LVBound 0))
          (FUnder (FAtom φ)))) ->
  m ⊨
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
          (expr_result_formula (tm_shift 0 e2) (LVBound 0))
          (FUnder (FAtom φ)))).
Proof.
Admitted.

Lemma ty_denote_gas_result_alias_over_body
    φ e x (m : WfWorldT) :
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
      forall σ mfib,
        res_fiber_from_projection my
          (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))) σ mfib ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula
              (tm_shift 0 (tret (vfvar x))) (LVBound 0))) ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula (tm_shift 0 e) (LVBound 0)))) ->
  formula_scoped_in_world m
    (FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
        (expr_result_formula
          (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FOver (FAtom φ))))) ->
  m ⊨
    (
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FOver (FAtom φ))))) ->
  m ⊨
    (
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
        (expr_result_formula
          (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FOver (FAtom φ))))).
Proof.
  intros [Lalias Halias] Htarget_scope Hsrc.
  eapply res_models_forall_fibvars_impl_map;
    [exact Htarget_scope| |exact Hsrc].
  exists Lalias.
  intros y Hy my Hdom Hrestrict σ mfib Hproj.
  split.
  - intros Hret_result.
    eapply Halias; eauto.
  - intros Hfib. exact Hfib.
Qed.

Lemma ty_denote_gas_result_alias_under_body
    φ e x (m : WfWorldT) :
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
      forall σ mfib,
        res_fiber_from_projection my
          (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))) σ mfib ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula
              (tm_shift 0 (tret (vfvar x))) (LVBound 0))) ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula (tm_shift 0 e) (LVBound 0)))) ->
  formula_scoped_in_world m
    (FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
        (expr_result_formula
          (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FUnder (FAtom φ))))) ->
  m ⊨
    (
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
        (expr_result_formula (tm_shift 0 e) (LVBound 0))
          (FUnder (FAtom φ))))) ->
  m ⊨
    (
    FForall
      (FFibVars (qual_vars φ ∖ {[LVBound 0]})
        (FImpl
        (expr_result_formula
          (tm_shift 0 (tret (vfvar x))) (LVBound 0))
          (FUnder (FAtom φ))))).
Proof.
  intros [Lalias Halias] Htarget_scope Hsrc.
  eapply res_models_forall_fibvars_impl_map;
    [exact Htarget_scope| |exact Hsrc].
  exists Lalias.
  intros y Hy my Hdom Hrestrict σ mfib Hproj.
  split.
  - intros Hret_result.
    eapply Halias; eauto.
  - intros Hfib. exact Hfib.
Qed.

Lemma ty_denote_gas_zero_project_context
    (Σ : lty_env) τsmall τbig e (m : WfWorldT) :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  erase_ty τsmall = erase_ty τbig ->
  context_ty_shape_ok τsmall ->
  m ⊨ ty_denote_gas 0 Σ τbig e ->
  m ⊨ ty_denote_gas 0 Σ τsmall e.
Proof.
Admitted.

Lemma ty_denote_gas_zero_inter_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (ty_denote_gas_zero_project_context
    Σ τ1 (CTInter τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply ty_denote_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma ty_denote_gas_zero_inter_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTInter τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTInter τ1 τ2)).
  {
    apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (ty_denote_gas_zero_project_context
    Σ τ2 (CTInter τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_equiv_inter_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ1 m e1 e2.
Proof.
  intros [Heq [Htotal [Hzero_src Hzero_tgt]]].
  split; [exact Heq|].
  split; [exact Htotal|]. split.
  - eapply ty_denote_gas_zero_inter_l; exact Hzero_src.
  - eapply ty_denote_gas_zero_inter_l; exact Hzero_tgt.
Qed.

Lemma typed_total_equiv_inter_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ2 m e1 e2.
Proof.
  intros [Heq [Htotal [Hzero_src Hzero_tgt]]].
  split; [exact Heq|].
  split; [exact Htotal|]. split.
  - eapply ty_denote_gas_zero_inter_r; exact Hzero_src.
  - eapply ty_denote_gas_zero_inter_r; exact Hzero_tgt.
Qed.

Lemma ty_denote_gas_tm_equiv_inter_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ1 e1 /\
  m ⊨ ty_denote_gas gas Σ τ2 e1 ->
  m ⊨ ty_denote_gas gas Σ τ1 e2 /\
  m ⊨ ty_denote_gas gas Σ τ2 e2.
Proof.
  intros Hequiv [H1 H2].
  split.
  - eapply IH; [|exact H1].
    eapply typed_total_equiv_inter_l; exact Hequiv.
  - eapply IH; [|exact H2].
    eapply typed_total_equiv_inter_r; exact Hequiv.
Qed.

Lemma ty_denote_gas_zero_union_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (ty_denote_gas_zero_project_context
    Σ τ1 (CTUnion τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply ty_denote_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma ty_denote_gas_zero_union_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTUnion τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTUnion τ1 τ2)).
  {
    apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (ty_denote_gas_zero_project_context
    Σ τ2 (CTUnion τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_equiv_union_l
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ1 m e1 e2.
Proof.
  intros [Heq [Htotal [Hzero_src Hzero_tgt]]].
  split; [exact Heq|].
  split; [exact Htotal|]. split.
  - eapply ty_denote_gas_zero_union_l; exact Hzero_src.
  - eapply ty_denote_gas_zero_union_l; exact Hzero_tgt.
Qed.

Lemma typed_total_equiv_union_r
    (Σ : lty_env) τ1 τ2 m e1 e2 :
  typed_total_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_total_equiv_on Σ τ2 m e1 e2.
Proof.
  intros [Heq [Htotal [Hzero_src Hzero_tgt]]].
  split; [exact Heq|].
  split; [exact Htotal|]. split.
  - eapply ty_denote_gas_zero_union_r; exact Hzero_src.
  - eapply ty_denote_gas_zero_union_r; exact Hzero_tgt.
Qed.

Lemma ty_denote_gas_scope_from_zero_any
    gas Σ τ e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ τ e ->
  formula_scoped_in_world m (ty_denote_gas gas Σ τ e).
Proof.
Admitted.

Lemma ty_denote_gas_tm_equiv_union_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  m ⊨
    FOr
      (ty_denote_gas gas Σ τ1 e1)
      (ty_denote_gas gas Σ τ2 e1) ->
  m ⊨
    FOr
	      (ty_denote_gas gas Σ τ1 e2)
	      (ty_denote_gas gas Σ τ2 e2).
Proof.
  intros Hequiv Hbody.
  pose proof (typed_total_equiv_union_l
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv1.
  pose proof (typed_total_equiv_union_r
    Σ τ1 τ2 m e1 e2 Hequiv) as Hequiv2.
  pose proof (res_models_scoped _ _ Hbody) as Hscope_body.
  apply (proj1 (res_models_or_iff m _ _ Hscope_body)) in Hbody.
  destruct Hbody as [H1|H2].
  - eapply res_models_or_intro_l_from_model.
    + eapply IH; [exact Hequiv1|exact H1].
    + eapply ty_denote_gas_scope_from_zero_any.
      exact (typed_total_equiv_target_zero
        Σ τ2 m e1 e2 Hequiv2).
  - eapply res_models_or_intro_r_from_model.
    + eapply ty_denote_gas_scope_from_zero_any.
      exact (typed_total_equiv_target_zero
        Σ τ1 m e1 e2 Hequiv1).
    + eapply IH; [exact Hequiv2|exact H2].
Qed.

Lemma ty_denote_gas_zero_res_subset
    (Σ : lty_env) τ e (m n : WfWorldT) :
  res_subset n m ->
  m ⊨ ty_denote_gas 0 Σ τ e ->
  n ⊨ ty_denote_gas 0 Σ τ e.
Proof.
  intros Hsub Hzero.
  apply ty_denote_gas_zero_of_guard.
  apply ty_denote_gas_guard_of_zero in Hzero.
  repeat rewrite res_models_and_iff in Hzero |- *.
  destruct Hzero as [Hwf [Hworld [Hbasic Htotal]]].
  pose proof Hsub as [Hdom _].
  split.
  - apply context_ty_wf_formula_models_iff in Hwf as [Hlc [Hscope Hbasic_ty]].
    apply context_ty_wf_formula_models_iff.
    split; [exact Hlc|]. split; [set_solver|exact Hbasic_ty].
  - split.
    + eapply basic_world_formula_res_subset; eauto.
    + split.
      * apply expr_basic_typing_formula_models_iff in Hbasic
          as [Hlc [Hscope Hty]].
        apply expr_basic_typing_formula_models_iff.
        split; [exact Hlc|]. split; [set_solver|exact Hty].
      * eapply expr_total_formula_res_subset; eauto.
Qed.

Lemma ty_denote_gas_zero_sum_l
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ1 e.
Proof.
  intros Hzero.
  eapply (ty_denote_gas_zero_project_context
    Σ τ1 (CTSum τ1 τ2) e m); [|reflexivity| |exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - apply ty_denote_gas_guard_of_zero in Hzero.
    repeat rewrite res_models_and_iff in Hzero.
    destruct Hzero as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    cbn [context_ty_shape_ok] in Hshape. tauto.
Qed.

Lemma ty_denote_gas_zero_sum_r
    (Σ : lty_env) τ1 τ2 e (m : WfWorldT) :
  m ⊨ ty_denote_gas 0 Σ (CTSum τ1 τ2) e ->
  m ⊨ ty_denote_gas 0 Σ τ2 e.
Proof.
  intros Hzero.
  assert (Hshape_big : context_ty_shape_ok (CTSum τ1 τ2)).
  {
    apply ty_denote_gas_guard_of_zero in Hzero as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [Hwf _].
    apply context_ty_wf_formula_models_iff in Hwf as [_ [_ [_ Hshape]]].
    exact Hshape.
  }
  cbn [context_ty_shape_ok] in Hshape_big.
  destruct Hshape_big as [_ [Hshape2 Herase]].
  eapply (ty_denote_gas_zero_project_context
    Σ τ2 (CTSum τ1 τ2) e m); [| |exact Hshape2|exact Hzero].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - cbn [erase_ty]. symmetry. exact Herase.
Qed.

Lemma typed_total_equiv_sum_l_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m1 : WfWorldT) :
  res_subset m1 m ->
  typed_total_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m1 ⊨ ty_denote_gas gas Σ τ1 e1 ->
  typed_total_equiv_on Σ τ1 m1 e1 e2.
Proof.
  intros Hsub [Heq [Htotal [_ Hzero_tgt]]] Hsrc.
  split.
  - eapply tm_equiv_res_store_subset; eauto.
  - split.
    + eapply tm_total_equiv_res_store_subset; eauto.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hsrc.
      * apply ty_denote_gas_zero_sum_l with (τ2 := τ2).
        eapply ty_denote_gas_zero_res_subset; eauto.
Qed.

Lemma typed_total_equiv_sum_r_pullback
    gas (Σ : lty_env) τ1 τ2 e1 e2 (m m2 : WfWorldT) :
  res_subset m2 m ->
  typed_total_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m2 ⊨ ty_denote_gas gas Σ τ2 e1 ->
  typed_total_equiv_on Σ τ2 m2 e1 e2.
Proof.
  intros Hsub [Heq [Htotal [_ Hzero_tgt]]] Hsrc.
  split.
  - eapply tm_equiv_res_store_subset; eauto.
  - split.
    + eapply tm_total_equiv_res_store_subset; eauto.
    + split.
      * apply ty_denote_gas_zero_of_guard.
        eapply ty_denote_gas_guard. exact Hsrc.
      * apply ty_denote_gas_zero_sum_r with (τ1 := τ1).
        eapply ty_denote_gas_zero_res_subset; eauto.
Qed.

Lemma ty_denote_gas_tm_equiv_sum_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula (tm_shift 0 e1) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTSum τ1 τ2) e1) (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTSum τ1 τ2) e1) (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula (tm_shift 0 e2) (LVBound 0))
        (FPlus
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTSum τ1 τ2) e2) (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas
            (typed_lty_env_bind
              (relevant_env Σ (CTSum τ1 τ2) e2) (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))).
Proof.
Admitted.

End TypeDenote.
