(** * Denotation.TypeEquivFiber

    The fiber-equality term transport theorem for type denotation.

    This file is intentionally kept as a small interface while the new
    nondeterministic result-graph semantics settles.  The previous proof
    attempt decomposed Over/Under/Sum/Arrow/Wand into several body lemmas whose
    statements mentioned the old [expr_result_formula] and [relevant_env]
    shapes.  Those old helper proofs are no longer on the compile path; use
    git history for the detailed script when reproving this theorem. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import TypeEquivCore TypeEquivTerm.
From Denotation Require Import TypeEquivFiberTransport.
From Denotation Require Import TypeEquivFiberBase.
Section TypeDenote.

Lemma formula_fv_open_over_body_obs b φ y :
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FOver (FAtom φ)))) ⊆
  lvars_fv (context_ty_lvars (CTOver b φ)) ∪ {[y]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
  rewrite formula_fv_fibvars, formula_fv_over, formula_fv_atom.
  rewrite context_ty_lvars_over_fv.
  intros a Ha.
  rewrite elem_of_union in Ha.
  destruct Ha as [Ha|Ha].
  - rewrite elem_of_union in Ha.
    destruct Ha as [Ha|Ha].
    + apply elem_of_union_l. unfold qual_dom.
      rewrite lvars_fv_elem in Ha |- *.
      apply elem_of_difference in Ha as [Ha _]. exact Ha.
    + apply elem_of_union_l. unfold qual_dom. exact Ha.
  - apply elem_of_union_r. exact Ha.
Qed.

Lemma formula_fv_open_under_body_obs b φ y :
  formula_fv
    (formula_open 0 y
      (FFibVars (qual_vars φ ∖ {[LVBound 0]}) (FUnder (FAtom φ)))) ⊆
  lvars_fv (context_ty_lvars (CTUnder b φ)) ∪ {[y]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
  rewrite formula_fv_fibvars, formula_fv_under, formula_fv_atom.
  rewrite context_ty_lvars_under_fv.
  intros a Ha.
  rewrite elem_of_union in Ha.
  destruct Ha as [Ha|Ha].
  - rewrite elem_of_union in Ha.
    destruct Ha as [Ha|Ha].
    + apply elem_of_union_l. unfold qual_dom.
      rewrite lvars_fv_elem in Ha |- *.
      apply elem_of_difference in Ha as [Ha _]. exact Ha.
    + apply elem_of_union_l. unfold qual_dom. exact Ha.
  - apply elem_of_union_r. exact Ha.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_over_body
    (gas : nat) (Σ : lty_env) (b : base_ty) φ e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTOver b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at (dom Σ) (tm_shift 0 e1) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FAtom φ)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at (dom Σ) (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FOver (FAtom φ)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ (CTOver b φ) e1 m Hzero_src)
    as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [Hworld_src _]].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ _].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTOver b φ) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  pose proof (typed_fiber_equiv_result_projected
    Σ (CTOver b φ) m e1 e2 Hequiv) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom Σ) ∪ lvars_fv (context_ty_lvars (CTOver b φ))).
  intros y Hy my Hdom Hrestrict.
  assert (Hy_dom : y ∉ lvars_fv (dom Σ)) by (clear -Hy; set_solver).
  assert (Hy_e1 : y ∉ fv_tm e1) by (clear -Hy; set_solver).
  assert (Hy_e2 : y ∉ fv_tm e2) by (clear -Hy; set_solver).
  assert (Hy_proj :
      y ∉ fv_tm e2 ∪ fv_tm e1 ∪ lvars_fv (dom Σ))
    by (clear -Hy; set_solver).
  assert (Hy_src : y ∉ Lsrc) by (clear -Hy; set_solver).
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (expr_result_formula_at (dom Σ) (tm_shift 0 e2) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FOver (FAtom φ)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
      - rewrite Hdom. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (try exact HlcΣ; try exact Hlc2; assumption).
  destruct (H21 y my Hy_proj Hdom Hrestrict Hres_tgt)
    as [my_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev y Hy_src my_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (try exact HlcΣ; try exact Hlc1; assumption).
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hbody_src.
  eapply res_models_projection; [|exact Hbody_src].
  eapply (res_restrict_eq_subset my_src my
    (lvars_fv (dom Σ) ∪
      lvars_fv (context_ty_lvars (CTOver b φ)) ∪ {[y]})).
  - etransitivity; [apply formula_fv_open_over_body_obs|].
    intros a Ha.
    apply elem_of_union in Ha as [Ha|Ha].
    + apply elem_of_union_l. apply elem_of_union_r. exact Ha.
    + apply elem_of_union_r. exact Ha.
  - exact Hproj_obs.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_under_body
    (gas : nat) (Σ : lty_env) (b : base_ty) φ e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTUnder b φ) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at (dom Σ) (tm_shift 0 e1) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FAtom φ)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at (dom Σ) (tm_shift 0 e2) (LVBound 0))
        (FFibVars (qual_vars φ ∖ {[LVBound 0]})
          (FUnder (FAtom φ)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ (CTUnder b φ) e1 m Hzero_src)
    as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [Hworld_src _]].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ _].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTUnder b φ) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  pose proof (typed_fiber_equiv_result_projected
    Σ (CTUnder b φ) m e1 e2 Hequiv) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom Σ) ∪ lvars_fv (context_ty_lvars (CTUnder b φ))).
  intros y Hy my Hdom Hrestrict.
  assert (Hy_dom : y ∉ lvars_fv (dom Σ)) by (clear -Hy; set_solver).
  assert (Hy_e1 : y ∉ fv_tm e1) by (clear -Hy; set_solver).
  assert (Hy_e2 : y ∉ fv_tm e2) by (clear -Hy; set_solver).
  assert (Hy_proj :
      y ∉ fv_tm e2 ∪ fv_tm e1 ∪ lvars_fv (dom Σ))
    by (clear -Hy; set_solver).
  assert (Hy_src : y ∉ Lsrc) by (clear -Hy; set_solver).
  rewrite formula_open_impl.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (expr_result_formula_at (dom Σ) (tm_shift 0 e2) (LVBound 0))
            (FFibVars (qual_vars φ ∖ {[LVBound 0]})
              (FUnder (FAtom φ)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Hres_tgt.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres_tgt
    by (try exact HlcΣ; try exact Hlc2; assumption).
  destruct (H21 y my Hy_proj Hdom Hrestrict Hres_tgt)
    as [my_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev y Hy_src my_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (try exact HlcΣ; try exact Hlc1; assumption).
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hbody_src.
  eapply res_models_projection; [|exact Hbody_src].
  eapply (res_restrict_eq_subset my_src my
    (lvars_fv (dom Σ) ∪
      lvars_fv (context_ty_lvars (CTUnder b φ)) ∪ {[y]})).
  - etransitivity; [apply formula_fv_open_under_body_obs|].
    intros a Ha.
    apply elem_of_union in Ha as [Ha|Ha].
    + apply elem_of_union_l. apply elem_of_union_r. exact Ha.
    + apply elem_of_union_r. exact Ha.
  - exact Hproj_obs.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_sum_body
    (gas : nat)
    (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_fiber_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τ1 τ2 e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at (dom Σ) (tm_shift 0 e1) (LVBound 0))
        (FPlus
          (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at (dom Σ) (tm_shift 0 e2) (LVBound 0))
        (FPlus
          (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            (cty_shift 0 τ1) (tret (vbvar 0)))
          (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
            (cty_shift 0 τ2) (tret (vbvar 0))))).
Proof.
Admitted.

Lemma tm_total_equiv_of_ty_denote_source_target_zero
    gas Σ τ e1 e2 (m : WfWorldT) :
  m ⊨ ty_denote_gas gas Σ τ e1 ->
  m ⊨ ty_denote_gas 0 Σ τ e2 ->
  tm_total_equiv_on m e1 e2.
Proof.
  intros Hsrc Htgt.
  pose proof (ty_denote_gas_guard gas Σ τ e1 m Hsrc) as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [_ [_ Htotal_src]]].
  pose proof (ty_denote_gas_total_guard_of_zero Σ τ e2 m Htgt)
    as Htotal_tgt.
  eapply tm_total_equiv_of_total_formulas; eauto.
Qed.

Lemma expr_result_formula_at_transport_tm_equiv
    (m my : WfWorldT) D e1 e2 y :
  lc_lvars D ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_lvars e1 ⊆ D ->
  tm_lvars e2 ⊆ D ->
  LVFree y ∉ D ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  tm_equiv_on m e1 e2 ->
  my ⊨ expr_result_formula_at D e1 (LVFree y) ->
  my ⊨ expr_result_formula_at D e2 (LVFree y).
Proof.
  intros HlcD Hlc1 Hlc2 He1D He2D HyD Hye Hdom Hrestrict Heq Hres1.
  pose proof Hres1 as Hres1_scope.
  unfold expr_result_formula_at in Hres1_scope.
  apply res_models_FFibVars_iff in Hres1_scope as [Hscope_src [_ _]].
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    apply (proj1 (formula_scoped_fibvars_iff my D
      (FAtom (expr_result_qual e1 (LVFree y))))) in Hscope_src as [HDmy _].
    intros a Ha.
    pose proof (HDmy a Ha) as Hamy.
    rewrite Hdom in Hamy.
    apply elem_of_union in Hamy as [Ham|Hay].
    - exact Ham.
    - apply elem_of_singleton in Hay. subst a.
      exfalso. apply HyD. apply lvars_fv_elem. exact Ha.
  }
  assert (Hfv_m : fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    apply elem_of_union in Ha as [Ha|Ha].
    - apply HDm. apply lvars_fv_elem. apply He1D.
      apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
    - apply HDm. apply lvars_fv_elem. apply He2D.
      apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
  }
  pose proof (tm_equiv_full_world_extend_fresh
    m my y e1 e2 Heq Hfv_m Hye Hdom Hrestrict) as Heq_my.
  assert (Hscope_tgt :
      formula_scoped_in_world my (expr_result_formula_at D e2 (LVFree y))).
  {
    unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula_at.
    intros a Ha.
    apply elem_of_union in Ha as [HaD|HaQ].
    - rewrite Hdom. apply elem_of_union_l. apply HDm. exact HaD.
    - apply lvars_fv_elem in HaQ.
      apply elem_of_union in HaQ as [HaE|Hay].
      + rewrite Hdom. apply elem_of_union_l. apply HDm.
        apply lvars_fv_elem. apply He2D. exact HaE.
      + apply elem_of_singleton in Hay. inversion Hay. subst a.
        rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  eapply expr_result_formula_at_intro; eauto.
  - intros σ Hσ.
    pose proof (expr_result_formula_at_models_elim D e1 y my
      He1D HyD Hres1 σ Hσ) as Hstore1.
    destruct Hstore1 as [Hyfresh [v [Hylookup Heval1]]].
    split.
    + intros HyE2. apply HyD. apply He2D. exact HyE2.
    + exists v. split; [exact Hylookup|].
      apply (proj1 (Heq_my σ v Hσ)).
      change (tm_eval_in_store σ e1 v). exact Heval1.
  - intros σ v Hσ Heval2_restrict.
    assert (Heval2_full : tm_eval_in_store σ e2 v).
    {
      apply (proj1 (tm_eval_in_store_restrict_fv_exact σ e2 v)).
      exact Heval2_restrict.
    }
    assert (Heval1_full : tm_eval_in_store σ e1 v).
    { apply (proj2 (Heq_my σ v Hσ)). exact Heval2_full. }
    pose proof (expr_result_formula_at_fiber_witness D e1 y my
      He1D HyD Hres1 σ v Hσ
      ltac:(apply (proj2 (tm_eval_in_store_restrict_fv_exact σ e1 v));
        exact Heval1_full))
      as [σv [Hσv [HσvD Hσvy]]].
    exists σv. repeat split; assumption.
Qed.

Lemma tm_equiv_on_to_result_projected
    (m : WfWorldT) Dinput Dobs e1 e2 :
  lc_lvars Dinput ->
  lc_tm e1 ->
  lc_tm e2 ->
  tm_lvars e1 ⊆ Dinput ->
  tm_lvars e2 ⊆ Dinput ->
  tm_equiv_on m e1 e2 ->
  tm_result_equiv_projected_on m Dinput Dobs e1 e2.
Proof.
  intros HlcD Hlc1 Hlc2 He1D He2D Heq.
  split.
  - intros y my Hy Hdom Hrestrict Hres.
    exists my. split; [exact Hdom|].
    split; [exact Hrestrict|].
    split.
    + eapply expr_result_formula_at_transport_tm_equiv
        with (m := m) (my := my) (D := Dinput)
             (e1 := e1) (e2 := e2) (y := y);
        try exact HlcD; try exact Hlc1; try exact Hlc2;
        try exact He1D; try exact He2D; try exact Hdom;
        try exact Hrestrict; try exact Heq; try exact Hres.
      * intros HyD. apply Hy.
        pose proof (proj2 (lvars_fv_elem Dinput y) HyD).
        set_solver.
      * clear -Hy. set_solver.
    + reflexivity.
  - intros y my Hy Hdom Hrestrict Hres.
    exists my. split; [exact Hdom|].
    split; [exact Hrestrict|].
    split.
    + eapply expr_result_formula_at_transport_tm_equiv
        with (m := m) (my := my) (D := Dinput)
             (e1 := e2) (e2 := e1) (y := y);
        try exact HlcD; try exact Hlc1; try exact Hlc2;
        try exact He1D; try exact He2D; try exact Hdom;
        try exact Hrestrict; try exact Hres.
      * intros HyD. apply Hy.
        pose proof (proj2 (lvars_fv_elem Dinput y) HyD).
        set_solver.
      * clear -Hy. set_solver.
      * intros σ v Hσ. symmetry. apply (Heq σ v Hσ).
    + reflexivity.
Qed.

Lemma typed_fiber_equiv_of_tm_equiv
    Σ τ m e1 e2 :
  tm_equiv_on m e1 e2 ->
  tm_total_equiv_on m e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1 ->
  m ⊨ ty_denote_gas 0 Σ τ e2 ->
  typed_fiber_equiv_on Σ τ m e1 e2.
Proof.
  intros Heq Htotal Hzero1 Hzero2.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [Hbasic1 _]]].
  destruct Hguard2 as [_ [_ [Hbasic2 _]]].
  apply basic_world_formula_models_iff in Hworld1 as [HlcΣ _].
  apply expr_basic_typing_formula_models_iff in Hbasic1
    as [HlcΣ1 [_ Hty1]].
  apply expr_basic_typing_formula_models_iff in Hbasic2
    as [HlcΣ2 [_ Hty2]].
  pose proof (basic_tm_has_ltype_lc Σ e1 (erase_ty τ) HlcΣ1 Hty1)
    as Hlc1.
  pose proof (basic_tm_has_ltype_lc Σ e2 (erase_ty τ) HlcΣ2 Hty2)
    as Hlc2.
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty1) as Hlv1.
  pose proof (basic_tm_has_ltype_lvars _ _ _ Hty2) as Hlv2.
  assert (Hres_projected :
      tm_result_equiv_projected_on m (dom Σ) (context_ty_lvars τ) e1 e2).
  {
    eapply tm_equiv_on_to_result_projected; eauto.
    - rewrite (tm_lvars_lc_eq_atoms e1 Hlc1).
      unfold lvars_of_atoms.
      intros v Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply Hlv1. unfold lvars_of_atoms.
      apply elem_of_map. exists a. split; [reflexivity|exact Ha].
    - rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
      unfold lvars_of_atoms.
      intros v Hv.
      apply elem_of_map in Hv as [a [-> Ha]].
      apply Hlv2. unfold lvars_of_atoms.
      apply elem_of_map. exists a. split; [reflexivity|exact Ha].
  }
  eapply typed_fiber_equiv_intro; eauto.
Qed.

Lemma typed_fiber_equiv_tm_equiv
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  tm_equiv_on m e1 e2.
Proof.
Admitted.
(*
  intros Hequiv σ v Hσ.
  pose proof (typed_fiber_equiv_result_open_at _ _ _ _ _ Hequiv)
    as Hres_open.
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (typed_fiber_equiv_term_lvars_env _ _ _ _ _ Hequiv)
    as Hlvars_env.
  pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv)
    as Hfv_env.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero2.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
  repeat rewrite res_models_and_iff in Hguard1.
  repeat rewrite res_models_and_iff in Hguard2.
  destruct Hguard1 as [_ [Hworld1 [_ Htotal1]]].
  destruct Hguard2 as [_ [_ [_ Htotal2]]].
  pose proof Hworld1 as Hworld_model.
  apply basic_world_formula_models_iff in Hworld1 as [HlcΣ [HΣdom _]].
  pose proof (expr_total_formula_to_atom_world e1 m Htotal1) as Htotal_atom1.
  pose proof (expr_total_formula_to_atom_world e2 m Htotal2) as Htotal_atom2.
  assert (HD_fv1 : fv_tm e1 ⊆ lvars_fv (dom Σ)) by set_solver.
  assert (HD_fv2 : fv_tm e2 ⊆ lvars_fv (dom Σ)) by set_solver.
  assert (HD_lvars1 : tm_lvars e1 ⊆ dom Σ).
  { intros z Hz. apply Hlvars_env. apply elem_of_union_l. exact Hz. }
  assert (HD_lvars2 : tm_lvars e2 ⊆ dom Σ).
  { intros z Hz. apply Hlvars_env. apply elem_of_union_r. exact Hz. }
  assert (HD_world : lvars_fv (dom Σ) ⊆ world_dom (m : WorldT)).
  { exact HΣdom. }
  assert (Hdir :
      forall es et,
        lc_tm es ->
        lc_tm et ->
        tm_lvars es ⊆ dom Σ ->
        tm_lvars et ⊆ dom Σ ->
        fv_tm es ⊆ lvars_fv (dom Σ) ->
        fv_tm et ⊆ lvars_fv (dom Σ) ->
        expr_total_on_atom_world es m ->
        (forall y (my : WfWorldT),
          y ∉ fv_tm e1 ∪ fv_tm e2 ∪ lvars_fv (dom Σ) ->
          world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
          res_restrict my (world_dom (m : WorldT)) = m ->
          my ⊨ formula_open 0 y
            (expr_result_formula_at (dom Σ) (tm_shift 0 es) (LVBound 0)) ->
          my ⊨ formula_open 0 y
            (expr_result_formula_at (dom Σ) (tm_shift 0 et) (LVBound 0))) ->
        forall σ v,
          (m : WorldT) σ ->
          tm_eval_in_store σ es v ->
          tm_eval_in_store σ et v).
  {
    intros es et Hlc_s Hlc_t Hlv_s Hlv_t Hfv_s Hfv_t Htotal_s
      Htransport σ0 v0 Hσ0 Heval_s.
    set (y := fresh_for
      (world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
       lvars_fv (dom Σ))).
    assert (Hyfresh_all :
        y ∉ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
          lvars_fv (dom Σ)).
    { subst y. apply fresh_for_not_in. }
    assert (Hyfresh :
        y ∉ fv_tm e1 ∪ fv_tm e2 ∪ lvars_fv (dom Σ)) by set_solver.
    assert (HyD : LVFree y ∉ dom Σ).
    {
      intros HyD.
      assert (Hyfv : y ∈ lvars_fv (dom Σ)).
      { apply lvars_fv_elem. exact HyD. }
      apply Hyfresh_all.
      set_solver.
    }
    destruct (expr_result_extension_witness_on_exists
      (lvars_fv (dom Σ)) es y Hfv_s ltac:(set_solver))
      as [F HF].
    assert (Happ : extension_applicable F m).
    {
      destruct HF as [_ _ [Hin Hout] _].
      constructor.
      - change (ext_in F ⊆ world_dom (m : WorldT)).
        rewrite Hin. exact HD_world.
      - change (ext_out F ## world_dom (m : WorldT)).
        rewrite Hout. set_solver.
    }
    destruct (res_extend_by_exists m F Happ) as [my Hext].
    assert (Hdom_my :
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
    {
      rewrite (res_extend_by_dom m F my Hext).
      destruct HF as [_ _ [_ Hout] _].
      change (world_dom (m : WorldT) ∪ ext_out F =
        world_dom (m : WorldT) ∪ {[y]}).
      rewrite Hout. reflexivity.
    }
    assert (Hrestrict_my : res_restrict my (world_dom (m : WorldT)) = m).
    { exact (res_extend_by_restrict_base m F my Hext). }
    assert (Hres_s_open :
        my ⊨ formula_open 0 y
          (expr_result_formula_at (dom Σ) (tm_shift 0 es) (LVBound 0))).
    {
      rewrite formula_open_expr_result_formula_at_shift0.
      - eapply expr_result_formula_at_of_result_extends_on; eauto.
      - exact HlcΣ.
      - set_solver.
      - exact Hlc_s.
      - set_solver.
    }
    pose proof (Htransport y my Hyfresh Hdom_my Hrestrict_my Hres_s_open)
      as Hres_t_open.
    rewrite formula_open_expr_result_formula_at_shift0 in Hres_t_open
      by (exact HlcΣ || exact Hlc_t || set_solver).
    set (σy := ((σ0 : StoreT) ∪ ({[y := v0]} : StoreT)) : StoreT).
    assert (Hσy_my : (my : WorldT) σy).
    {
      apply (proj2 (resA_extend_by_store_iff m F my σy Hext)).
	      exists σ0.
	      set (we := expr_result_output_world es y
	        (store_restrict σ0 (lvars_fv (dom Σ)))).
	      exists we, ({[y := v0]} : StoreT).
        split; [exact Hσ0|].
        split.
        { pose proof HF as [_ _ [Hin _] Hrel].
	          change (ext_rel F (store_restrict σ0 (ext_in F)) we).
	          subst we. rewrite Hin.
	          apply Hrel.
	          rewrite storeA_restrict_dom.
	          rewrite (wfworld_store_dom m σ0 Hσ0).
	          apply set_eq. intros a. rewrite elem_of_intersection.
          split.
          - intros [_ Ha]. exact Ha.
          - intros Ha. split; [exact (HD_world a Ha)|exact Ha]. }
        split.
        { eapply expr_result_extension_apply_total_store_on.
          - exact HF.
          - rewrite storeA_restrict_dom.
            rewrite (wfworld_store_dom m σ0 Hσ0).
            apply set_eq. intros a. rewrite elem_of_intersection.
            split.
            + intros [_ Ha]. exact Ha.
            + intros Ha. split; [exact (HD_world a Ha)|exact Ha].
          - destruct HF as [_ _ [_ _] Hrel].
	          apply Hrel.
	          rewrite storeA_restrict_dom.
	          rewrite (wfworld_store_dom m σ0 Hσ0).
	          apply set_eq. intros a. rewrite elem_of_intersection.
	          split.
            + intros [_ Ha]. exact Ha.
            + intros Ha. split; [exact (HD_world a Ha)|exact Ha].
          - apply (proj2 (tm_eval_in_store_restrict_fv_subset
	            σ0 es v0 (lvars_fv (dom Σ)) Hfv_s)).
            exact Heval_s. }
        { subst σy. reflexivity. }
	    }
    pose proof (expr_result_formula_at_models_elim
      (dom Σ) et y my Hlv_t HyD Hres_t_open σy Hσy_my)
      as [_ [v' [Hy_lookup Heval_t_l]]].
    assert (Hy_lookup_atom : (σy : StoreT) !! y = Some v').
    {
      change (((lstore_lift_free σy : LStoreT) : gmap logic_var value) !!
        LVFree y = Some v') in Hy_lookup.
      rewrite lstore_lift_free_lookup_free in Hy_lookup.
      exact Hy_lookup.
    }
    assert (Hy_lookup_v0 : (σy : StoreT) !! y = Some v0).
    {
	      subst σy.
	      change ((((σ0 : StoreT) ∪ ({[y := v0]} : StoreT)) : gmap atom value)
	        !! y = Some v0).
      transitivity (({[y := v0]} : gmap atom value) !! y).
      - apply (lookup_union_r (M:=gmap atom) (A:=value)).
        apply not_elem_of_dom.
        rewrite (wfworld_store_dom m σ0 Hσ0). set_solver.
      - apply map_lookup_singleton.
	    }
    assert (Hv_eq : Some v0 = Some v').
    { rewrite <- Hy_lookup_v0. exact Hy_lookup_atom. }
    inversion Hv_eq. subst v'.
    change (tm_eval_in_store σy et v0) in Heval_t_l.
    eapply tm_eval_in_store_agree_on_fv; [|exact Heval_t_l].
    subst σy.
    symmetry.
    apply storeA_restrict_union_ignore_r.
    change (dom ({[y := v0]} : gmap atom value) ## fv_tm et).
    assert (Hy_et : y ∉ fv_tm et).
    {
      intros Hyet.
      assert (Hyfv : y ∈ lvars_fv (dom Σ)).
      { apply Hfv_t. exact Hyet. }
      clear -Hyfresh Hyfv. set_solver.
    }
    intros a Ha_dom Ha_fv.
    apply elem_of_dom in Ha_dom as [va Ha_lookup].
    apply (proj1 (lookup_singleton_Some y a v0 va)) in Ha_lookup
      as [-> _].
    exact (Hy_et Ha_fv).
  }
  split.
  - eapply Hdir; eauto.
    intros y my Hy Hdom Hrestrict Hres.
    apply (proj1 (Hres_open y my Hy Hdom Hrestrict)). exact Hres.
  - eapply Hdir; eauto.
    intros y my Hy Hdom Hrestrict Hres.
    apply (proj2 (Hres_open y my Hy Hdom Hrestrict)). exact Hres.
Qed.
*)

Lemma typed_fiber_equiv_tapp_tm_equiv_frame
    (Σ : lty_env) τ (T : ty) e1 e2 (m w : WfWorldT) y :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  world_dom (w : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict w (world_dom (m : WorldT)) = m ->
  wfworld_closed_on ({[y]} : aset) w ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv (dom Σ) ->
  tm_equiv_on w
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hclosed_y Hye HyΣ.
  pose proof (typed_fiber_equiv_tm_equiv _ _ _ _ _ Hequiv) as Heq_m.
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv) as Hscope_env.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [_ _]]].
  pose proof Hworld as Hworld_model.
  apply basic_world_formula_models_iff in Hworld as [_ [HΣdom _]].
  assert (Hfv_m : fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT)).
  {
    intros x Hx.
    apply HΣdom. apply Hscope_env. exact Hx.
  }
  assert (Heq_w : tm_equiv_on w e1 e2).
  { eapply tm_equiv_full_world_extend_fresh; eauto. }
  assert (Hle_mw : m ⊑ w).
  {
    change ((m : WorldT) =
      raw_restrict (w : WorldT) (world_dom (m : WorldT))).
    symmetry.
    exact (f_equal (fun r : WfWorldT => (r : WorldT)) Hrestrict).
  }
  assert (Hclosed_env_w : wfworld_closed_on (lvars_fv (dom Σ)) w).
  {
    eapply wfworld_closed_on_le.
    - exact HΣdom.
    - exact Hle_mw.
    - eapply basic_world_formula_wfworld_closed_on_dom.
      exact Hworld_model.
  }
  eapply tm_equiv_tapp_fvar.
  - eapply wfworld_closed_on_mono.
    + cbn [fv_tm fv_value]. unfold tapp_tm. cbn [fv_tm fv_value].
      intros x Hx. apply elem_of_union in Hx as [Hx|Hx].
      * apply elem_of_union in Hx as [Hx|Hx].
        -- apply elem_of_union_l. apply Hscope_env.
           apply elem_of_union_l. exact Hx.
        -- apply elem_of_union_r. exact Hx.
      * apply elem_of_union in Hx as [Hx|Hx].
        -- apply elem_of_union_l. apply Hscope_env.
           apply elem_of_union_r. exact Hx.
        -- apply elem_of_union_r. exact Hx.
    + match goal with
      | |- wfworld_closed_on ?X w =>
          eapply (wfworld_closed_on_mono X
            (lvars_fv (dom Σ) ∪ ({[y]} : aset)) w)
      end.
      * cbn [fv_tm fv_value]. unfold tapp_tm. cbn [fv_tm fv_value].
        set_solver.
      * eapply (wfworld_closed_on_union
          (lvars_fv (dom Σ)) ({[y]} : aset));
          [exact Hclosed_env_w|exact Hclosed_y].
  - exact Hlc1.
  - exact Hlc2.
  - exact Heq_w.
Qed.

Lemma tm_result_equiv_projected_tapp_fvar_frame
    (Σ : lty_env) τ T τr e1 e2 (m w : WfWorldT) y :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  world_dom (w : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict w (world_dom (m : WorldT)) = m ->
  wfworld_closed_on ({[y]} : aset) w ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv (dom Σ) ->
  tm_result_equiv_projected_on w
    (dom (lty_env_open_one 0 y (typed_lty_env_bind Σ T)))
    (context_ty_lvars (cty_open 0 y τr))
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)).
Proof.
Admitted.
(*
  intros Hequiv Hdom Hrestrict Hclosed_y Hye HyΣ.
  assert (HlcΣ : lc_lvars (dom Σ)).
  {
    pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_m.
    pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero_m) as Hguard.
    repeat rewrite res_models_and_iff in Hguard.
    destruct Hguard as [_ [Hworld [_ _]]].
    apply basic_world_formula_models_iff in Hworld as [HlcΣ _].
    exact HlcΣ.
  }
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv) as [Hlc1 Hlc2].
  eapply tm_equiv_on_to_result_open_at.
  - replace (lty_env_open_one 0 y (typed_lty_env_bind Σ T))
      with (<[LVFree y := T]> Σ).
    + rewrite dom_insert_L.
      unfold lc_lvars. intros [k|a] Hv; cbn [lc_logic_var_key]; [|exact I].
      apply elem_of_union in Hv as [Hv|Hv]; [set_solver|].
      exact (HlcΣ (LVBound k) Hv).
    + symmetry. apply typed_lty_env_bind_open_current.
      * intros HyD. apply HyΣ. apply (proj2 (lvars_fv_elem (dom Σ) y)).
        exact HyD.
      * exact HlcΣ.
  - apply lc_tapp_tm; [exact Hlc1|constructor].
  - apply lc_tapp_tm; [exact Hlc2|constructor].
  - rewrite tm_lvars_tapp_tm_fvar.
    pose proof (typed_fiber_equiv_term_lvars_env _ _ _ _ _ Hequiv) as Hfv.
    intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + destruct v as [k|a].
      * exfalso. exact ((tm_lvars_lc e1 Hlc1) (LVBound k) Hv).
      * apply elem_of_dom.
        assert (HaΣ : LVFree a ∈ dom Σ).
        { apply Hfv. apply elem_of_union_l. exact Hv. }
        apply elem_of_dom in HaΣ as [U HU].
        exists U. rewrite lty_env_open_one_typed_bind_lookup_free_ne.
        -- exact HU.
        -- intros ->. apply Hye. apply elem_of_union_l.
           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
    + apply elem_of_singleton in Hv as ->.
      apply elem_of_dom. exists T.
      apply lty_env_open_one_typed_bind_lookup_current.
  - rewrite tm_lvars_tapp_tm_fvar.
    pose proof (typed_fiber_equiv_term_lvars_env _ _ _ _ _ Hequiv) as Hfv.
    intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + destruct v as [k|a].
      * exfalso. exact ((tm_lvars_lc e2 Hlc2) (LVBound k) Hv).
      * apply elem_of_dom.
        assert (HaΣ : LVFree a ∈ dom Σ).
        { apply Hfv. apply elem_of_union_r. exact Hv. }
        apply elem_of_dom in HaΣ as [U HU].
        exists U. rewrite lty_env_open_one_typed_bind_lookup_free_ne.
        -- exact HU.
        -- intros ->. apply Hye. apply elem_of_union_r.
           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
    + apply elem_of_singleton in Hv as ->.
      apply elem_of_dom. exists T.
      apply lty_env_open_one_typed_bind_lookup_current.
  - eapply typed_fiber_equiv_tapp_tm_equiv_frame; eauto.
Qed.
*)

Lemma ty_denote_gas_zero_tapp_fvar_from_result_graph
    gas (Σ : lty_env) τfun τx τr e1 e2
    (m w : WfWorldT) y :
  typed_fiber_equiv_on Σ τfun m e1 e2 ->
  erase_ty τfun = erase_ty (CTArrow τx τr) ->
  world_dom (w : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict w (world_dom (m : WorldT)) = m ->
  w ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (tapp_tm e1 (vfvar y)) ->
  w ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)) ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv (dom Σ) ->
  w ⊨ ty_denote_gas 0
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Herase Hdom Hrestrict Hsrc Harg Hyτx Hyτr Hye HyΣ.
  set (Σy := lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx))).
  pose proof (ty_denote_gas_guard gas Σy (cty_open 0 y τr)
    (tapp_tm e1 (vfvar y)) w Hsrc) as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [Hwf [Hworld [Hbasic_src Htotal_src]]].
  pose proof (ty_denote_gas_guard gas Σy
    (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y)) w Harg)
    as Hguard_arg.
  repeat rewrite res_models_and_iff in Hguard_arg.
  destruct Hguard_arg as [_ [_ [_ Htotal_arg]]].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv) as [Hlc1 Hlc2].
  pose proof (typed_fiber_equiv_term_lvars_env _ _ _ _ _ Hequiv) as Hlv_env.
  pose proof (typed_fiber_equiv_tm_equiv _ _ _ _ _ Hequiv) as Heq_m.
  pose proof (typed_fiber_equiv_total_equiv _ _ _ _ _ Hequiv) as Htotal_m.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_fun_src.
  pose proof (ty_denote_gas_guard_of_zero Σ τfun e1 m Hzero_fun_src)
    as Hguard_fun_src.
  repeat rewrite res_models_and_iff in Hguard_fun_src.
  destruct Hguard_fun_src as [_ [Hworld_fun_src [_ _]]].
  apply basic_world_formula_models_iff in Hworld_fun_src
    as [_ [HΣdom_m _]].
  assert (Hfv_m : fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT)).
  {
    pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv)
      as Hfv_env.
    intros a Ha. exact (HΣdom_m a (Hfv_env a Ha)).
  }
  assert (Heq_w : tm_equiv_on w e1 e2).
  { eapply tm_equiv_full_world_extend_fresh; eauto. }
  assert (Htotal_w : tm_total_equiv_on w e1 e2).
  { eapply tm_total_equiv_full_world_extend_fresh; eauto. }
  assert (Happs_lvars_env :
      lvars_of_atoms
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) ⊆ dom Σy).
  {
    subst Σy.
    unfold tapp_tm. cbn [fv_tm fv_value].
    intros v Hv.
    unfold lvars_of_atoms in Hv.
    apply elem_of_map in Hv as [a [-> Ha]].
    repeat rewrite lty_env_open_one_dom.
    rewrite typed_lty_env_bind_dom.
    unfold set_swap.
    apply elem_of_map.
    destruct (decide (a = y)) as [->|Hay].
    - exists (LVBound 0). split; [rewrite swap_l; reflexivity|].
      apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    - exists (LVFree a). split.
      + unfold swap. repeat destruct decide; try congruence; reflexivity.
      + apply elem_of_union_l.
        unfold lvars_shift_from. apply elem_of_map.
        exists (LVFree a). split; [reflexivity|].
        apply Hlv_env.
        rewrite (tm_lvars_lc_eq_atoms e1 Hlc1).
        rewrite (tm_lvars_lc_eq_atoms e2 Hlc2).
        unfold lvars_of_atoms.
        cbn [fv_tm fv_value] in Ha.
        unfold tapp_tm in Ha.
        cbn [fv_tm fv_value] in Ha.
        set_solver.
  }
  assert (Hclosed_apps :
      wfworld_closed_on
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
         fv_tm (tapp_tm e2 (vfvar y))) w).
  {
    eapply basic_world_formula_wfworld_closed_on_atoms; eauto.
  }
  apply ty_denote_gas_zero_of_guard.
  repeat rewrite res_models_and_iff. split; [exact Hwf|].
  split; [exact Hworld|].
  split.
  - apply expr_basic_typing_formula_models_iff.
    apply basic_world_formula_models_iff in Hworld as [HlcΣy [HscopeΣy _]].
    split; [exact HlcΣy|].
    split; [exact HscopeΣy|].
    rewrite cty_open_preserves_erasure.
    eapply basic_tm_has_ltype_tapp_tm_lvar.
    + exact HlcΣy.
    + eapply basic_tm_has_ltype_weaken.
      * eapply basic_tm_has_ltype_open_result_target_fun.
        -- exact Herase.
        -- unfold typed_total_equiv_on.
           split; [exact (typed_fiber_equiv_tm_equiv _ _ _ _ _ Hequiv)|].
           split; [exact (typed_fiber_equiv_total_equiv _ _ _ _ _ Hequiv)|].
           split; [exact (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv)|].
           exact (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv).
        -- exact Hye.
      * apply map_subseteq_spec. intros v T Hlook.
        unfold relevant_env, lty_env_restrict_lvars in Hlook.
        change ((storeA_restrict Σy
          (relevant_lvars (cty_open 0 y τr) (tapp_tm e2 (vfvar y)))
          : gmap logic_var ty) !! v = Some T) in Hlook.
        apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
        exact Hlook.
    + eapply BVT_FVar.
      apply lty_env_open_one_typed_bind_lookup_current.
  - eapply tm_equiv_total.
    + eapply tm_total_equiv_tapp_fvar; eauto.
    + apply lc_tapp_tm; [exact Hlc2|constructor].
    + intros a Ha.
      apply basic_world_formula_models_iff in Hworld as [_ [HscopeΣy _]].
      apply HscopeΣy.
      apply lvars_fv_elem. apply Happs_lvars_env.
      unfold lvars_of_atoms. apply elem_of_map.
      exists a. split; [reflexivity|].
      apply elem_of_union_r. exact Ha.
    + exact Htotal_src.
Qed.

Lemma typed_fiber_equiv_arrow_open_app_fvar_mid
    gas (Σ : lty_env) τx τr e1 e2
    (m my : WfWorldT) y :
  typed_fiber_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv (dom Σ) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (tapp_tm e1 (vfvar y)) ->
  typed_fiber_equiv_on
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr) my
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)) /\
  my ⊨ ty_denote_gas 0
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hrestrict Hyτx Hyτr Hye HyΣ Harg Hsrc.
  pose proof (ty_denote_gas_zero_tapp_fvar_from_result_graph
    gas Σ (CTArrow τx τr) τx τr e1 e2 m my y
    Hequiv eq_refl Hdom Hrestrict Hsrc Harg Hyτx Hyτr Hye HyΣ)
    as Hzero_mid.
  assert (Hclosed_y : wfworld_closed_on ({[y]} : aset) my).
  {
    pose proof (ty_denote_gas_guard gas
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
      my Harg) as Hguard_arg.
    repeat rewrite res_models_and_iff in Hguard_arg.
    destruct Hguard_arg as [_ [Hworld_arg [_ _]]].
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld_arg].
    intros v Hv.
    unfold lvars_of_atoms in Hv.
	    apply elem_of_map in Hv as [a [-> Ha]].
	    apply elem_of_singleton in Ha as ->.
	    rewrite lty_env_open_one_dom.
	    unfold set_swap. apply elem_of_map.
	    exists (LVBound 0). split.
	    - rewrite swap_l. reflexivity.
	    - rewrite typed_lty_env_bind_dom.
	      apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  split; [|exact Hzero_mid].
  eapply typed_fiber_equiv_intro.
  - eapply (tm_result_equiv_projected_tapp_fvar_frame
      Σ (CTArrow τx τr) (erase_ty τx) τr e1 e2 m my y); eauto.
  - eapply tm_total_equiv_of_ty_denote_source_target_zero;
      [exact Hsrc|exact Hzero_mid].
  - apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hsrc.
  - exact Hzero_mid.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_arrow_body
    (gas : nat)
    (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_fiber_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx)) τr
          (tapp_tm (tm_shift 0 e1) (vbvar 0)))) ->
  m ⊨
    FForall
      (FImpl
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx))
          (cty_shift 0 τx) (tret (vbvar 0)))
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx)) τr
          (tapp_tm (tm_shift 0 e2) (vbvar 0)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (typed_fiber_equiv_term_lc Σ (CTArrow τx τr) m e1 e2 Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTArrow τx τr) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  eapply res_models_forall_full_world_map; [exact Hscope_tgt| |exact Hsrc].
  exists (fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τx ∪ fv_cty τr ∪ lvars_fv (dom Σ)).
  intros y Hy my Hdom Hrestrict Hopened.
  rewrite !formula_open_impl in Hopened |- *.
  assert (Hopened_scope :
      formula_scoped_in_world my
        (formula_open 0 y
          (FImpl
            (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx))
              (cty_shift 0 τx) (tret (vbvar 0)))
            (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx)) τr
              (tapp_tm (tm_shift 0 e2) (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_tgt.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite formula_open_impl in Hopened_scope.
  eapply res_models_impl_intro; [exact Hopened_scope|].
  intros Harg.
  pose proof (res_models_impl_elim my _ _ Hopened Harg) as Hconseq.
  pose proof Harg as Harg_norm.
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind Σ (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg_norm
    by (rewrite ?typed_lty_env_bind_lvars_fv_dom, ?cty_shift_fv;
        cbn [fv_tm fv_value]; clear -Hy; better_set_solver).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg_norm.
  type_open_env_syntax_norm_in Harg_norm.
  ty_denote_open_one_norm_in Hconseq.
  ty_denote_open_one_norm.
  destruct (typed_fiber_equiv_arrow_open_app_fvar_mid
    gas Σ τx τr e1 e2 m my y) as [Hmid Hzero_mid].
  - exact Hequiv.
  - exact Hdom.
  - exact Hrestrict.
  - clear -Hy. better_set_solver.
  - clear -Hy. better_set_solver.
  - clear -Hy. better_set_solver.
  - clear -Hy. better_set_solver.
  - exact Harg_norm.
  - exact Hconseq.
  - eapply IH; [exact Hmid|exact Hconseq].
Qed.

Lemma typed_fiber_equiv_wand_open_app_fvar_mid
    gas (Σ : lty_env) τx τr e1 e2
    (m n : WfWorldT) y (Hc : world_compat n m) :
  typed_fiber_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ {[y]} ->
  y ∉ fv_cty τx ->
  y ∉ fv_cty τr ->
  y ∉ fv_tm e1 ∪ fv_tm e2 ->
  y ∉ lvars_fv (dom Σ) ->
  n ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y (cty_shift 0 τx))
    (tret (vfvar y)) ->
  res_product n m Hc ⊨ ty_denote_gas gas
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (tapp_tm e1 (vfvar y)) ->
  typed_fiber_equiv_on
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (res_product n m Hc)
    (tapp_tm e1 (vfvar y))
    (tapp_tm e2 (vfvar y)) /\
  res_product n m Hc ⊨ ty_denote_gas 0
    (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
    (cty_open 0 y τr)
    (tapp_tm e2 (vfvar y)).
Proof.
  intros Hequiv Hdom Hyτx Hyτr Hye HyΣ Harg Hsrc.
  pose proof (res_restrict_eq_of_le m (res_product n m Hc)
    (res_product_le_r n m Hc)) as Hrestrict.
  pose proof (ty_denote_gas_zero_tapp_fvar_from_result_graph
    gas Σ (CTWand τx τr) τx τr e1 e2 m (res_product n m Hc) y
    Hequiv eq_refl Hdom Hrestrict Hsrc) as Hzero_mid.
  assert (Harg_prod :
      res_product n m Hc ⊨ ty_denote_gas gas
        (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
        (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))).
  {
    eapply res_models_kripke; [apply res_product_le_l|exact Harg].
  }
  specialize (Hzero_mid
    Harg_prod
    Hyτx Hyτr Hye HyΣ).
  assert (Hclosed_y : wfworld_closed_on ({[y]} : aset) (res_product n m Hc)).
  {
    pose proof (ty_denote_gas_guard gas
      (lty_env_open_one 0 y (typed_lty_env_bind Σ (erase_ty τx)))
      (cty_open 0 y (cty_shift 0 τx)) (tret (vfvar y))
      (res_product n m Hc) Harg_prod) as Hguard_arg.
    repeat rewrite res_models_and_iff in Hguard_arg.
    destruct Hguard_arg as [_ [Hworld_arg [_ _]]].
    eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld_arg].
    intros v Hv.
    unfold lvars_of_atoms in Hv.
	    apply elem_of_map in Hv as [a [-> Ha]].
	    apply elem_of_singleton in Ha as ->.
	    rewrite lty_env_open_one_dom.
	    unfold set_swap. apply elem_of_map.
	    exists (LVBound 0). split.
	    - rewrite swap_l. reflexivity.
	    - rewrite typed_lty_env_bind_dom.
	      apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  split; [|exact Hzero_mid].
  eapply typed_fiber_equiv_intro.
  - eapply (tm_result_equiv_projected_tapp_fvar_frame
      Σ (CTWand τx τr) (erase_ty τx) τr e1 e2 m
      (res_product n m Hc) y); eauto.
  - eapply tm_total_equiv_of_ty_denote_source_target_zero;
      [exact Hsrc|exact Hzero_mid].
  - apply ty_denote_gas_zero_of_guard.
    eapply ty_denote_gas_guard. exact Hsrc.
  - exact Hzero_mid.
Qed.

Lemma ty_denote_gas_tm_fiber_equiv_wand_body
    (gas : nat)
    (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_fiber_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ (CTWand τx τr) m e1 e2 ->
  m ⊨
    FBWand 1
      (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))
      (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx)) τr
        (tapp_tm (tm_shift 0 e1) (vbvar 0))) ->
  m ⊨
    FBWand 1
      (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx))
        (cty_shift 0 τx) (tret (vbvar 0)))
      (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τx)) τr
        (tapp_tm (tm_shift 0 e2) (vbvar 0))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (typed_fiber_equiv_term_lc Σ (CTWand τx τr) m e1 e2 Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTWand τx τr) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  destruct (res_models_fbwand_rev _ _ _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_fbwand_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    fv_cty τx ∪ fv_cty τr ∪ lvars_fv (dom Σ)).
  intros η n Hc Hbind Hfresh Hdom Harg.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite !formula_open_env_singleton in Harg |- *.
  assert (Hatoms : open_env_atoms (<[0 := y]> (∅ : gmap nat atom)) = {[y]}).
  {
    rewrite open_env_atoms_insert by apply lookup_empty.
    rewrite open_env_atoms_empty. set_solver.
  }
  assert (Hy :
      y ∉ fv_tm e1 ∪ fv_tm e2 ∪ fv_cty τx ∪ fv_cty τr ∪
        lvars_fv (dom Σ)).
  {
    rewrite Hatoms in Hfresh.
    clear -Hfresh. better_set_solver.
  }
  pose proof Harg as Harg_norm.
  rewrite (formula_open_ty_denote_gas_singleton 0 y gas
    (typed_lty_env_bind Σ (erase_ty τx))
    (cty_shift 0 τx) (tret (vbvar 0))) in Harg_norm
    by (rewrite ?typed_lty_env_bind_lvars_fv_dom, ?cty_shift_fv;
        cbn [fv_tm fv_value]; clear -Hy; better_set_solver).
  change (open_tm 0 (vfvar y) (tret (vbvar 0)))
    with (tret (vfvar y)) in Harg_norm.
  type_open_env_syntax_norm_in Harg_norm.
  pose proof (Hsrc_rev (<[0 := y]> (∅ : gmap nat atom)) n Hc Hbind)
    as Hsrc_open.
  rewrite formula_open_env_singleton in Hsrc_open.
  assert (Hfresh_src : open_env_atoms (<[0 := y]> (∅ : gmap nat atom)) ## Lsrc).
  {
    rewrite Hatoms.
    rewrite Hatoms in Hfresh.
    clear -Hfresh. better_set_solver.
  }
  specialize (Hsrc_open Hfresh_src Hdom Harg).
  rewrite formula_open_env_singleton in Hsrc_open.
  ty_denote_open_one_norm_in Hsrc_open.
  ty_denote_open_one_norm.
  destruct (typed_fiber_equiv_wand_open_app_fvar_mid
    gas Σ τx τr e1 e2 m n y Hc) as [Hmid Hzero_mid].
  - exact Hequiv.
  - rewrite Hatoms in Hdom. exact Hdom.
  - clear -Hy. better_set_solver.
  - clear -Hy. better_set_solver.
  - clear -Hy. better_set_solver.
  - clear -Hy. better_set_solver.
  - exact Harg_norm.
  - exact Hsrc_open.
  - eapply IH; [exact Hmid|exact Hsrc_open].
Qed.

Lemma ty_denote_gas_tm_fiber_equiv
    gas Σ τ e1 e2 (m : WfWorldT) :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  m ⊨ ty_denote_gas gas Σ τ e1 ->
  m ⊨ ty_denote_gas gas Σ τ e2.
Proof.
  revert Σ τ e1 e2 m.
  induction gas as [|gas IH]; intros Σ τ e1 e2 m Hequiv Hden.
  - eapply typed_fiber_equiv_zero_tgt. exact Hequiv.
  - cbn [ty_denote_gas] in Hden |- *.
    pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
    rewrite res_models_and_iff in Hden |- *.
    destruct Hden as [Hzero_src Hbody].
    split.
    + eapply ty_denote_gas_guard_of_zero.
      exact Hzero_tgt.
    + destruct τ.
      * eapply ty_denote_gas_tm_fiber_equiv_over_body; eauto.
      * eapply ty_denote_gas_tm_fiber_equiv_under_body; eauto.
      * rewrite res_models_and_iff in Hbody |- *.
        destruct Hbody as [Hleft Hright]. split.
        -- eapply IH.
           ++ eapply typed_fiber_equiv_inter_l. exact Hequiv.
           ++ exact Hleft.
        -- eapply IH.
           ++ eapply typed_fiber_equiv_inter_r. exact Hequiv.
           ++ exact Hright.
      * pose proof (res_models_scoped _ _ Hbody) as Hscope_body.
        pose proof (proj1 (formula_scoped_or_iff m _ _) Hscope_body)
          as [Hscope_left Hscope_right].
        assert (Hscope_left_tgt :
            formula_scoped_in_world m (ty_denote_gas gas Σ τ1 e2)).
        {
          eapply ty_denote_gas_scope_from_zero_any.
          eapply ty_denote_gas_zero_union_l.
          exact Hzero_tgt.
        }
        assert (Hscope_right_tgt :
            formula_scoped_in_world m (ty_denote_gas gas Σ τ2 e2)).
        {
          eapply ty_denote_gas_scope_from_zero_any.
          eapply ty_denote_gas_zero_union_r.
          exact Hzero_tgt.
        }
        apply (proj1 (res_models_or_iff m _ _ Hscope_body)) in Hbody
          as [Hleft|Hright].
        -- eapply res_models_or_intro_l_from_model.
           ++ eapply IH.
              ** eapply typed_fiber_equiv_union_l. exact Hequiv.
              ** exact Hleft.
           ++ exact Hscope_right_tgt.
        -- eapply res_models_or_intro_r_from_model.
           ++ exact Hscope_left_tgt.
           ++ eapply IH.
              ** eapply typed_fiber_equiv_union_r. exact Hequiv.
              ** exact Hright.
      * eapply ty_denote_gas_tm_fiber_equiv_sum_body.
        -- exact IH.
        -- exact Hequiv.
        -- exact Hbody.
      * eapply ty_denote_gas_tm_fiber_equiv_arrow_body.
        -- exact IH.
        -- exact Hequiv.
        -- exact Hbody.
      * eapply ty_denote_gas_tm_fiber_equiv_wand_body.
        -- exact IH.
        -- exact Hequiv.
        -- exact Hbody.
Qed.

End TypeDenote.
