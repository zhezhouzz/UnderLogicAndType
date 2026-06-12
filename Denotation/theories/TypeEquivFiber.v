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

Lemma formula_fv_open_sum_body_obs gas Σ τ1 τ2 y :
  formula_fv
    (formula_open 0 y
      (FPlus
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
          (cty_shift 0 τ1) (tret (vbvar 0)))
        (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
          (cty_shift 0 τ2) (tret (vbvar 0))))) ⊆
  lvars_fv (dom Σ) ∪
    lvars_fv (context_ty_lvars (CTSum τ1 τ2)) ∪ {[y]}.
Proof.
  etransitivity; [apply formula_open_fv_subset|].
  rewrite formula_fv_plus.
  intros a Ha.
  apply elem_of_union in Ha as [Hab|Ha].
  - apply elem_of_union in Hab as [Ha|Ha].
    + pose proof (ty_denote_gas_fv_subset gas
        (typed_lty_env_bind Σ (erase_ty τ1))
        (cty_shift 0 τ1) (tret (vbvar 0)) a Ha) as HaΣ.
      rewrite typed_lty_env_bind_lvars_fv_dom in HaΣ.
      apply elem_of_union_l. apply elem_of_union_l. exact HaΣ.
    + pose proof (ty_denote_gas_fv_subset gas
        (typed_lty_env_bind Σ (erase_ty τ1))
        (cty_shift 0 τ2) (tret (vbvar 0)) a Ha) as HaΣ.
      rewrite typed_lty_env_bind_lvars_fv_dom in HaΣ.
      apply elem_of_union_l. apply elem_of_union_l. exact HaΣ.
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
  intros Hequiv Hsrc.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero_src.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ (CTSum τ1 τ2) e1 m Hzero_src)
    as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [_ [Hworld_src _]].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ _].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas) Σ (CTSum τ1 τ2) e2
    m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  pose proof (typed_fiber_equiv_result_projected
    Σ (CTSum τ1 τ2) m e1 e2 Hequiv) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom Σ) ∪ lvars_fv (context_ty_lvars (CTSum τ1 τ2))).
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
            (FPlus
              (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
                (cty_shift 0 τ1) (tret (vbvar 0)))
              (ty_denote_gas gas (typed_lty_env_bind Σ (erase_ty τ1))
                (cty_shift 0 τ2) (tret (vbvar 0))))))).
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
      lvars_fv (context_ty_lvars (CTSum τ1 τ2)) ∪ {[y]})).
  - apply formula_fv_open_sum_body_obs.
  - exact Hproj_obs.
Qed.

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

Local Lemma res_restrict_eq_store_lift
    (m n : WfWorldT) X σ :
  res_restrict m X = res_restrict n X ->
  (m : WorldT) σ ->
  exists τ,
    (n : WorldT) τ /\
    store_restrict τ X = store_restrict σ X.
Proof.
  intros Hproj Hσ.
  assert ((res_restrict m X : WorldT) (store_restrict σ X)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  rewrite Hproj in H.
  cbn [res_restrict raw_world raw_worldA world_stores] in H.
  destruct H as [τ [Hτ HτX]].
  exists τ. split; [exact Hτ|exact HτX].
Qed.

Lemma typed_fiber_equiv_tm_equiv
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  tm_equiv_on m e1 e2.
Proof.
  intros Hequiv σ v Hσ.
  pose proof (typed_fiber_equiv_result_projected _ _ _ _ _ Hequiv)
    as [H12 H21].
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv)
    as [Hlc1 Hlc2].
  pose proof (typed_fiber_equiv_term_lvars_env _ _ _ _ _ Hequiv)
    as Hlv_env.
  pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv)
    as Hfv_env.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero1.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero1) as Hguard1.
  repeat rewrite res_models_and_iff in Hguard1.
  destruct Hguard1 as [_ [Hworld1 [_ Htotal1]]].
  pose proof Hworld1 as Hworld_model.
  apply basic_world_formula_models_iff in Hworld1 as [HlcΣ [HΣdom _]].
  pose proof (expr_total_formula_to_atom_world e1 m Htotal1) as Htotal1_atom.
  assert (HD_world : lvars_fv (dom Σ) ⊆ world_dom (m : WorldT)).
  { exact HΣdom. }
  assert (Hfv1 : fv_tm e1 ⊆ lvars_fv (dom Σ)).
  { intros a Ha. apply Hfv_env. apply elem_of_union_l. exact Ha. }
  assert (Hfv2 : fv_tm e2 ⊆ lvars_fv (dom Σ)).
  { intros a Ha. apply Hfv_env. apply elem_of_union_r. exact Ha. }
  assert (Hlv1 : tm_lvars e1 ⊆ dom Σ).
  { intros z Hz. apply Hlv_env. apply elem_of_union_l. exact Hz. }
  assert (Hlv2 : tm_lvars e2 ⊆ dom Σ).
  { intros z Hz. apply Hlv_env. apply elem_of_union_r. exact Hz. }
  assert (Hdir :
      forall es et,
        lc_tm es ->
        lc_tm et ->
        tm_lvars es ⊆ dom Σ ->
        tm_lvars et ⊆ dom Σ ->
        fv_tm es ⊆ lvars_fv (dom Σ) ->
        fv_tm et ⊆ lvars_fv (dom Σ) ->
        expr_total_on_atom_world es m ->
        tm_result_refines_projected_on m (dom Σ) (context_ty_lvars τ) es et ->
        forall σ0 v0,
          (m : WorldT) σ0 ->
          tm_eval_in_store σ0 es v0 ->
          tm_eval_in_store σ0 et v0).
  {
    intros es et Hlc_s Hlc_t Hlv_s Hlv_t Hfv_s Hfv_t Htotal_s
      Htransport σ0 v0 Hσ0 Heval_s.
    set (r := fresh_for
      (world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
       lvars_fv (dom Σ))).
    assert (Hrfresh_all :
        r ∉ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
          lvars_fv (dom Σ)).
    { subst r. apply fresh_for_not_in. }
    assert (Hrfresh :
        r ∉ fv_tm es ∪ fv_tm et ∪ lvars_fv (dom Σ)).
    {
      clear -Hrfresh_all Hfv_s Hfv_t.
      set_solver.
    }
    assert (HrD : LVFree r ∉ dom Σ).
    {
      intros HrD.
      assert (Hrfv : r ∈ lvars_fv (dom Σ)).
      { apply lvars_fv_elem. exact HrD. }
      clear -Hrfresh_all Hrfv. set_solver.
    }
    destruct (expr_result_extension_witness_on_exists
      (lvars_fv (dom Σ)) es r Hfv_s ltac:(set_solver))
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
    destruct (res_extend_by_exists m F Happ) as [my_src Hext].
    assert (Hdom_src :
        world_dom (my_src : WorldT) = world_dom (m : WorldT) ∪ {[r]}).
    {
      rewrite (res_extend_by_dom m F my_src Hext).
      destruct HF as [_ _ [_ Hout] _].
      change (world_dom (m : WorldT) ∪ ext_out F =
        world_dom (m : WorldT) ∪ {[r]}).
      rewrite Hout. reflexivity.
    }
    assert (Hrestrict_src :
        res_restrict my_src (world_dom (m : WorldT)) = m).
    { exact (res_extend_by_restrict_base m F my_src Hext). }
    assert (Hres_s :
        my_src ⊨ expr_result_formula_at (dom Σ) es (LVFree r)).
    {
      eapply (expr_result_formula_at_of_result_extends_on
        (dom Σ) es r F m my_src); eauto.
    }
    destruct (Htransport r my_src Hrfresh Hdom_src Hrestrict_src Hres_s)
      as [my_tgt [Hdom_tgt [Hrestrict_tgt [Hres_t Hproj_obs]]]].
    set (σr := ((σ0 : StoreT) ∪ ({[r := v0]} : StoreT)) : StoreT).
    assert (Hσr_src : (my_src : WorldT) σr).
    {
      apply (proj2 (resA_extend_by_store_iff m F my_src σr Hext)).
      exists σ0.
      set (we := expr_result_output_world es r
        (store_restrict σ0 (lvars_fv (dom Σ)))).
      exists we, ({[r := v0]} : StoreT).
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
      { subst σr. reflexivity. }
    }
    assert (Hproj_small :
        res_restrict my_tgt (lvars_fv (dom Σ) ∪ {[r]}) =
        res_restrict my_src (lvars_fv (dom Σ) ∪ {[r]})).
    {
      eapply res_restrict_eq_subset; [|exact Hproj_obs].
      set_solver.
    }
    destruct (res_restrict_eq_store_lift my_src my_tgt
      (lvars_fv (dom Σ) ∪ {[r]}) σr ltac:(symmetry; exact Hproj_small) Hσr_src)
      as [τr [Hτr_tgt Hτr_proj]].
    pose proof (expr_result_formula_at_models_elim
      (dom Σ) et r my_tgt Hlv_t HrD Hres_t τr Hτr_tgt)
      as [_ [v' [Hr_lookup Heval_t_l]]].
    assert (Hr_lookup_atom : (τr : StoreT) !! r = Some v').
    {
      change (((lstore_lift_free τr : LStoreT) : gmap logic_var value) !!
        LVFree r = Some v') in Hr_lookup.
      rewrite lstore_lift_free_lookup_free in Hr_lookup.
      exact Hr_lookup.
    }
    assert (Hr_lookup_v0 : (τr : StoreT) !! r = Some v0).
    {
      assert (Hσr_lookup : (σr : StoreT) !! r = Some v0).
      {
        subst σr.
        change ((((σ0 : StoreT) ∪ ({[r := v0]} : StoreT)) : gmap atom value)
          !! r = Some v0).
        transitivity (({[r := v0]} : gmap atom value) !! r).
        - apply (lookup_union_r (M:=gmap atom) (A:=value)).
          apply not_elem_of_dom.
          rewrite (wfworld_store_dom m σ0 Hσ0). set_solver.
        - apply map_lookup_singleton.
      }
      assert (Hr_in : r ∈ lvars_fv (dom Σ) ∪ {[r]}).
      { set_solver. }
      assert (Hτr_restrict_lookup :
          (store_restrict τr (lvars_fv (dom Σ) ∪ {[r]}) : StoreT)
            !! r = Some v0).
      {
        rewrite Hτr_proj.
        apply storeA_restrict_lookup_some_2; [exact Hσr_lookup|exact Hr_in].
      }
      apply storeA_restrict_lookup_some in Hτr_restrict_lookup as [_ Hlook].
      exact Hlook.
    }
    assert (Hv_eq : Some v0 = Some v').
    { rewrite <- Hr_lookup_v0. exact Hr_lookup_atom. }
    inversion Hv_eq. subst v'.
    change (tm_eval_in_store τr et v0) in Heval_t_l.
    assert (Hagree_et :
        store_restrict τr (fv_tm et) = store_restrict σ0 (fv_tm et)).
    {
      transitivity (store_restrict σr (fv_tm et)).
      - eapply storeA_restrict_eq_mono; [|exact Hτr_proj].
        intros a Ha. apply elem_of_union_l.
        apply Hfv_t. exact Ha.
      - subst σr.
        apply storeA_restrict_union_ignore_r.
        change (dom ({[r := v0]} : gmap atom value) ## fv_tm et).
        assert (Hr_et : r ∉ fv_tm et).
        {
          intros Hret.
          assert (Hrfv : r ∈ lvars_fv (dom Σ)).
          { apply Hfv_t. exact Hret. }
          clear -Hrfresh_all Hrfv. set_solver.
        }
        intros a Ha_dom Ha_fv.
        apply elem_of_dom in Ha_dom as [va Ha_lookup].
        apply (proj1 (lookup_singleton_Some r a v0 va)) in Ha_lookup
          as [-> _].
        exact (Hr_et Ha_fv).
    }
    eapply tm_eval_in_store_agree_on_fv; [|exact Heval_t_l].
    symmetry. exact Hagree_et.
  }
  split.
  - exact (Hdir e1 e2 Hlc1 Hlc2 Hlv1 Hlv2 Hfv1 Hfv2
      Htotal1_atom H12 σ v Hσ).
  - assert (Htotal2_atom : expr_total_on_atom_world e2 m).
    {
      pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero2.
      pose proof (ty_denote_gas_guard_of_zero Σ τ e2 m Hzero2) as Hguard2.
      repeat rewrite res_models_and_iff in Hguard2.
      destruct Hguard2 as [_ [_ [_ Htotal2]]].
      apply expr_total_formula_to_atom_world. exact Htotal2.
    }
    exact (Hdir e2 e1 Hlc2 Hlc1 Hlv2 Hlv1 Hfv2 Hfv1
      Htotal2_atom H21 σ v Hσ).
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
  pose proof (typed_fiber_equiv_tm_equiv _ _ _ _ _ Hequiv) as Heq_m.
  pose proof (typed_fiber_equiv_term_lvars_env _ _ _ _ _ Hequiv) as Hlv_env.
  pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv) as Hfv_env.
  pose proof (typed_fiber_equiv_zero_src _ _ _ _ _ Hequiv) as Hzero.
  pose proof (ty_denote_gas_guard_of_zero Σ τ e1 m Hzero) as Hguard.
  repeat rewrite res_models_and_iff in Hguard.
  destruct Hguard as [_ [Hworld [_ _]]].
  pose proof Hworld as Hworld_model.
  apply basic_world_formula_models_iff in Hworld as [_ [HΣdom _]].
  assert (Hfv_m : fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT)).
  {
    intros x Hx.
    apply HΣdom. apply Hfv_env. exact Hx.
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
  assert (Happ_eq : tm_equiv_on w
      (tapp_tm e1 (vfvar y))
      (tapp_tm e2 (vfvar y))).
  {
    eapply tm_equiv_tapp_fvar.
    - eapply (wfworld_closed_on_mono
        (fv_tm (tapp_tm e1 (vfvar y)) ∪
          fv_tm (tapp_tm e2 (vfvar y)))
        (lvars_fv (dom Σ) ∪ ({[y]} : aset))).
      + unfold tapp_tm. cbn [fv_tm fv_value].
        clear -Hfv_env. better_set_solver.
      + eapply (wfworld_closed_on_union
          (lvars_fv (dom Σ)) ({[y]} : aset));
          [exact Hclosed_env_w|exact Hclosed_y].
    - exact Hlc1.
    - exact Hlc2.
    - exact Heq_w.
  }
  eapply tm_equiv_on_to_result_projected.
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
    intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + destruct v as [k|a].
      * exfalso. exact ((tm_lvars_lc e1 Hlc1) (LVBound k) Hv).
      * apply elem_of_dom.
        assert (HaΣ : LVFree a ∈ dom Σ).
        { apply Hlv_env. apply elem_of_union_l. exact Hv. }
        apply elem_of_dom in HaΣ as [U HU].
        exists U. rewrite lty_env_open_one_typed_bind_lookup_free_ne.
        -- exact HU.
        -- intros ->. apply Hye. apply elem_of_union_l.
           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
    + apply elem_of_singleton in Hv as ->.
      apply elem_of_dom. exists T.
      apply lty_env_open_one_typed_bind_lookup_current.
  - rewrite tm_lvars_tapp_tm_fvar.
    intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + destruct v as [k|a].
      * exfalso. exact ((tm_lvars_lc e2 Hlc2) (LVBound k) Hv).
      * apply elem_of_dom.
        assert (HaΣ : LVFree a ∈ dom Σ).
        { apply Hlv_env. apply elem_of_union_r. exact Hv. }
        apply elem_of_dom in HaΣ as [U HU].
        exists U. rewrite lty_env_open_one_typed_bind_lookup_free_ne.
        -- exact HU.
        -- intros ->. apply Hye. apply elem_of_union_r.
           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
    + apply elem_of_singleton in Hv as ->.
      apply elem_of_dom. exists T.
      apply lty_env_open_one_typed_bind_lookup_current.
  - exact Happ_eq.
Qed.

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
  set (Σy := lty_env_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty τx))).
  set (τres := cty_open 0 y τr).
  set (app1 := tapp_tm e1 (vfvar y)).
  set (app2 := tapp_tm e2 (vfvar y)).
  pose proof (ty_denote_gas_guard gas Σy τres app1 w Hsrc) as Hguard_src.
  repeat rewrite res_models_and_iff in Hguard_src.
  destruct Hguard_src as [Hwf_res [Hworld_y [Hbasic_src Htotal_src]]].
  pose proof Hworld_y as Hworld_y_model.
  pose proof (typed_fiber_equiv_zero_tgt _ _ _ _ _ Hequiv) as Hzero_fun_tgt.
  pose proof (ty_denote_gas_guard_of_zero Σ τfun e2 m Hzero_fun_tgt)
    as Hguard_fun_tgt.
  repeat rewrite res_models_and_iff in Hguard_fun_tgt.
  destruct Hguard_fun_tgt as [_ [Hworld_m [Hbasic_fun_tgt Htotal_fun_tgt]]].
  apply basic_world_formula_models_iff in Hworld_y as [HlcΣy [HΣy_dom _]].
  pose proof Hworld_m as Hworld_m_model.
  apply basic_world_formula_models_iff in Hworld_m as [HlcΣ [HΣdom _]].
  apply expr_basic_typing_formula_models_iff in Hbasic_fun_tgt
    as [_ [_ Hty_fun_tgt]].
  rewrite Herase in Hty_fun_tgt.
  pose proof (basic_tm_has_ltype_lc Σ e2
    (erase_ty τx →ₜ erase_ty τr) HlcΣ Hty_fun_tgt) as Hlc2.
  pose proof (typed_fiber_equiv_term_lc _ _ _ _ _ Hequiv) as [Hlc1 _].
  pose proof (typed_fiber_equiv_term_scope_env _ _ _ _ _ Hequiv)
    as Hfv_env.
  assert (Hfv_m : fv_tm e1 ∪ fv_tm e2 ⊆ world_dom (m : WorldT)).
  {
    intros a Ha. apply HΣdom. apply Hfv_env. exact Ha.
  }
  pose proof (typed_fiber_equiv_tm_equiv _ _ _ _ _ Hequiv) as Heq_m.
  assert (Heq_w : tm_equiv_on w e1 e2).
  { eapply tm_equiv_full_world_extend_fresh; eauto. }
  assert (Htotal_w : tm_total_equiv_on w e1 e2).
  {
    eapply tm_total_equiv_full_world_extend_fresh.
    - eapply typed_fiber_equiv_total_equiv. exact Hequiv.
    - exact Hlc1.
    - exact Hlc2.
    - exact Hfv_m.
    - exact Hye.
    - exact Hdom.
    - exact Hrestrict.
  }
  assert (Hclosed_env_w : wfworld_closed_on (lvars_fv (dom Σ)) w).
  {
    assert (Hle_mw : m ⊑ w).
    {
      change ((m : WorldT) =
        raw_restrict (w : WorldT) (world_dom (m : WorldT))).
      symmetry.
      exact (f_equal (fun r : WfWorldT => (r : WorldT)) Hrestrict).
    }
    eapply wfworld_closed_on_le.
    - exact HΣdom.
    - exact Hle_mw.
    - eapply basic_world_formula_wfworld_closed_on_dom.
      exact Hworld_m_model.
  }
  assert (Hclosed_app : wfworld_closed_on
      (fv_tm app1 ∪ fv_tm app2) w).
  {
    subst app1 app2.
    eapply (wfworld_closed_on_mono
      (fv_tm (tapp_tm e1 (vfvar y)) ∪
        fv_tm (tapp_tm e2 (vfvar y)))
      (lvars_fv (dom Σ) ∪ ({[y]} : aset))).
    - unfold tapp_tm. cbn [fv_tm fv_value].
      clear -Hfv_env. better_set_solver.
    - eapply wfworld_closed_on_union; [exact Hclosed_env_w|].
      eapply basic_world_formula_wfworld_closed_on_atoms; [|exact Hworld_y_model].
      subst Σy.
      intros a Ha.
      unfold lvars_of_atoms in Ha.
      apply elem_of_map in Ha as [b [-> Hb]].
      apply elem_of_singleton in Hb as ->.
      rewrite lty_env_open_one_dom.
      unfold set_swap. apply elem_of_map.
      exists (LVBound 0). split; [rewrite swap_l; reflexivity|].
      rewrite typed_lty_env_bind_dom.
      apply elem_of_union_r. apply elem_of_singleton. reflexivity.
  }
  assert (Happ_total : tm_total_equiv_on w app1 app2).
  {
    subst app1 app2.
    eapply tm_total_equiv_tapp_fvar; eauto.
  }
  apply ty_denote_gas_zero_of_guard.
  repeat rewrite res_models_and_iff.
  split; [exact Hwf_res|].
  split; [exact Hworld_y_model|].
  split.
  - apply expr_basic_typing_formula_models_iff.
    split; [exact HlcΣy|]. split; [exact HΣy_dom|].
    subst app2 τres Σy.
    rewrite cty_open_preserves_erasure.
    eapply basic_tm_has_ltype_tapp_tm_lvar.
    + exact HlcΣy.
    + eapply basic_tm_has_ltype_weaken.
      * exact Hty_fun_tgt.
      * apply map_subseteq_spec. intros v U Hlook.
        destruct v as [k|a].
        -- exfalso.
           assert (LVBound k ∈ dom Σ) by (eapply elem_of_dom_2; exact Hlook).
           exact (HlcΣ _ H).
        -- rewrite lty_env_open_one_typed_bind_lookup_free_ne.
           ++ exact Hlook.
           ++ intros ->. apply HyΣ.
              apply lvars_fv_elem. eapply elem_of_dom_2. exact Hlook.
    + eapply BVT_FVar.
      apply lty_env_open_one_typed_bind_lookup_current.
  - apply expr_total_atom_world_to_formula.
    apply expr_total_formula_to_atom_world in Htotal_src as Htotal_src_atom.
    destruct Htotal_src_atom as [Hdom_total_src Hstores_src].
    split.
    + subst app2.
      rewrite res_lift_free_dom.
      rewrite tm_lvars_tapp_tm_fvar.
      intros v Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      * destruct v as [k|a].
        -- exfalso. exact ((tm_lvars_lc e2 Hlc2) (LVBound k) Hv).
        -- unfold lvars_of_atoms. apply elem_of_map.
           exists a. split; [reflexivity|].
           assert (LVFree a ∈ dom Σ).
           {
             pose proof (basic_tm_has_ltype_lvars _ _ _ Hty_fun_tgt) as Hlv.
             apply Hlv.
             unfold lvars_of_atoms. apply elem_of_map.
             exists a. split; [reflexivity|].
             rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hv.
           }
           apply HΣy_dom.
           apply lvars_fv_elem.
           apply elem_of_dom in H as [U HU].
           eapply elem_of_dom_2.
           subst Σy.
           rewrite lty_env_open_one_typed_bind_lookup_free_ne by
             (intros ->; apply Hye; apply elem_of_union_r;
              rewrite <- tm_lvars_fv; apply lvars_fv_elem; exact Hv).
           exact HU.
      * apply elem_of_singleton in Hv as ->.
        unfold lvars_of_atoms. apply elem_of_map.
        exists y. split; [reflexivity|].
        apply HΣy_dom.
        subst Σy.
        rewrite lty_env_open_one_dom.
        apply lvars_fv_elem.
        unfold set_swap. apply elem_of_map.
        exists (LVBound 0). split; [rewrite swap_l; reflexivity|].
        rewrite typed_lty_env_bind_dom.
        apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    + intros τL HτL.
      destruct HτL as [σ [Hσ ->]].
      apply (proj1 (Happ_total σ Hσ)).
      apply Hstores_src.
      exists σ. split; [exact Hσ|reflexivity].
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
