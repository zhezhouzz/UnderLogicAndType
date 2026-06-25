(** * Denotation.TypeEquivArrowResultFirst
    Result-first Arrow transport helpers. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTerm
  TypeEquivFiberBase
  TypeEquivBody
  TypeEquivArrow.

Section TypeDenote.
Lemma arrow_result_first_arg_drop_fun_slot
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  f ∉ fv_cty τx ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e)))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)).
Proof.
  intros HfΣ Hfy Hfτx Harg.
  rewrite lvar_store_insert_free_commute in Harg by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) f (erase_ty (CTArrow τx τr))) in Harg.
  2:{
    rewrite dom_insert_L.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. congruence.
    - exact (HfΣ Hbad).
  }
  2:{
    intros Hbad. apply Hfτx.
    rewrite <- context_ty_lvars_fv.
    apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  exact Harg.
Qed.

Lemma arrow_result_first_arg_add_fun_slot
    gas (Σ : lty_env) τx τr e
    (my : WfWorldT) f y :
  LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e : lty_env) ->
  f <> y ->
  f ∉ fv_cty τx ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e)))
    τx (tret (vfvar y)).
Proof.
  intros HfΣ Hfy Hfτx Harg.
  rewrite lvar_store_insert_free_commute by congruence.
  rewrite (ty_denote_gas_insert_fresh_lty_env_eq gas
    (<[LVFree y := erase_ty τx]>
      (relevant_env Σ (CTArrow τx τr) e))
    τx (tret (vfvar y)) f (erase_ty (CTArrow τx τr))).
  2:{
    rewrite dom_insert_L.
    intros Hbad. apply elem_of_union in Hbad as [Hbad|Hbad].
    - apply elem_of_singleton in Hbad. congruence.
    - exact (HfΣ Hbad).
  }
  2:{
    intros Hbad. apply Hfτx.
    rewrite <- context_ty_lvars_fv.
    apply lvars_fv_elem. exact Hbad.
  }
  2:{ cbn [fv_tm fv_value]. set_solver. }
  exact Harg.
Qed.

Local Lemma arrow_result_body_relevant_subset τx τr e f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  (context_ty_lvars (cty_open 0 y τr) ∪
    tm_lvars (tapp_tm (tret (vfvar f)) (vfvar y))) ∖
    {[LVFree y]} ∖ {[LVFree f]} ⊆
  context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e.
Proof.
  intros Hlcτr Hffresh Hyfresh.
  eapply result_first_result_body_relevant_subset; [exact Hlcτr| |].
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - intros Hy. apply Hyfresh. apply elem_of_union_r. exact Hy.
Qed.

Lemma arrow_result_first_result_env_agree
    gas (Σ : lty_env) τx τr e1 e2
    (my : WfWorldT) f y :
  cty_lc_at 1 τr ->
  f ∉ fv_cty τx ∪ fv_cty τr ->
  y ∉ fv_cty τx ∪ fv_cty τr ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e1)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)) ->
  my ⊨ ty_denote_gas gas
    (<[LVFree y := erase_ty τx]>
      (<[LVFree f := erase_ty (CTArrow τx τr)]>
        (relevant_env Σ (CTArrow τx τr) e2)))
    (cty_open 0 y τr)
    (tapp_tm (tret (vfvar f)) (vfvar y)).
Proof.
  intros Hlcτr Hffresh Hyfresh Hres.
  eapply result_first_result_env_agree_general.
  - eapply arrow_result_body_relevant_subset; eauto.
  - eapply arrow_result_body_relevant_subset; eauto.
  - exact Hres.
Qed.

Local Lemma arrow_lvars_shift_from_lc_eq k D :
  lc_lvars D ->
  lvars_shift_from k D = D.
Proof.
  apply result_first_lvars_shift_from_lc_eq.
Qed.

Local Ltac arrow_expr_result_shift0_side :=
  first
    [ assumption
    | apply result_first_lc_lvars_shift_from; assumption
    | rewrite lvars_shift_from_fv; assumption ].


Lemma ty_denote_gas_tm_equiv_arrow_body
    gas (IH : forall Σ τ e1 e2 (m : WfWorldT),
      typed_total_equiv_on Σ τ m e1 e2 ->
      m ⊨ ty_denote_gas gas Σ τ e1 ->
      m ⊨ ty_denote_gas gas Σ τ e2)
    (Σ : lty_env) τx τr e1 e2 (m : WfWorldT) :
  typed_total_equiv_on Σ (CTArrow τx τr) m e1 e2 ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e1)))
          (tm_shift 0 e1) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e1)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
          (tret (vbvar 0)))) ->
  m ⊨
    FForall
      (FImpl
        (expr_result_formula_at
          (lvars_shift_from 0
            (dom (relevant_env Σ (CTArrow τx τr) e2)))
          (tm_shift 0 e2) (LVBound 0))
        (arrow_value_denote_gas_with ty_denote_gas gas
          (typed_lty_env_bind
            (relevant_env Σ (CTArrow τx τr) e2)
            (erase_ty (CTArrow τx τr)))
          (cty_shift 0 τx) (cty_shift 1 τr)
	        (tret (vbvar 0)))).
Proof.
  intros Hequiv Hsrc.
  pose proof (typed_total_equiv_source_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_src.
  pose proof (typed_total_equiv_target_zero
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as Hzero_tgt.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e1 m Hzero_src) as Hguard_src.
  pose proof (ty_denote_gas_guard_of_zero
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hguard_tgt.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_src) as Hwf_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src)
    as Hworld_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_tgt)
    as Hworld_tgt.
  apply context_ty_wf_formula_models_iff in Hwf_src
    as [HlcΣ_wf_src [_ Hbasic_arrow_src]].
  pose proof (basic_context_ty_lvars_lc
    (dom (relevant_env Σ (CTArrow τx τr) e1)) _
    HlcΣ_wf_src Hbasic_arrow_src) as Hlc_arrow.
  cbn [lc_context_ty cty_lc_at] in Hlc_arrow.
  destruct Hlc_arrow as [Hlcτx Hlcτr].
  apply basic_world_formula_models_iff in Hworld_src as [HlcΣ_src _].
  apply basic_world_formula_models_iff in Hworld_tgt as [HlcΣ_tgt _].
  pose proof (typed_total_equiv_term_lc
    Σ (CTArrow τx τr) m e1 e2 Hequiv) as [Hlc1 Hlc2].
  pose proof (ty_denote_gas_scope_from_zero_any (S gas)
    Σ (CTArrow τx τr) e2 m Hzero_tgt) as Hscope_full.
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_tgt.
  assert (Hfib :
      tm_fiber_equiv_on m (lvars_fv (context_ty_lvars (CTArrow τx τr)))
        e1 e2).
  {
    apply tm_equiv_on_to_fiber_equiv.
    eapply typed_total_equiv_tm_equiv. exact Hequiv.
  }
  pose proof (tm_fiber_equiv_to_projected_on
    Σ (CTArrow τx τr) m (context_ty_lvars (CTArrow τx τr))
    e1 e2 Hfib Hzero_src Hzero_tgt) as [_ H21].
  destruct (res_models_forall_rev _ _ Hsrc) as [Lsrc Hsrc_rev].
  eapply res_models_forall_rev_intro; [exact Hscope_tgt|].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ fv_tm e1 ∪ fv_tm e2 ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e1)) ∪
    lvars_fv (dom (relevant_env Σ (CTArrow τx τr) e2)) ∪
    lvars_fv (context_ty_lvars (CTArrow τx τr)) ∪
    fv_cty τx ∪ fv_cty τr).
  intros f Hf mf Hdom Hrestrict.
  assert (Hf_proj :
      f ∉ world_dom (m : WorldT) ∪ fv_tm e2 ∪ fv_tm e1 ∪
        lvars_fv (context_ty_lvars (CTArrow τx τr))).
  { clear -Hf. set_solver. }
  assert (Hf_src : f ∉ Lsrc).
  { clear -Hf. set_solver. }
  assert (Hfτx : f ∉ fv_cty τx).
  { clear -Hf. set_solver. }
  assert (Hfτr : f ∉ fv_cty τr).
  { clear -Hf. set_solver. }
  assert (Hfe : f ∉ fv_tm e1 ∪ fv_tm e2).
  { clear -Hf. set_solver. }
  assert (HfΣ1 :
      f ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))).
  {
    clear -Hf.
    rewrite typed_lty_env_bind_lvars_fv_dom.
    set_solver.
  }
	  assert (HfΣ2 :
	      f ∉ lvars_fv
	        (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
	  {
	    clear -Hf.
	    rewrite typed_lty_env_bind_lvars_fv_dom.
	    set_solver.
	  }
	  assert (Hf_rel1 :
	      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
	  {
	    intros Hbad. apply HfΣ1.
	    apply lvars_fv_elem.
	    rewrite typed_lty_env_bind_dom.
	    rewrite (arrow_lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
	    apply elem_of_union_l. exact Hbad.
	  }
	  assert (Hf_rel2 :
	      LVFree f ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
	  {
	    intros Hbad. apply HfΣ2.
	    apply lvars_fv_elem.
	    rewrite typed_lty_env_bind_dom.
	    rewrite (arrow_lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
	    apply elem_of_union_l. exact Hbad.
	  }
	  assert (Hopened_scope :
	      formula_scoped_in_world mf
	        (FImpl
	          (expr_result_formula_at
	            (context_ty_lvars (CTArrow τx τr) ∪ tm_lvars e2)
	            e2 (LVFree f))
	          (arrow_value_denote_gas_with ty_denote_gas gas
	            (<[LVFree f := erase_ty (CTArrow τx τr)]>
	              (relevant_env Σ (CTArrow τx τr) e2))
	            τx τr (tret (vfvar f))))).
	  {
	    pose proof (formula_scoped_forall_open_res_le m mf f
	      _ Hscope_tgt
	      ltac:(rewrite <- Hrestrict; apply res_restrict_le)
	      ltac:(rewrite Hdom; clear; set_solver)) as Hopened_scope_raw.
	    rewrite formula_open_impl in Hopened_scope_raw.
	    rewrite formula_open_expr_result_formula_at_shift0 in Hopened_scope_raw
	      by (first
	        [ exact Hlc2
	        | apply result_first_lc_lvars_shift_from; exact HlcΣ_tgt
	        | rewrite lvars_shift_from_fv; clear -Hf; set_solver
	        | clear -Hfe; set_solver ]).
	    rewrite (arrow_lvars_shift_from_lc_eq 0
	      (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt)
	      in Hopened_scope_raw.
	    rewrite (ty_denote_gas_zero_relevant_env_dom_eq
	      Σ (CTArrow τx τr) e2 m Hzero_tgt) in Hopened_scope_raw.
	    rewrite (formula_open_result_first_arrow_value_ret_bvar0
	      gas (relevant_env Σ (CTArrow τx τr) e2) τx τr
	      (erase_ty (CTArrow τx τr)) f) in Hopened_scope_raw.
	    2: exact HlcΣ_tgt.
	    2: exact Hf_rel2.
	    2: exact Hlcτx.
	    2: exact Hlcτr.
	    2: exact Hfτx.
	    2: exact Hfτr.
	    exact Hopened_scope_raw.
	  }
	  rewrite formula_open_impl.
	  rewrite formula_open_expr_result_formula_at_shift0
	    by (first
	      [ exact Hlc2
	      | apply result_first_lc_lvars_shift_from; exact HlcΣ_tgt
	      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
	      | clear -Hfe; set_solver ]).
	  rewrite (arrow_lvars_shift_from_lc_eq 0
	    (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
	  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
	    Σ (CTArrow τx τr) e2 m Hzero_tgt).
	  rewrite (formula_open_result_first_arrow_value_ret_bvar0
	    gas (relevant_env Σ (CTArrow τx τr) e2) τx τr
	    (erase_ty (CTArrow τx τr)) f).
	  2: exact HlcΣ_tgt.
	  2: exact Hf_rel2.
	  2: exact Hlcτx.
	  2: exact Hlcτr.
	  2: exact Hfτx.
	  2: exact Hfτr.
	  eapply res_models_impl_intro; [exact Hopened_scope|].
	  intros Hres_tgt.
	  destruct (H21 f mf Hf_proj Hdom Hrestrict Hres_tgt)
    as [mf_src [Hdom_src [Hrestrict_src [Hres_src Hproj_obs]]]].
  pose proof (Hsrc_rev f Hf_src mf_src Hdom_src Hrestrict_src)
    as Hopened_src.
  rewrite formula_open_impl in Hopened_src.
  rewrite formula_open_expr_result_formula_at_shift0 in Hopened_src
    by (first
      [ exact Hlc1
      | apply result_first_lc_lvars_shift_from; exact HlcΣ_src
      | rewrite lvars_shift_from_fv; clear -Hf; set_solver
      | clear -Hfe; set_solver ]).
  rewrite (arrow_lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src) in Hopened_src.
  rewrite (ty_denote_gas_zero_relevant_env_dom_eq
    Σ (CTArrow τx τr) e1 m Hzero_src) in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hres_src)
    as Hvalue_src.
  assert (Hequiv_src :
      typed_total_equiv_on Σ (CTArrow τx τr) mf_src e1 e2).
  {
    split.
    - eapply tm_equiv_full_world_extend_fresh.
      + eapply typed_total_equiv_tm_equiv. exact Hequiv.
      + eapply typed_total_equiv_term_scope. exact Hequiv.
      + exact Hfe.
      + exact Hdom_src.
      + exact Hrestrict_src.
    - split.
      + eapply tm_total_equiv_full_world_extend_fresh.
        * eapply typed_total_equiv_total_equiv. exact Hequiv.
        * exact Hlc1.
        * exact Hlc2.
        * eapply typed_total_equiv_term_scope. exact Hequiv.
        * exact Hfe.
        * exact Hdom_src.
        * exact Hrestrict_src.
	      + split.
	        * eapply (res_models_kripke m mf_src).
	          -- rewrite <- Hrestrict_src. apply res_restrict_le.
	          -- exact Hzero_src.
	        * eapply (res_models_kripke m mf_src).
	          -- rewrite <- Hrestrict_src. apply res_restrict_le.
	          -- exact Hzero_tgt.
  }
	  rewrite (formula_open_result_first_arrow_value_ret_bvar0
	    gas (relevant_env Σ (CTArrow τx τr) e1) τx τr
	    (erase_ty (CTArrow τx τr)) f) in Hvalue_src.
	  2: exact HlcΣ_src.
	  2: exact Hf_rel1.
	  2: exact Hlcτx.
	  2: exact Hlcτr.
	  2: exact Hfτx.
	  2: exact Hfτr.
	  assert (Hvalue_tgt_src :
	      mf_src ⊨
	        arrow_value_denote_gas_with ty_denote_gas gas
	          (<[LVFree f := erase_ty (CTArrow τx τr)]>
	            (relevant_env Σ (CTArrow τx τr) e2))
	          τx τr (tret (vfvar f))).
	  {
	    assert (Hvalue_tgt_scope_src :
	        formula_scoped_in_world mf_src
	          (arrow_value_denote_gas_with ty_denote_gas gas
	            (<[LVFree f := erase_ty (CTArrow τx τr)]>
	              (relevant_env Σ (CTArrow τx τr) e2))
	            τx τr (tret (vfvar f)))).
	    {
	      eapply formula_scoped_arrow_value_body_obs.
	      pose proof (ty_denote_gas_zero_type_fv_world
	        Σ (CTArrow τx τr) e1 m Hzero_src) as Hτworld.
	      rewrite Hdom_src.
	      intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - apply elem_of_union_l. exact (Hτworld a Ha).
      - apply elem_of_union_r. exact Ha.
    }
		    eapply res_models_forall_full_world_map;
		      [exact Hvalue_tgt_scope_src| |exact Hvalue_src].
	    exists (world_dom (mf_src : WorldT) ∪ world_dom (mf : WorldT) ∪
	        fv_cty τx ∪ fv_cty τr ∪ fv_tm e1 ∪ fv_tm e2 ∪
	        lvars_fv (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx))) ∪
	        lvars_fv (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
      intros y Hy my Hdom_y Hrestrict_y Hopened_arg.
      cbn [formula_open] in Hopened_arg |- *.
      pose proof (formula_scoped_forall_open_res_le mf_src my y
        _ Hvalue_tgt_scope_src
        ltac:(rewrite <- Hrestrict_y; apply res_restrict_le)
        ltac:(rewrite Hdom_y; clear; set_solver)) as Htarget_impl_scope.
      cbn [formula_open] in Htarget_impl_scope.
      eapply res_models_impl_intro.
      { exact Htarget_impl_scope. }
      intros Harg_tgt.
      assert (Hyτx : y ∉ fv_cty τx).
      { clear -Hy. set_solver. }
      assert (Hyτr : y ∉ fv_cty τr).
      { clear -Hy. set_solver. }
      assert (Hye : y ∉ fv_tm e1 ∪ fv_tm e2).
      { clear -Hy. set_solver. }
      assert (HyΣ1 : y ∉ lvars_fv
        (dom (typed_lty_env_bind
          (relevant_env Σ (CTArrow τx τr) e1) (erase_ty τx)))).
      { clear -Hy. set_solver. }
	      assert (HyΣ2 : y ∉ lvars_fv
	        (dom (typed_lty_env_bind
	          (relevant_env Σ (CTArrow τx τr) e2) (erase_ty τx)))).
	      { clear -Hy. set_solver. }
        assert (Hy_rel1 :
            LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e1 : lty_env)).
        {
          intros Hbad. apply HyΣ1.
          apply lvars_fv_elem.
          rewrite typed_lty_env_bind_dom.
          rewrite (arrow_lvars_shift_from_lc_eq 0
            (dom (relevant_env Σ (CTArrow τx τr) e1)) HlcΣ_src).
          apply elem_of_union_l. exact Hbad.
        }
        assert (Hy_rel2 :
            LVFree y ∉ dom (relevant_env Σ (CTArrow τx τr) e2 : lty_env)).
        {
          intros Hbad. apply HyΣ2.
          apply lvars_fv_elem.
          rewrite typed_lty_env_bind_dom.
          rewrite (arrow_lvars_shift_from_lc_eq 0
            (dom (relevant_env Σ (CTArrow τx τr) e2)) HlcΣ_tgt).
          apply elem_of_union_l. exact Hbad.
        }
        assert (Hfy : f <> y).
        {
          intros ->. apply Hy.
          clear -Hdom.
          rewrite Hdom. set_solver.
        }
		      assert (Harg_tgt_open :
		          my ⊨ ty_denote_gas gas
		            (<[LVFree y := erase_ty τx]>
		              (relevant_env Σ (CTArrow τx τr) e2))
		            τx (tret (vfvar y))).
		      {
		        rewrite (formula_open_ty_denote_gas_bind_ret_bvar0
		          y gas
		          (<[LVFree f := erase_ty (CTArrow τx τr)]>
		            (relevant_env Σ (CTArrow τx τr) e2))
		          τx) in Harg_tgt.
		        2:{ apply lty_env_closed_insert_free. exact HlcΣ_tgt. }
		        2:{
		          rewrite dom_insert_L.
		          intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
		          - apply elem_of_singleton in Hybad. congruence.
		          - exact (Hy_rel2 Hybad).
		        }
		        2: exact Hyτx.
		        2: exact Hlcτx.
		        eapply arrow_result_first_arg_drop_fun_slot.
		        - exact Hf_rel2.
		        - clear -Hfy. congruence.
	        - exact Hfτx.
	        - exact Harg_tgt.
      }
		      pose proof (ty_denote_gas_tm_equiv_arrow_open_arg
		        gas Σ τx τr e1 e2 my y Harg_tgt_open) as Harg_src.
	      assert (Harg_src_formula :
          my ⊨ ty_denote_gas gas
            (<[LVFree y := erase_ty τx]>
              (<[LVFree f := erase_ty (CTArrow τx τr)]>
                (relevant_env Σ (CTArrow τx τr) e1)))
            τx (tret (vfvar y))).
		      {
			eapply arrow_result_first_arg_add_fun_slot.
			- exact Hf_rel1.
				- intros ->. apply Hy.
				  clear -Hdom.
				  rewrite Hdom. set_solver.
			- exact Hfτx.
			- exact Harg_src.
		      }
		      pose proof (arrow_value_open_arg_to_regular_imp
		        gas (relevant_env Σ (CTArrow τx τr) e1) τx τr
		        (erase_ty (CTArrow τx τr)) f y mf_src my
		        HlcΣ_src Hf_rel1 Hfy
		        ltac:(rewrite dom_insert_L; clear -Hfy Hy_rel1; set_solver)
		        Hlcτx Hlcτr
		        ltac:(clear -Hfτx Hfτr; set_solver)
		        ltac:(clear -Hyτx Hyτr; set_solver)
		        Hvalue_src
		        ltac:(clear -Hy; set_solver)
		        Hdom_y Hrestrict_y) as Hopened_arg_regular.
		      pose proof (res_models_impl_elim _ _ _ Hopened_arg_regular Harg_src_formula)
		        as Hres_src_inner.
	      assert (Hres_src_regular :
		  my ⊨ ty_denote_gas gas
		    (<[LVFree y := erase_ty τx]>
		      (<[LVFree f := erase_ty (CTArrow τx τr)]>
			(relevant_env Σ (CTArrow τx τr) e1)))
		    (cty_open 0 y τr)
		    (tapp_tm (tret (vfvar f)) (vfvar y))).
	      {
          exact Hres_src_inner.
	      }
	      assert (Hres_tgt_regular :
		  my ⊨ ty_denote_gas gas
		    (<[LVFree y := erase_ty τx]>
		      (<[LVFree f := erase_ty (CTArrow τx τr)]>
			(relevant_env Σ (CTArrow τx τr) e2)))
		    (cty_open 0 y τr)
		    (tapp_tm (tret (vfvar f)) (vfvar y))).
	      {
			eapply arrow_result_first_result_env_agree.
			- exact Hlcτr.
			- intros Hin.
			  apply elem_of_union in Hin as [Hin|Hin].
			  + exact (Hfτx Hin).
			  + exact (Hfτr Hin).
			- intros Hin.
			  apply elem_of_union in Hin as [Hin|Hin].
			  + exact (Hyτx Hin).
			  + exact (Hyτr Hin).
			- exact Hres_src_regular.
	      }
	        rewrite (formula_open_ty_denote_gas_bind_tapp_shift_bvar0
	          y gas
	          (<[LVFree f := erase_ty (CTArrow τx τr)]>
	            (relevant_env Σ (CTArrow τx τr) e2))
	          τr (erase_ty τx) (tret (vfvar f))).
	        2:{ apply lty_env_closed_insert_free. exact HlcΣ_tgt. }
	        2:{
	          rewrite dom_insert_L.
	          intros Hybad. apply elem_of_union in Hybad as [Hybad|Hybad].
	          - apply elem_of_singleton in Hybad. congruence.
	          - exact (Hy_rel2 Hybad).
	        }
	        2:{ cbn [fv_tm fv_value]. clear -Hfy. set_solver. }
	        2:{ clear -Hyτx Hyτr. set_solver. }
	        2:{ constructor. constructor. }
	        exact Hres_tgt_regular.
		  }
			  eapply res_models_projection; [|exact Hvalue_tgt_src].
		  eapply res_restrict_eq_subset; [|exact Hproj_obs].
		  apply formula_fv_open_arrow_value_body_obs.
Qed.

End TypeDenote.
