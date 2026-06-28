(** * Denotation.TypePersistArrow

    Arrow-specific consequences of type-level persistency. *)

From Denotation Require Import Notation TypeDenote TypeDenoteRegular ResultFirstOpen
  DenotationSetMapFacts TypeEquivCore TypeEquivFiberBaseCore TypeEquivFiberBaseProjected TypeEquivBody TypeEquiv
  TypePersistBase.
From ContextAlgebra Require Import ResourceAlgebra.

Section TypePersist.

Lemma arrow_value_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr ef (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  lc_context_ty (cty_shift 0 (CTOver bx φx)) ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world m
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (cty_shift 0 (CTPersist (CTOver bx φx))) τr ef) ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_src Σ
    (cty_shift 0 (CTOver bx φx)) τr ef ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (cty_shift 0 (CTPersist (CTOver bx φx))) τr ef.
Proof.
  intros HΣclosed Hlc_over Hlc_shift_over
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue.
  cbn [arrow_value_denote_gas_with] in Hvalue |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  destruct gas_tgt' as [|gas_tgt'']; [lia|].
  destruct (res_models_forall_rev _ _ Hvalue) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro.
  { exact Hscope_tgt. }
	  exists (Lsrc ∪ lvars_fv (dom Σ) ∪ qual_dom φx ∪
	    fv_cty τr ∪ fv_tm ef).
  intros y Hy my Hdom Hrestrict.
  cbn [formula_open].
  eapply res_models_impl_intro.
  {
    pose proof (formula_scoped_forall_open_res_le m my y
      (FImpl
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ
            (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx)))))
          (cty_shift 0 (cty_shift 0 (CTPersist (CTOver bx φx))))
          (tret (vbvar 0)))
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ
            (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx)))))
          τr (tapp_tm (tm_shift 0 ef) (vbvar 0))))
      Hscope_tgt
      ltac:(rewrite <- Hrestrict; apply res_restrict_le)
      ltac:(rewrite Hdom; apply elem_of_union_r; apply elem_of_singleton;
        reflexivity)) as Hopened_scope.
    cbn [formula_open] in Hopened_scope.
    exact Hopened_scope.
  }
  intros Harg_persist.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by (clear -Hy; set_solver).
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
	  assert (Hyφ : y ∉ qual_dom φx) by (clear -Hy; set_solver).
	  assert (Hyτr : y ∉ fv_cty τr) by (clear -Hy; set_solver).
	  assert (Hyef : y ∉ fv_tm ef) by (clear -Hy; set_solver).
  assert (Harg_over :
      my ⊨ formula_open 0 y
        (ty_denote_gas (S gas_src')
          (typed_lty_env_bind Σ (erase_ty (cty_shift 0 (CTOver bx φx))))
          (cty_shift 0 (cty_shift 0 (CTOver bx φx))) (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2: {
      rewrite typed_lty_env_bind_lvars_fv_dom.
      exact HyΣ.
    }
    2:{
      cbn [fv_tm fv_value]. intros Hin.
      rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      rewrite !cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2: exact Hlc_shift_over.
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
	    replace (lvar_store_open_one 0 y
	      (typed_lty_env_bind Σ (erase_ty (cty_shift 0 (CTOver bx φx)))))
	      with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
	    2:{
	      rewrite cty_shift_preserves_erasure.
	      symmetry.
	      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	    }
	    assert (Harg_over_base :
	        my ⊨ ty_denote_gas (S gas_tgt'')
	          (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	          (cty_shift 0 (CTOver bx φx)) (tret (vfvar y))).
	    {
	      rewrite formula_open_ty_denote_gas_singleton in Harg_persist.
      2: {
        rewrite typed_lty_env_bind_lvars_fv_dom.
        exact HyΣ.
      }
      2:{
        cbn [fv_tm fv_value]. intros Hin.
        rewrite elem_of_empty in Hin. contradiction.
      }
      2:{
        rewrite !cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφ.
      }
	      replace (lvar_store_open_one 0 y
	        (typed_lty_env_bind Σ
	          (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx))))))
	        with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	        in Harg_persist.
	      2:{
	        rewrite cty_shift_preserves_erasure.
	        symmetry.
	        apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	      }
	      replace (cty_open 0 y
	        (cty_shift 0 (cty_shift 0 (CTPersist (CTOver bx φx)))))
	        with (cty_shift 0 (CTPersist (CTOver bx φx))) in Harg_persist.
	      2:{
	        symmetry. apply cty_open_shift_from_lc_fresh.
	        - cbn [lc_context_ty cty_lc_at]. exact Hlc_shift_over.
	        - rewrite cty_shift_fv.
	          unfold fv_cty, qual_dom in *.
	          cbn [context_ty_lvars context_ty_lvars_at] in *.
	          rewrite lvars_fv_lvars_at_depth.
	          exact Hyφ.
	      }
	      cbn [open_tm open_value] in Harg_persist.
	      change (cty_shift 0 (CTPersist (CTOver bx φx)))
	        with (CTPersist (CTOver bx (qual_shift_from 1 φx))) in Harg_persist.
	      change (cty_shift 0 (CTOver bx φx))
	        with (CTOver bx (qual_shift_from 1 φx)).
	      eapply (ty_denote_gas_persist_over_ret_fvar_elim
	        (S gas_tgt'')
	        (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	        bx (qual_shift_from 1 φx) y).
	      - apply lty_env_closed_insert_free. exact HΣclosed.
	      - unfold qual_dom.
	        change (qual_lvars (qual_shift_from 1 φx)) with
	          (qual_vars (qual_shift_from 1 φx)).
	        rewrite qual_shift_from_vars.
	        rewrite lvars_shift_from_fv.
	        exact Hyφ.
	      - exact Harg_persist.
	    }
	    rewrite (ty_denote_gas_saturate (S gas_src')
	      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	      (cty_shift 0 (CTOver bx φx)) (tret (vfvar y)))
	      by (rewrite cty_shift_preserves_depth; cbn [cty_depth]; lia).
	    rewrite (ty_denote_gas_saturate (S gas_tgt'')
	      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	      (cty_shift 0 (CTOver bx φx)) (tret (vfvar y))) in Harg_over_base
	      by (rewrite cty_shift_preserves_depth; cbn [cty_depth]; lia).
	    exact Harg_over_base.
	  }
  assert (HyLsrc : y ∉ Lsrc) by (clear -Hy; set_solver).
  pose proof (Hsrc y HyLsrc my Hdom Hrestrict)
    as Hopened_src.
  cbn [formula_open] in Hopened_src.
	  pose proof (res_models_impl_elim _ _ _ Hopened_src Harg_over) as Hres.
	  rewrite formula_open_ty_denote_gas_singleton in Hres.
	  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
	  2:{
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_tm fv_value].
	    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
	    - exact (Hyef Hin).
	    - rewrite elem_of_empty in Hin. contradiction.
	  }
	  2:{ exact Hyτr. }
	  rewrite formula_open_ty_denote_gas_singleton.
	  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
	  2:{
	    rewrite fv_tapp_tm, tm_shift_fv.
	    cbn [fv_tm fv_value].
	    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
	    - exact (Hyef Hin).
	    - rewrite elem_of_empty in Hin. contradiction.
	  }
	  2:{ exact Hyτr. }
	  replace (lvar_store_open_one 0 y
	    (typed_lty_env_bind Σ (erase_ty (cty_shift 0 (CTOver bx φx)))))
	    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ) in Hres.
	  2:{
	    rewrite cty_shift_preserves_erasure.
	    symmetry.
	    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	  }
	  replace (lvar_store_open_one 0 y
	    (typed_lty_env_bind Σ
	      (erase_ty (cty_shift 0 (CTPersist (CTOver bx φx))))))
	    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
	  2:{
	    rewrite cty_shift_preserves_erasure.
	    symmetry.
	    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
	  }
	  rewrite (ty_denote_gas_saturate (S gas_src')
	    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	    (cty_open 0 y τr)
	    (open_tm 0 (vfvar y)
	      (tapp_tm (tm_shift 0 ef) (vbvar 0)))) in Hres
	    by (rewrite cty_open_preserves_depth; lia).
	  rewrite (ty_denote_gas_saturate (S (S gas_tgt''))
	    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
	    (cty_open 0 y τr)
	    (open_tm 0 (vfvar y)
	      (tapp_tm (tm_shift 0 ef) (vbvar 0))))
	    by (rewrite cty_open_preserves_depth; lia).
	  exact Hres.
Qed.

Lemma ty_guard_formula_transport
    Σ1 Σ2 τ1 τ2 e (m : WfWorldT) :
  (m ⊨ context_ty_wf_formula Σ1 τ1 ->
   m ⊨ context_ty_wf_formula Σ2 τ2) ->
  Σ1 = Σ2 ->
  erase_ty τ1 = erase_ty τ2 ->
  m ⊨ ty_guard_formula Σ1 τ1 e ->
  m ⊨ ty_guard_formula Σ2 τ2 e.
Proof.
  intros Hwf -> Herase Hguard.
  unfold ty_guard_formula in *.
  repeat rewrite res_models_and_iff in Hguard |- *.
  destruct Hguard as [Hwf1 [Hworld [Hbasic Htotal]]].
  split; [apply Hwf; exact Hwf1|].
  split; [exact Hworld|].
  split; [|exact Htotal].
  rewrite <- Herase. exact Hbasic.
Qed.

Local Ltac persist_over_context_wf :=
  apply context_ty_wf_formula_models_iff;
  let Hlc := fresh "Hlc" in
  let Hdom := fresh "Hdom" in
  let Hbasic_ty := fresh "Hbasic_ty" in
  match goal with
  | H : _ ⊨ context_ty_wf_formula _ _ |- _ =>
      apply context_ty_wf_formula_models_iff in H as [Hlc [Hdom Hbasic_ty]]
  end;
  split; [exact Hlc|];
  split; [exact Hdom|];
  destruct Hbasic_ty as [Hvars Hshape];
  split;
  [ cbn [context_ty_lvars context_ty_lvars_at] in Hvars |- *; exact Hvars
  | cbn [context_ty_shape_ok] in Hshape |- *; exact Hshape ].

Lemma ty_guard_arrow_over_arg_to_persist_over_arg
    Σ bx φx τr e (m : WfWorldT) :
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
      (CTArrow (CTOver bx φx) τr) e ->
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
      (CTArrow (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros Hguard.
  eapply ty_guard_formula_transport; [|reflexivity|reflexivity|exact Hguard].
  intros Hwf. persist_over_context_wf.
Qed.

Lemma ty_guard_arrow_persist_over_arg_to_over_arg
    Σ bx φx τr e (m : WfWorldT) :
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
      (CTArrow (CTPersist (CTOver bx φx)) τr) e ->
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
      (CTArrow (CTOver bx φx) τr) e.
Proof.
  intros Hguard.
  change (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
    with (relevant_env Σ (CTArrow (CTOver bx φx) τr) e) in Hguard.
  eapply ty_guard_formula_transport; [|reflexivity|reflexivity|exact Hguard].
  intros Hwf. persist_over_context_wf.
Qed.

Lemma ty_guard_wand_over_arg_to_persist_over_arg
    Σ bx φx τr e (m : WfWorldT) :
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
      (CTWand (CTOver bx φx) τr) e ->
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
      (CTWand (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros Hguard.
  eapply ty_guard_formula_transport; [|reflexivity|reflexivity|exact Hguard].
  intros Hwf. persist_over_context_wf.
Qed.

Lemma ty_guard_wand_persist_over_arg_to_over_arg
    Σ bx φx τr e (m : WfWorldT) :
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
      (CTWand (CTPersist (CTOver bx φx)) τr) e ->
  m ⊨ ty_guard_formula
      (relevant_env Σ (CTWand (CTOver bx φx) τr) e)
      (CTWand (CTOver bx φx) τr) e.
Proof.
  intros Hguard.
  change (relevant_env Σ (CTWand (CTPersist (CTOver bx φx)) τr) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) τr) e) in Hguard.
  eapply ty_guard_formula_transport; [|reflexivity|reflexivity|exact Hguard].
  intros Hwf. persist_over_context_wf.
Qed.

Lemma cty_lc_at_shift_at d τ :
  cty_lc_at d τ ->
  cty_lc_at d (cty_shift d τ).
Proof.
  induction τ in d |- *; cbn [cty_lc_at cty_shift]; intros Hlc;
    try tauto.
  - rewrite qual_shift_from_vars.
    rewrite lvars_shift_from_lc_at_id by exact Hlc.
    exact Hlc.
  - rewrite qual_shift_from_vars.
    rewrite lvars_shift_from_lc_at_id by exact Hlc.
    exact Hlc.
  - destruct Hlc as [H1 H2]. split; [apply IHτ1|apply IHτ2]; assumption.
  - destruct Hlc as [H1 H2]. split; [apply IHτ1|apply IHτ2]; assumption.
  - destruct Hlc as [H1 H2]. split; [apply IHτ1|apply IHτ2]; assumption.
  - destruct Hlc as [H1 H2]. split.
    + apply IHτ1. exact H1.
    + apply IHτ2. exact H2.
  - destruct Hlc as [H1 H2]. split.
    + apply IHτ1. exact H1.
    + apply IHτ2. exact H2.
  - apply IHτ. exact Hlc.
Qed.

Lemma arrow_value_over_arg_to_persist_over_arg_plain
    gas_src gas_tgt (Σ : lty_env) bx φx τr ef (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world m
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (CTPersist (CTOver bx φx)) τr ef) ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_src Σ
    (CTOver bx φx) τr ef ->
  m ⊨ arrow_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (CTPersist (CTOver bx φx)) τr ef.
Proof.
  intros HΣclosed Hlc_over Hlcτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue.
  cbn [arrow_value_denote_gas_with] in Hvalue |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  destruct gas_tgt' as [|gas_tgt'']; [lia|].
  destruct (res_models_forall_rev _ _ Hvalue) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro.
  { exact Hscope_tgt. }
  exists (Lsrc ∪ lvars_fv (dom Σ) ∪ qual_dom φx ∪
    fv_cty τr ∪ fv_tm ef).
  intros y Hy my Hdom Hrestrict.
  cbn [formula_open].
  eapply res_models_impl_intro.
  {
    pose proof (formula_scoped_forall_open_res_le m my y
      (FImpl
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx))))
          (cty_shift 0 (CTPersist (CTOver bx φx)))
          (tret (vbvar 0)))
        (ty_denote_gas (S (S gas_tgt''))
          (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx))))
          τr (tapp_tm (tm_shift 0 ef) (vbvar 0))))
      Hscope_tgt
      ltac:(rewrite <- Hrestrict; apply res_restrict_le)
      ltac:(rewrite Hdom; apply elem_of_union_r; apply elem_of_singleton;
        reflexivity)) as Hopened_scope.
    cbn [formula_open] in Hopened_scope.
    exact Hopened_scope.
  }
  intros Harg_persist.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by (clear -Hy; set_solver).
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyφ : y ∉ qual_dom φx) by (clear -Hy; set_solver).
  assert (Hyτr : y ∉ fv_cty τr) by (clear -Hy; set_solver).
  assert (Hyef : y ∉ fv_tm ef) by (clear -Hy; set_solver).
  assert (Harg_over :
      my ⊨ formula_open 0 y
        (ty_denote_gas (S gas_src')
          (typed_lty_env_bind Σ (erase_ty (CTOver bx φx)))
          (cty_shift 0 (CTOver bx φx)) (tret (vbvar 0)))).
  {
    rewrite formula_open_ty_denote_gas_singleton.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{
      cbn [fv_tm fv_value]. intros Hin.
      rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    rewrite cty_open_shift_from_lc_fresh.
    2: exact Hlc_over.
    2:{
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφ.
    }
    replace (lvar_store_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
      with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
    2:{
      symmetry.
      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
    }
    assert (Harg_over_base :
        my ⊨ ty_denote_gas (S gas_tgt'')
          (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
          (CTOver bx φx) (tret (vfvar y))).
    {
      rewrite formula_open_ty_denote_gas_singleton in Harg_persist.
      2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
      2:{
        cbn [fv_tm fv_value]. intros Hin.
        rewrite elem_of_empty in Hin. contradiction.
      }
      2:{
        rewrite cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφ.
      }
      replace (lvar_store_open_one 0 y
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx)))))
        with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
        in Harg_persist.
      2:{
        symmetry.
        apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
      }
      replace (cty_open 0 y
        (cty_shift 0 (CTPersist (CTOver bx φx))))
        with (CTPersist (CTOver bx φx)) in Harg_persist.
      2:{
        symmetry. apply cty_open_shift_from_lc_fresh.
        - cbn [lc_context_ty cty_lc_at]. exact Hlc_over.
        - unfold fv_cty, qual_dom in *.
          cbn [context_ty_lvars context_ty_lvars_at] in *.
          rewrite lvars_fv_lvars_at_depth.
          exact Hyφ.
      }
      cbn [open_tm open_value] in Harg_persist.
      eapply (ty_denote_gas_persist_over_ret_fvar_elim
        (S gas_tgt'')
        (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
        bx φx y).
      - apply lty_env_closed_insert_free. exact HΣclosed.
      - exact Hyφ.
      - exact Harg_persist.
    }
    rewrite (ty_denote_gas_saturate (S gas_src')
      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
      (CTOver bx φx) (tret (vfvar y)))
      by (cbn [cty_depth]; lia).
    rewrite (ty_denote_gas_saturate (S gas_tgt'')
      (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
      (CTOver bx φx) (tret (vfvar y))) in Harg_over_base
      by (cbn [cty_depth]; lia).
    exact Harg_over_base.
  }
  assert (HyLsrc : y ∉ Lsrc) by (clear -Hy; set_solver).
  pose proof (Hsrc y HyLsrc my Hdom Hrestrict)
    as Hopened_src.
  cbn [formula_open] in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Harg_over) as Hres.
  rewrite formula_open_ty_denote_gas_singleton in Hres.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{ exact Hyτr. }
  rewrite formula_open_ty_denote_gas_singleton.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - exact (Hyef Hin).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{ exact Hyτr. }
  replace (lvar_store_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ) in Hres.
  2:{
    symmetry.
    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
  }
  replace (lvar_store_open_one 0 y
    (typed_lty_env_bind Σ (erase_ty (CTPersist (CTOver bx φx)))))
    with (<[LVFree y := erase_ty (CTOver bx φx)]> Σ).
  2:{
    symmetry.
    apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
  }
  rewrite (ty_denote_gas_saturate (S gas_src')
    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
    (cty_open 0 y τr)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 ef) (vbvar 0)))) in Hres
    by (rewrite cty_open_preserves_depth; lia).
  rewrite (ty_denote_gas_saturate (S (S gas_tgt''))
    (<[LVFree y := erase_ty (CTOver bx φx)]> Σ)
    (cty_open 0 y τr)
    (open_tm 0 (vfvar y)
      (tapp_tm (tm_shift 0 ef) (vbvar 0))))
    by (rewrite cty_open_preserves_depth; lia).
  exact Hres.
Qed.

Lemma arrow_result_first_open_value_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr Tf f (mf : WfWorldT) :
  lty_env_closed Σ ->
  LVFree f ∉ dom Σ ->
  lc_context_ty (CTOver bx φx) ->
  lc_context_ty (cty_shift 0 (CTOver bx φx)) ->
  cty_lc_at 1 τr ->
  f ∉ qual_dom φx ->
  f ∉ fv_cty τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  formula_scoped_in_world mf
    (formula_open 0 f
      (arrow_value_denote_gas_with ty_denote_gas gas_tgt
        (typed_lty_env_bind Σ Tf)
        (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
        (tret (vbvar 0)))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas_src
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
      (tret (vbvar 0))) ->
  mf ⊨ formula_open 0 f
    (arrow_value_denote_gas_with ty_denote_gas gas_tgt
      (typed_lty_env_bind Σ Tf)
      (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
      (tret (vbvar 0))).
Proof.
  intros HΣclosed HfΣ Hlc_over Hlc_shift_over Hlcτr Hfφ Hfτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hscope_tgt Hvalue_src.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas_tgt Σ (CTPersist (CTOver bx φx)) τr Tf f) in Hscope_tgt.
  2: exact HΣclosed.
  2: exact HfΣ.
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2: exact Hlcτr.
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2: exact Hfτr.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas_src Σ (CTOver bx φx) τr Tf f) in Hvalue_src.
  2: exact HΣclosed.
  2: exact HfΣ.
  2: exact Hlc_over.
  2: exact Hlcτr.
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2: exact Hfτr.
  rewrite (formula_open_result_first_arrow_value_ret_bvar0
    gas_tgt Σ (CTPersist (CTOver bx φx)) τr Tf f).
  2: exact HΣclosed.
  2: exact HfΣ.
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2: exact Hlcτr.
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφ.
  }
  2: exact Hfτr.
  eapply arrow_value_over_arg_to_persist_over_arg_plain.
  - apply lty_env_closed_insert_free; assumption.
  - exact Hlc_over.
  - exact Hlcτr.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - exact Hscope_tgt.
  - exact Hvalue_src.
Qed.

Lemma ty_denote_gas_arrow_over_arg_to_persist_over_arg
    gas_src gas_tgt (Σ : lty_env) bx φx τr e (m : WfWorldT) :
  lty_env_closed Σ ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  cty_depth τr <= gas_src ->
  cty_depth τr <= gas_tgt ->
  1 <= gas_src ->
  2 <= gas_tgt ->
  m ⊨ ty_denote_gas (S gas_src) Σ
    (CTArrow (CTOver bx φx) τr) e ->
  m ⊨ ty_denote_gas (S gas_tgt) Σ
    (CTArrow (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros HΣclosed Hlc_over Hlcτr
    Hres_src Hres_tgt Harg_src Harg_tgt Hden.
  pose proof (ty_denote_gas_guard (S gas_src) Σ
    (CTArrow (CTOver bx φx) τr) e m Hden) as Hguard_src.
  change (m ⊨ ty_guard_formula
    (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
    (CTArrow (CTOver bx φx) τr) e) in Hguard_src.
  assert (Hbody_src :
      m ⊨ FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)))
            (tm_shift 0 e) (LVBound 0))
          (arrow_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
              (erase_ty (CTArrow (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0))))).
  {
    change (m ⊨ FAnd
      (ty_guard_formula
        (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
        (CTArrow (CTOver bx φx) τr) e)
      (FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)))
            (tm_shift 0 e) (LVBound 0))
          (arrow_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
              (erase_ty (CTArrow (CTOver bx φx) τr)))
            (cty_shift 0 (CTOver bx φx)) (cty_shift 1 τr)
            (tret (vbvar 0)))))) in Hden.
    eapply res_models_and_elim_r. exact Hden.
  }
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
        (CTArrow (CTPersist (CTOver bx φx)) τr) e).
  { apply ty_guard_arrow_over_arg_to_persist_over_arg. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hlc_shift_over : lc_context_ty (cty_shift 0 (CTOver bx φx))).
  { apply cty_lc_at_shift_at. exact Hlc_over. }
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas_tgt) Σ
          (CTArrow (CTPersist (CTOver bx φx)) τr) e)).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  destruct (res_models_forall_rev _ _ Hbody_src) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (Σg := relevant_env Σ (CTArrow (CTOver bx φx) τr) e).
  exists (Lsrc ∪ lvars_fv (dom Σg) ∪ qual_dom φx ∪
    fv_cty τr ∪ fv_tm e).
  intros f Hf mf Hdom Hrestrict.
  assert (HfΣg : LVFree f ∉ dom (Σg : lty_env)).
  {
    intros Hbad.
    apply lvars_fv_elem in Hbad.
    clear -Hf Hbad. set_solver.
  }
  assert (Hfφ : f ∉ qual_dom φx).
  { clear -Hf. set_solver. }
  assert (Hfτr : f ∉ fv_cty τr).
  { clear -Hf. set_solver. }
  assert (Hfe : f ∉ fv_tm e).
  { clear -Hf. set_solver. }
  pose proof (formula_scoped_forall_open_res_le m mf f
    (FImpl
      (expr_result_formula_at
        (lvars_shift_from 0
          (dom (relevant_env Σ
            (CTArrow (CTPersist (CTOver bx φx)) τr) e)))
        (tm_shift 0 e) (LVBound 0))
      (arrow_value_denote_gas_with ty_denote_gas gas_tgt
        (typed_lty_env_bind
          (relevant_env Σ
            (CTArrow (CTPersist (CTOver bx φx)) τr) e)
          (erase_ty (CTArrow (CTPersist (CTOver bx φx)) τr)))
        (cty_shift 0 (CTPersist (CTOver bx φx))) (cty_shift 1 τr)
        (tret (vbvar 0))))
    Hscope_forall
    ltac:(rewrite <- Hrestrict; apply res_restrict_le)
    ltac:(rewrite Hdom; apply elem_of_union_r; apply elem_of_singleton;
      reflexivity)) as Hscope_open.
  cbn [formula_open].
  eapply res_models_impl_intro.
  { cbn [formula_open] in Hscope_open. exact Hscope_open. }
  intros Hresult_tgt.
  pose proof (Hsrc f ltac:(subst Σg; clear -Hf; set_solver)
    mf Hdom Hrestrict) as Hopened_src.
  cbn [formula_open] in Hopened_src.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hresult_tgt)
    as Hvalue_src.
  eapply arrow_result_first_open_value_over_arg_to_persist_over_arg.
  - subst Σg. apply relevant_env_closed. exact HΣclosed.
  - exact HfΣg.
  - exact Hlc_over.
  - exact Hlc_shift_over.
  - exact Hlcτr.
  - exact Hfφ.
  - exact Hfτr.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Harg_src.
  - exact Harg_tgt.
  - subst Σg.
    change (relevant_env Σ (CTArrow (CTPersist (CTOver bx φx)) τr) e)
      with (relevant_env Σ (CTArrow (CTOver bx φx) τr) e)
      in Hscope_open.
    change (erase_ty (CTArrow (CTPersist (CTOver bx φx)) τr))
      with (erase_ty (CTArrow (CTOver bx φx) τr))
      in Hscope_open.
    eapply formula_scoped_impl_r. exact Hscope_open.
	  - subst Σg. exact Hvalue_src.
Qed.

Lemma ty_denote_arrow_over_arg_to_persist_over_arg
    Δ bx φx τr e (m : WfWorldT) :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 τr ->
  m ⊨ ty_denote Δ (CTArrow (CTOver bx φx) τr) e ->
  m ⊨ ty_denote Δ (CTArrow (CTPersist (CTOver bx φx)) τr) e.
Proof.
  intros HΔclosed Hlc_over Hlcτr Hden.
  unfold ty_denote in *.
  cbn [cty_depth].
  eapply ty_denote_gas_arrow_over_arg_to_persist_over_arg.
  - exact HΔclosed.
  - exact Hlc_over.
  - exact Hlcτr.
  - apply Nat.le_max_r.
  - apply Nat.le_max_r.
  - apply Nat.le_max_l.
  - apply Nat.le_max_l.
  - exact Hden.
Qed.

Theorem ty_denote_arrow_over_param_persist_over_result_forward
    Δ bx φx br φr e :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 (CTOver br φr) ->
  ty_denote Δ (CTArrow (CTOver bx φx) (CTOver br φr)) e ⊫
  ty_denote Δ
    (CTArrow (CTPersist (CTOver bx φx)) (CTOver br φr)) e.
Proof.
  unfold entails.
  intros HΔclosed Hlc_arg Hlc_res m Hden.
	  eapply ty_denote_arrow_over_arg_to_persist_over_arg; eauto.
Qed.

Theorem ty_denote_arrow_over_param_persist_under_result_forward
    Δ bx φx br φr e :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  lc_context_ty (CTOver bx φx) ->
  cty_lc_at 1 (CTUnder br φr) ->
  ty_denote Δ (CTArrow (CTOver bx φx) (CTUnder br φr)) e ⊫
  ty_denote Δ
    (CTArrow (CTPersist (CTOver bx φx)) (CTUnder br φr)) e.
Proof.
  unfold entails.
  intros HΔclosed Hlc_arg Hlc_res m Hden.
  eapply ty_denote_arrow_over_arg_to_persist_over_arg; eauto.
Qed.

End TypePersist.
