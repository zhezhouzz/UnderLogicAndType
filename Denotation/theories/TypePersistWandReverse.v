(** * Denotation.TypePersistWandReverse

    Reverse Wand facts for persistent-over arguments. *)

From Denotation Require Import Notation TypeDenote TypeDenoteRegular ResultFirstOpen
  DenotationSetMapFacts TypeEquivCore TypeEquivFiberBaseCore TypeEquivFiberBaseProjected TypeEquivBody TypeEquiv
  TypePersistBase TypePersistArrow TypePersistSingleton TypePersistWandForward.
From ContextAlgebra Require Import ResourceAlgebra.

Section TypePersist.

Local Ltac persist_eta_fresh_from H :=
  clear -H; set_solver.

Local Ltac persist_outer_fresh_from H :=
  clear -H; set_solver.

Local Ltac persist_lvar_fresh_from H :=
  intros Hbad; apply lvars_fv_elem in Hbad; clear -H Hbad; set_solver.

Lemma wand_value_ret_fvar_persist_over_arg_to_over_arg_over_result
    gas_src gas_tgt (Σ : lty_env) bx φx br φr f Tf
    (m : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed Σ ->
  Σ !! LVFree f = Some Tf ->
  cty_lc_at 1 (CTOver br φr) ->
  cty_depth (CTOver br φr) <= gas_src ->
  cty_depth (CTOver br φr) <= gas_tgt ->
  2 <= gas_src ->
  1 <= gas_tgt ->
  formula_scoped_in_world m
    (wand_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (CTOver bx φx) (CTOver br φr) (tret (vfvar f))) ->
  m ⊨ wand_value_denote_gas_with ty_denote_gas gas_src Σ
    (CTPersist (CTOver bx φx)) (CTOver br φr) (tret (vfvar f)) ->
  m ⊨ wand_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (CTOver bx φx) (CTOver br φr) (tret (vfvar f)).
Proof.
  intros Hbasic_over HΣclosed HΣf Hlc_res
    Hres_src_depth Hres_tgt_depth Hsrc_pos Htgt_pos Hscope_tgt Hvalue_src.
  pose proof (basic_context_ty_lc ∅ (CTOver bx φx) Hbasic_over)
    as Hlc_over.
  cbn [wand_value_denote_gas_with] in Hvalue_src |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_src' as [|gas_src'']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  eapply res_models_fbwand_intro; [exact Hscope_tgt|].
  destruct (res_models_fbwand_rev _ _ _ _ Hvalue_src) as [Lsrc Hsrc].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Σ) ∪
    qual_dom φx ∪ qual_dom φr ∪ {[f]}).
  intros η n Hc Hbind Hηfresh Hdom_prod Harg_open.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite formula_open_env_singleton in Harg_open |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
  rewrite open_env_atoms_empty in Hdom_prod.
  assert (Hym : y ∉ world_dom (m : WorldT)) by
    persist_eta_fresh_from Hηfresh.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by
    persist_eta_fresh_from Hηfresh.
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyφx : y ∉ qual_dom φx) by
    persist_eta_fresh_from Hηfresh.
  assert (Hyφr : y ∉ qual_dom φr) by
    persist_eta_fresh_from Hηfresh.
  assert (Hyf : y <> f) by persist_eta_fresh_from Hηfresh.
  assert (Harg_over_tgt :
      n ⊨ ty_denote_gas (S gas_tgt')
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y))).
  {
    rewrite formula_open_ty_denote_gas_singleton in Harg_open.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{ cbn [fv_tm fv_value]. apply not_elem_of_empty. }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφx.
    }
    replace (lvar_store_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
      with (<[LVFree y := TBase bx]> Σ) in Harg_open.
    2:{
      symmetry.
      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
    }
	    rewrite cty_open_shift_from_lc_fresh in Harg_open.
	    2: exact Hlc_over.
	    2:{
	      unfold fv_cty, qual_dom in *.
	      cbn [context_ty_lvars context_ty_lvars_at] in *.
	      rewrite lvars_fv_lvars_at_depth.
	      exact Hyφx.
	    }
    cbn [open_tm open_value] in Harg_open.
    exact Harg_open.
  }
  rewrite formula_open_ty_denote_gas_singleton.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. subst. exact (Hyf eq_refl).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{
    unfold fv_cty, qual_dom.
    cbn [context_ty_lvars context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    exact Hyφr.
  }
  rewrite typed_lty_env_bind_open_current.
  2:{ exact HyΣlv. }
  2:{ exact HΣclosed. }
  change (erase_ty (CTOver bx φx)) with (TBase bx).
  replace (cty_open 0 y (CTOver br φr))
    with (CTOver br (qual_open_atom 1 y φr)) by reflexivity.
  cbn [tm_shift value_shift open_tm open_value].
  eapply (fiberwise_joinable_on_ty_denote_gas_over
    ({[y]} : aset) (S gas_tgt')
    (<[LVFree y := TBase bx]> Σ) br (qual_open_atom 1 y φr)
    (tapp_tm (tret (vfvar f)) (vfvar y))).
  - apply lty_env_closed_insert_free. exact HΣclosed.
  - apply lc_tapp_tm; constructor; constructor.
  - eapply tm_lvars_tapp_ret_fvar_fvar_relevant_env_dom.
    + rewrite lookup_insert_ne by
        (intros Heq; inversion Heq; subst; exact (Hyf eq_refl)).
      exact HΣf.
    + rewrite lookup_insert_eq. reflexivity.
  - eapply singleton_lvar_subset_tapp_ret_fvar_fvar_relevant_env_dom.
    + rewrite lookup_insert_ne by
        (intros Heq; inversion Heq; subst; exact (Hyf eq_refl)).
      exact HΣf.
    + rewrite lookup_insert_eq. reflexivity.
  - intros σp pfib Hproj_p.
    destruct (res_fiber_product_subset_of_projection
      n m pfib ({[y]} : aset) σp Hc Hproj_p)
      as [σn [σm [nfib [mfib [Hc_fib [Hproj_n [Hproj_m Hle]]]]]]].
	    assert (Hmfib_eq : mfib = m).
	    {
	      eapply res_fiber_from_projection_fresh_eq.
	      - intros a Ha Hm.
	        apply elem_of_singleton in Ha. subst a. exact (Hym Hm).
	      - exact Hproj_m.
	    }
    subst mfib.
    assert (Harg_over_src_gas :
        n ⊨ ty_denote_gas (S gas_src'')
          (<[LVFree y := TBase bx]> Σ)
          (CTOver bx φx) (tret (vfvar y))).
    {
      rewrite (ty_denote_gas_saturate (S gas_tgt')
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y))) in Harg_over_tgt
        by (cbn [cty_depth]; lia).
      rewrite (ty_denote_gas_saturate (S gas_src'')
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y)))
        by (cbn [cty_depth]; lia).
      exact Harg_over_tgt.
    }
    assert (Harg_persist_fib :
        nfib ⊨ ty_denote_gas (S (S gas_src''))
          (<[LVFree y := TBase bx]> Σ)
          (CTPersist (CTOver bx φx)) (tret (vfvar y))).
    {
      eapply wand_arg_fiber_models_persist_over_arg.
      - exact Hbasic_over.
      - exact HΣclosed.
      - exact HyΣ.
      - exact Hyφx.
      - exact Hproj_n.
      - exact Harg_over_src_gas.
    }
    assert (Harg_persist_open :
        nfib ⊨ formula_open 0 y
          (ty_denote_gas (S (S gas_src''))
            (typed_lty_env_bind Σ
              (erase_ty (CTPersist (CTOver bx φx))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (tret (vbvar 0)))).
    {
      rewrite formula_open_ty_denote_gas_singleton.
      2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
      2:{ cbn [fv_tm fv_value]. apply not_elem_of_empty. }
      2:{
        rewrite cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφx.
      }
      rewrite typed_lty_env_bind_open_current.
      2:{ exact HyΣlv. }
      2:{ exact HΣclosed. }
	      rewrite cty_open_shift_from_lc_fresh.
	      2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
	      2:{
	        unfold fv_cty, qual_dom in *.
	        cbn [context_ty_lvars context_ty_lvars_at] in *.
	        rewrite lvars_fv_lvars_at_depth.
	        exact Hyφx.
	      }
      change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx).
      exact Harg_persist_fib.
    }
    assert (Hdom_fib :
        world_dom (res_product nfib m Hc_fib : WorldT) =
          world_dom (m : WorldT) ∪ {[y]}).
	    {
	      rewrite res_product_dom.
	      rewrite (res_fiber_from_projection_world_dom n nfib ({[y]} : aset)
	        σn Hproj_n).
	      rewrite res_product_dom in Hdom_prod.
	      replace (world_dom (m : WorldT) ∪ ({[y]} ∪ ∅))
	        with (world_dom (m : WorldT) ∪ {[y]}) in Hdom_prod
	        by (symmetry; apply union_singleton_empty_r).
	      exact Hdom_prod.
	    }
    pose proof (res_models_fbwand_open_one_named_fresh
      m nfib y
      (ty_denote_gas (S (S gas_src''))
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        (cty_shift 0 (CTPersist (CTOver bx φx))) (tret (vbvar 0)))
      (ty_denote_gas (S (S gas_src''))
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        (CTOver br φr)
        (tapp_tm (tm_shift 0 (tret (vfvar f))) (vbvar 0)))
      Hc_fib Hvalue_src Hym Hdom_fib Harg_persist_open)
      as Hres_src_open.
    rewrite formula_open_ty_denote_gas_singleton in Hres_src_open.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{
      rewrite fv_tapp_tm, tm_shift_fv.
      cbn [fv_tm fv_value].
      intros Hin. apply elem_of_union in Hin as [Hin|Hin].
      - apply elem_of_singleton in Hin. subst.
        clear -Hyf. congruence.
      - rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      unfold fv_cty, qual_dom.
      cbn [context_ty_lvars context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφr.
    }
    rewrite typed_lty_env_bind_open_current in Hres_src_open.
    2:{ exact HyΣlv. }
    2:{ exact HΣclosed. }
    change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx)
      in Hres_src_open.
    replace (cty_open 0 y (CTOver br φr))
      with (CTOver br (qual_open_atom 1 y φr)) in Hres_src_open
      by reflexivity.
    cbn [tm_shift value_shift open_tm open_value] in Hres_src_open.
    rewrite (ty_denote_gas_saturate (S (S gas_src''))
      (<[LVFree y := TBase bx]> Σ)
      (CTOver br (qual_open_atom 1 y φr))
      (tapp_tm (tret (vfvar f)) (vfvar y))) in Hres_src_open
      by (cbn [cty_depth]; lia).
    rewrite (ty_denote_gas_saturate (S gas_tgt')
      (<[LVFree y := TBase bx]> Σ)
      (CTOver br (qual_open_atom 1 y φr))
      (tapp_tm (tret (vfvar f)) (vfvar y)))
      by (cbn [cty_depth]; lia).
    eapply res_models_kripke; [exact Hle|exact Hres_src_open].
Qed.

Lemma wand_value_ret_fvar_persist_over_arg_to_over_arg_under_result
    gas_src gas_tgt (Σ : lty_env) bx φx br φr f Tf
    (m : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed Σ ->
  Σ !! LVFree f = Some Tf ->
  cty_lc_at 1 (CTUnder br φr) ->
  cty_depth (CTUnder br φr) <= gas_src ->
  cty_depth (CTUnder br φr) <= gas_tgt ->
  2 <= gas_src ->
  1 <= gas_tgt ->
  formula_scoped_in_world m
    (wand_value_denote_gas_with ty_denote_gas gas_tgt Σ
      (CTOver bx φx) (CTUnder br φr) (tret (vfvar f))) ->
  m ⊨ wand_value_denote_gas_with ty_denote_gas gas_src Σ
    (CTPersist (CTOver bx φx)) (CTUnder br φr) (tret (vfvar f)) ->
  m ⊨ wand_value_denote_gas_with ty_denote_gas gas_tgt Σ
    (CTOver bx φx) (CTUnder br φr) (tret (vfvar f)).
Proof.
  intros Hbasic_over HΣclosed HΣf Hlc_res
    Hres_src_depth Hres_tgt_depth Hsrc_pos Htgt_pos Hscope_tgt Hvalue_src.
  pose proof (basic_context_ty_lc ∅ (CTOver bx φx) Hbasic_over)
    as Hlc_over.
  cbn [wand_value_denote_gas_with] in Hvalue_src |- *.
  destruct gas_src as [|gas_src']; [lia|].
  destruct gas_src' as [|gas_src'']; [lia|].
  destruct gas_tgt as [|gas_tgt']; [lia|].
  eapply res_models_fbwand_intro; [exact Hscope_tgt|].
  destruct (res_models_fbwand_rev _ _ _ _ Hvalue_src) as [Lsrc Hsrc].
  exists (Lsrc ∪ world_dom (m : WorldT) ∪ lvars_fv (dom Σ) ∪
    qual_dom φx ∪ qual_dom φr ∪ {[f]}).
  intros η n Hc Hbind Hηfresh Hdom_prod Harg_open.
  destruct (open_env_binds_one_inv η Hbind) as [y ->].
  rewrite formula_open_env_singleton in Harg_open |- *.
  rewrite open_env_atoms_insert in Hηfresh by apply lookup_empty.
  rewrite open_env_atoms_empty in Hηfresh.
  rewrite open_env_atoms_insert in Hdom_prod by apply lookup_empty.
  rewrite open_env_atoms_empty in Hdom_prod.
  assert (Hym : y ∉ world_dom (m : WorldT)) by
    persist_eta_fresh_from Hηfresh.
  assert (HyΣ : y ∉ lvars_fv (dom Σ)) by
    persist_eta_fresh_from Hηfresh.
  assert (HyΣlv : LVFree y ∉ dom (Σ : lty_env)).
  {
    intros Hbad. apply HyΣ.
    apply lvars_fv_elem. exact Hbad.
  }
  assert (Hyφx : y ∉ qual_dom φx) by
    persist_eta_fresh_from Hηfresh.
  assert (Hyφr : y ∉ qual_dom φr) by
    persist_eta_fresh_from Hηfresh.
  assert (Hyf : y <> f) by persist_eta_fresh_from Hηfresh.
  assert (Harg_over_tgt :
      n ⊨ ty_denote_gas (S gas_tgt')
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y))).
  {
    rewrite formula_open_ty_denote_gas_singleton in Harg_open.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{ cbn [fv_tm fv_value]. apply not_elem_of_empty. }
    2:{
      rewrite cty_shift_fv.
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφx.
    }
    replace (lvar_store_open_one 0 y
      (typed_lty_env_bind Σ (erase_ty (CTOver bx φx))))
      with (<[LVFree y := TBase bx]> Σ) in Harg_open.
    2:{
      symmetry.
      apply typed_lty_env_bind_open_current; [exact HyΣlv|exact HΣclosed].
    }
	    rewrite cty_open_shift_from_lc_fresh in Harg_open.
	    2: exact Hlc_over.
	    2:{
	      unfold fv_cty, qual_dom in *.
	      cbn [context_ty_lvars context_ty_lvars_at] in *.
	      rewrite lvars_fv_lvars_at_depth.
	      exact Hyφx.
	    }
    cbn [open_tm open_value] in Harg_open.
    exact Harg_open.
  }
  rewrite formula_open_ty_denote_gas_singleton.
  2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
  2:{
    rewrite fv_tapp_tm, tm_shift_fv.
    cbn [fv_tm fv_value].
    intros Hin. apply elem_of_union in Hin as [Hin|Hin].
    - apply elem_of_singleton in Hin. subst. exact (Hyf eq_refl).
    - rewrite elem_of_empty in Hin. contradiction.
  }
  2:{
    unfold fv_cty, qual_dom.
    cbn [context_ty_lvars context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    exact Hyφr.
  }
  rewrite typed_lty_env_bind_open_current.
  2:{ exact HyΣlv. }
  2:{ exact HΣclosed. }
  change (erase_ty (CTOver bx φx)) with (TBase bx).
  replace (cty_open 0 y (CTUnder br φr))
    with (CTUnder br (qual_open_atom 1 y φr)) by reflexivity.
  cbn [tm_shift value_shift open_tm open_value].
  eapply (fiberwise_joinable_on_ty_denote_gas_under
    ({[y]} : aset) (S gas_tgt')
    (<[LVFree y := TBase bx]> Σ) br (qual_open_atom 1 y φr)
    (tapp_tm (tret (vfvar f)) (vfvar y))).
  - apply lty_env_closed_insert_free. exact HΣclosed.
  - apply lc_tapp_tm; constructor; constructor.
  - eapply tm_lvars_tapp_ret_fvar_fvar_relevant_env_dom.
    + rewrite lookup_insert_ne by
        (intros Heq; inversion Heq; subst; exact (Hyf eq_refl)).
      exact HΣf.
    + rewrite lookup_insert_eq. reflexivity.
  - eapply singleton_lvar_subset_tapp_ret_fvar_fvar_relevant_env_dom.
    + rewrite lookup_insert_ne by
        (intros Heq; inversion Heq; subst; exact (Hyf eq_refl)).
      exact HΣf.
    + rewrite lookup_insert_eq. reflexivity.
  - intros σp pfib Hproj_p.
    destruct (res_fiber_product_subset_of_projection
      n m pfib ({[y]} : aset) σp Hc Hproj_p)
      as [σn [σm [nfib [mfib [Hc_fib [Hproj_n [Hproj_m Hle]]]]]]].
    assert (Hmfib_eq : mfib = m).
    {
      eapply res_fiber_from_projection_fresh_eq.
      - intros a Ha Hm.
        apply elem_of_singleton in Ha. subst a. exact (Hym Hm).
      - exact Hproj_m.
    }
    subst mfib.
    assert (Harg_over_src_gas :
        n ⊨ ty_denote_gas (S gas_src'')
          (<[LVFree y := TBase bx]> Σ)
          (CTOver bx φx) (tret (vfvar y))).
    {
      rewrite (ty_denote_gas_saturate (S gas_tgt')
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y))) in Harg_over_tgt
        by (cbn [cty_depth]; lia).
      rewrite (ty_denote_gas_saturate (S gas_src'')
        (<[LVFree y := TBase bx]> Σ)
        (CTOver bx φx) (tret (vfvar y)))
        by (cbn [cty_depth]; lia).
      exact Harg_over_tgt.
    }
    assert (Harg_persist_fib :
        nfib ⊨ ty_denote_gas (S (S gas_src''))
          (<[LVFree y := TBase bx]> Σ)
          (CTPersist (CTOver bx φx)) (tret (vfvar y))).
    {
      eapply wand_arg_fiber_models_persist_over_arg.
      - exact Hbasic_over.
      - exact HΣclosed.
      - exact HyΣ.
      - exact Hyφx.
      - exact Hproj_n.
      - exact Harg_over_src_gas.
    }
    assert (Harg_persist_open :
        nfib ⊨ formula_open 0 y
          (ty_denote_gas (S (S gas_src''))
            (typed_lty_env_bind Σ
              (erase_ty (CTPersist (CTOver bx φx))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (tret (vbvar 0)))).
    {
      rewrite formula_open_ty_denote_gas_singleton.
      2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
      2:{ cbn [fv_tm fv_value]. apply not_elem_of_empty. }
      2:{
        rewrite cty_shift_fv.
        unfold fv_cty, qual_dom in *.
        cbn [context_ty_lvars context_ty_lvars_at] in *.
        rewrite lvars_fv_lvars_at_depth.
        exact Hyφx.
      }
      rewrite typed_lty_env_bind_open_current.
      2:{ exact HyΣlv. }
      2:{ exact HΣclosed. }
	      rewrite cty_open_shift_from_lc_fresh.
	      2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
	      2:{
	        unfold fv_cty, qual_dom in *.
	        cbn [context_ty_lvars context_ty_lvars_at] in *.
	        rewrite lvars_fv_lvars_at_depth.
	        exact Hyφx.
	      }
      change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx).
      exact Harg_persist_fib.
    }
    assert (Hdom_fib :
        world_dom (res_product nfib m Hc_fib : WorldT) =
          world_dom (m : WorldT) ∪ {[y]}).
    {
	      rewrite res_product_dom.
	      rewrite (res_fiber_from_projection_world_dom n nfib ({[y]} : aset)
	        σn Hproj_n).
	      rewrite res_product_dom in Hdom_prod.
	      replace (world_dom (m : WorldT) ∪ ({[y]} ∪ ∅))
	        with (world_dom (m : WorldT) ∪ {[y]}) in Hdom_prod
	        by (symmetry; apply union_singleton_empty_r).
      exact Hdom_prod.
    }
    pose proof (res_models_fbwand_open_one_named_fresh
      m nfib y
      (ty_denote_gas (S (S gas_src''))
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        (cty_shift 0 (CTPersist (CTOver bx φx))) (tret (vbvar 0)))
      (ty_denote_gas (S (S gas_src''))
        (typed_lty_env_bind Σ
          (erase_ty (CTPersist (CTOver bx φx))))
        (CTUnder br φr)
        (tapp_tm (tm_shift 0 (tret (vfvar f))) (vbvar 0)))
      Hc_fib Hvalue_src Hym Hdom_fib Harg_persist_open)
      as Hres_src_open.
    rewrite formula_open_ty_denote_gas_singleton in Hres_src_open.
    2:{ rewrite typed_lty_env_bind_lvars_fv_dom. exact HyΣ. }
    2:{
      rewrite fv_tapp_tm, tm_shift_fv.
      cbn [fv_tm fv_value].
      intros Hin. apply elem_of_union in Hin as [Hin|Hin].
      - apply elem_of_singleton in Hin. subst.
        clear -Hyf. congruence.
      - rewrite elem_of_empty in Hin. contradiction.
    }
    2:{
      unfold fv_cty, qual_dom.
      cbn [context_ty_lvars context_ty_lvars_at].
      rewrite lvars_fv_lvars_at_depth.
      exact Hyφr.
    }
    rewrite typed_lty_env_bind_open_current in Hres_src_open.
    2:{ exact HyΣlv. }
    2:{ exact HΣclosed. }
    change (erase_ty (CTPersist (CTOver bx φx))) with (TBase bx)
      in Hres_src_open.
    replace (cty_open 0 y (CTUnder br φr))
      with (CTUnder br (qual_open_atom 1 y φr)) in Hres_src_open
      by reflexivity.
    cbn [tm_shift value_shift open_tm open_value] in Hres_src_open.
    rewrite (ty_denote_gas_saturate (S (S gas_src''))
      (<[LVFree y := TBase bx]> Σ)
      (CTUnder br (qual_open_atom 1 y φr))
      (tapp_tm (tret (vfvar f)) (vfvar y))) in Hres_src_open
      by (cbn [cty_depth]; lia).
    rewrite (ty_denote_gas_saturate (S gas_tgt')
      (<[LVFree y := TBase bx]> Σ)
      (CTUnder br (qual_open_atom 1 y φr))
      (tapp_tm (tret (vfvar f)) (vfvar y)))
      by (cbn [cty_depth]; lia).
    eapply res_models_kripke; [exact Hle|exact Hres_src_open].
Qed.

Lemma ty_denote_gas_wand_persist_over_arg_to_over_arg_over_result
    gas_src gas_tgt (Σ : lty_env) bx φx br φr e (m : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed Σ ->
  cty_lc_at 1 (CTOver br φr) ->
  cty_depth (CTOver br φr) <= gas_src ->
  cty_depth (CTOver br φr) <= gas_tgt ->
  2 <= gas_src ->
  1 <= gas_tgt ->
  m ⊨ ty_denote_gas (S gas_src) Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e ->
  m ⊨ ty_denote_gas (S gas_tgt) Σ
    (CTWand (CTOver bx φx) (CTOver br φr)) e.
Proof.
  intros Hbasic_over HΣclosed Hlc_res
    Hres_src Hres_tgt Hsrc_pos Htgt_pos Hden.
  pose proof (basic_context_ty_lc ∅ (CTOver bx φx) Hbasic_over)
    as Hlc_over.
  pose proof (ty_denote_gas_guard (S gas_src) Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e m Hden)
    as Hguard_src.
  change (m ⊨ ty_guard_formula
    (relevant_env Σ
      (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
    in Hguard_src.
  assert (Hbody_src :
      m ⊨ FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
              (erase_ty
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (cty_shift 1 (CTOver br φr))
            (tret (vbvar 0))))).
  {
    change (m ⊨ FAnd
      (ty_guard_formula
        (relevant_env Σ
          (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
        (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
      (FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
              (erase_ty
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (cty_shift 1 (CTOver br φr))
            (tret (vbvar 0)))))) in Hden.
    eapply res_models_and_elim_r. exact Hden.
  }
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
        (CTWand (CTOver bx φx) (CTOver br φr)) e).
  { apply ty_guard_wand_persist_over_arg_to_over_arg. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas_tgt) Σ
          (CTWand (CTOver bx φx) (CTOver br φr)) e)).
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
  set (Σg := relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e).
  exists (Lsrc ∪ lvars_fv (dom Σg) ∪ qual_dom φx ∪
    qual_dom φr ∪ fv_tm e).
  intros f Hf mf Hdom Hrestrict.
  assert (Hscope_open :
      formula_scoped_in_world mf
        (formula_open 0 f
          (FImpl
            (expr_result_formula_at
              (lvars_shift_from 0
                (dom (relevant_env Σ
                  (CTWand (CTOver bx φx) (CTOver br φr)) e)))
              (tm_shift 0 e) (LVBound 0))
            (wand_value_denote_gas_with ty_denote_gas gas_tgt
              (typed_lty_env_bind
                (relevant_env Σ
                  (CTWand (CTOver bx φx) (CTOver br φr)) e)
                (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))))
              (cty_shift 0 (CTOver bx φx))
              (cty_shift 1 (CTOver br φr))
              (tret (vbvar 0)))))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  cbn [formula_open].
  eapply res_models_impl_intro.
  { cbn [formula_open] in Hscope_open. exact Hscope_open. }
  intros Hresult_tgt.
  assert (HfΣg : LVFree f ∉ dom (Σg : lty_env)).
  { persist_lvar_fresh_from Hf. }
  assert (Hfφx : f ∉ qual_dom φx).
  { persist_outer_fresh_from Hf. }
  assert (Hfφr : f ∉ qual_dom φr).
  { persist_outer_fresh_from Hf. }
  assert (Hopened_src :
      mf ⊨ formula_open 0 f
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0 (dom Σg))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind Σg
              (erase_ty
                (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (cty_shift 1 (CTOver br φr))
            (tret (vbvar 0))))).
  {
    subst Σg.
    apply Hsrc.
    - persist_outer_fresh_from Hf.
    - exact Hdom.
    - exact Hrestrict.
  }
  change (mf ⊨ FImpl
    (formula_open 0 f
      (expr_result_formula_at
        (lvars_shift_from 0 (dom Σg))
        (tm_shift 0 e) (LVBound 0)))
    (formula_open 0 f
      (wand_value_denote_gas_with ty_denote_gas gas_src
        (typed_lty_env_bind Σg
          (erase_ty
            (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr))))
        (cty_shift 0 (CTPersist (CTOver bx φx)))
        (cty_shift 1 (CTOver br φr))
        (tret (vbvar 0))))) in Hopened_src.
  change (relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
    in Hopened_src.
  change (erase_ty
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)))
    with (erase_ty (CTWand (CTOver bx φx) (CTOver br φr)))
    in Hopened_src.
  change (relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
    in Hresult_tgt.
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hresult_tgt)
    as Hvalue_src.
  assert (Hvalue_tgt_scope :
      formula_scoped_in_world mf
        (formula_open 0 f
          (wand_value_denote_gas_with ty_denote_gas gas_tgt
            (typed_lty_env_bind
              (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
              (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))))
            (cty_shift 0 (CTOver bx φx))
            (cty_shift 1 (CTOver br φr))
            (tret (vbvar 0))))).
  {
    change (formula_scoped_in_world mf
      (FImpl
        (formula_open 0 f
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ
                (CTWand (CTOver bx φx) (CTOver br φr)) e)))
            (tm_shift 0 e) (LVBound 0)))
        (formula_open 0 f
          (wand_value_denote_gas_with ty_denote_gas gas_tgt
            (typed_lty_env_bind
              (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
              (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))))
            (cty_shift 0 (CTOver bx φx))
            (cty_shift 1 (CTOver br φr))
            (tret (vbvar 0)))))) in Hscope_open.
    eapply formula_scoped_impl_r. exact Hscope_open.
  }
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_src Σg (CTPersist (CTOver bx φx)) (CTOver br φr)
    (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))) f)
    in Hvalue_src.
  2:{ subst Σg. apply relevant_env_closed. exact HΣclosed. }
  2:{ exact HfΣg. }
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2:{ exact Hlc_res. }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφx.
  }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφr.
  }
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_tgt (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
    (CTOver bx φx) (CTOver br φr)
    (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))) f)
    in Hvalue_tgt_scope.
  2:{ subst Σg. apply relevant_env_closed. exact HΣclosed. }
  2:{ exact HfΣg. }
  2:{ exact Hlc_over. }
  2:{ exact Hlc_res. }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφx.
  }
	  2:{
	    unfold fv_cty, qual_dom in *.
	    cbn [context_ty_lvars context_ty_lvars_at] in *.
	    rewrite lvars_fv_lvars_at_depth.
	    exact Hfφr.
	  }
  change (mf ⊨
    ((wand_value_denote_gas_with ty_denote_gas gas_tgt
      (typed_lty_env_bind
        (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
        (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))))
      (cty_shift 0 (CTOver bx φx)) (cty_shift 1 (CTOver br φr))
      (tret (vbvar 0)) ^^ f)%formula)).
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_tgt (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
    (CTOver bx φx) (CTOver br φr)
    (erase_ty (CTWand (CTOver bx φx) (CTOver br φr))) f).
  2:{ apply relevant_env_closed. exact HΣclosed. }
  2:{ exact HfΣg. }
  2:{ exact Hlc_over. }
  2:{ exact Hlc_res. }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφx.
  }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφr.
  }
  subst Σg.
  change (relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) (CTOver br φr)) e)
    in Hvalue_src.
  eapply wand_value_ret_fvar_persist_over_arg_to_over_arg_over_result.
  - exact Hbasic_over.
  - apply lty_env_closed_insert_free.
    apply relevant_env_closed. exact HΣclosed.
  - rewrite lookup_insert_eq. reflexivity.
  - exact Hlc_res.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Hsrc_pos.
  - exact Htgt_pos.
  - exact Hvalue_tgt_scope.
  - exact Hvalue_src.
Qed.

Lemma ty_denote_gas_wand_persist_over_arg_to_over_arg_under_result
    gas_src gas_tgt (Σ : lty_env) bx φx br φr e (m : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed Σ ->
  cty_lc_at 1 (CTUnder br φr) ->
  cty_depth (CTUnder br φr) <= gas_src ->
  cty_depth (CTUnder br φr) <= gas_tgt ->
  2 <= gas_src ->
  1 <= gas_tgt ->
  m ⊨ ty_denote_gas (S gas_src) Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e ->
  m ⊨ ty_denote_gas (S gas_tgt) Σ
    (CTWand (CTOver bx φx) (CTUnder br φr)) e.
Proof.
  intros Hbasic_over HΣclosed Hlc_res
    Hres_src Hres_tgt Hsrc_pos Htgt_pos Hden.
  pose proof (basic_context_ty_lc ∅ (CTOver bx φx) Hbasic_over)
    as Hlc_over.
  pose proof (ty_denote_gas_guard (S gas_src) Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e m Hden)
    as Hguard_src.
  change (m ⊨ ty_guard_formula
    (relevant_env Σ
      (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
    in Hguard_src.
  assert (Hbody_src :
      m ⊨ FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
              (erase_ty
                (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (cty_shift 1 (CTUnder br φr))
            (tret (vbvar 0))))).
  {
    change (m ⊨ FAnd
      (ty_guard_formula
        (relevant_env Σ
          (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
        (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
      (FForall
        (FImpl
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)))
            (tm_shift 0 e) (LVBound 0))
          (wand_value_denote_gas_with ty_denote_gas gas_src
            (typed_lty_env_bind
              (relevant_env Σ
                (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
              (erase_ty
                (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr))))
            (cty_shift 0 (CTPersist (CTOver bx φx)))
            (cty_shift 1 (CTUnder br φr))
            (tret (vbvar 0)))))) in Hden.
    eapply res_models_and_elim_r. exact Hden.
  }
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
        (CTWand (CTOver bx φx) (CTUnder br φr)) e).
  { apply ty_guard_wand_persist_over_arg_to_over_arg. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas_tgt) Σ
          (CTWand (CTOver bx φx) (CTUnder br φr)) e)).
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
  set (Σg := relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e).
  exists (Lsrc ∪ lvars_fv (dom Σg) ∪ qual_dom φx ∪
    qual_dom φr ∪ fv_tm e).
  intros f Hf mf Hdom Hrestrict.
  pose proof (formula_scoped_forall_open_res_le m mf f
    (FImpl
      (expr_result_formula_at
        (lvars_shift_from 0
          (dom (relevant_env Σ
            (CTWand (CTOver bx φx) (CTUnder br φr)) e)))
        (tm_shift 0 e) (LVBound 0))
      (wand_value_denote_gas_with ty_denote_gas gas_tgt
        (typed_lty_env_bind
          (relevant_env Σ
            (CTWand (CTOver bx φx) (CTUnder br φr)) e)
          (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))))
        (cty_shift 0 (CTOver bx φx))
        (cty_shift 1 (CTUnder br φr))
        (tret (vbvar 0))))
    Hscope_forall
    ltac:(rewrite <- Hrestrict; apply res_restrict_le)
    ltac:(rewrite Hdom; apply elem_of_union_r; apply elem_of_singleton;
      reflexivity)) as Hscope_open.
  cbn [formula_open].
  eapply res_models_impl_intro.
  { cbn [formula_open] in Hscope_open. exact Hscope_open. }
  intros Hresult_tgt.
  assert (HfΣg : LVFree f ∉ dom (Σg : lty_env)).
  { persist_lvar_fresh_from Hf. }
  assert (Hfφx : f ∉ qual_dom φx).
  { persist_outer_fresh_from Hf. }
  assert (Hfφr : f ∉ qual_dom φr).
  { persist_outer_fresh_from Hf. }
  pose proof (Hsrc f ltac:(subst Σg; persist_outer_fresh_from Hf)
    mf Hdom Hrestrict) as Hopened_src.
  cbn [formula_open] in Hopened_src.
  change (mf ⊨ FImpl
    (formula_open 0 f
      (expr_result_formula_at
        (lvars_shift_from 0 (dom Σg))
        (tm_shift 0 e) (LVBound 0)))
    (formula_open 0 f
      (wand_value_denote_gas_with ty_denote_gas gas_src
        (typed_lty_env_bind Σg
          (erase_ty
            (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr))))
        (cty_shift 0 (CTPersist (CTOver bx φx)))
        (cty_shift 1 (CTUnder br φr))
        (tret (vbvar 0))))) in Hopened_src.
  change (relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
    in Hopened_src.
  change (erase_ty
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)))
    with (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr)))
    in Hopened_src.
  change (relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
    in Hresult_tgt.
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_src Σg (CTPersist (CTOver bx φx)) (CTUnder br φr)
    (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))) f)
    in Hopened_src.
  2:{ subst Σg. apply relevant_env_closed. exact HΣclosed. }
  2:{ exact HfΣg. }
  2:{ cbn [lc_context_ty cty_lc_at]. exact Hlc_over. }
  2:{ exact Hlc_res. }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφx.
  }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφr.
  }
  pose proof (res_models_impl_elim _ _ _ Hopened_src Hresult_tgt)
    as Hvalue_src.
  assert (Hvalue_tgt_scope :
      formula_scoped_in_world mf
        (wand_value_denote_gas_with ty_denote_gas gas_tgt
          (<[LVFree f := erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))]>
            (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e))
          (CTOver bx φx) (CTUnder br φr) (tret (vfvar f)))).
  {
    change (formula_scoped_in_world mf
      (FImpl
        (formula_open 0 f
          (expr_result_formula_at
            (lvars_shift_from 0
              (dom (relevant_env Σ
                (CTWand (CTOver bx φx) (CTUnder br φr)) e)))
            (tm_shift 0 e) (LVBound 0)))
        (formula_open 0 f
          (wand_value_denote_gas_with ty_denote_gas gas_tgt
            (typed_lty_env_bind
              (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
              (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))))
            (cty_shift 0 (CTOver bx φx))
            (cty_shift 1 (CTUnder br φr))
            (tret (vbvar 0)))))) in Hscope_open.
    pose proof (formula_scoped_impl_r _ _ _ Hscope_open) as Hvalue_scope_open.
    rewrite (formula_open_result_first_wand_value_ret_bvar0
      gas_tgt (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
      (CTOver bx φx) (CTUnder br φr)
      (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))) f)
      in Hvalue_scope_open.
    2:{ subst Σg. apply relevant_env_closed. exact HΣclosed. }
    2:{ exact HfΣg. }
    2:{ exact Hlc_over. }
    2:{ exact Hlc_res. }
    2:{
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hfφx.
    }
    2:{
      unfold fv_cty, qual_dom in *.
      cbn [context_ty_lvars context_ty_lvars_at] in *.
      rewrite lvars_fv_lvars_at_depth.
      exact Hfφr.
    }
    exact Hvalue_scope_open.
  }
  change (mf ⊨
    ((wand_value_denote_gas_with ty_denote_gas gas_tgt
      (typed_lty_env_bind
        (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
        (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))))
      (cty_shift 0 (CTOver bx φx)) (cty_shift 1 (CTUnder br φr))
      (tret (vbvar 0)) ^^ f)%formula)).
  rewrite (formula_open_result_first_wand_value_ret_bvar0
    gas_tgt (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
    (CTOver bx φx) (CTUnder br φr)
    (erase_ty (CTWand (CTOver bx φx) (CTUnder br φr))) f).
  2:{ apply relevant_env_closed. exact HΣclosed. }
  2:{ exact HfΣg. }
  2:{ exact Hlc_over. }
  2:{ exact Hlc_res. }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφx.
  }
  2:{
    unfold fv_cty, qual_dom in *.
    cbn [context_ty_lvars context_ty_lvars_at] in *.
    rewrite lvars_fv_lvars_at_depth.
    exact Hfφr.
  }
  subst Σg.
  change (relevant_env Σ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e)
    with (relevant_env Σ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
    in Hvalue_src.
  eapply wand_value_ret_fvar_persist_over_arg_to_over_arg_under_result.
  - exact Hbasic_over.
  - apply lty_env_closed_insert_free.
    apply relevant_env_closed. exact HΣclosed.
  - rewrite lookup_insert_eq. reflexivity.
  - exact Hlc_res.
  - exact Hres_src.
  - exact Hres_tgt.
  - exact Hsrc_pos.
  - exact Htgt_pos.
  - exact Hvalue_tgt_scope.
  - exact Hvalue_src.
Qed.

Lemma ty_denote_wand_persist_over_arg_to_over_arg_over_result
    Δ bx φx br φr e (m : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed (atom_env_to_lty_env Δ) ->
  cty_lc_at 1 (CTOver br φr) ->
  m ⊨ ty_denote Δ
    (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e ->
  m ⊨ ty_denote Δ (CTWand (CTOver bx φx) (CTOver br φr)) e.
Proof.
  intros Hbasic_over HΔclosed Hlc_res Hden.
  unfold ty_denote in *.
  cbn [cty_depth] in *.
  eapply (ty_denote_gas_wand_persist_over_arg_to_over_arg_over_result
    (Nat.max (cty_depth (CTPersist (CTOver bx φx)))
      (cty_depth (CTOver br φr)))
    (Nat.max (cty_depth (CTOver bx φx))
      (cty_depth (CTOver br φr)))).
  - exact Hbasic_over.
  - exact HΔclosed.
  - exact Hlc_res.
  - cbn [cty_depth]; lia.
  - cbn [cty_depth]; lia.
  - cbn [cty_depth]; lia.
  - cbn [cty_depth]; lia.
  - exact Hden.
Qed.

Lemma ty_denote_wand_persist_over_arg_to_over_arg_under_result
    Δ bx φx br φr e (m : WfWorldT) :
  basic_context_ty ∅ (CTOver bx φx) ->
  lty_env_closed (atom_env_to_lty_env Δ) ->
  cty_lc_at 1 (CTUnder br φr) ->
  m ⊨ ty_denote Δ
    (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e ->
  m ⊨ ty_denote Δ (CTWand (CTOver bx φx) (CTUnder br φr)) e.
Proof.
  intros Hbasic_over HΔclosed Hlc_res Hden.
  unfold ty_denote in *.
  cbn [cty_depth] in *.
  eapply (ty_denote_gas_wand_persist_over_arg_to_over_arg_under_result
    (Nat.max (cty_depth (CTPersist (CTOver bx φx)))
      (cty_depth (CTUnder br φr)))
    (Nat.max (cty_depth (CTOver bx φx))
      (cty_depth (CTUnder br φr)))).
  - exact Hbasic_over.
  - exact HΔclosed.
  - exact Hlc_res.
  - cbn [cty_depth]; lia.
  - cbn [cty_depth]; lia.
  - cbn [cty_depth]; lia.
  - cbn [cty_depth]; lia.
  - exact Hden.
Qed.

Theorem ty_denote_wand_over_param_persist_over_result_equiv
    Δ bx φx br φr e :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  basic_context_ty ∅ (CTOver bx φx) ->
  cty_lc_at 1 (CTOver br φr) ->
  formula_equiv
    (ty_denote Δ (CTWand (CTOver bx φx) (CTOver br φr)) e)
    (ty_denote Δ
      (CTWand (CTPersist (CTOver bx φx)) (CTOver br φr)) e).
Proof.
  intros HΔclosed Hbasic_over Hlc_res.
  split; unfold entails; intros m Hden.
  - eapply ty_denote_wand_over_arg_to_persist_over_arg.
    + exact HΔclosed.
    + eapply basic_context_ty_lc. exact Hbasic_over.
    + exact Hlc_res.
    + exact Hden.
  - eapply ty_denote_wand_persist_over_arg_to_over_arg_over_result.
    + exact Hbasic_over.
    + exact HΔclosed.
    + exact Hlc_res.
    + exact Hden.
Qed.

Theorem ty_denote_wand_over_param_persist_under_result_equiv
    Δ bx φx br φr e :
  lty_env_closed (atom_env_to_lty_env Δ) ->
  basic_context_ty ∅ (CTOver bx φx) ->
  cty_lc_at 1 (CTUnder br φr) ->
  formula_equiv
    (ty_denote Δ (CTWand (CTOver bx φx) (CTUnder br φr)) e)
    (ty_denote Δ
      (CTWand (CTPersist (CTOver bx φx)) (CTUnder br φr)) e).
Proof.
  intros HΔclosed Hbasic_over Hlc_res.
  split; unfold entails; intros m Hden.
  - eapply ty_denote_wand_over_arg_to_persist_over_arg.
    + exact HΔclosed.
    + eapply basic_context_ty_lc. exact Hbasic_over.
    + exact Hlc_res.
    + exact Hden.
  - eapply ty_denote_wand_persist_over_arg_to_over_arg_under_result.
    + exact Hbasic_over.
    + exact HΔclosed.
    + exact Hlc_res.
    + exact Hden.
Qed.

End TypePersist.
