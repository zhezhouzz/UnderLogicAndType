(** * Denotation.TypeEquivFiberBaseProjected

    Projected result transport and typed-fiber projection helpers. *)

From Denotation Require Import Notation DenotationSetMapFacts TypeDenote TypeEquivCore TypeEquivTerm TypeEquivFiberBaseCore TypeEquivFiberBaseResult.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Lemma expr_result_formula_at_projection_eq_of_domains
    Dsmall Dbig Dobs e y (m my_small my_big : WfWorldT) :
  Dsmall ⊆ Dbig ->
  Dobs ⊆ Dsmall ->
  tm_lvars e ⊆ Dsmall ->
  LVFree y ∉ Dbig ->
  lvars_fv Dbig ⊆ world_dom (m : WorldT) ->
  world_dom (my_small : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my_small (world_dom (m : WorldT)) = m ->
  world_dom (my_big : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my_big (world_dom (m : WorldT)) = m ->
  my_small ⊨ expr_result_formula_at Dsmall e (LVFree y) ->
  my_big ⊨ expr_result_formula_at Dbig e (LVFree y) ->
  res_restrict my_big (lvars_fv Dobs ∪ {[y]}) =
  res_restrict my_small (lvars_fv Dobs ∪ {[y]}).
Proof.
  intros Hsmall_big Hobs_small He_small Hy_big Hbig_dom
    Hdom_small Hbase_small Hdom_big Hbase_big Hsmall Hbig.
  set (S := lvars_fv Dobs ∪ {[y]}).
  assert (Hy_small : LVFree y ∉ Dsmall) by set_solver.
  assert (He_big : tm_lvars e ⊆ Dbig) by set_solver.
  assert (Hobs_base : lvars_fv Dobs ⊆ world_dom (m : WorldT)).
  {
    intros a Ha. apply Hbig_dom.
    apply lvars_fv_elem. apply Hsmall_big. apply Hobs_small.
    apply lvars_fv_elem. exact Ha.
  }
  apply wfworld_eq_by_dom_stores.
  - rewrite !res_restrict_dom, Hdom_big, Hdom_small.
    subst S.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros [τbig [Hτbig HτbigS]].
      assert (Hτbig_base :
          (res_restrict my_big (world_dom (m : WorldT)) : WorldT)
            (store_restrict τbig (world_dom (m : WorldT)))).
      { exists τbig. split; [exact Hτbig|reflexivity]. }
      rewrite Hbase_big in Hτbig_base.
      rewrite <- Hbase_small in Hτbig_base.
      destruct Hτbig_base as [τbase [Hτbase Hτbase_eq]].
      assert (Hτbase_eq_m :
          store_restrict τbase (world_dom (m : WorldT)) =
          store_restrict τbig (world_dom (m : WorldT))).
      {
        transitivity (store_restrict τbig
          (world_dom (res_restrict my_small (world_dom (m : WorldT)) :
            WorldT))).
        - exact Hτbase_eq.
        - f_equal. rewrite res_restrict_dom, Hdom_small.
          apply set_eq. intros a. set_solver.
      }
      pose proof (expr_result_formula_at_models_elim
        Dbig e y my_big He_big Hy_big Hbig τbig Hτbig)
        as [_ [v [Hybig_lookup Heval_big]]].
      rewrite lstore_lift_free_lookup_free in Hybig_lookup.
      assert (Heval_base :
          tm_eval_in_store (store_restrict τbase (fv_tm e)) e v).
      {
        apply (proj2 (tm_eval_in_store_restrict_fv_exact τbase e v)).
        assert (Hagree :
            store_restrict τbase (fv_tm e) =
            store_restrict τbig (fv_tm e)).
        {
          eapply storeA_restrict_eq_mono; [|exact Hτbase_eq_m].
          intros a Ha.
          apply Hbig_dom.
          apply lvars_fv_elem. apply Hsmall_big. apply He_small.
          apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
        }
        apply (proj2 (tm_eval_in_store_agree_on_fv τbase τbig e v Hagree)).
        change (tm_eval_in_store τbig e v).
        exact Heval_big.
      }
      destruct (expr_result_formula_at_fiber_witness
        Dsmall e y my_small He_small Hy_small Hsmall
        τbase v Hτbase Heval_base)
        as [τsmall [Hτsmall [HτsmallD Hy_small_lookup]]].
      exists τsmall. split; [exact Hτsmall|].
      subst S.
      transitivity (store_restrict τbig (lvars_fv Dobs ∪ {[y]})).
      * eapply (store_restrict_obs_result_eq
          τsmall τbase τbig Dsmall Dobs (world_dom (m : WorldT)) y v).
        -- exact Hobs_small.
        -- exact Hobs_base.
        -- exact HτsmallD.
        -- exact Hτbase_eq_m.
        -- exact Hy_small_lookup.
        -- exact Hybig_lookup.
      * exact HτbigS.
    + intros [τsmall [Hτsmall HτsmallS]].
      assert (Hτsmall_base :
          (res_restrict my_small (world_dom (m : WorldT)) : WorldT)
            (store_restrict τsmall (world_dom (m : WorldT)))).
      { exists τsmall. split; [exact Hτsmall|reflexivity]. }
      rewrite Hbase_small in Hτsmall_base.
      rewrite <- Hbase_big in Hτsmall_base.
      destruct Hτsmall_base as [τbase [Hτbase Hτbase_eq]].
      assert (Hτbase_eq_m :
          store_restrict τbase (world_dom (m : WorldT)) =
          store_restrict τsmall (world_dom (m : WorldT))).
      {
        transitivity (store_restrict τsmall
          (world_dom (res_restrict my_big (world_dom (m : WorldT)) :
            WorldT))).
        - exact Hτbase_eq.
        - f_equal. rewrite res_restrict_dom, Hdom_big.
          apply set_eq. intros a. set_solver.
      }
      pose proof (expr_result_formula_at_models_elim
        Dsmall e y my_small He_small Hy_small Hsmall τsmall Hτsmall)
        as [_ [v [Hysmall_lookup Heval_small]]].
      rewrite lstore_lift_free_lookup_free in Hysmall_lookup.
      assert (Heval_base :
          tm_eval_in_store (store_restrict τbase (fv_tm e)) e v).
      {
        apply (proj2 (tm_eval_in_store_restrict_fv_exact τbase e v)).
        assert (Hagree :
            store_restrict τbase (fv_tm e) =
            store_restrict τsmall (fv_tm e)).
        {
          eapply storeA_restrict_eq_mono; [|exact Hτbase_eq_m].
          intros a Ha.
          apply Hbig_dom.
          apply lvars_fv_elem. apply Hsmall_big. apply He_small.
          apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
        }
        apply (proj2 (tm_eval_in_store_agree_on_fv τbase τsmall e v Hagree)).
        change (tm_eval_in_store τsmall e v).
        exact Heval_small.
      }
      destruct (expr_result_formula_at_fiber_witness
        Dbig e y my_big He_big Hy_big Hbig
        τbase v Hτbase Heval_base)
        as [τbig [Hτbig [HτbigD Hy_big_lookup]]].
      exists τbig. split; [exact Hτbig|].
      subst S.
      transitivity (store_restrict τsmall (lvars_fv Dobs ∪ {[y]})).
      * eapply (store_restrict_obs_result_eq
          τbig τbase τsmall Dbig Dobs (world_dom (m : WorldT)) y v).
        -- intros z Hz. apply Hsmall_big. apply Hobs_small. exact Hz.
        -- exact Hobs_base.
        -- exact HτbigD.
        -- exact Hτbase_eq_m.
        -- exact Hy_big_lookup.
        -- exact Hysmall_lookup.
      * exact HτsmallS.
Qed.

Lemma expr_result_formula_at_refine_domain_projected
    Dsmall Dbig Dobs e y (m my : WfWorldT) :
  Dsmall ⊆ Dbig ->
  Dobs ⊆ Dsmall ->
  lc_lvars Dbig ->
  tm_lvars e ⊆ Dsmall ->
  y ∉ world_dom (m : WorldT) ->
  lvars_fv Dbig ⊆ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  expr_total_on_atom_world e m ->
  my ⊨ expr_result_formula_at Dsmall e (LVFree y) ->
  exists my_big : WfWorldT,
    world_dom (my_big : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my_big (world_dom (m : WorldT)) = m /\
    my_big ⊨ expr_result_formula_at Dbig e (LVFree y) /\
    res_restrict my_big (lvars_fv Dobs ∪ {[y]}) =
    res_restrict my (lvars_fv Dobs ∪ {[y]}).
Proof.
  intros Hsmall_big Hobs_small Hlc_big He_small Hy_m Hbig_dom
    Hdom_my Hbase_my Htotal Hsmall.
  assert (He_big : tm_lvars e ⊆ Dbig) by set_solver.
  assert (Hy_big : LVFree y ∉ Dbig).
  {
    intros HyD. apply Hy_m. apply Hbig_dom.
    apply lvars_fv_elem. exact HyD.
  }
  assert (Hfv_big : fv_tm e ⊆ lvars_fv Dbig).
  {
    intros a Ha. apply lvars_fv_elem. apply He_big.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
  }
  assert (Hy_fv_big : y ∉ lvars_fv Dbig).
  { intros Hy. apply Hy_big. apply lvars_fv_elem. exact Hy. }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dbig) e y Hfv_big Hy_fv_big) as [F HF].
  assert (Happ : extension_applicable F m).
  {
    destruct HF as [_ _ [Hin Hout] _].
    constructor.
    - change (ext_in F ⊆ world_dom (m : WorldT)).
      rewrite Hin. exact Hbig_dom.
    - change (ext_out F ## world_dom (m : WorldT)).
      rewrite Hout.
      intros a Ha_out Ha_m.
      apply elem_of_singleton in Ha_out. subst a.
      exact (Hy_m Ha_m).
  }
  destruct (res_extend_by_exists m F Happ) as [my_big Hext].
  exists my_big.
  assert (Hdom_big :
      world_dom (my_big : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  {
    rewrite (res_extend_by_dom m F my_big Hext).
    destruct HF as [_ _ [_ Hout] _].
    change (world_dom (m : WorldT) ∪ ext_out F =
      world_dom (m : WorldT) ∪ {[y]}).
    rewrite Hout. reflexivity.
  }
  assert (Hbase_big :
      res_restrict my_big (world_dom (m : WorldT)) = m).
  { exact (res_extend_by_restrict_base m F my_big Hext). }
  assert (Hbig :
      my_big ⊨ expr_result_formula_at Dbig e (LVFree y)).
  {
    eapply (expr_result_formula_at_of_result_extends_on
      Dbig e y F m my_big); eauto.
  }
  split; [exact Hdom_big|].
  split; [exact Hbase_big|].
  split; [exact Hbig|].
  eapply (expr_result_formula_at_projection_eq_of_domains
    Dsmall Dbig Dobs e y m my my_big); eauto.
Qed.

Lemma expr_result_formula_at_projection_eq_of_fiber_equiv
    D e_src e_tgt y (m my_src my_tgt : WfWorldT) :
  LVFree y ∉ D ∪ tm_lvars e_src ∪ tm_lvars e_tgt ->
  world_dom (my_src : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my_src (world_dom (m : WorldT)) = m ->
  world_dom (my_tgt : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my_tgt (world_dom (m : WorldT)) = m ->
  tm_fiber_equiv_on m (lvars_fv D) e_src e_tgt ->
  my_src ⊨ expr_result_formula_at (D ∪ tm_lvars e_src) e_src (LVFree y) ->
  my_tgt ⊨ expr_result_formula_at (D ∪ tm_lvars e_tgt) e_tgt (LVFree y) ->
  res_restrict my_tgt (lvars_fv D ∪ {[y]}) =
  res_restrict my_src (lvars_fv D ∪ {[y]}).
Proof.
  intros HyD Hdom_src Hbase_src Hdom_tgt Hbase_tgt Hfib Hsrc Htgt.
  set (Dsrc := D ∪ tm_lvars e_src).
  set (Dtgt := D ∪ tm_lvars e_tgt).
  set (S := lvars_fv D ∪ {[y]}).
  pose proof Hsrc as Hsrc_info.
  unfold expr_result_formula_at in Hsrc_info.
  apply res_models_FFibVars_iff in Hsrc_info
    as [Hscope_src [Hlc_src _]].
  pose proof Htgt as Htgt_info.
  unfold expr_result_formula_at in Htgt_info.
  apply res_models_FFibVars_iff in Htgt_info
    as [Hscope_tgt [Hlc_tgt _]].
  assert (He_src : tm_lvars e_src ⊆ Dsrc) by (subst Dsrc; set_solver).
  assert (He_tgt : tm_lvars e_tgt ⊆ Dtgt) by (subst Dtgt; set_solver).
  assert (Hy_src : LVFree y ∉ Dsrc) by (subst Dsrc Dtgt; set_solver).
  assert (Hy_tgt : LVFree y ∉ Dtgt) by (subst Dsrc Dtgt; set_solver).
  assert (Hsrc_world : lvars_fv Dsrc ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    assert (Ha_src : a ∈ world_dom (my_src : WorldT)).
    {
      apply Hscope_src.
      change (a ∈ formula_fv
        (expr_result_formula_at Dsrc e_src (LVFree y))).
      rewrite formula_fv_expr_result_formula_at.
      apply elem_of_union_l. exact Ha.
    }
    rewrite Hdom_src in Ha_src.
    apply elem_of_union in Ha_src as [Ha_m|Ha_y]; [exact Ha_m|].
    apply elem_of_singleton in Ha_y. subst a.
    exfalso. apply HyD.
    subst Dsrc. apply elem_of_union_l.
    apply lvars_fv_elem. exact Ha.
  }
  assert (Htgt_world : lvars_fv Dtgt ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    assert (Ha_tgt : a ∈ world_dom (my_tgt : WorldT)).
    {
      apply Hscope_tgt.
      change (a ∈ formula_fv
        (expr_result_formula_at Dtgt e_tgt (LVFree y))).
      rewrite formula_fv_expr_result_formula_at.
      apply elem_of_union_l. exact Ha.
    }
    rewrite Hdom_tgt in Ha_tgt.
    apply elem_of_union in Ha_tgt as [Ha_m|Ha_y]; [exact Ha_m|].
    apply elem_of_singleton in Ha_y. subst a.
    exfalso. apply HyD.
    subst Dtgt.
    apply lvars_fv_elem in Ha.
    set_solver.
  }
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    intros a Ha. apply Hsrc_world.
    subst Dsrc. rewrite lvars_fv_union. apply elem_of_union_l. exact Ha.
  }
  apply wfworld_eq_by_dom_stores.
  - rewrite !res_restrict_dom, Hdom_tgt, Hdom_src.
    subst S. apply set_eq. intros a. set_solver.
	  - intros σ. split.
	    + intros [τtgt [Hτtgt HτtgtS]].
	      set (τbase := store_restrict τtgt (world_dom (m : WorldT))).
	      assert (Hτbase_m : (m : WorldT) τbase).
	      {
	        rewrite <- Hbase_tgt.
	        subst τbase. exists τtgt. split; [exact Hτtgt|reflexivity].
	      }
	      pose proof (expr_result_formula_at_models_elim
	        Dtgt e_tgt y my_tgt He_tgt Hy_tgt Htgt τtgt Hτtgt)
	        as [_ [v [Hytgt_lookup Heval_tgt]]].
	      rewrite lstore_lift_free_lookup_free in Hytgt_lookup.
	      assert (Heval_base_tgt :
	          tm_eval_in_store τbase e_tgt v).
	      {
	        eapply tm_eval_in_store_agree_on_fv; [|exact Heval_tgt].
	        eapply storeA_restrict_eq_mono.
	        - intros a Ha. apply Htgt_world.
	          subst Dtgt. rewrite lvars_fv_union. apply elem_of_union_r.
	          rewrite tm_lvars_fv. exact Ha.
	        - subst τbase. apply storeA_restrict_twice_same.
	      }
	      destruct (tm_fiber_equiv_result_pullback
	        m (lvars_fv D) e_src e_tgt τbase v Hfib Hτbase_m Heval_base_tgt)
	        as [σsrc [Hσsrc [HσsrcD Heval_src]]].
	      assert (Hσsrc_restrict :
	          (res_restrict my_src (world_dom (m : WorldT)) : WorldT) σsrc).
	      { rewrite Hbase_src. exact Hσsrc. }
	      change ((rawA_restrict (my_src : WorldT) (world_dom (m : WorldT))) σsrc)
	        in Hσsrc_restrict.
	      cbn [rawA_restrict worldA_stores] in Hσsrc_restrict.
	      destruct Hσsrc_restrict as [τpre [Hτpre Hτpre_base]].
	      assert (Heval_src_pre :
	          tm_eval_in_store (store_restrict τpre (fv_tm e_src)) e_src v).
	      {
	        assert (Hagree :
	            store_restrict τpre (fv_tm e_src) =
	            store_restrict σsrc (fv_tm e_src)).
	        {
	          eapply storeA_restrict_eq_mono.
	          - intros a Ha. apply Hsrc_world.
	            subst Dsrc. rewrite lvars_fv_union. apply elem_of_union_r.
	            rewrite tm_lvars_fv. exact Ha.
	          - transitivity σsrc.
	            + exact Hτpre_base.
	            + symmetry. apply storeA_restrict_idemp_eq.
	              exact (wfworld_store_dom m σsrc Hσsrc).
	        }
	        rewrite Hagree.
	        apply (proj2 (tm_eval_in_store_restrict_fv_exact σsrc e_src v)).
	        exact Heval_src.
	      }
	      destruct (expr_result_formula_at_fiber_witness
	        Dsrc e_src y my_src He_src Hy_src Hsrc
	        τpre v Hτpre Heval_src_pre)
	        as [τsrc [Hτsrc [HτsrcD Hysrc_lookup]]].
	      exists τsrc. split; [exact Hτsrc|].
	      subst S.
	      transitivity (store_restrict τtgt (lvars_fv D ∪ {[y]})).
	      * eapply (store_restrict_obs_result_eq
	          τsrc τpre τtgt D D (lvars_fv D) y v).
	        -- intros a Ha. exact Ha.
	        -- intros a Ha. exact Ha.
	        -- eapply storeA_restrict_eq_mono; [|exact HτsrcD].
	           subst Dsrc. rewrite lvars_fv_union. set_solver.
	        -- transitivity (store_restrict σsrc (lvars_fv D)).
	           ++ eapply storeA_restrict_eq_mono.
	              ** exact HDm.
	              ** transitivity σsrc.
	                 --- exact Hτpre_base.
	                 --- symmetry. apply storeA_restrict_idemp_eq.
	                     exact (wfworld_store_dom m σsrc Hσsrc).
	           ++ transitivity (store_restrict τbase (lvars_fv D)).
	              ** exact HσsrcD.
	              ** subst τbase. apply storeA_restrict_twice_subset.
	                 exact HDm.
	        -- exact Hysrc_lookup.
	        -- exact Hytgt_lookup.
      * exact HτtgtS.
	    + intros [τsrc [Hτsrc HτsrcS]].
	      set (τbase := store_restrict τsrc (world_dom (m : WorldT))).
	      assert (Hτbase_m : (m : WorldT) τbase).
	      {
	        rewrite <- Hbase_src.
	        subst τbase. exists τsrc. split; [exact Hτsrc|reflexivity].
	      }
	      pose proof (expr_result_formula_at_models_elim
	        Dsrc e_src y my_src He_src Hy_src Hsrc τsrc Hτsrc)
	        as [_ [v [Hysrc_lookup Heval_src]]].
	      rewrite lstore_lift_free_lookup_free in Hysrc_lookup.
	      assert (Heval_base_src :
	          tm_eval_in_store τbase e_src v).
	      {
	        eapply tm_eval_in_store_agree_on_fv; [|exact Heval_src].
	        eapply storeA_restrict_eq_mono.
	        - intros a Ha. apply Hsrc_world.
	          subst Dsrc. rewrite lvars_fv_union. apply elem_of_union_r.
	          rewrite tm_lvars_fv. exact Ha.
	        - subst τbase. apply storeA_restrict_twice_same.
	      }
	      pose proof (Hfib (store_restrict τbase (lvars_fv D))
	        ltac:(exists τbase; split; [exact Hτbase_m|reflexivity]) v)
	        as [Hforward _].
	      assert (Hsrc_res :
	          tm_fiber_result_on m (lvars_fv D) e_src
	            (store_restrict τbase (lvars_fv D)) v).
	      {
	        exists τbase. split; [exact Hτbase_m|].
	        split; [reflexivity|exact Heval_base_src].
	      }
	      destruct (Hforward Hsrc_res)
	        as [σtgt [Hσtgt [HσtgtD Heval_tgt]]].
	      assert (Hσtgt_restrict :
	          (res_restrict my_tgt (world_dom (m : WorldT)) : WorldT) σtgt).
	      { rewrite Hbase_tgt. exact Hσtgt. }
	      change ((rawA_restrict (my_tgt : WorldT) (world_dom (m : WorldT))) σtgt)
	        in Hσtgt_restrict.
	      cbn [rawA_restrict worldA_stores] in Hσtgt_restrict.
	      destruct Hσtgt_restrict as [τpre [Hτpre Hτpre_base]].
	      assert (Heval_tgt_restrict :
	          tm_eval_in_store (store_restrict τpre (fv_tm e_tgt)) e_tgt v).
	      {
	        assert (Hagree :
	            store_restrict τpre (fv_tm e_tgt) =
	            store_restrict σtgt (fv_tm e_tgt)).
	        {
	          eapply storeA_restrict_eq_mono.
	          - intros a Ha. apply Htgt_world.
	            subst Dtgt. rewrite lvars_fv_union. apply elem_of_union_r.
	            rewrite tm_lvars_fv. exact Ha.
	          - transitivity σtgt.
	            + exact Hτpre_base.
	            + symmetry. apply storeA_restrict_idemp_eq.
	              exact (wfworld_store_dom m σtgt Hσtgt).
	        }
	        rewrite Hagree.
	        apply (proj2 (tm_eval_in_store_restrict_fv_exact σtgt e_tgt v)).
	        exact Heval_tgt.
	      }
	      destruct (expr_result_formula_at_fiber_witness
	        Dtgt e_tgt y my_tgt He_tgt Hy_tgt Htgt
	        τpre v Hτpre Heval_tgt_restrict)
	        as [τtgt [Hτtgt [HτtgtD Hytgt_lookup]]].
	      exists τtgt. split; [exact Hτtgt|].
	      subst S.
	      transitivity (store_restrict τsrc (lvars_fv D ∪ {[y]})).
	      * eapply (store_restrict_obs_result_eq
	          τtgt τpre τsrc D D (lvars_fv D) y v).
	        -- intros a Ha. exact Ha.
	        -- intros a Ha. exact Ha.
	        -- eapply storeA_restrict_eq_mono; [|exact HτtgtD].
	           subst Dtgt. rewrite lvars_fv_union. set_solver.
	        -- transitivity (store_restrict σtgt (lvars_fv D)).
	           ++ eapply storeA_restrict_eq_mono.
	              ** exact HDm.
	              ** transitivity σtgt.
	                 --- exact Hτpre_base.
	                 --- symmetry. apply storeA_restrict_idemp_eq.
	                     exact (wfworld_store_dom m σtgt Hσtgt).
	           ++ transitivity (store_restrict τbase (lvars_fv D)).
	              ** exact HσtgtD.
	              ** subst τbase. apply storeA_restrict_twice_subset.
	                 exact HDm.
	        -- exact Hytgt_lookup.
	        -- exact Hysrc_lookup.
      * exact HτsrcS.
Qed.

Lemma tm_fiber_equiv_refines_projected_on
    Σ τ (m : WfWorldT) D e_src e_tgt :
  tm_fiber_equiv_on m (lvars_fv D) e_src e_tgt ->
  m ⊨ ty_denote_gas 0 Σ τ e_tgt ->
  tm_result_refines_projected_on m D e_src e_tgt.
Proof.
  intros Hfib Hzero_tgt y my_src Hy Hdom_src Hbase_src Hres_src.
  set (Dsrc := D ∪ tm_lvars e_src).
  set (Dtgt := D ∪ tm_lvars e_tgt).
  pose proof Hres_src as Hres_src_info.
  unfold expr_result_formula_at in Hres_src_info.
  apply res_models_FFibVars_iff in Hres_src_info
    as [Hscope_src [Hlc_src _]].
  assert (HlcD : lc_lvars D).
  {
    intros v Hv. apply Hlc_src. subst Dsrc.
    apply elem_of_union_l. exact Hv.
  }
  assert (Hsrc_world : lvars_fv Dsrc ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    unfold formula_scoped_in_world in Hscope_src.
    assert (Ha_src : a ∈ world_dom (my_src : WorldT)).
	    {
	      apply Hscope_src.
	      subst Dsrc.
	      change (a ∈ formula_fv
	        (expr_result_formula_at (D ∪ tm_lvars e_src) e_src (LVFree y))).
	      rewrite formula_fv_expr_result_formula_at.
	      apply elem_of_union_l. exact Ha.
	    }
	    rewrite Hdom_src in Ha_src.
	    apply elem_of_union in Ha_src as [Ha_m|Ha_y]; [exact Ha_m|].
	    apply elem_of_singleton in Ha_y. subst a.
	    exfalso. apply Hy.
	    subst Dsrc. rewrite lvars_fv_union in Ha.
	    apply elem_of_union in Ha as [HaD|HaE].
	    - clear -HaD. set_solver.
	    - rewrite tm_lvars_fv in HaE.
	      clear -HaE. set_solver.
	  }
  assert (Hlc_tgt : lc_lvars Dtgt).
  {
    intros v Hv.
    subst Dtgt.
    apply elem_of_union in Hv as [Hv|Hv].
    - exact (HlcD v Hv).
    - eapply ty_denote_gas_zero_lc_relevant_lvars; [exact Hzero_tgt|].
      apply elem_of_union_r. exact Hv.
  }
  assert (Htgt_world : lvars_fv Dtgt ⊆ world_dom (m : WorldT)).
  {
    intros a Ha.
    subst Dtgt.
    rewrite lvars_fv_union in Ha.
    apply elem_of_union in Ha as [HaD|HaE].
    - apply Hsrc_world. subst Dsrc.
      rewrite lvars_fv_union. apply elem_of_union_l. exact HaD.
    - eapply ty_denote_gas_zero_relevant_lvars_world; [exact Hzero_tgt|].
      rewrite lvars_fv_union. apply elem_of_union_r. exact HaE.
  }
  assert (Hy_Dtgt : LVFree y ∉ Dtgt).
  {
	    intros HyDtgt. apply Hy.
	    subst Dtgt.
	    apply elem_of_union in HyDtgt as [HyD|HyE].
	    - apply lvars_fv_elem in HyD.
	      clear -HyD. set_solver.
	    - apply lvars_fv_elem in HyE.
	      rewrite tm_lvars_fv in HyE.
	      clear -HyE. set_solver.
  }
  assert (Hy_m : y ∉ world_dom (m : WorldT)).
  { intros Hy_m. apply Hy. clear -Hy_m. set_solver. }
  assert (Hfv_tgt : fv_tm e_tgt ⊆ lvars_fv Dtgt).
  {
    intros a Ha. subst Dtgt.
    rewrite lvars_fv_union. apply elem_of_union_r.
    rewrite tm_lvars_fv. exact Ha.
  }
  assert (Hy_tgt_fv : y ∉ lvars_fv Dtgt).
  { intros Hyfv. apply Hy_Dtgt. apply lvars_fv_elem. exact Hyfv. }
  destruct (expr_result_extension_witness_on_exists
    (lvars_fv Dtgt) e_tgt y Hfv_tgt Hy_tgt_fv) as [F HF].
  assert (Happ : extension_applicable F m).
  {
    destruct HF as [_ _ [Hin Hout] _].
    constructor.
    - change (ext_in F ⊆ world_dom (m : WorldT)).
      rewrite Hin. exact Htgt_world.
    - change (ext_out F ## world_dom (m : WorldT)).
      rewrite Hout.
      intros a Ha_out Ha_m.
      apply elem_of_singleton in Ha_out. subst a.
      exact (Hy_m Ha_m).
  }
  destruct (res_extend_by_exists m F Happ) as [my_tgt Hext].
  assert (Hdom_tgt :
      world_dom (my_tgt : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  {
    rewrite (res_extend_by_dom m F my_tgt Hext).
    destruct HF as [_ _ [_ Hout] _].
    change (world_dom (m : WorldT) ∪ ext_out F =
      world_dom (m : WorldT) ∪ {[y]}).
    rewrite Hout. reflexivity.
  }
  assert (Hbase_tgt :
      res_restrict my_tgt (world_dom (m : WorldT)) = m).
  { exact (res_extend_by_restrict_base m F my_tgt Hext). }
  assert (Htotal_tgt : expr_total_on_atom_world e_tgt m).
  { eapply ty_denote_gas_zero_total_atom_world. exact Hzero_tgt. }
	  assert (Hres_tgt :
	      my_tgt ⊨ expr_result_formula_at Dtgt e_tgt (LVFree y)).
	  {
	    eapply (expr_result_formula_at_of_result_extends_on
	      Dtgt e_tgt y F m my_tgt).
	    - exact Hlc_tgt.
	    - subst Dtgt. intros v Hv. apply elem_of_union_r. exact Hv.
	    - exact Hy_Dtgt.
	    - exact Htgt_world.
	    - exact HF.
	    - exact Hext.
	    - exact Htotal_tgt.
	  }
  exists my_tgt.
  split; [exact Hdom_tgt|].
	  split; [exact Hbase_tgt|].
	  split; [exact Hres_tgt|].
	  eapply (expr_result_formula_at_projection_eq_of_fiber_equiv
	    D e_src e_tgt y m my_src my_tgt).
	  - intros Hybad. apply Hy.
	    apply elem_of_union in Hybad as [Hybad|HyT].
	    apply elem_of_union in Hybad as [HyD|HyS].
	    + apply lvars_fv_elem in HyD. clear -HyD. set_solver.
	    + apply lvars_fv_elem in HyS. rewrite tm_lvars_fv in HyS.
	      clear -HyS. set_solver.
	    + apply lvars_fv_elem in HyT. rewrite tm_lvars_fv in HyT.
	      clear -HyT. set_solver.
	  - exact Hdom_src.
	  - exact Hbase_src.
	  - exact Hdom_tgt.
	  - exact Hbase_tgt.
	  - exact Hfib.
	  - exact Hres_src.
	  - exact Hres_tgt.
Qed.

Lemma tm_fiber_equiv_to_projected_on
    Σ τ (m : WfWorldT) D e1 e2 :
  tm_fiber_equiv_on m (lvars_fv D) e1 e2 ->
  m ⊨ ty_denote_gas 0 Σ τ e1 ->
  m ⊨ ty_denote_gas 0 Σ τ e2 ->
  tm_result_equiv_projected_on m D e1 e2.
Proof.
  intros Hfib Hzero1 Hzero2.
  split.
  - eapply tm_fiber_equiv_refines_projected_on; eauto.
  - eapply tm_fiber_equiv_refines_projected_on; [|exact Hzero1].
    apply tm_fiber_equiv_on_sym. exact Hfib.
Qed.

Lemma typed_fiber_equiv_result_projected
    Σ τ m e1 e2 :
  typed_fiber_equiv_on Σ τ m e1 e2 ->
  tm_result_equiv_projected_on m (context_ty_lvars τ) e1 e2.
Proof.
  intros Hequiv.
  eapply tm_fiber_equiv_to_projected_on.
  - eapply typed_fiber_equiv_fiber. exact Hequiv.
  - eapply typed_fiber_equiv_zero_src. exact Hequiv.
  - eapply typed_fiber_equiv_zero_tgt. exact Hequiv.
Qed.

Lemma tm_result_refines_projected_project
    (m : WfWorldT) Dsmall Dbig e_src e_tgt :
  Dsmall ⊆ Dbig ->
  lc_lvars (Dbig ∪ tm_lvars e_src) ->
  lc_lvars (Dbig ∪ tm_lvars e_tgt) ->
  lvars_fv (Dbig ∪ tm_lvars e_src) ⊆ world_dom (m : WorldT) ->
  lvars_fv (Dbig ∪ tm_lvars e_tgt) ⊆ world_dom (m : WorldT) ->
  expr_total_on_atom_world e_src m ->
  tm_result_refines_projected_on m Dbig e_src e_tgt ->
  tm_result_refines_projected_on m Dsmall e_src e_tgt.
Proof.
  intros Hsmall_big Hlc_src_big Hlc_tgt_big Hsrc_big_world
    Htgt_big_world Htotal_src Hbig.
  intros y my_src Hy Hdom_src Hrestrict_src Hres_src_small.
  assert (Hy_m : y ∉ world_dom (m : WorldT)).
  { set_solver. }
  assert (Hy_src_big : LVFree y ∉ Dbig ∪ tm_lvars e_src).
  {
    intros HyD.
    apply Hy_m. apply Hsrc_big_world.
    apply lvars_fv_elem. exact HyD.
  }
  assert (Hy_tgt_big : LVFree y ∉ Dbig ∪ tm_lvars e_tgt).
  {
    intros HyD.
    apply Hy_m. apply Htgt_big_world.
    apply lvars_fv_elem. exact HyD.
  }
  pose proof (expr_result_formula_at_refine_domain_projected
    (Dsmall ∪ tm_lvars e_src)
    (Dbig ∪ tm_lvars e_src)
    Dsmall e_src y m my_src
    ltac:(set_solver)
    ltac:(set_solver)
    Hlc_src_big
    ltac:(set_solver)
    Hy_m
    Hsrc_big_world
    Hdom_src
    Hrestrict_src
    Htotal_src
    Hres_src_small)
    as [my_src_big
      [Hdom_src_big [Hrestrict_src_big [Hres_src_big Hproj_src_big]]]].
  assert (Hy_big :
      y ∉ world_dom (m : WorldT) ∪ fv_tm e_src ∪ fv_tm e_tgt ∪
        lvars_fv Dbig).
  {
    intros Hybad.
    repeat rewrite elem_of_union in Hybad.
    destruct Hybad as [[[Hybad|Hybad]|Hybad]|Hybad].
    - exact (Hy_m Hybad).
    - apply Hy. set_solver.
    - apply Hy. set_solver.
    - apply Hy_m. apply Hsrc_big_world.
      rewrite lvars_fv_union. apply elem_of_union_l. exact Hybad.
  }
  destruct (Hbig y my_src_big Hy_big Hdom_src_big Hrestrict_src_big
    Hres_src_big) as
  [my_tgt [Hdom_tgt [Hrestrict_tgt [Hres_tgt_big Hproj_big]]]].
  exists my_tgt.
  split; [exact Hdom_tgt|].
  split; [exact Hrestrict_tgt|].
  split.
  - eapply (expr_result_formula_at_coarsen_domain
      (Dsmall ∪ tm_lvars e_tgt)
      (Dbig ∪ tm_lvars e_tgt)
      e_tgt y my_tgt).
    + intros a Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      * apply elem_of_union_l. exact (Hsmall_big a Ha).
      * apply elem_of_union_r. exact Ha.
    + intros a Ha. apply elem_of_union_r. exact Ha.
    + exact Hy_tgt_big.
    + exact Hres_tgt_big.
  - transitivity
      (res_restrict my_src_big (lvars_fv Dsmall ∪ {[y]})).
    + eapply res_restrict_eq_subset; [|exact Hproj_big].
      intros a Ha.
      repeat rewrite elem_of_union in Ha |- *.
      destruct Ha as [Ha|Ha].
      * left.
        apply lvars_fv_elem. apply Hsmall_big.
        apply lvars_fv_elem. exact Ha.
      * right. exact Ha.
    + exact Hproj_src_big.
Qed.

Lemma typed_fiber_equiv_project
    Σ τsmall τbig m e1 e2 :
  context_ty_lvars τsmall ⊆ context_ty_lvars τbig ->
  m ⊨ ty_denote_gas 0 Σ τsmall e1 ->
  m ⊨ ty_denote_gas 0 Σ τsmall e2 ->
  typed_fiber_equiv_on Σ τbig m e1 e2 ->
  typed_fiber_equiv_on Σ τsmall m e1 e2.
Proof.
  intros Hlv Hzero1_small Hzero2_small Hequiv.
  apply typed_fiber_equiv_intro.
  - eapply tm_fiber_equiv_on_mono.
    + apply lvars_fv_mono. exact Hlv.
    + eapply typed_fiber_equiv_fiber. exact Hequiv.
  - exact Hzero1_small.
  - exact Hzero2_small.
Qed.

Lemma typed_fiber_equiv_inter_l
    Σ τ1 τ2 m e1 e2 :
  m ⊨ ty_denote_gas 0 Σ τ1 e1 ->
  m ⊨ ty_denote_gas 0 Σ τ1 e2 ->
  typed_fiber_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_fiber_equiv_on Σ τ1 m e1 e2.
Proof.
  intros Hzero1 Hzero2 Hequiv.
  eapply (typed_fiber_equiv_project Σ τ1 (CTInter τ1 τ2) m e1 e2).
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - exact Hzero1.
  - exact Hzero2.
  - exact Hequiv.
Qed.

Lemma typed_fiber_equiv_inter_r
    Σ τ1 τ2 m e1 e2 :
  m ⊨ ty_denote_gas 0 Σ τ2 e1 ->
  m ⊨ ty_denote_gas 0 Σ τ2 e2 ->
  typed_fiber_equiv_on Σ (CTInter τ1 τ2) m e1 e2 ->
  typed_fiber_equiv_on Σ τ2 m e1 e2.
Proof.
  intros Hzero1 Hzero2 Hequiv.
  eapply (typed_fiber_equiv_project Σ τ2 (CTInter τ1 τ2) m e1 e2).
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - exact Hzero1.
  - exact Hzero2.
  - exact Hequiv.
Qed.

Lemma typed_fiber_equiv_union_l
    Σ τ1 τ2 m e1 e2 :
  m ⊨ ty_denote_gas 0 Σ τ1 e1 ->
  m ⊨ ty_denote_gas 0 Σ τ1 e2 ->
  typed_fiber_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_fiber_equiv_on Σ τ1 m e1 e2.
Proof.
  intros Hzero1 Hzero2 Hequiv.
  eapply (typed_fiber_equiv_project Σ τ1 (CTUnion τ1 τ2) m e1 e2).
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - exact Hzero1.
  - exact Hzero2.
  - exact Hequiv.
Qed.

Lemma typed_fiber_equiv_union_r
    Σ τ1 τ2 m e1 e2 :
  m ⊨ ty_denote_gas 0 Σ τ2 e1 ->
  m ⊨ ty_denote_gas 0 Σ τ2 e2 ->
  typed_fiber_equiv_on Σ (CTUnion τ1 τ2) m e1 e2 ->
  typed_fiber_equiv_on Σ τ2 m e1 e2.
Proof.
  intros Hzero1 Hzero2 Hequiv.
  eapply (typed_fiber_equiv_project Σ τ2 (CTUnion τ1 τ2) m e1 e2).
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - exact Hzero1.
  - exact Hzero2.
  - exact Hequiv.
Qed.

Lemma typed_fiber_equiv_sum_l
    Σ τ1 τ2 m e1 e2 :
  m ⊨ ty_denote_gas 0 Σ τ1 e1 ->
  m ⊨ ty_denote_gas 0 Σ τ1 e2 ->
  typed_fiber_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  typed_fiber_equiv_on Σ τ1 m e1 e2.
Proof.
  intros Hzero1 Hzero2 Hequiv.
  eapply (typed_fiber_equiv_project Σ τ1 (CTSum τ1 τ2) m e1 e2).
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - exact Hzero1.
  - exact Hzero2.
  - exact Hequiv.
Qed.

Lemma typed_fiber_equiv_sum_r
    Σ τ1 τ2 m e1 e2 :
  m ⊨ ty_denote_gas 0 Σ τ2 e1 ->
  m ⊨ ty_denote_gas 0 Σ τ2 e2 ->
  typed_fiber_equiv_on Σ (CTSum τ1 τ2) m e1 e2 ->
  typed_fiber_equiv_on Σ τ2 m e1 e2.
Proof.
  intros Hzero1 Hzero2 Hequiv.
  eapply (typed_fiber_equiv_project Σ τ2 (CTSum τ1 τ2) m e1 e2).
  - cbn [context_ty_lvars context_ty_lvars_at]. set_solver.
  - exact Hzero1.
  - exact Hzero2.
  - exact Hequiv.
Qed.


End TypeDenote.
