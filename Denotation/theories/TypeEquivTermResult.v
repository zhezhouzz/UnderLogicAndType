(** * Denotation.TypeEquivTermResult

    Result-graph, result-alias, and result-extension support for term transport. *)

From Denotation Require Import Notation DenotationSetMapFacts TypeEquivTermBase.

Section TypeDenote.

Lemma expr_result_formula_transport_fv_subset
    (m : WfWorldT) e1 e2 y :
  lc_tm e1 ->
  tm_equiv_on m e1 e2 ->
  fv_tm e1 ⊆ fv_tm e2 ->
  m ⊨ expr_result_formula e2 (LVFree y) ->
  m ⊨ expr_result_formula e1 (LVFree y).
Proof.
  intros Hlc1 Heq Hfv Hres2.
  pose proof (expr_result_formula_to_atom_world e2 (LVFree y) m Hres2)
    as Hworld2.
  destruct Hworld2 as [Hy2 [Hdom2 Hstores2]].
  apply expr_result_atom_world_to_formula.
  - split.
    + intros Hy1. apply Hy2.
      apply lvars_fv_elem. rewrite tm_lvars_fv.
      apply Hfv. rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy1.
    + split.
      * intros z Hz.
        apply elem_of_union in Hz as [Hz|Hz].
        -- pose proof (tm_lvars_lc_subset_atoms_fv e1
             (tm_lvars_lc e1 Hlc1) _ Hz) as Hzfv.
           unfold lvars_of_atoms in Hzfv.
           apply elem_of_map in Hzfv as [a [-> Ha]].
           apply Hdom2. apply elem_of_union_l.
           apply lvars_fv_elem. rewrite tm_lvars_fv. apply Hfv. exact Ha.
        -- apply Hdom2. apply elem_of_union_r. exact Hz.
      * intros σL HσL.
        destruct HσL as [σ [Hσ ->]].
        specialize (Hstores2 (lstore_lift_free σ)
          ltac:(exists σ; split; [exact Hσ|reflexivity])).
        destruct Hstores2 as [_ [v [Hy_lookup Heval2]]].
        split.
        -- intros Hy1. apply Hy2.
           apply lvars_fv_elem. rewrite tm_lvars_fv.
           apply Hfv. rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy1.
        -- exists v. split; [exact Hy_lookup|].
           change (tm_eval_in_store σ e1 v).
           apply (proj2 (Heq σ v Hσ)).
           change (tm_eval_in_store σ e2 v). exact Heval2.
  - intros z σ v Heq_x Hσ Heval1.
    inversion Heq_x. subst z.
    assert (Heval1_full : tm_eval_in_store σ e1 v).
    {
      apply (proj1 (tm_eval_in_store_restrict_fv_exact σ e1 v)).
      exact Heval1.
    }
    assert (Heval2_full : tm_eval_in_store σ e2 v).
    { apply (proj1 (Heq σ v Hσ)). exact Heval1_full. }
    pose proof (expr_result_formula_fiber_witness e2 y m
      Hres2 σ v Hσ
      ltac:(apply (proj2 (tm_eval_in_store_restrict_fv_exact σ e2 v));
        exact Heval2_full))
      as [σv [Hσv [Hproj2 Hy_lookup]]].
    exists σv. split; [exact Hσv|]. split; [|exact Hy_lookup].
    eapply storeA_restrict_eq_mono.
    + rewrite !tm_lvars_fv. exact Hfv.
		    + rewrite tm_lvars_fv in Hproj2. exact Hproj2.
Qed.

Lemma expr_result_formula_alias_ret_fvar
    (m my : WfWorldT) e x y :
  y ∉ fv_tm e ∪ {[x]} ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  wfworld_closed_on ({[x]} : aset) my ->
  m ⊨ expr_result_formula e (LVFree x) ->
  my ⊨ expr_result_formula (tret (vfvar x)) (LVFree y) ->
  my ⊨ expr_result_formula e (LVFree y).
Proof.
  intros Hyfresh Hdom Hrestrict Hclosed_x Hresx Hretxy.
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hresx)
    as Hworld_x.
  pose proof (expr_result_formula_to_atom_world
    (tret (vfvar x)) (LVFree y) my Hretxy) as Hworld_y.
  pose proof (expr_result_formula_models_elim e (LVFree x) m Hresx)
    as [_ [_ Hstore_x]].
  pose proof (expr_result_formula_models_elim
    (tret (vfvar x)) (LVFree y) my Hretxy) as [_ [_ Hstore_y]].
  apply expr_result_atom_world_to_formula.
  - destruct Hworld_x as [Hx_fresh [Hdom_x _]].
    split.
    + intros Hy_lvar.
      apply Hyfresh. apply elem_of_union_l.
      rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy_lvar.
    + split.
      * intros z Hz.
        apply elem_of_union in Hz as [Hz|Hz].
        -- pose proof (Hdom_x z (elem_of_union_l _ _ _ Hz)) as Hz_m.
           rewrite res_lift_free_dom in Hz_m |- *.
           unfold lvars_of_atoms in Hz_m |- *.
	           apply elem_of_map in Hz_m as [a [-> Ha]].
	           apply elem_of_map. exists a. split; [reflexivity|].
	           change (a ∈ world_dom (my : WorldT)).
	           rewrite Hdom. set_solver.
        -- apply elem_of_singleton in Hz as ->.
           rewrite res_lift_free_dom.
	           unfold lvars_of_atoms. apply elem_of_map.
	           exists y. split; [reflexivity|].
	           change (y ∈ world_dom (my : WorldT)).
	           rewrite Hdom. set_solver.
      * intros σL HσL.
        destruct HσL as [σ [Hσ ->]].
        pose proof (Hstore_y σ Hσ) as [_ [vy [Hy_lookup Heval_ret]]].
	        assert (Hx_dom_my : x ∈ world_dom (my : WorldT)).
	        {
	          pose proof (Hdom_x (LVFree x)
	            ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	          rewrite res_lift_free_dom in Hx_lift_m.
	          unfold lvars_of_atoms in Hx_lift_m.
	          apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	          inversion Heq. subst a.
	          rewrite Hdom. set_solver.
	        }
	        pose proof (wfworldA_store_dom my σ Hσ) as Hσdom.
	        assert (Hx_dom_σ : x ∈ dom (σ : gmap atom value)).
	        {
	          change (x ∈ dom (σ : gmap atom value)).
	          rewrite Hσdom. exact Hx_dom_my.
	        }
        assert (Hret_restrict :
            tm_eval_in_store (store_restrict (σ : gmap atom value) ({[x]} : aset))
              (tret (vfvar x)) vy).
        {
          apply (proj2 (tm_eval_in_store_restrict_fv_subset
            σ (tret (vfvar x)) vy ({[x]} : aset)
            ltac:(cbn [fv_tm fv_value]; set_solver))).
          change (tm_eval_in_store σ (tret (vfvar x)) vy).
          exact Heval_ret.
        }
	        assert (Hx_dom_restrict :
            x ∈ dom (store_restrict (σ : gmap atom value) ({[x]} : aset) : gmap atom value)).
	        {
	          destruct (σ !! x) as [vx|] eqn:Hx_lookup0.
	          - eapply elem_of_dom_2.
	            eapply storeA_restrict_lookup_some_2;
	              [exact Hx_lookup0|set_solver].
	          - apply not_elem_of_dom in Hx_lookup0. contradiction.
	        }
        pose proof (tm_eval_in_store_ret_fvar_inv
          (store_restrict (σ : gmap atom value) ({[x]} : aset)) x vy
          (Hclosed_x σ Hσ) Hx_dom_restrict Hret_restrict) as Hx_lookup_r.
        apply storeA_restrict_lookup_some in Hx_lookup_r as [_ Hx_lookup].
        assert (Hσm :
            (m : WorldT) (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
        {
          assert (Hr :
              (res_restrict my (world_dom (m : WorldT)) : WorldT)
                (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
          { exists σ. split; [exact Hσ|reflexivity]. }
          rewrite Hrestrict in Hr. exact Hr.
        }
        pose proof (Hstore_x _ Hσm) as [_ [vx [Hx_lookup_m Heval_e_m]]].
	        assert (Hx_in_m : x ∈ world_dom (m : WorldT)).
	        {
	          pose proof (Hdom_x (LVFree x)
	            ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	          rewrite res_lift_free_dom in Hx_lift_m.
	          unfold lvars_of_atoms in Hx_lift_m.
	          apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	          inversion Heq. subst a. exact Ha.
	        }
	        assert (Hx_lookup_restrict :
            store_restrict (σ : gmap atom value) (world_dom (m : WorldT)) !! x = Some vy).
	        {
	          apply storeA_restrict_lookup_some_2;
	            [exact Hx_lookup|exact Hx_in_m].
	        }
	        rewrite lstore_lift_free_lookup_free in Hx_lookup_m.
	        rewrite Hx_lookup_m in Hx_lookup_restrict.
        inversion Hx_lookup_restrict. subst vx.
        split.
        -- intros Hy_bad.
           apply Hyfresh. apply elem_of_union_l.
           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy_bad.
	        -- exists vy. split; [exact Hy_lookup|].
	           assert (Hfv_m : fv_tm e ⊆ world_dom (m : WorldT)).
	           {
	             intros a Ha.
	             assert (Ha_lvar : LVFree a ∈ tm_lvars e).
	             {
	               apply lvars_fv_elem.
	               rewrite tm_lvars_fv. exact Ha.
	             }
	             pose proof (Hdom_x (LVFree a)
	               (elem_of_union_l _ _ _ Ha_lvar)) as Ha_lift_m.
	             rewrite res_lift_free_dom in Ha_lift_m.
	             unfold lvars_of_atoms in Ha_lift_m.
	             apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
	             inversion Heq. subst b. exact Hb.
	           }
	           change (tm_eval_in_store σ e vy).
	           apply (proj1 (tm_eval_in_store_restrict_fv_subset
	             σ e vy (world_dom (m : WorldT)) Hfv_m)).
	           exact Heval_e_m.
  - intros z σ v Heq_z Hσ Heval_e.
    inversion Heq_z. subst z.
    pose proof (expr_result_formula_fiber_witness e x m Hresx
      (store_restrict (σ : gmap atom value) (world_dom (m : WorldT))) v) as Hwit.
    assert (Hσm :
        (m : WorldT) (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
    {
      assert (Hr :
          (res_restrict my (world_dom (m : WorldT)) : WorldT)
            (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))).
      { exists σ. split; [exact Hσ|reflexivity]. }
      rewrite Hrestrict in Hr. exact Hr.
    }
    assert (Heval_m :
        tm_eval_in_store
          (store_restrict
            (store_restrict (σ : gmap atom value) (world_dom (m : WorldT))) (fv_tm e)) e v).
    {
      rewrite storeA_restrict_twice_subset.
      - exact Heval_e.
      - intros a Ha.
        destruct Hworld_x as [_ [Hdom_x _]].
        pose proof (Hdom_x (LVFree a)
          ltac:(apply elem_of_union_l; apply lvars_fv_elem;
            rewrite tm_lvars_fv; exact Ha)) as Ha_lift_m.
        rewrite res_lift_free_dom in Ha_lift_m.
        unfold lvars_of_atoms in Ha_lift_m.
        apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
        inversion Heq. subst b. exact Hb.
    }
    specialize (Hwit Hσm Heval_m) as [σx [Hσx [Hproj_x Hx_lookup]]].
    assert (Hσx_my :
        (res_restrict my (world_dom (m : WorldT)) : WorldT) σx).
    { rewrite Hrestrict. exact Hσx. }
    destruct Hσx_my as [σxy [Hσxy Hσxy_restrict]].
    pose proof (Hstore_y σxy Hσxy) as [_ [vy [Hy_lookup Heval_ret]]].
	    assert (Hx_dom_my : x ∈ world_dom (my : WorldT)).
	    {
	      pose proof Hworld_x as [_ [Hdom_x _]].
	      pose proof (Hdom_x (LVFree x)
	        ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	      rewrite res_lift_free_dom in Hx_lift_m.
	      unfold lvars_of_atoms in Hx_lift_m.
	      apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	      inversion Heq. subst a.
	      rewrite Hdom. set_solver.
	    }
	    pose proof (wfworldA_store_dom my σxy Hσxy) as Hσxy_dom.
	    assert (Hx_dom_σxy : x ∈ dom (σxy : gmap atom value)).
	    {
	      change (x ∈ dom (σxy : gmap atom value)).
	      rewrite Hσxy_dom. exact Hx_dom_my.
	    }
    assert (Hret_restrict :
        tm_eval_in_store (store_restrict (σxy : gmap atom value) ({[x]} : aset))
          (tret (vfvar x)) vy).
    {
      apply (proj2 (tm_eval_in_store_restrict_fv_subset
        σxy (tret (vfvar x)) vy ({[x]} : aset)
        ltac:(cbn [fv_tm fv_value]; set_solver))).
      change (tm_eval_in_store σxy (tret (vfvar x)) vy).
      exact Heval_ret.
    }
    assert (Hx_dom_restrict :
        x ∈ dom (store_restrict (σxy : gmap atom value) ({[x]} : aset) : gmap atom value)).
    {
      destruct (σxy !! x) as [vx|] eqn:Hx_lookup0.
      - eapply elem_of_dom_2.
        eapply storeA_restrict_lookup_some_2;
          [exact Hx_lookup0|set_solver].
      - apply not_elem_of_dom in Hx_lookup0. contradiction.
    }
    pose proof (tm_eval_in_store_ret_fvar_inv
      (store_restrict (σxy : gmap atom value) ({[x]} : aset)) x vy
      (Hclosed_x σxy Hσxy) Hx_dom_restrict Hret_restrict) as Hx_lookup_xy_r.
    apply storeA_restrict_lookup_some in Hx_lookup_xy_r as [_ Hx_lookup_xy].
	    assert (Hx_in_m : x ∈ world_dom (m : WorldT)).
	    {
	      pose proof Hworld_x as [_ [Hdom_x _]].
	      pose proof (Hdom_x (LVFree x)
	        ltac:(apply elem_of_union_r; set_solver)) as Hx_lift_m.
	      rewrite res_lift_free_dom in Hx_lift_m.
	      unfold lvars_of_atoms in Hx_lift_m.
	      apply elem_of_map in Hx_lift_m as [a [Heq Ha]].
	      inversion Heq. subst a. exact Ha.
	    }
    assert (Hx_lookup_xy_restrict :
        store_restrict (σxy : gmap atom value) (world_dom (m : WorldT)) !! x = Some vy).
    {
      apply storeA_restrict_lookup_some_2;
        [exact Hx_lookup_xy|exact Hx_in_m].
    }
    rewrite Hσxy_restrict in Hx_lookup_xy_restrict.
	    rewrite Hx_lookup in Hx_lookup_xy_restrict.
	    inversion Hx_lookup_xy_restrict. subst vy.
	    exists σxy. split; [exact Hσxy|]. split.
		    + transitivity (store_restrict (σx : gmap atom value) (lvars_fv (tm_lvars e))).
	      * symmetry.
	        rewrite <- Hσxy_restrict.
	        apply storeA_restrict_twice_subset.
	        intros a Ha.
	        pose proof Hworld_x as [_ [Hdom_x _]].
	        pose proof (Hdom_x (LVFree a)
	          ltac:(apply elem_of_union_l; apply lvars_fv_elem; exact Ha))
	          as Ha_lift_m.
	        rewrite res_lift_free_dom in Ha_lift_m.
	        unfold lvars_of_atoms in Ha_lift_m.
	        apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
	        inversion Heq. subst b. exact Hb.
	      * transitivity
		          (store_restrict (store_restrict (σ : gmap atom value) (world_dom (m : WorldT)))
	            (lvars_fv (tm_lvars e))).
	        -- exact Hproj_x.
	        -- apply storeA_restrict_twice_subset.
	           intros a Ha.
	           pose proof Hworld_x as [_ [Hdom_x _]].
	           pose proof (Hdom_x (LVFree a)
	             ltac:(apply elem_of_union_l; apply lvars_fv_elem; exact Ha))
	             as Ha_lift_m.
	           rewrite res_lift_free_dom in Ha_lift_m.
	           unfold lvars_of_atoms in Ha_lift_m.
	           apply elem_of_map in Ha_lift_m as [b [Heq Hb]].
	           inversion Heq. subst b. exact Hb.
	    + rewrite lstore_lift_free_lookup_free in Hy_lookup.
		      exact Hy_lookup.
Qed.

Lemma expr_result_extension_fiber_models_result_slot
    e x F (m mx my mfib : WfWorldT) X σ :
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  lc_tm e ->
  expr_total_on_atom_world e m ->
  wfworld_closed_on (fv_tm e) m ->
  x ∉ X ->
  X ∩ world_dom (my : WorldT) ⊆ world_dom (mx : WorldT) ->
  res_restrict my (world_dom (mx : WorldT)) = mx ->
  res_fiber_from_projection my X σ mfib ->
  mfib ⊨ formula_msubst_store (store_restrict σ (fv_tm e))
    (expr_result_formula e (LVFree x)).
Proof.
  intros HF Hext Hlc_e Htotal Hclosed_e HxX HXmy Hrestrict_my Hproj.
  set (σe := store_restrict σ (fv_tm e)).
  assert (HσeD : dom (σe : StoreT) ⊆ lvars_fv (tm_lvars e)).
  {
    subst σe. rewrite tm_lvars_fv.
    apply storeA_restrict_dom_subset.
  }
  assert (Hfixed :
      forall τ, (mfib : WorldT) τ ->
        store_restrict τ (dom (σe : StoreT)) = σe).
  {
    subst σe. intros τ Hτ.
    eapply res_fiber_from_projection_store_restrict_substore; eauto.
  }
  apply (proj1 (res_models_fibvars_msubst_store_fixed
    mfib (tm_lvars e) (FAtom (expr_result_qual e (LVFree x)))
    σe HσeD Hfixed)).
  assert (Hplain : mfib ⊨ expr_result_formula e (LVFree x)).
  2:{ exact Hplain. }
  pose proof (expr_result_extension_world_models_closed
    e x F m mx Hclosed_e HF Hext Htotal) as Hworld_mx.
  apply expr_result_atom_world_to_formula.
  - destruct Hworld_mx as [Hxfresh [Hdom_mx Hstores_mx]].
    split.
    + exact Hxfresh.
    + split.
	      * intros lv Hlv.
	        destruct lv as [k|a].
	        -- exfalso.
	           apply elem_of_union in Hlv as [Hlv|Hlv].
	           ++ rewrite (tm_lvars_lc_eq_atoms e Hlc_e) in Hlv.
	              unfold lvars_of_atoms in Hlv.
	              apply elem_of_map in Hlv as [? [Hbad _]]. discriminate.
	           ++ apply elem_of_singleton in Hlv. discriminate.
	        -- assert (Ha_mx : a ∈ world_dom (mx : WorldT)).
	           {
	             assert (HLV : LVFree a ∈ worldA_dom (res_lift_free mx)).
	             {
	               apply Hdom_mx.
	               apply elem_of_union in Hlv as [Hlv|Hlv].
	               - apply elem_of_union_l. exact Hlv.
	               - apply elem_of_singleton in Hlv as ->.
	                 apply elem_of_union_r. apply elem_of_singleton. reflexivity.
	             }
	             rewrite res_lift_free_dom in HLV.
	             unfold lvars_of_atoms in HLV.
	             apply elem_of_map in HLV as [b [Heq Hb]].
	             inversion Heq. subst b. exact Hb.
	           }
           destruct Hproj as [_ Hfib_eq].
	           change ((mfib : WorldT) = rawA_fiber (my : WorldT) σ) in Hfib_eq.
	           pose proof (f_equal world_dom Hfib_eq) as Hdom_fib.
	           change (world_dom (mfib : WorldT) = world_dom (my : WorldT)) in Hdom_fib.
           rewrite res_lift_free_dom.
           unfold lvars_of_atoms.
           apply elem_of_map. exists a. split; [reflexivity|].
           change (a ∈ world_dom (mfib : WorldT)).
           rewrite Hdom_fib.
           assert (Ha_my : a ∈ world_dom (my : WorldT)).
           {
             assert (Ha_restrict :
                 a ∈ world_dom
                   (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
             { rewrite Hrestrict_my. exact Ha_mx. }
             change (a ∈ world_dom
               (res_restrict my (world_dom (mx : WorldT)) : WorldT))
               in Ha_restrict.
             rewrite res_restrict_dom in Ha_restrict.
             set_solver.
           }
           exact Ha_my.
      * intros τL HτL.
        destruct HτL as [τ [Hτ ->]].
        destruct Hproj as [Hproj_src Hfib_eq].
        pose proof (res_fiber_from_projection_store_source
          my mfib X σ τ (conj Hproj_src Hfib_eq) Hτ) as Hτ_my.
        set (τmx := store_restrict τ (world_dom (mx : WorldT))).
        assert (Hτmx_mx : (mx : WorldT) τmx).
        {
          rewrite <- Hrestrict_my.
          subst τmx.
          exists τ. split; [exact Hτ_my|reflexivity].
        }
        specialize (Hstores_mx (lstore_lift_free τmx)
          ltac:(exists τmx; split; [exact Hτmx_mx|reflexivity])).
        destruct Hstores_mx as [Hx_fresh [v [Hxlook Heval]]].
        split; [exact Hx_fresh|].
        exists v. split.
        -- rewrite lstore_lift_free_lookup_free in Hxlook |- *.
           subst τmx.
           change ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! x =
             Some v) in Hxlook.
           apply storeA_restrict_lookup_some in Hxlook as [_ Hxlook].
           exact Hxlook.
	        -- eapply tm_eval_in_store_agree_on_fv; [|exact Heval].
	           apply storeA_map_eq. intros a.
	           rewrite !storeA_restrict_lookup.
	           destruct (decide (a ∈ fv_tm e)) as [Ha|Ha]; [|reflexivity].
	           subst τmx.
	           rewrite storeA_restrict_lookup.
	           destruct (decide (a ∈ world_dom (mx : WorldT))) as [_|Hbad];
	             [reflexivity|].
	           exfalso. apply Hbad.
	           assert (HLV : LVFree a ∈ worldA_dom (res_lift_free mx)).
		   {
		     apply Hdom_mx. apply elem_of_union_l.
	             apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
		   }
	           rewrite res_lift_free_dom in HLV.
	           unfold lvars_of_atoms in HLV.
	           apply elem_of_map in HLV as [b [Heq Hb]].
	           inversion Heq. subst b. exact Hb.
  - intros y τ v Heq Hτ Heval.
    inversion Heq. subst y.
    destruct HF as [Hx_fresh [Hin Hout] Hrel].
    destruct Hproj as [Hproj_src Hfib_eq].
    pose proof (res_fiber_from_projection_store_source
      my mfib X σ τ (conj Hproj_src Hfib_eq) Hτ) as Hτ_my.
    set (τmx := store_restrict τ (world_dom (mx : WorldT))).
    assert (Hτmx_mx : (mx : WorldT) τmx).
    {
      rewrite <- Hrestrict_my.
      subst τmx. exists τ. split; [exact Hτ_my|reflexivity].
    }
    apply (proj1 (resA_extend_by_store_iff m F mx τmx Hext)) in Hτmx_mx.
    destruct Hτmx_mx as [τm [we [τe [Hτm [HFrel [Hτe Hτmx_eq]]]]]].
    assert (Hτe_dom : dom (τe : StoreT) = {[x]}).
    {
      pose proof (wfworldA_store_dom we τe Hτe) as Hdomτe.
      change (dom (τe : StoreT) = world_dom (we : WorldT)) in Hdomτe.
      rewrite Hdomτe.
      pose proof (extA_rel_dom F (store_restrict τm (ext_in F)) we) as Hdom_we.
      rewrite <- Hout.
      apply Hdom_we; [|exact HFrel].
      rewrite storeA_restrict_dom.
      pose proof (wfworldA_store_dom m τm Hτm) as Hdomτm.
      change (dom (τm : StoreT) = world_dom (m : WorldT)) in Hdomτm.
      pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
      unfold ext_in in Hin_sub. unfold ext_in in Hin.
      rewrite Hin in Hin_sub.
      apply set_eq. intros a. split.
      - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
      - intros Ha. apply elem_of_intersection. split; [|exact Ha].
        change (a ∈ dom (τm : StoreT)).
        rewrite Hdomτm. rewrite Hin in Ha. exact (Hin_sub a Ha).
    }
    assert (Heval_m :
        tm_eval_in_store (store_restrict τm (fv_tm e)) e v).
    {
      assert (Hτ_agree :
          store_restrict τ (fv_tm e) =
          store_restrict τm (fv_tm e)).
	      {
	        subst τmx.
	        rewrite <- (storeA_restrict_twice_subset τ
	          (world_dom (mx : WorldT)) (fv_tm e)).
	        2:{
	          denotation_regular_res_extend_input.
	          denotation_regular_res_extend_dom.
	          rewrite <- Hin, Hdom_ext.
	          set_solver.
	        }
		        rewrite Hτmx_eq.
	        apply storeA_map_eq. intros a.
	        rewrite !storeA_restrict_lookup.
	        destruct (decide (a ∈ fv_tm e)) as [Ha|Ha]; [|reflexivity].
	        change ((((τm : StoreT) ∪ τe) : gmap atom value) !! a =
	          (τm : StoreT) !! a).
	        destruct ((τm : StoreT) !! a) eqn:Hτma.
	        - change ((((τm : StoreT) : gmap atom value) ∪
	              ((τe : StoreT) : gmap atom value)) !! a = Some v0).
	          transitivity (((τm : StoreT) : gmap atom value) !! a).
	          + apply lookup_union_l'. exists v0. exact Hτma.
	          + exact Hτma.
	        - apply (proj2 (map_lookup_union_None
	            (τm : StoreT) τe a)).
	          split; [exact Hτma|].
              apply not_elem_of_dom_1.
	            change (a ∉ dom (τe : StoreT)).
	            rewrite Hτe_dom.
              apply not_elem_of_singleton_2.
              intros ->. exact (Hx_fresh Ha).
	      }
      rewrite <- Hτ_agree.
      exact Heval.
    }
    assert (Hτm_dom_fv :
        dom (store_restrict τm (ext_in F) : StoreT) = ext_in F).
    {
      eapply extA_projection_dom.
      - apply resA_extend_by_applicable in Hext. exact Hext.
      - exact Hτm.
    }
    assert (Hwe_v : (we : WorldT) ({[x := v]} : StoreT)).
    {
      eapply expr_result_extension_apply_total_store.
	      - exact {| expr_result_extension_witness_fresh := Hx_fresh;
	                 expr_result_extension_witness_shape := conj Hin Hout;
	                 expr_result_extension_witness_rel := Hrel |}.
	      - rewrite <- Hin. exact Hτm_dom_fv.
      - exact HFrel.
      - rewrite Hin. exact Heval_m.
    }
    set (τmxv := (τm : StoreT) ∪ ({[x := v]} : StoreT)).
    assert (Hτmxv_mx : (mx : WorldT) τmxv).
    {
      apply (proj2 (resA_extend_by_store_iff m F mx τmxv Hext)).
      exists τm, we, ({[x := v]} : StoreT).
      split; [exact Hτm|]. split; [exact HFrel|].
      split; [exact Hwe_v|reflexivity].
    }
    assert (Hτmxv_X :
        store_restrict τmxv (X ∩ world_dom (mx : WorldT)) =
        store_restrict τ (X ∩ world_dom (mx : WorldT))).
	    {
	      subst τmxv.
	      apply storeA_map_eq. intros a.
	      rewrite !storeA_restrict_lookup.
	      destruct (decide (a ∈ X ∩ world_dom (mx : WorldT))) as [Ha|Ha];
	        [|reflexivity].
	      apply elem_of_intersection in Ha as [HaX Hamx].
	      assert (Hτ_lookup :
	          τ !! a = (((τm : StoreT) ∪ τe) : StoreT) !! a).
	      {
	        pose proof (f_equal (fun s : StoreT => s !! a) Hτmx_eq)
	          as Htmp.
	        subst τmx.
	        change ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a =
	          (((τm : StoreT) ∪ τe) : StoreT) !! a) in Htmp.
	        transitivity ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a).
	        - destruct (τ !! a) eqn:Hτa.
	          + symmetry. apply storeA_restrict_lookup_some_2; [exact Hτa|exact Hamx].
	          + exfalso.
	            assert (Ha_my : a ∈ world_dom (my : WorldT)).
	            {
	              assert (Ha_restrict :
	                  a ∈ world_dom
	                    (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	              { rewrite Hrestrict_my. exact Hamx. }
		              change (a ∈ world_dom
		                (res_restrict my (world_dom (mx : WorldT)) : WorldT))
		                in Ha_restrict.
		              rewrite res_restrict_dom in Ha_restrict.
		              apply elem_of_intersection in Ha_restrict as [Ha_my _].
                  exact Ha_my.
	            }
		            pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
		            change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
		            assert (a ∈ dom (τ : StoreT)) by (rewrite Hdomτ; exact Ha_my).
		            change (a ∈ dom (τ : gmap atom value)) in H.
		            apply elem_of_dom in H as [? Hlook].
		            rewrite Hτa in Hlook. discriminate.
	        - exact Htmp.
	      }
			      assert (Hax : a <> x).
          { intros ->. exact (HxX HaX). }
      change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value) !! a =
        ((τ : StoreT) : gmap atom value) !! a).
      rewrite Hτ_lookup.
      change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value) !! a =
        (((τm : StoreT) ∪ τe) : gmap atom value) !! a).
	      destruct ((τm : StoreT) !! a) eqn:Hτma.
	      - transitivity ((τm : StoreT) !! a).
	        + apply lookup_union_l'. exists v0. exact Hτma.
	        + symmetry. apply lookup_union_l'. exists v0. exact Hτma.
	      - transitivity (@None value).
	        + apply (proj2 (map_lookup_union_None
	            (τm : StoreT) ({[x := v]} : StoreT) a)).
	          split.
	          * exact Hτma.
	          * change ((({[x := v]} : gmap atom value) !! a) = None).
	            apply lookup_singleton_ne. congruence.
	        + symmetry. apply (proj2 (map_lookup_union_None
	            (τm : StoreT) τe a)). split.
	          * exact Hτma.
	          * apply not_elem_of_dom_1.
	            change (a ∉ dom (τe : StoreT)).
	            rewrite Hτe_dom.
              apply not_elem_of_singleton_2.
              intros ->. exact (HxX HaX).
    }
	    assert (Hτmxv_in_restrict :
	        (res_restrict my (world_dom (mx : WorldT)) : WorldT) τmxv).
	    { rewrite Hrestrict_my. exact Hτmxv_mx. }
	    change ((rawA_restrict (my : WorldT) (world_dom (mx : WorldT))) τmxv)
	      in Hτmxv_in_restrict.
	    cbn [rawA_restrict worldA_stores] in Hτmxv_in_restrict.
	    destruct Hτmxv_in_restrict as [τv [Hτv_my Hτv_restrict]].
	    exists τv.
	    split.
	    + subst τmxv.
	        assert (Hτv_X : store_restrict τv X = σ).
        {
	          apply storeA_map_eq. intros a.
	          rewrite !storeA_restrict_lookup.
	          destruct (decide (a ∈ X)) as [HaX|HaX]; [|].
	          2:{
	            destruct (σ !! a) eqn:Hσa; [|reflexivity].
	            exfalso. apply HaX.
	            pose proof (wfworld_store_dom (res_restrict my X) σ Hproj_src)
	              as Hdomσ.
	            change (dom (σ : StoreT) =
	              world_dom (res_restrict my X : WorldT)) in Hdomσ.
	            rewrite res_restrict_dom in Hdomσ.
	            assert (a ∈ dom (σ : StoreT)).
	            {
	              change (a ∈ dom (σ : gmap atom value)).
	              rewrite elem_of_dom. eauto.
			            }
			            rewrite Hdomσ in H.
                apply elem_of_intersection in H as [_ HaX'].
                exact HaX'.
	          }
	          destruct (decide (a ∈ world_dom (my : WorldT))) as [Ha_my|Ha_not_my].
		          2:{
		            assert (Hτv_none : τv !! a = None).
		            {
		              destruct (τv !! a) eqn:Hτva; [|reflexivity].
		              exfalso. apply Ha_not_my.
		              pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
		              change (dom (τv : StoreT) = world_dom (my : WorldT))
		                in Hdomτv.
		              rewrite <- Hdomτv.
		              change (a ∈ dom (τv : gmap atom value)).
		              rewrite elem_of_dom. eauto.
		            }
	            assert (Hσ_none : σ !! a = None).
	            {
	              apply not_elem_of_dom_1.
	              change (a ∉ dom (σ : StoreT)).
	              pose proof (wfworld_store_dom (res_restrict my X) σ Hproj_src)
	                as Hdomσ.
	              change (dom (σ : StoreT) =
	                world_dom (res_restrict my X : WorldT)) in Hdomσ.
			              rewrite Hdomσ, res_restrict_dom.
                    intros Haσ.
                    apply elem_of_intersection in Haσ as [Ha_my _].
                    exact (Ha_not_my Ha_my).
		            }
		            change ((τv : StoreT) !! a = (σ : StoreT) !! a).
		            transitivity (@None value); [exact Hτv_none|].
		            symmetry. exact Hσ_none.
		          }
	          assert (Ha_mx : a ∈ world_dom (mx : WorldT)).
	          { apply HXmy. apply elem_of_intersection. split; [exact HaX|exact Ha_my]. }
	          assert (Hv_lookup :
	              τv !! a =
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
	          {
	            pose proof (f_equal (fun s : StoreT => s !! a) Hτv_restrict)
	              as Hv_restrict.
	            change ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a =
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a)
	              in Hv_restrict.
	            transitivity ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a).
	            - destruct (τv !! a) eqn:Hτva.
	              + symmetry. apply storeA_restrict_lookup_some_2;
	                  [exact Hτva|exact Ha_mx].
	              + exfalso.
	                pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
	                change (dom (τv : StoreT) = world_dom (my : WorldT))
	                  in Hdomτv.
	                assert (a ∈ dom (τv : StoreT)) by
	                  (rewrite Hdomτv; exact Ha_my).
	                change (a ∈ dom (τv : gmap atom value)) in H.
	                apply elem_of_dom in H as [? Hlook].
	                rewrite Hτva in Hlook. discriminate.
		            - exact Hv_restrict.
		          }
	          change ((τv : StoreT) !! a = (σ : StoreT) !! a).
	          transitivity
	            ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
	          { exact Hv_lookup. }
	          assert (Hmxv_lookup :
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a =
	              τ !! a).
	          {
	            pose proof (f_equal (fun s : StoreT => s !! a) Hτmxv_X)
	              as Hmxv.
	            change ((store_restrict
	              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)
	              (X ∩ world_dom (mx : WorldT)) : StoreT) !! a =
	              (store_restrict τ (X ∩ world_dom (mx : WorldT)) : StoreT) !! a)
	              in Hmxv.
		            transitivity ((store_restrict
		              (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)
		              (X ∩ world_dom (mx : WorldT)) : StoreT) !! a).
		            - destruct ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a)
		                eqn:Hlook.
		              + symmetry. apply storeA_restrict_lookup_some_2.
		                * exact Hlook.
		                * apply elem_of_intersection. split; [exact HaX|exact Ha_mx].
		              + exfalso.
		                pose proof (wfworld_store_dom mx
		                  (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)
		                  Hτmxv_mx) as Hdommxv.
		                change (dom ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT)) =
		                  world_dom (mx : WorldT)) in Hdommxv.
			                assert (a ∈ dom (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT))
		                  by (rewrite Hdommxv; exact Ha_mx).
			                change (a ∈ dom (((τm : StoreT) : gmap atom value) ∪
			                  (({[x := v]} : StoreT) : gmap atom value))) in H.
			                apply elem_of_dom in H as [? Hbad].
			                change ((((τm : StoreT) : gmap atom value) ∪
			                  (({[x := v]} : StoreT) : gmap atom value)) !! a = None)
			                  in Hlook.
			                rewrite Hlook in Hbad. discriminate.
	            - transitivity ((store_restrict τ
	                (X ∩ world_dom (mx : WorldT)) : StoreT) !! a).
	              + exact Hmxv.
	              + destruct (τ !! a) eqn:Hτa.
	                * apply storeA_restrict_lookup_some_2.
	                  -- exact Hτa.
	                  -- apply elem_of_intersection. split; [exact HaX|exact Ha_mx].
	                * exfalso.
	                  pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
	                  change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
	                  assert (a ∈ dom (τ : StoreT)) by
	                    (rewrite Hdomτ; exact Ha_my).
	                  change (a ∈ dom (τ : gmap atom value)) in H.
	                  apply elem_of_dom in H as [? Hbad].
	                  rewrite Hτa in Hbad. discriminate.
	          }
		          rewrite Hmxv_lookup.
		          pose proof (res_fiber_from_projection_store_restrict
		            my mfib X σ τ (conj Hproj_src Hfib_eq) Hτ) as Hτfix.
	          assert (Haσ : a ∈ dom (σ : StoreT)).
	          {
	            pose proof (wfworld_store_dom (res_restrict my X) σ Hproj_src)
	              as Hdomσ.
	            change (dom (σ : StoreT) =
		              world_dom (res_restrict my X : WorldT)) in Hdomσ.
		            rewrite Hdomσ, res_restrict_dom.
                apply elem_of_intersection. split; [exact Ha_my|exact HaX].
	          }
	          pose proof (f_equal (fun s : StoreT => s !! a) Hτfix) as Hfixa.
	          change ((store_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
	            σ !! a) in Hfixa.
	          transitivity ((store_restrict τ (dom (σ : StoreT)) : StoreT) !! a).
	          -- destruct (τ !! a) eqn:Hτa.
	             ++ symmetry. apply storeA_restrict_lookup_some_2;
	                  [exact Hτa|exact Haσ].
	             ++ exfalso.
	                pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
	                change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
	                assert (a ∈ dom (τ : StoreT)) by
	                  (rewrite Hdomτ; exact Ha_my).
	                change (a ∈ dom (τ : gmap atom value)) in H.
	                apply elem_of_dom in H as [? Hbad].
	                rewrite Hτa in Hbad. discriminate.
	          -- exact Hfixa.
	        }
	        change ((mfib : WorldT) = rawA_fiber (my : WorldT) σ) in Hfib_eq.
	        rewrite Hfib_eq.
	        split; [exact Hτv_my|].
	        eapply storeA_restrict_projection_dom.
	        exact Hτv_X.
	    + split.
	      * apply storeA_map_eq. intros a.
	        rewrite !storeA_restrict_lookup.
	        destruct (decide (a ∈ lvars_fv (tm_lvars e))) as [Ha|Ha];
	          [|reflexivity].
	        assert (Ha_fv : a ∈ fv_tm e) by (rewrite <- tm_lvars_fv; exact Ha).
		        assert (Ha_mx : a ∈ world_dom (mx : WorldT)).
		        {
              pose proof (res_extend_by_input_dom m F mx Hext) as Hin_sub.
              unfold ext_in in Hin_sub. unfold ext_in in Hin.
              rewrite Hin in Hin_sub.
              pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
              rewrite Hdom_mx. apply elem_of_union_l.
              exact (Hin_sub a Ha_fv).
		        }
	        assert (Hv_lookup :
	            τv !! a =
	            (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
	        {
	          pose proof (f_equal (fun s : StoreT => s !! a) Hτv_restrict)
	            as Htmp.
	          change ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a =
	            (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a)
	            in Htmp.
	          transitivity ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! a).
	          - destruct (τv !! a) eqn:Hτva.
	            + symmetry. apply storeA_restrict_lookup_some_2;
	                [exact Hτva|exact Ha_mx].
	            + exfalso.
	              pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
	              change (dom (τv : StoreT) = world_dom (my : WorldT)) in Hdomτv.
	              assert (a ∈ world_dom (my : WorldT)).
	              {
	                assert (Ha_restrict :
	                    a ∈ world_dom
	                      (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	                { rewrite Hrestrict_my. exact Ha_mx. }
	                change (a ∈ world_dom
		                  (res_restrict my (world_dom (mx : WorldT)) : WorldT))
		                  in Ha_restrict.
		                rewrite res_restrict_dom in Ha_restrict.
		                apply elem_of_intersection in Ha_restrict as [Ha_my _].
                    exact Ha_my.
	              }
	              assert (a ∈ dom (τv : StoreT)) by (rewrite Hdomτv; exact H).
	              change (a ∈ dom (τv : gmap atom value)) in H0.
	              apply elem_of_dom in H0 as [? Hbad].
	              rewrite Hτva in Hbad. discriminate.
	          - exact Htmp.
	        }
	        assert (Hτ_lookup :
	            τ !! a = (((τm : StoreT) ∪ τe) : StoreT) !! a).
	        {
	          pose proof (f_equal (fun s : StoreT => s !! a) Hτmx_eq) as Htmp.
	          subst τmx.
	          change ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a =
	            (((τm : StoreT) ∪ τe) : StoreT) !! a) in Htmp.
	          transitivity ((store_restrict τ (world_dom (mx : WorldT)) : StoreT) !! a).
	          - destruct (τ !! a) eqn:Hτa.
	            + symmetry. apply storeA_restrict_lookup_some_2;
	                [exact Hτa|exact Ha_mx].
	            + exfalso.
	              pose proof (wfworld_store_dom my τ Hτ_my) as Hdomτ.
	              change (dom (τ : StoreT) = world_dom (my : WorldT)) in Hdomτ.
	              assert (a ∈ world_dom (my : WorldT)).
	              {
	                assert (Ha_restrict :
	                    a ∈ world_dom
	                      (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	                { rewrite Hrestrict_my. exact Ha_mx. }
	                change (a ∈ world_dom
	                  (res_restrict my (world_dom (mx : WorldT)) : WorldT))
	                  in Ha_restrict.
	                rewrite res_restrict_dom in Ha_restrict.
	                set_solver.
	              }
	              assert (a ∈ dom (τ : StoreT)) by (rewrite Hdomτ; exact H).
	              change (a ∈ dom (τ : gmap atom value)) in H0.
	              apply elem_of_dom in H0 as [? Hbad].
	              rewrite Hτa in Hbad. discriminate.
	          - exact Htmp.
	        }
		        change ((τv : StoreT) !! a = (τ : StoreT) !! a).
		        transitivity
		          ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! a).
		        { exact Hv_lookup. }
		        transitivity ((((τm : StoreT) ∪ τe) : StoreT) !! a).
		        2:{ symmetry. exact Hτ_lookup. }
			        assert (Hax_fv : a <> x).
              { intros ->. exact (Hx_fresh Ha_fv). }
	        change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value) !! a =
	          (((τm : StoreT) ∪ τe) : gmap atom value) !! a).
	        destruct ((τm : StoreT) !! a) eqn:Hτma.
	        -- transitivity ((τm : StoreT) !! a).
	           ++ apply lookup_union_l'. exists v0. exact Hτma.
	           ++ symmetry. apply lookup_union_l'. exists v0. exact Hτma.
	        -- transitivity (@None value).
	           ++ apply (proj2 (map_lookup_union_None
	                (τm : StoreT) ({[x := v]} : StoreT) a)).
	              split; [exact Hτma|].
	              change ((({[x := v]} : gmap atom value) !! a) = None).
	              apply lookup_singleton_ne. congruence.
	           ++ symmetry. apply (proj2 (map_lookup_union_None
	                (τm : StoreT) τe a)). split; [exact Hτma|].
		              apply not_elem_of_dom_1.
		              change (a ∉ dom (τe : StoreT)).
		              rewrite Hτe_dom.
                  apply not_elem_of_singleton_2.
                  intros ->. exact (Hx_fresh Ha_fv).
	      * subst τmxv.
	        pose proof (f_equal (fun s : StoreT => s !! x) Hτv_restrict) as Hxlook.
	        assert (Hx_mx : x ∈ world_dom (mx : WorldT)).
	        { exact (res_extend_by_singleton_output_in_world m mx F x Hext Hout). }
	        change ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! x =
	          (((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! x)
	          in Hxlook.
	        transitivity
	          ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : StoreT) !! x).
	        2:{
	        change ((((τm : StoreT) ∪ ({[x := v]} : StoreT)) : gmap atom value)
	          !! x = Some v).
	        apply map_lookup_union_Some_raw. right.
	        split.
	        - apply not_elem_of_dom_1.
	           exact (res_extend_by_singleton_output_notin_base_store
	             m mx F x τm Hext Hout Hτm).
	        - change ((({[x := v]} : gmap atom value) !! x) = Some v).
		           apply map_lookup_singleton.
		        }
		        destruct (τv !! x) eqn:Hτvx.
		        { transitivity
		            ((store_restrict τv (world_dom (mx : WorldT)) : StoreT) !! x).
		          - symmetry. apply storeA_restrict_lookup_some_2;
		              [exact Hτvx|exact Hx_mx].
		          - exact Hxlook.
		        }
		        { exfalso.
		          pose proof (wfworld_store_dom my τv Hτv_my) as Hdomτv.
		          change (dom (τv : StoreT) = world_dom (my : WorldT)) in Hdomτv.
		          assert (x ∈ world_dom (my : WorldT)).
	          {
	            assert (Hx_restrict :
	                x ∈ world_dom
	                  (res_restrict my (world_dom (mx : WorldT)) : WfWorldT)).
	            { rewrite Hrestrict_my. exact Hx_mx. }
	            change (x ∈ world_dom
		              (res_restrict my (world_dom (mx : WorldT)) : WorldT))
		              in Hx_restrict.
		            rewrite res_restrict_dom in Hx_restrict.
		            apply elem_of_intersection in Hx_restrict as [Hx_my _].
                exact Hx_my.
	          }
	          assert (x ∈ dom (τv : StoreT)) by (rewrite Hdomτv; exact H).
		          change (x ∈ dom (τv : gmap atom value)) in H0.
		          apply elem_of_dom in H0 as [? Hbad].
		          rewrite Hτvx in Hbad. discriminate.
		        }
Qed.

Lemma expr_result_formula_at_of_result_extends
    D e x F (m mx : WfWorldT) :
  lc_lvars D ->
  lc_tm e ->
  lvars_fv D ⊆ world_dom (m : WorldT) ->
  fv_tm e ⊆ world_dom (m : WorldT) ->
  x ∉ lvars_fv D ∪ fv_tm e ->
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  wfworld_closed_on (fv_tm e) m ->
  mx ⊨ expr_result_formula_at (D ∪ tm_lvars e) e (LVFree x).
Proof.
  intros HlcD Hlc_e HDm Hfv_m HxD HF Hext Htotal Hclosed.
  apply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    change (formula_fv (expr_result_formula_at (D ∪ tm_lvars e) e (LVFree x)) ⊆
      world_dom (mx : WorldT)).
    rewrite formula_fv_expr_result_formula_at.
    intros a Ha.
    pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
    destruct HF as [_ [Hin Hout] _].
    rewrite Hdom_mx.
    change (extA_out F) with (ext_out F).
    rewrite Hout.
    rewrite lvars_fv_union in Ha.
    apply elem_of_union in Ha as [HaD|HaQ].
    + apply elem_of_union in HaD as [HaD|HaE].
      * apply elem_of_union_l. exact (HDm a HaD).
      * apply elem_of_union_l. apply Hfv_m.
        rewrite <- tm_lvars_fv. exact HaE.
    + rewrite lvars_fv_union in HaQ.
      apply elem_of_union in HaQ as [HaE|Hax].
      * apply elem_of_union_l. apply Hfv_m.
        rewrite <- tm_lvars_fv. exact HaE.
      * apply elem_of_union_r.
        rewrite <- lvars_fv_singleton_free. exact Hax.
  - intros v Hv.
    apply elem_of_union in Hv as [Hv|Hv].
    + exact (HlcD v Hv).
    + exact (tm_lvars_lc e Hlc_e v Hv).
  - intros σ mfib Hproj.
    assert (HlcDe : lc_lvars (D ∪ tm_lvars e)).
    {
      intros v Hv.
      apply elem_of_union in Hv as [Hv|Hv].
      - exact (HlcD v Hv).
      - exact (tm_lvars_lc e Hlc_e v Hv).
    }
    assert (HXmx :
        lvars_fv (D ∪ tm_lvars e) ⊆ world_dom (mx : WorldT)).
    {
      intros a Ha.
      pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx.
      rewrite Hdom_mx.
      apply elem_of_union_l.
      rewrite lvars_fv_union in Ha.
      apply elem_of_union in Ha as [Ha|Ha].
      - exact (HDm a Ha).
      - apply Hfv_m. rewrite <- tm_lvars_fv. exact Ha.
    }
    destruct Hproj as [Hproj_store Hfib_eq].
    pose proof (wfworld_store_dom
      (res_restrict mx (lvars_fv (D ∪ tm_lvars e))) σ Hproj_store)
      as Hdomσ.
    change (dom (σ : StoreT) =
      world_dom (res_restrict mx (lvars_fv (D ∪ tm_lvars e)) : WorldT))
      in Hdomσ.
    rewrite res_restrict_dom in Hdomσ.
    assert (Hdomσ_eq : dom (σ : StoreT) = lvars_fv (D ∪ tm_lvars e)).
    {
      rewrite Hdomσ.
      apply set_eq. intros a. split.
      - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
      - intros Ha. apply elem_of_intersection. split; [exact (HXmx a Ha)|exact Ha].
    }
    assert (Hxσ : x ∉ dom (σ : StoreT)).
    {
      rewrite Hdomσ_eq. intros Hx.
      apply HxD.
      rewrite lvars_fv_union in Hx.
      apply elem_of_union in Hx as [Hx|Hx].
      - apply elem_of_union_l. exact Hx.
      - apply elem_of_union_r. rewrite <- tm_lvars_fv. exact Hx.
    }
    pose proof (expr_result_extension_fiber_models_result_slot
      e x F m mx mx mfib
      (lvars_fv (D ∪ tm_lvars e)) σ
      HF Hext Hlc_e Htotal Hclosed
      ltac:(rewrite ?lvars_fv_union;
        rewrite (tm_lvars_lc_eq_atoms e Hlc_e);
        rewrite ?lvars_fv_of_atoms; set_solver)
      ltac:(set_solver)
      ltac:(apply res_restrict_eq_of_le; apply raw_le_refl)
      (conj Hproj_store Hfib_eq)) as Hplain.
    eapply (expr_result_formula_msubst_store_to_atom
      mfib D e x σ).
    + exact HlcD.
    + exact Hlc_e.
    + exact Hxσ.
    + exact Hdomσ_eq.
    + exact Hplain.
Qed.

Lemma expr_result_formula_msubst_alias_ret_fvar
    (m : WfWorldT) e x y σ :
  y ∉ fv_tm e ∪ {[x]} ->
  x ∉ dom (σ : StoreT) ->
  y ∉ dom (σ : StoreT) ->
  wfworld_closed_on ({[x]} : aset) m ->
  (forall τ, (m : WorldT) τ ->
    store_restrict τ (dom (store_restrict σ (fv_tm e) : StoreT)) =
      store_restrict σ (fv_tm e)) ->
  m ⊨ formula_msubst_store σ (expr_result_formula e (LVFree x)) ->
  m ⊨ expr_result_formula (tret (vfvar x)) (LVFree y) ->
  m ⊨ formula_msubst_store σ (expr_result_formula e (LVFree y)).
Proof.
  intros Hyfresh Hxσ Hyσ Hclosed_x Hfixed Hresx Hret.
  rewrite formula_msubst_store_expr_result_formula_restrict in Hresx
    by exact Hxσ.
  rewrite formula_msubst_store_expr_result_formula_restrict
    by exact Hyσ.
  set (σe := store_restrict σ (fv_tm e)).
  assert (HσeD : dom (σe : StoreT) ⊆ lvars_fv (tm_lvars e)).
  {
    subst σe. rewrite tm_lvars_fv.
    apply storeA_restrict_dom_subset.
  }
  pose proof (res_models_fibvars_msubst_store_fixed
    m (tm_lvars e) (FAtom (expr_result_qual e (LVFree x))) σe
    HσeD Hfixed) as Hiffx.
  pose proof (res_models_fibvars_msubst_store_fixed
    m (tm_lvars e) (FAtom (expr_result_qual e (LVFree y))) σe
    HσeD Hfixed) as Hiffy.
  change (expr_result_formula e (LVFree x))
    with (FFibVars (tm_lvars e) (FAtom (expr_result_qual e (LVFree x))))
    in Hresx.
  change (expr_result_formula e (LVFree y))
    with (FFibVars (tm_lvars e) (FAtom (expr_result_qual e (LVFree y)))).
  apply Hiffy.
  assert (Hplainx : m ⊨ expr_result_formula e (LVFree x)).
  { apply Hiffx. exact Hresx. }
  pose proof (expr_result_formula_to_atom_world e (LVFree x) m Hplainx)
    as Hworld_x.
  pose proof (expr_result_formula_to_atom_world
    (tret (vfvar x)) (LVFree y) m Hret) as Hworld_y.
  pose proof (expr_result_formula_models_elim e (LVFree x) m Hplainx)
    as [_ [_ Hstore_x]].
  pose proof (expr_result_formula_models_elim
    (tret (vfvar x)) (LVFree y) m Hret) as [_ [_ Hstore_y]].
  apply expr_result_atom_world_to_formula.
  - destruct Hworld_x as [Hx_fresh [Hdom_x _]].
    destruct Hworld_y as [Hy_fresh [Hdom_y _]].
    split.
    + intros Hy_lvar.
      apply Hyfresh. apply elem_of_union_l.
      rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hy_lvar.
    + split.
      * intros z Hz.
        apply elem_of_union in Hz as [Hz|Hz].
        -- apply Hdom_x. apply elem_of_union_l. exact Hz.
        -- apply elem_of_singleton in Hz as ->.
           apply Hdom_y. apply elem_of_union_r. apply elem_of_singleton. reflexivity.
      * intros τL HτL.
        destruct HτL as [τ [Hτ ->]].
        specialize (Hstore_x τ Hτ) as [Hx_fresh_store [v [Hxlook Heval]]].
	        specialize (Hstore_y τ Hτ) as [_ [vy [Hylook Heval_ret]]].
	        split.
	        -- intros Hbad. apply Hyfresh.
	           apply elem_of_union_l.
	           rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hbad.
        -- exists v. split.
	           ++ transitivity (Some vy).
              ** exact Hylook.
	              ** assert (Heval_ret_full :
	                    tm_eval_in_store τ (tret (vfvar x)) vy).
	                 {
	                   change (tm_eval_in_store τ (tret (vfvar x)) vy).
	                   exact Heval_ret.
	                 }
	                 assert (Heval_ret_restrict :
	                     tm_eval_in_store (store_restrict τ ({[x]} : aset))
	                       (tret (vfvar x)) vy).
	                 {
	                   apply (proj2 (tm_eval_in_store_restrict_fv_subset
	                     τ (tret (vfvar x)) vy ({[x]} : aset)
	                     ltac:(cbn [fv_tm fv_value]; set_solver))).
	                   exact Heval_ret_full.
	                 }
	                 pose proof (tm_eval_in_store_ret_fvar_inv
	                   (store_restrict τ ({[x]} : aset)) x vy
	                   (Hclosed_x τ Hτ)
	                   ltac:(change (x ∈ dom
	                     (store_restrict τ ({[x]} : aset) : gmap atom value));
		                     rewrite elem_of_dom; eexists;
		                     apply storeA_restrict_lookup_some_2;
	                     [rewrite <- lstore_lift_free_lookup_free; exact Hxlook
	                     |set_solver])
		                   Heval_ret_restrict) as Hxvy.
	                 apply storeA_restrict_lookup_some in Hxvy as [_ Hxvy].
		                 assert (Hxlook_atom : τ !! x = Some v).
		                 { rewrite <- lstore_lift_free_lookup_free. exact Hxlook. }
	                 change ((τ : StoreT) !! x = Some vy) in Hxvy.
	                 pose proof (eq_trans (eq_sym Hxvy) Hxlook_atom) as HeqSome.
	                 inversion HeqSome.
		                 reflexivity.
           ++ exact Heval.
  - intros z τ v Heq Hτ Heval.
    inversion Heq. subst z.
    pose proof (expr_result_formula_fiber_witness e x m Hplainx
      τ v Hτ Heval) as [τv [Hτv [Hproj Hxlook]]].
    specialize (Hstore_y τv Hτv) as [_ [vy [Hylook Heval_ret]]].
	    exists τv. split; [exact Hτv|]. split; [exact Hproj|].
	    transitivity (Some vy).
	    + rewrite <- lstore_lift_free_lookup_free. exact Hylook.
	    + assert (Heval_ret_full :
	          tm_eval_in_store τv (tret (vfvar x)) vy).
	      {
	        change (tm_eval_in_store τv (tret (vfvar x)) vy).
	        exact Heval_ret.
	      }
	      assert (Heval_ret_restrict :
	          tm_eval_in_store (store_restrict τv ({[x]} : aset))
	            (tret (vfvar x)) vy).
	      {
	        apply (proj2 (tm_eval_in_store_restrict_fv_subset
	          τv (tret (vfvar x)) vy ({[x]} : aset)
	          ltac:(cbn [fv_tm fv_value]; set_solver))).
	        exact Heval_ret_full.
	      }
	      pose proof (tm_eval_in_store_ret_fvar_inv
	        (store_restrict τv ({[x]} : aset)) x vy
	        (Hclosed_x τv Hτv)
	        ltac:(change (x ∈ dom
	          (store_restrict τv ({[x]} : aset) : gmap atom value));
	          rewrite elem_of_dom; eexists;
	          apply storeA_restrict_lookup_some_2;
	          [exact Hxlook|set_solver])
		        Heval_ret_restrict) as Hxvy.
	      apply storeA_restrict_lookup_some in Hxvy as [_ Hxvy].
	      change ((τv : StoreT) !! x = Some vy) in Hxvy.
	      pose proof (eq_trans (eq_sym Hxvy) Hxlook) as HeqSome.
	      inversion HeqSome.
	      reflexivity.
Qed.

Lemma expr_result_extension_open_fiber_alias
    e x F (m mx : WfWorldT) (φ : qualifier (V := value)) :
  expr_result_extension_witness e x F ->
  res_extend_by m F mx ->
  expr_total_on_atom_world e m ->
  lc_tm e ->
  wfworld_closed_on (fv_tm e) m ->
  x ∉ lvars_fv (qual_vars φ) ->
  wfworld_closed_on ({[x]} : aset) mx ->
  ∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (mx : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (mx : WorldT)) = mx ->
      forall σ mfib,
        res_fiber_from_projection my
          (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))) σ mfib ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula
              (tm_shift 0 (tret (vfvar x))) (LVBound 0))) ->
        mfib ⊨ formula_msubst_store σ
          (formula_open 0 y
            (expr_result_formula (tm_shift 0 e) (LVBound 0))).
Proof.
  intros HF Hext Htotal Hlc_e Hclosed_e Hxφ Hclosed_x.
  exists (world_dom (mx : WorldT) ∪ fv_tm e ∪ lvars_fv (qual_vars φ)).
  intros y Hy my Hdom_my Hrestrict_my σ mfib Hproj Hret.
  assert (Hy_e : y ∉ fv_tm e) by set_solver.
  assert (Hy_x : y <> x).
  {
    intros ->. apply Hy.
    pose proof (res_extend_by_dom m F mx Hext) as Hmx_dom.
    destruct HF as [_ [_ Hout] _].
    unfold ext_out in Hout.
    rewrite Hmx_dom, Hout. set_solver.
  }
  assert (Hyφ : y ∉ lvars_fv (qual_vars φ)) by set_solver.
  assert (Hopen_dom :
      lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})) ⊆
      lvars_fv (qual_vars φ)).
  {
    intros a Ha.
    rewrite lvars_open_fresh_index in Ha.
    - eapply lvars_fv_mono; [|exact Ha].
      intros v Hv. apply elem_of_difference in Hv as [Hv _]. exact Hv.
    - intros Hbad.
      rewrite lvars_bv_elem in Hbad.
      apply elem_of_difference in Hbad as [_ Hbad].
      apply Hbad. apply elem_of_singleton. reflexivity.
    - intros Hbad. apply Hyφ.
      eapply lvars_fv_mono; [|exact Hbad].
      intros v Hv. apply elem_of_difference in Hv as [Hv _]. exact Hv.
  }
  assert (Hx_proj :
      x ∉ lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))).
  { intros Hbad. apply Hxφ. apply Hopen_dom. exact Hbad. }
  assert (Hy_proj :
      y ∉ lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))).
  { intros Hbad. apply Hyφ. apply Hopen_dom. exact Hbad. }
  assert (Hxσ : x ∉ dom (σ : StoreT)).
  {
    intros Hbad.
    apply res_fiber_from_projection_store_dom_subset in Hproj.
    exact (Hx_proj (Hproj _ Hbad)).
  }
  assert (Hyσ : y ∉ dom (σ : StoreT)).
  {
    intros Hbad.
    apply res_fiber_from_projection_store_dom_subset in Hproj.
    exact (Hy_proj (Hproj _ Hbad)).
  }
  assert (Hy_ret_x : y ∉ fv_tm (tret (vfvar x))).
  { cbn [fv_tm fv_value]. set_solver. }
  rewrite formula_msubst_store_expr_result_formula_shift0 in Hret by
    (try (apply lc_ret_iff_value; apply LC_fvar);
     try exact Hy_ret_x; exact Hyσ).
  cbn [tm_shift] in Hret.
  rewrite formula_msubst_store_expr_result_formula_restrict in Hret by exact Hyσ.
  replace (store_restrict σ (fv_tm (tret (vfvar x))) : StoreT)
    with (∅ : StoreT) in Hret.
  2:{
    apply storeA_map_eq. intros a.
    cbn [fv_tm fv_value].
    rewrite storeA_restrict_lookup.
    destruct (decide (a ∈ {[x]})) as [Ha|Ha]; [|reflexivity].
    apply elem_of_singleton in Ha. subst a.
    destruct (σ !! x) as [vx|] eqn:Hxlook; [|reflexivity].
    exfalso. apply Hxσ.
    change (x ∈ dom (σ : gmap atom value)).
    rewrite elem_of_dom. eauto.
  }
  rewrite formula_msubst_store_empty in Hret by reflexivity.
  rewrite formula_msubst_store_expr_result_formula_shift0 by
    (try exact Hlc_e; try exact Hy_e; exact Hyσ).
  rewrite formula_msubst_store_expr_result_formula_restrict by exact Hyσ.
  eapply expr_result_formula_msubst_alias_ret_fvar.
  - intros Hy_bad.
    apply elem_of_union in Hy_bad as [Hy_bad|Hy_bad].
    + exact (Hy_e Hy_bad).
    + apply elem_of_singleton in Hy_bad. exact (Hy_x Hy_bad).
	  - intros Hbad. apply Hxσ.
	    change (x ∈ dom (store_restrict σ (fv_tm e) : gmap atom value)) in Hbad.
	    rewrite elem_of_dom in Hbad.
	    destruct Hbad as [vx Hlook].
	    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
	    change (x ∈ dom (σ : gmap atom value)).
	    rewrite elem_of_dom. eauto.
	  - intros Hbad. apply Hyσ.
	    change (y ∈ dom (store_restrict σ (fv_tm e) : gmap atom value)) in Hbad.
	    rewrite elem_of_dom in Hbad.
	    destruct Hbad as [vy Hlook].
	    apply storeA_restrict_lookup_some in Hlook as [_ Hlook].
	    change (y ∈ dom (σ : gmap atom value)).
	    rewrite elem_of_dom. eauto.
  - intros τ Hτ.
    pose proof (res_fiber_from_projection_store_source
      my mfib (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})))
      σ τ Hproj Hτ) as Hτ_my.
	    assert (Hτmx : (mx : WorldT)
	        (store_restrict τ (world_dom (mx : WorldT)))).
	    {
	      assert (Hr :
	          (res_restrict my (world_dom (mx : WorldT)) : WorldT)
	            (store_restrict τ (world_dom (mx : WorldT)))).
	      {
	        change ((rawA_restrict (my : WorldT) (world_dom (mx : WorldT)))
	          (store_restrict τ (world_dom (mx : WorldT)))).
	        cbn [rawA_restrict worldA_stores].
	        exists τ. split; [exact Hτ_my|reflexivity].
	      }
	      rewrite Hrestrict_my in Hr. exact Hr.
	    }
	    specialize (Hclosed_x _ Hτmx).
	    rewrite <- (storeA_restrict_twice_subset τ (world_dom (mx : WorldT))
	      ({[x]} : aset)) by
	      (pose proof (res_extend_by_dom m F mx Hext) as Hdom_mx;
	      destruct HF as [_ [_ Hout] _];
	      rewrite Hdom_mx; set_solver).
	    exact Hclosed_x.
  - intros τ Hτ.
    pose proof (res_fiber_from_projection_store_restrict_substore
      my mfib
      (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]})))
      (fv_tm e) σ τ Hproj Hτ) as Hfix.
    replace (dom ((store_restrict (store_restrict σ (fv_tm e)) (fv_tm e)) : StoreT))
      with (dom (store_restrict σ (fv_tm e) : StoreT)).
    2:{
      rewrite storeA_restrict_twice_subset by set_solver.
      reflexivity.
    }
    rewrite storeA_restrict_twice_subset by set_solver.
    exact Hfix.
  - eapply (expr_result_extension_fiber_models_result_slot
      e x F m mx my mfib
      (lvars_fv (lvars_open 0 y (qual_vars φ ∖ {[LVBound 0]}))) σ);
      eauto.
    intros a Ha.
    apply elem_of_intersection in Ha as [HaX Hamy].
    rewrite Hdom_my in Hamy.
    apply elem_of_union in Hamy as [Hamx|Hay].
    * exact Hamx.
    * apply elem_of_singleton in Hay. subst a.
      exfalso. exact (Hy_proj HaX).
  - exact Hret.
Qed.


End TypeDenote.
