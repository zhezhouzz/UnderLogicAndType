(** * ChoiceType.TypeDenotation.ResultExtensionTLet.legacy

    Legacy TLet-specific expression-result bridge proofs.  These are kept out
    of the compiled mainline because current TLet workbenches do not depend on
    them, and the large proof dominates [ResultExtension.v] clean-build time. *)

From CoreLang Require Import Instantiation InstantiationProps LocallyNamelessProps
  OperationalProps.
From ChoiceAlgebra Require Import Resource.
From ChoiceType Require Import TypeDenotation.ResultExtension.

Lemma result_extends_on_fiber_expr_result_tlet_iff
    X e1 e2 x ν (my n : WfWorld) Fx :
  result_extends_on X e1 x my Fx n →
  fv_tm e1 ⊆ X →
  fv_tm e2 ⊆ X →
  lc_tm e1 →
  body_tm e2 →
  ν ∉ X →
  world_dom (my : World) = X ∪ {[ν]} →
  world_closed_on X my →
  expr_total_on e1 my →
  ((∀ σXx Hproj_n,
      expr_result_in_world (store_restrict σXx (X ∪ {[x]}))
        (e2 ^^ x) ν
        (res_fiber_from_projection n (X ∪ {[x]}) σXx Hproj_n)) <->
   (∀ σX Hproj_my,
      expr_result_in_world (store_restrict σX X)
        (tlete e1 e2) ν
        (res_fiber_from_projection my X σX Hproj_my))).
Proof.
  intros Hext Hfv1 Hfv2 Hlc1 Hbody HνX Hdom_my Hclosed Htotal.
  assert (HxX : x ∉ X).
  { exact (result_extends_on_fresh_input _ _ _ _ _ _ Hext). }
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  assert (Hfreshx_my : x ∉ world_dom (my : World)).
  { exact (result_extends_on_fresh _ _ _ _ _ _ Hext). }
  assert (Hxν : x <> ν).
  { rewrite Hdom_my in Hfreshx_my. set_solver. }
  split.
  - intros Hbody_result σX Hproj_my σν. split.
    + intros Hσν_my.
      destruct Hσν_my as [σall [Hfiber_my Hσν]].
      destruct Hfiber_my as [Hσall_my HσallX].
      pose proof (wfworld_store_dom (res_restrict my X) σX Hproj_my)
        as HdomσX.
      simpl in HdomσX.
      assert (HdomσX_exact : dom σX = X).
      {
        transitivity (world_dom (my : World) ∩ X).
        - exact HdomσX.
        - rewrite Hdom_my. set_solver.
      }
      assert (HσX_base : store_restrict σall X = σX).
      {
        rewrite <- HdomσX_exact.
        exact HσallX.
      }
      destruct (proj2 Htotal σall Hσall_my) as [vx Hsteps_fv].
      assert (HstepsX :
        subst_map (store_restrict σX X) e1 →* tret vx).
      {
        rewrite <- (subst_map_restrict_to_fv_from_superset
          e1 X σX Hfv1).
        - replace (store_restrict σX (fv_tm e1))
            with (store_restrict σall (fv_tm e1)).
          + exact Hsteps_fv.
          + rewrite <- HσX_base.
            rewrite store_restrict_twice_subset by exact Hfv1.
            reflexivity.
        - rewrite <- HσX_base.
          rewrite store_restrict_twice_subset by reflexivity.
          exact (proj1 (Hclosed σall Hσall_my)).
      }
      assert (Hclosedρ : closed_env (store_restrict σX X)).
      {
        rewrite <- HσX_base.
        rewrite store_restrict_twice_subset by reflexivity.
        exact (proj1 (Hclosed σall Hσall_my)).
      }
      assert (Hlcρ : lc_env (store_restrict σX X)).
      {
        rewrite <- HσX_base.
        rewrite store_restrict_twice_subset by reflexivity.
        exact (proj2 (Hclosed σall Hσall_my)).
      }
      assert (Hvx : stale vx = ∅ ∧ is_lc vx).
      {
        eapply (steps_closed_result_of_restrict_world X e1 my σX vx).
        - set_solver.
        - exact Hfv1.
        - exact Hlc1.
        - exact Hclosed.
        - exact Hproj_my.
        - exact HstepsX.
      }
      destruct Hvx as [Hvx_closed Hvx_lc].
      assert (Hbodyρ : body_tm (subst_map (store_restrict σX X) e2)).
      {
        eapply body_tm_msubst_restrict_world; eauto.
      }
      destruct (result_extends_on_fiber_projection_member
        X e1 x my n Fx σall vx Hext Hfv1 Hσall_my Hsteps_fv)
        as [Hproj_n Hfiber_n].
      set (σXx := store_restrict (<[x := vx]> σall) (X ∪ {[x]})).
      pose proof (Hbody_result σXx Hproj_n) as Hbody_world.
      assert (Hσν_n :
        (res_restrict
          (res_fiber_from_projection n (X ∪ {[x]}) σXx Hproj_n)
          {[ν]} : World) σν).
      {
        exists (<[x := vx]> σall). split; [exact Hfiber_n |].
        rewrite store_restrict_insert_singleton_ne by exact Hxν.
        exact Hσν.
      }
      pose proof (expr_result_in_world_sound
        (store_restrict σXx (X ∪ {[x]})) (e2 ^^ x) ν
        (res_fiber_from_projection n (X ∪ {[x]}) σXx Hproj_n)
        σν Hbody_world Hσν_n) as Hbody_store.
      assert (Hρx :
        store_restrict σXx (X ∪ {[x]}) =
        <[x := vx]> σX).
      {
        subst σXx.
        rewrite store_restrict_idemp_eq.
        - rewrite store_restrict_insert_fresh_union.
          + rewrite HσX_base.
            reflexivity.
          + apply store_lookup_none_of_dom with (X := world_dom (my : World)).
            * apply wfworld_store_dom. exact Hσall_my.
            * exact Hfreshx_my.
          + exact HxX.
        - rewrite store_restrict_dom.
          rewrite (dom_insert_L (M:=gmap atom) (A:=value) σall x vx).
          rewrite (wfworld_store_dom my σall Hσall_my), Hdom_my.
          set_solver.
      }
      rewrite Hρx in Hbody_store.
      replace (store_restrict σX X) with σX
        by (symmetry; apply store_restrict_idemp_eq; exact HdomσX_exact).
      replace (store_restrict σX X) with σX in HstepsX
        by (symmetry; apply store_restrict_idemp_eq; exact HdomσX_exact).
      replace (store_restrict σX X) with σX in Hclosedρ
        by (symmetry; apply store_restrict_idemp_eq; exact HdomσX_exact).
      replace (store_restrict σX X) with σX in Hlcρ
        by (symmetry; apply store_restrict_idemp_eq; exact HdomσX_exact).
      replace (store_restrict σX X) with σX in Hbodyρ
        by (symmetry; apply store_restrict_idemp_eq; exact HdomσX_exact).
      eapply expr_result_store_body_open_to_tlete.
      * exact Hclosedρ.
      * exact Hlcρ.
      * exact Hbodyρ.
      * apply not_elem_of_union. split.
        -- intros Hxdom.
           apply HxX.
           rewrite <- HdomσX_exact.
           exact Hxdom.
        -- exact Hxe2.
      * exact Hvx_closed.
      * exact Hvx_lc.
      * exact HstepsX.
      * exact Hbody_store.
    + intros Hstore_tlet.
      pose proof Hproj_my as Hproj_my0.
      destruct Hproj_my as [σall [Hσall_my HσallX]].
      pose proof (wfworld_store_dom (res_restrict my X) σX Hproj_my0)
        as HdomσX.
      simpl in HdomσX.
      assert (HdomσX_exact : dom σX = X).
      {
        transitivity (world_dom (my : World) ∩ X).
        - exact HdomσX.
        - rewrite Hdom_my. set_solver.
      }
      assert (HσX_base : store_restrict σall X = σX).
      {
        exact HσallX.
      }
      assert (Hclosedρ : closed_env (store_restrict σX X)).
      {
        rewrite <- HσX_base.
        rewrite store_restrict_twice_subset by reflexivity.
        exact (proj1 (Hclosed σall Hσall_my)).
      }
      assert (Hlcρ : lc_env (store_restrict σX X)).
      {
        rewrite <- HσX_base.
        rewrite store_restrict_twice_subset by reflexivity.
        exact (proj2 (Hclosed σall Hσall_my)).
      }
      assert (Hresult_closed :
        ∀ vx, subst_map (store_restrict σX X) e1 →* tret vx ->
          stale vx = ∅ ∧ is_lc vx).
      {
        intros vx HstepsX.
        eapply (steps_closed_result_of_restrict_world X e1 my σX vx).
        - set_solver.
        - exact Hfv1.
        - exact Hlc1.
        - exact Hclosed.
        - exact Hproj_my0.
        - exact HstepsX.
      }
      destruct (expr_result_store_tlete_to_body_open_atom
        (store_restrict σX X) e1 e2 x ν σν
        Hclosedρ Hlcρ ltac:(
          apply not_elem_of_union; split;
          [intros Hxdom; apply elem_of_dom in Hxdom as [v Hlookup];
           apply store_restrict_lookup_some in Hlookup as [Hx_in _];
           exact (HxX Hx_in)
          | exact Hxe2])
        Hresult_closed Hstore_tlet)
        as [vx [HstepsX Hbody_store]].
      assert (Hsteps_fv :
        subst_map (store_restrict σall (fv_tm e1)) e1 →* tret vx).
      {
        rewrite (subst_map_restrict_to_fv_from_superset e1 X σall Hfv1
          (proj1 (Hclosed σall Hσall_my))).
        rewrite HσX_base.
        replace (store_restrict σX X) with σX in HstepsX
          by (symmetry; apply store_restrict_idemp_eq; exact HdomσX_exact).
        exact HstepsX.
      }
      destruct (result_extends_on_fiber_projection_member
        X e1 x my n Fx σall vx Hext Hfv1 Hσall_my Hsteps_fv)
        as [Hproj_n Hfiber_n].
      set (σXx := store_restrict (<[x := vx]> σall) (X ∪ {[x]})).
      pose proof (Hbody_result σXx Hproj_n) as Hbody_world.
      assert (Hρx :
        store_restrict σXx (X ∪ {[x]}) =
        <[x := vx]> (store_restrict σX X)).
      {
        subst σXx.
        rewrite store_restrict_idemp_eq.
        - rewrite store_restrict_insert_fresh_union.
          + rewrite HσX_base.
            rewrite store_restrict_idemp_eq by exact HdomσX_exact.
            reflexivity.
          + apply store_lookup_none_of_dom with (X := world_dom (my : World)).
            * apply wfworld_store_dom. exact Hσall_my.
            * exact Hfreshx_my.
          + exact HxX.
        - rewrite store_restrict_dom.
          rewrite (dom_insert_L (M:=gmap atom) (A:=value) σall x vx).
          rewrite (wfworld_store_dom my σall Hσall_my), Hdom_my.
          set_solver.
      }
      assert (Hbody_store_n :
        expr_result_store ν
          (subst_map (store_restrict σXx (X ∪ {[x]})) (e2 ^^ x)) σν).
      {
        rewrite Hρx.
        exact Hbody_store.
      }
      apply (proj2 (Hbody_world σν)) in Hbody_store_n.
      destruct Hbody_store_n as [σbody [Hfiber_body Hσbodyν]].
      destruct (result_extends_on_fiber_projection_elim
        X e1 x my n Fx σXx Hproj_n σbody Hext Hfv1 Htotal Hfiber_body)
        as [σbase [vx' [Hσbase [Hsteps_base [Hσbody_eq HσbaseX]]]]].
      subst σbody.
      exists σbase. split.
      * eapply res_fiber_from_projection_member; [exact Hσbase |].
        rewrite HσbaseX.
        subst σXx.
        rewrite store_restrict_twice_subset by set_solver.
        rewrite store_restrict_insert_notin by exact HxX.
        rewrite HσX_base.
        reflexivity.
      * rewrite store_restrict_insert_singleton_ne in Hσbodyν by exact Hxν.
        exact Hσbodyν.
  - intros Htlet_result σXx Hproj_n σν. split.
    + intros Hσν_n.
      destruct Hσν_n as [σbody [Hfiber_n Hσbodyν]].
      pose proof Hfiber_n as Hfiber_n_proj.
      destruct Hfiber_n_proj as [_ Hσbody_proj].
      destruct (result_extends_on_fiber_projection_elim
        X e1 x my n Fx σXx Hproj_n σbody Hext Hfv1 Htotal Hfiber_n)
        as [σbase [vx [Hσbase [Hsteps_fv [Hσbody_eq HσbaseX]]]]].
      subst σbody.
      pose proof (wfworld_store_dom (res_restrict n (X ∪ {[x]}))
        σXx Hproj_n) as HdomσXx.
      simpl in HdomσXx.
      assert (HdomσXx_exact : dom σXx = X ∪ {[x]}).
      {
        transitivity (world_dom (n : World) ∩ (X ∪ {[x]})).
        - exact HdomσXx.
        - rewrite (result_extends_on_dom _ _ _ _ _ _ Hext), Hdom_my.
          set_solver.
      }
      set (σX := store_restrict σXx X).
      assert (HσX_base : store_restrict σbase X = σX).
      { subst σX. exact HσbaseX. }
      assert (Hproj_my : (res_restrict my X : World) σX).
      { exists σbase. split; [exact Hσbase | exact HσX_base]. }
      pose proof (Htlet_result σX Hproj_my) as Htlet_world.
      assert (Hσν_my :
        (res_restrict (res_fiber_from_projection my X σX Hproj_my)
          {[ν]} : World) σν).
      {
        exists σbase. split.
        - eapply res_fiber_from_projection_member; [exact Hσbase | exact HσX_base].
        - rewrite store_restrict_insert_singleton_ne in Hσbodyν by exact Hxν.
          exact Hσbodyν.
      }
      pose proof (expr_result_in_world_sound
        (store_restrict σX X) (tlete e1 e2) ν
        (res_fiber_from_projection my X σX Hproj_my)
        σν Htlet_world Hσν_my) as Hstore_tlet.
      assert (HdomσX_exact : dom σX = X).
      {
        subst σX.
        rewrite store_restrict_dom, HdomσXx_exact.
        set_solver.
      }
      assert (Hclosedρ : closed_env (store_restrict σX X)).
      {
        replace (store_restrict σX X) with (store_restrict σbase X).
        - exact (proj1 (Hclosed σbase Hσbase)).
        - rewrite HσX_base.
          symmetry. apply store_restrict_idemp_eq. exact HdomσX_exact.
      }
      assert (Hlcρ : lc_env (store_restrict σX X)).
      {
        replace (store_restrict σX X) with (store_restrict σbase X).
        - exact (proj2 (Hclosed σbase Hσbase)).
        - rewrite HσX_base.
          symmetry. apply store_restrict_idemp_eq. exact HdomσX_exact.
      }
      assert (Hresult_closed :
        ∀ vx', subst_map (store_restrict σX X) e1 →* tret vx' ->
          stale vx' = ∅ ∧ is_lc vx').
      {
        intros vx' HstepsX.
        eapply (steps_closed_result_of_restrict_world X e1 my σX vx').
        - set_solver.
        - exact Hfv1.
        - exact Hlc1.
        - exact Hclosed.
        - exact Hproj_my.
        - exact HstepsX.
      }
      destruct (expr_result_store_tlete_to_body_open_atom
        (store_restrict σX X) e1 e2 x ν σν
        Hclosedρ Hlcρ ltac:(
          apply not_elem_of_union; split;
          [intros Hxdom; apply elem_of_dom in Hxdom as [v Hlookup];
           apply store_restrict_lookup_some in Hlookup as [Hx_in _];
           exact (HxX Hx_in)
          | exact Hxe2])
        Hresult_closed Hstore_tlet)
        as [vx' [HstepsX' Hbody_store]].
      assert (HstepsX :
        subst_map (store_restrict σX X) e1 →* tret vx).
      {
        rewrite <- (subst_map_restrict_to_fv_from_superset
          e1 X σX Hfv1).
        - replace (store_restrict σX (fv_tm e1))
            with (store_restrict σbase (fv_tm e1)).
          + exact Hsteps_fv.
          + rewrite <- HσX_base.
            rewrite store_restrict_twice_subset by exact Hfv1.
            reflexivity.
        - rewrite <- HσX_base.
          rewrite store_restrict_twice_subset by reflexivity.
          exact (proj1 (Hclosed σbase Hσbase)).
      }
      assert (Hvx' : vx' = vx) by (eapply steps_result_unique; eauto).
      subst vx'.
      assert (Hxσbase : σbase !! x = None).
      {
        eapply store_lookup_none_of_dom.
        - apply wfworld_store_dom. exact Hσbase.
        - exact Hfreshx_my.
      }
      assert (Hρx :
        store_restrict σXx (X ∪ {[x]}) =
        <[x := vx]> (store_restrict σX X)).
      {
        assert (Hσbody_proj_X :
          store_restrict (<[x := vx]> σbase) (X ∪ {[x]}) = σXx).
        {
          transitivity (store_restrict (<[x := vx]> σbase) (dom σXx)).
          - rewrite HdomσXx_exact. reflexivity.
          - exact Hσbody_proj.
        }
        rewrite store_restrict_idemp_eq by exact HdomσXx_exact.
        rewrite <- Hσbody_proj_X.
        rewrite store_restrict_insert_fresh_union by eauto.
        rewrite HσX_base.
        rewrite store_restrict_idemp_eq by exact HdomσX_exact.
        reflexivity.
      }
      rewrite Hρx.
      exact Hbody_store.
    + intros Hstore_body.
      destruct Hproj_n as [σbase_x [Hσbase_x_n Hσbase_x_proj]].
      destruct (result_extends_on_elim X e1 x my n Fx σbase_x
        Hext Hfv1 (proj2 Htotal) Hσbase_x_n)
        as [σbase [vx [Hσbase [Hsteps_fv Hσbase_x_eq]]]].
      subst σbase_x.
      pose proof (wfworld_store_dom (res_restrict n (X ∪ {[x]}))
        σXx (ex_intro _ (<[x:=vx]> σbase)
          (conj Hσbase_x_n Hσbase_x_proj))) as HdomσXx.
      simpl in HdomσXx.
      assert (HdomσXx_exact : dom σXx = X ∪ {[x]}).
      {
        transitivity (world_dom (n : World) ∩ (X ∪ {[x]})).
        - exact HdomσXx.
        - rewrite (result_extends_on_dom _ _ _ _ _ _ Hext), Hdom_my.
          set_solver.
      }
      set (σX := store_restrict σXx X).
      assert (HσX_base : store_restrict σbase X = σX).
      {
        subst σX.
        rewrite <- Hσbase_x_proj.
        rewrite store_restrict_twice_subset by set_solver.
        rewrite store_restrict_insert_notin by exact HxX.
        reflexivity.
      }
      assert (HdomσX_exact : dom σX = X).
      {
        subst σX.
        rewrite store_restrict_dom, HdomσXx_exact.
        set_solver.
      }
      assert (Hproj_my : (res_restrict my X : World) σX).
      { exists σbase. split; [exact Hσbase | exact HσX_base]. }
      pose proof (Htlet_result σX Hproj_my) as Htlet_world.
      assert (Hclosedρ : closed_env (store_restrict σX X)).
      {
        replace (store_restrict σX X) with (store_restrict σbase X).
        - exact (proj1 (Hclosed σbase Hσbase)).
        - rewrite HσX_base.
          symmetry. apply store_restrict_idemp_eq. exact HdomσX_exact.
      }
      assert (Hlcρ : lc_env (store_restrict σX X)).
      {
        replace (store_restrict σX X) with (store_restrict σbase X).
        - exact (proj2 (Hclosed σbase Hσbase)).
        - rewrite HσX_base.
          symmetry. apply store_restrict_idemp_eq. exact HdomσX_exact.
      }
      assert (HstepsX :
        subst_map (store_restrict σX X) e1 →* tret vx).
      {
        rewrite <- (subst_map_restrict_to_fv_from_superset
          e1 X σX Hfv1).
        - replace (store_restrict σX (fv_tm e1))
            with (store_restrict σbase (fv_tm e1)).
          + exact Hsteps_fv.
          + rewrite <- HσX_base.
            rewrite store_restrict_twice_subset by exact Hfv1.
            reflexivity.
        - rewrite <- HσX_base.
          rewrite store_restrict_twice_subset by reflexivity.
          exact (proj1 (Hclosed σbase Hσbase)).
      }
      assert (Hvx : stale vx = ∅ ∧ is_lc vx).
      {
        eapply (steps_closed_result_of_restrict_world X e1 my σX vx).
        - set_solver.
        - exact Hfv1.
        - exact Hlc1.
        - exact Hclosed.
        - exact Hproj_my.
        - exact HstepsX.
      }
      destruct Hvx as [Hvx_closed Hvx_lc].
      assert (Hbodyρ : body_tm (subst_map (store_restrict σX X) e2)).
      { eapply body_tm_msubst_restrict_world; eauto. }
      assert (Hxσbase : σbase !! x = None).
      {
        eapply store_lookup_none_of_dom.
        - apply wfworld_store_dom. exact Hσbase.
        - exact Hfreshx_my.
      }
      assert (Hρx :
        store_restrict σXx (X ∪ {[x]}) =
        <[x := vx]> (store_restrict σX X)).
      {
        rewrite store_restrict_idemp_eq by exact HdomσXx_exact.
        rewrite <- Hσbase_x_proj.
        rewrite store_restrict_insert_fresh_union by eauto.
        rewrite HσX_base.
        rewrite store_restrict_idemp_eq by exact HdomσX_exact.
        reflexivity.
      }
      assert (Hstore_body_base :
        expr_result_store ν
          (subst_map (<[x := vx]> (store_restrict σX X)) (e2 ^^ x)) σν).
      {
        rewrite <- Hρx.
        exact Hstore_body.
      }
      assert (Hstore_tlet :
        expr_result_store ν (subst_map (store_restrict σX X)
          (tlete e1 e2)) σν).
      {
        eapply expr_result_store_body_open_to_tlete.
        - exact Hclosedρ.
        - exact Hlcρ.
        - exact Hbodyρ.
        - apply not_elem_of_union. split.
          + intros Hxdom.
            apply elem_of_dom in Hxdom as [v Hlookup].
            apply store_restrict_lookup_some in Hlookup as [Hx_in _].
            exact (HxX Hx_in).
          + exact Hxe2.
        - exact Hvx_closed.
        - exact Hvx_lc.
        - exact HstepsX.
        - exact Hstore_body_base.
      }
      apply (proj2 (Htlet_world σν)) in Hstore_tlet.
      destruct Hstore_tlet as [σmy [Hfiber_my Hσmyν]].
      destruct Hfiber_my as [Hσmy_my HσmyXdom].
      assert (HσmyX : store_restrict σmy X = σX).
      {
        rewrite <- HdomσX_exact.
        exact HσmyXdom.
      }
      destruct (proj2 Htotal σmy Hσmy_my) as [vx' Hsteps_my_fv].
      assert (Hsteps_my_X :
        subst_map (store_restrict σX X) e1 →* tret vx').
      {
        rewrite <- (subst_map_restrict_to_fv_from_superset
          e1 X σX Hfv1).
        - replace (store_restrict σX (fv_tm e1))
            with (store_restrict σmy (fv_tm e1)).
          + exact Hsteps_my_fv.
          + rewrite <- HσmyX.
            rewrite store_restrict_twice_subset by exact Hfv1.
            reflexivity.
        - rewrite <- HσmyX.
          rewrite store_restrict_twice_subset by reflexivity.
          exact (proj1 (Hclosed σmy Hσmy_my)).
      }
      assert (Hvx' : vx' = vx) by (eapply steps_result_unique; eauto).
      subst vx'.
      assert (Hσmy_x : σmy !! x = None).
      {
        eapply store_lookup_none_of_dom.
        - apply wfworld_store_dom. exact Hσmy_my.
        - exact Hfreshx_my.
      }
      assert (Hn_my : (n : World) (<[x := vx]> σmy)).
      { eapply result_extends_on_member; eauto. }
      assert (HσXx_insert : σXx = <[x := vx]> σX).
      {
        rewrite <- (store_restrict_idemp_eq σXx (X ∪ {[x]})
          HdomσXx_exact).
        rewrite Hρx.
        rewrite store_restrict_idemp_eq by exact HdomσX_exact.
        reflexivity.
      }
      exists (<[x := vx]> σmy). split.
      * eapply res_fiber_from_projection_member; [exact Hn_my |].
        rewrite store_restrict_insert_fresh_union by eauto.
        rewrite HσmyX.
        symmetry. exact HσXx_insert.
      * rewrite store_restrict_insert_singleton_ne by exact Hxν.
        exact Hσmyν.
Qed.

Lemma FExprResultAt_tlet_result_extension_iff
    X e1 e2 x ν (my n : WfWorld) Fx :
  result_extends_on X e1 x my Fx n →
  fv_tm e1 ⊆ X →
  fv_tm e2 ⊆ X →
  lc_tm (tlete e1 e2) →
  body_tm e2 →
  ν ∉ X →
  world_dom (my : World) = X ∪ {[ν]} →
  world_closed_on X my →
  expr_total_on e1 my →
  (n ⊨ FExprResultAt (X ∪ {[x]}) (e2 ^^ x) ν <->
   my ⊨ FExprResultAt X (tlete e1 e2) ν).
Proof.
  intros Hext Hfv1 Hfv2 Hlc_tlet Hbody HνX Hdom_my Hclosed Htotal.
  pose proof (result_extends_on_dom _ _ _ _ _ _ Hext) as Hdom_n.
  pose proof (result_extends_on_fresh _ _ _ _ _ _ Hext) as Hfreshx_my.
  assert (Hlc_body_open : lc_tm (e2 ^^ x)).
  {
    apply body_open_tm; [exact Hbody | constructor].
  }
  assert (HνXx : ν ∉ X ∪ {[x]}).
  {
    rewrite Hdom_my in Hfreshx_my. set_solver.
  }
  assert (Hdom_n_body :
    world_dom (n : World) = (X ∪ {[x]}) ∪ {[ν]}).
  {
    rewrite Hdom_n, Hdom_my. set_solver.
  }
  pose proof (result_extends_on_fiber_expr_result_tlet_iff
    X e1 e2 x ν my n Fx Hext Hfv1 Hfv2
    (proj1 (proj1 (lc_lete_iff_body e1 e2) Hlc_tlet))
    Hbody HνX Hdom_my Hclosed Htotal)
    as Hfib.
  split.
  - intros Hn.
    eapply FExprResultAt_intro_from_expr_result_in_world; eauto.
    intros σX Hproj_my.
    apply (proj1 Hfib).
    intros σXx Hproj_n.
    eapply FExprResultAt_fiber_expr_result_in_world; eauto.
  - intros Hmy.
    eapply FExprResultAt_intro_from_expr_result_in_world; eauto.
    intros σXx Hproj_n.
    apply (proj2 Hfib).
    intros σX Hproj_my.
    eapply FExprResultAt_fiber_expr_result_in_world; eauto.
Qed.
