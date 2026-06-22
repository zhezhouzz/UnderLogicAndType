(** * Denotation.TypePersist

    Semantic support lemmas for the type-level persistency modality. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivFiberBaseResult TypeEquiv.

Section TypePersist.

Lemma ty_denote_gas_persist_open_result
    gas (Σ : lty_env) τ e y (m my : WfWorldT) :
  m ⊨ ty_denote_gas (S gas) Σ (CTPersist τ) e ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 y
    (expr_result_formula_at
      (lvars_shift_from 0
        (dom (relevant_env Σ (CTPersist τ) e)))
      (tm_shift 0 e) (LVBound 0)) ->
  my ⊨ formula_open 0 y
    (FPersist
      (ty_denote_gas gas
        (typed_lty_env_bind
          (relevant_env Σ (CTPersist τ) e)
          (erase_ty (CTPersist τ)))
        (cty_shift 0 τ) (tret (vbvar 0)))).
Proof.
  intros Hden Hy Hdom Hrestrict Hresult.
  cbn [ty_denote_gas] in Hden.
  rewrite res_models_and_iff in Hden.
  destruct Hden as [_ Hbody].
  eapply result_first_forall_impl_open_elim; eauto.
Qed.

Lemma expr_result_formula_at_ret_fvar_lookup_eq
    D x y (m : WfWorldT) σ :
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  store_closed (store_restrict σ ({[x]} : aset)) ->
  x ∈ dom (store_restrict σ ({[x]} : aset) : StoreT) ->
  m ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  (m : WorldT) σ ->
  σ !! y = σ !! x.
Proof.
  intros HD HyD Hclosed Hxdom Hres Hσ.
  pose proof (expr_result_formula_at_models_elim
    D (tret (vfvar x)) y m HD HyD Hres σ Hσ) as Hstore.
  destruct Hstore as [_ [v [Hy Heval]]].
  assert (Heval_restrict :
      tm_eval_in_store (store_restrict σ ({[x]} : aset))
        (tret (vfvar x)) v).
  {
    apply (proj2 (tm_eval_in_store_restrict_fv_subset
      σ (tret (vfvar x)) v ({[x]} : aset)
      ltac:(cbn [fv_tm fv_value]; set_solver))).
    exact Heval.
  }
  pose proof (tm_eval_in_store_ret_fvar_inv
    (store_restrict σ ({[x]} : aset)) x v Hclosed Hxdom Heval_restrict)
    as Hx.
  rewrite lstore_lift_free_lookup_free in Hy.
  apply storeA_restrict_lookup_some in Hx as [_ Hx].
  transitivity (Some v); [exact Hy|symmetry; exact Hx].
Qed.

Lemma expr_result_formula_at_ret_fvar_flip
    Dsrc Dtgt x y (m : WfWorldT) :
  tm_lvars (tret (vfvar x)) ⊆ Dsrc ->
  LVFree y ∉ Dsrc ->
  lc_lvars Dtgt ->
  tm_lvars (tret (vfvar y)) ⊆ Dtgt ->
  LVFree x ∉ Dtgt ->
  lvars_fv Dtgt ∪ {[x; y]} ⊆ world_dom (m : WorldT) ->
  wfworld_closed_on ({[x]} : aset) m ->
  wfworld_closed_on ({[y]} : aset) m ->
  m ⊨ expr_result_formula_at Dsrc (tret (vfvar x)) (LVFree y) ->
  m ⊨ expr_result_formula_at Dtgt (tret (vfvar y)) (LVFree x).
Proof.
  intros HsrcD HyD HlcDtgt HtgtD HxD Hscope_dom Hclosed_x Hclosed_y Hres.
  eapply expr_result_formula_at_intro.
  - exact HlcDtgt.
  - exact HtgtD.
  - exact HxD.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_expr_result_formula_at.
    cbn [tm_lvars tm_lvars_at value_lvars_at lvar_value_keys].
    rewrite lvars_fv_union, !lvars_fv_singleton_free.
    intros a Ha. apply Hscope_dom.
    set_solver.
  - intros σ Hσ.
    pose proof (expr_result_formula_at_ret_fvar_lookup_eq
      Dsrc x y m σ HsrcD HyD (Hclosed_x σ Hσ) ltac:(
        change (x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value));
        rewrite storeA_restrict_dom;
        rewrite (wfworld_store_dom m σ Hσ);
        set_solver) Hres Hσ) as Hxy.
    unfold expr_result_at_store.
    split.
    + intros Hbad. apply HxD. apply HtgtD.
      exact Hbad.
    + destruct (σ !! y) as [v|] eqn:Hylookup.
      * exists v. split.
        -- rewrite lstore_lift_free_lookup_free.
           rewrite <- Hxy. reflexivity.
        -- apply (proj1 (tm_eval_in_store_restrict_fv_subset
             σ (tret (vfvar y)) v ({[y]} : aset)
             ltac:(cbn [fv_tm fv_value]; set_solver))).
           apply tm_eval_in_store_ret_fvar_lookup.
           ++ exact (Hclosed_y σ Hσ).
           ++ change ((storeA_restrict σ ({[y]} : aset) : gmap atom value)
                !! y = Some v).
              apply storeA_restrict_lookup_some_2; [exact Hylookup|set_solver].
      * exfalso.
        apply not_elem_of_dom in Hylookup.
        apply Hylookup.
        rewrite (wfworld_store_dom m σ Hσ).
        set_solver.
  - intros σ v Hσ Heval.
    exists σ. split; [exact Hσ|]. split; [reflexivity|].
    pose proof (expr_result_formula_at_ret_fvar_lookup_eq
      Dsrc x y m σ HsrcD HyD (Hclosed_x σ Hσ) ltac:(
        change (x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom value));
        rewrite storeA_restrict_dom;
        rewrite (wfworld_store_dom m σ Hσ);
        set_solver) Hres Hσ) as Hxy.
    pose proof (tm_eval_in_store_ret_fvar_inv
      (store_restrict σ ({[y]} : aset)) y v) as Hinv.
    assert (Hclosed_yσ : store_closed (store_restrict σ ({[y]} : aset))).
    { exact (Hclosed_y σ Hσ). }
    assert (Hydom :
        y ∈ dom (store_restrict σ ({[y]} : aset) : StoreT)).
    {
      change (y ∈ dom (storeA_restrict σ ({[y]} : aset) : gmap atom value)).
      rewrite storeA_restrict_dom.
      rewrite (wfworld_store_dom m σ Hσ).
      set_solver.
    }
    change (tm_eval_in_store (store_restrict σ ({[y]} : aset))
      (tret (vfvar y)) v) in Heval.
    specialize (Hinv Hclosed_yσ Hydom Heval).
    apply storeA_restrict_lookup_some in Hinv as [_ Hlookup_y].
    rewrite <- Hxy. exact Hlookup_y.
Qed.

Lemma res_restrict_singleton_pullback_ret_fvar_result
    A D x y (m my : WfWorldT) σy :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ A ->
  y ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict my (A ∪ {[y]}) =
    (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT) ->
  exists σx : StoreT,
    dom (σx : StoreT) = A ∪ {[x]} /\
    res_restrict m (A ∪ {[x]}) =
      (exist _ (singleton_world σx) (wf_singleton_world σx) : WfWorldT).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase
    Hsingle_y.
  destruct (wfA_ne _ (worldA_wf m)) as [σ0 Hσ0].
  set (σx := store_restrict σ0 (A ∪ {[x]}) : StoreT).
  exists σx.
  assert (Hdomσx : dom (σx : StoreT) = A ∪ {[x]}).
  {
    subst σx.
    change (dom (storeA_restrict σ0 (A ∪ {[x]}) : gmap atom value) =
      A ∪ {[x]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m σ0 Hσ0).
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσx|].
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict m (A ∪ {[x]}) : WorldT) =
      dom (σx : StoreT)).
    rewrite res_restrict_dom, Hdomσx.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σm [Hσm Hσeq]]. subst σ.
      rewrite <- Hbase in Hσm.
      destruct Hσm as [σmy [Hσmy Hσmy_base]].
      assert (Hσ0proj : (res_restrict my (world_dom (m : WorldT)) : WorldT) σ0).
      { rewrite Hbase. exact Hσ0. }
      destruct Hσ0proj as [σ0my [Hσ0my Hσ0my_base]].
      pose proof (res_restrict_singleton_store_eq
        my (A ∪ {[y]}) σy σmy Hsingle_y Hσmy) as Hσmy_y.
      pose proof (res_restrict_singleton_store_eq
        my (A ∪ {[y]}) σy σ0my Hsingle_y Hσ0my) as Hσ0my_y.
      assert (Hxy_my : σmy !! y = σmy !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σmy);
          [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
        change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
        set_solver.
      }
      assert (Hxy_0 : σ0my !! y = σ0my !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0my);
          [exact HD|exact HyD|exact (Hclosed_x σ0my Hσ0my)| |exact Hres|exact Hσ0my].
        change (x ∈ dom (storeA_restrict σ0my ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σ0my Hσ0my), Hdom_my.
        set_solver.
      }
      subst σx.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[x]})) as [Ha|Ha].
      * destruct (decide (a = x)) as [->|Hax].
        -- assert (Hbase_my_x : σmy !! x = σm !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσmy_base.
           }
           assert (Hbase_0_x : σ0my !! x = σ0 !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσ0my_base.
           }
           assert (Hy_my : σmy !! y = σy !! y).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσmy_y.
           }
           assert (Hy_0 : σ0my !! y = σy !! y).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσ0my_y.
           }
           change (σm !! x = σ0 !! x).
           rewrite <- Hbase_my_x, <- Hbase_0_x.
           rewrite <- Hxy_my, <- Hxy_0.
           congruence.
        -- assert (HaA : a ∈ A) by set_solver.
           assert (HaDom : a ∈ world_dom (m : WorldT)) by set_solver.
           assert (Hbase_my_a : σmy !! a = σm !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσmy_base.
           }
           assert (Hbase_0_a : σ0my !! a = σ0 !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσ0my_base.
           }
           assert (Hy_my_a : σmy !! a = σy !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσmy_y.
           }
           assert (Hy_0_a : σ0my !! a = σy !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσ0my_y.
           }
           change (σm !! a = σ0 !! a).
           rewrite <- Hbase_my_a, <- Hbase_0_a.
           congruence.
      * reflexivity.
    + intros Hσ.
      unfold singleton_world in Hσ.
      cbn [raw_world raw_worldA] in Hσ.
      change (σ = store_restrict σ0 (A ∪ {[x]})) in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

Lemma res_restrict_singleton_push_ret_fvar_result
    A D x y (m my : WfWorldT) σx :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  x ∉ A ->
  y ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
  LVFree y ∉ D ->
  my ⊨ expr_result_formula_at D (tret (vfvar x)) (LVFree y) ->
  wfworld_closed_on ({[x]} : aset) my ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict m (A ∪ {[x]}) =
    (exist _ (singleton_world σx) (wf_singleton_world σx) : WfWorldT) ->
  exists σy : StoreT,
    dom (σy : StoreT) = A ∪ {[y]} /\
    res_restrict my (A ∪ {[y]}) =
      (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorldT).
Proof.
  intros HAm Hxm Hym HxA HyA HD HyD Hres Hclosed_x Hdom_my Hbase
    Hsingle_x.
  destruct (wfA_ne _ (worldA_wf my)) as [σ0 Hσ0].
  set (σy := store_restrict σ0 (A ∪ {[y]}) : StoreT).
  exists σy.
  assert (Hdomσy : dom (σy : StoreT) = A ∪ {[y]}).
  {
    subst σy.
    change (dom (storeA_restrict σ0 (A ∪ {[y]}) : gmap atom value) =
      A ∪ {[y]}).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
    apply set_eq. intros a. set_solver.
  }
  split; [exact Hdomσy|].
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict my (A ∪ {[y]}) : WorldT) =
      dom (σy : StoreT)).
    rewrite res_restrict_dom, Hdomσy.
    apply set_eq. intros a. set_solver.
  - intros σ. split.
    + intros Hσproj.
      destruct Hσproj as [σmy [Hσmy Hσeq]]. subst σ.
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        rewrite <- Hbase.
        subst σm. exists σmy. split; [exact Hσmy|reflexivity].
      }
      assert (Hσm_base : store_restrict σmy (world_dom (m : WorldT)) = σm)
        by (subst σm; reflexivity).
      assert (Hσ0_base : (res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict σ0 (world_dom (m : WorldT)))).
      {
        exists σ0. split; [exact Hσ0|reflexivity].
      }
      rewrite Hbase in Hσ0_base.
      pose proof (res_restrict_singleton_store_eq
        m (A ∪ {[x]}) σx σm Hsingle_x Hσm) as Hσm_x.
      pose proof (res_restrict_singleton_store_eq
        m (A ∪ {[x]}) σx
        (store_restrict σ0 (world_dom (m : WorldT)))
        Hsingle_x Hσ0_base) as Hσ0_x.
      assert (Hxy_my : σmy !! y = σmy !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σmy);
          [exact HD|exact HyD|exact (Hclosed_x σmy Hσmy)| |exact Hres|exact Hσmy].
        change (x ∈ dom (storeA_restrict σmy ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σmy Hσmy), Hdom_my.
        set_solver.
      }
      assert (Hxy_0 : σ0 !! y = σ0 !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0);
          [exact HD|exact HyD|exact (Hclosed_x σ0 Hσ0)| |exact Hres|exact Hσ0].
        change (x ∈ dom (storeA_restrict σ0 ({[x]} : aset) : gmap atom value)).
        rewrite storeA_restrict_dom.
        rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
        set_solver.
      }
      subst σy.
      apply storeA_map_eq. intros a.
      rewrite !storeA_restrict_lookup.
      destruct (decide (a ∈ A ∪ {[y]})) as [Ha|Ha].
      * destruct (decide (a = y)) as [->|Hay].
        -- assert (Hmy_x : σmy !! x = σm !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact Hxm.
             - exact Hσm_base.
           }
           assert (H0_x :
               σ0 !! x = store_restrict σ0 (world_dom (m : WorldT)) !! x).
           {
             destruct (σ0 !! x) as [vx|] eqn:H0look.
             - symmetry.
               change (
                 (storeA_restrict σ0 (world_dom (m : WorldT))
                   : gmap atom value) !! x = Some vx).
               apply storeA_restrict_lookup_some_2; [exact H0look|exact Hxm].
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               set_solver.
           }
           assert (H0base_x :
               store_restrict σ0 (world_dom (m : WorldT)) !! x =
               σx !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσ0_x.
           }
           assert (Hm_x :
               σm !! x = σx !! x).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_r. apply elem_of_singleton. reflexivity.
             - exact Hσm_x.
           }
           change (σmy !! y = σ0 !! y).
           rewrite Hxy_my, Hxy_0.
           rewrite Hmy_x, H0_x, H0base_x, Hm_x.
           reflexivity.
        -- assert (HaA : a ∈ A) by set_solver.
           assert (HaDom : a ∈ world_dom (m : WorldT)) by set_solver.
           assert (Hmy_a : σmy !! a = σm !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - exact HaDom.
             - exact Hσm_base.
           }
           assert (H0_a :
               σ0 !! a = store_restrict σ0 (world_dom (m : WorldT)) !! a).
           {
             destruct (σ0 !! a) as [va|] eqn:H0look.
             - symmetry.
               change (
                 (storeA_restrict σ0 (world_dom (m : WorldT))
                   : gmap atom value) !! a = Some va).
               apply storeA_restrict_lookup_some_2; [exact H0look|exact HaDom].
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               set_solver.
           }
           assert (H0base_a :
               store_restrict σ0 (world_dom (m : WorldT)) !! a =
               σx !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσ0_x.
           }
           assert (Hm_a : σm !! a = σx !! a).
           {
             eapply store_lookup_eq_of_restrict_eq_full.
             - apply elem_of_union_l. exact HaA.
             - exact Hσm_x.
           }
           change (σmy !! a = σ0 !! a).
           rewrite Hmy_a, H0_a, H0base_a, Hm_a.
           reflexivity.
      * reflexivity.
    + intros Hσ.
      unfold singleton_world in Hσ.
      cbn [raw_world raw_worldA] in Hσ.
      change (σ = store_restrict σ0 (A ∪ {[y]})) in Hσ.
      subst σ.
      exists σ0. split; [exact Hσ0|reflexivity].
Qed.

End TypePersist.
