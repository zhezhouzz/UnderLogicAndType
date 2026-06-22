(** * Denotation.TypePersist

    Semantic support lemmas for the type-level persistency modality. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivFiberBaseResult.

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

End TypePersist.
