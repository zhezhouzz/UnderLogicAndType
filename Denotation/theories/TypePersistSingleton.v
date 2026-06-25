(** * Denotation.TypePersistSingleton

    Singleton and result-slot support for type-level persistency. *)

From Denotation Require Import Notation TypeDenote ResultFirstOpen
  DenotationSetMapFacts TypeEquivCore TypeEquivFiberBaseCore TypeEquivFiberBaseProjected TypeEquivBody TypeEquiv
  TypePersistBase.
From ContextAlgebra Require Import ResourceAlgebra.

Section TypePersist.

Lemma res_restrict_singleton_pullback_ret_fvar_result
    A D x y (m my : WfWorldT) σy :
  A ⊆ world_dom (m : WorldT) ->
  x ∈ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ∪ A ∪ lvars_fv D ->
  x ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
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
  intros HAm Hxm Hyfresh HxA HD Hres Hclosed_x Hdom_my Hbase
    Hsingle_y.
  assert (Hym : y ∉ world_dom (m : WorldT)) by (clear -Hyfresh; set_solver).
  assert (HyA : y ∉ A) by (clear -Hyfresh; set_solver).
  assert (HyD : LVFree y ∉ D).
  {
    intros HyD.
    apply Hyfresh.
    assert (HyDfv : y ∈ lvars_fv D) by (rewrite lvars_fv_elem; exact HyD).
    set_solver.
  }
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
	        apply elem_open_world_inter_singleton. exact Hxm.
      }
      assert (Hxy_0 : σ0my !! y = σ0my !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0my);
          [exact HD|exact HyD|exact (Hclosed_x σ0my Hσ0my)| |exact Hres|exact Hσ0my].
	        change (x ∈ dom (storeA_restrict σ0my ({[x]} : aset) : gmap atom value)).
	        rewrite storeA_restrict_dom.
	        rewrite (wfworld_store_dom my σ0my Hσ0my), Hdom_my.
	        apply elem_open_world_inter_singleton. exact Hxm.
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
        -- assert (HaA : a ∈ A).
           {
             apply elem_of_union in Ha as [HaA|HaX]; [exact HaA|].
             apply elem_of_singleton in HaX. subst a. contradiction.
           }
           assert (HaDom : a ∈ world_dom (m : WorldT)).
           { exact (HAm _ HaA). }
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
  y ∉ world_dom (m : WorldT) ∪ A ∪ lvars_fv D ->
  x ∉ A ->
  tm_lvars (tret (vfvar x)) ⊆ D ->
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
  intros HAm Hxm Hyfresh HxA HD Hres Hclosed_x Hdom_my Hbase
    Hsingle_x.
  assert (Hym : y ∉ world_dom (m : WorldT)) by (clear -Hyfresh; set_solver).
  assert (HyA : y ∉ A) by (clear -Hyfresh; set_solver).
  assert (HyD : LVFree y ∉ D).
  {
    intros HyD.
    apply Hyfresh.
    assert (HyDfv : y ∈ lvars_fv D) by (rewrite lvars_fv_elem; exact HyD).
    set_solver.
  }
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
	        apply elem_open_world_inter_singleton. exact Hxm.
      }
      assert (Hxy_0 : σ0 !! y = σ0 !! x).
      {
        eapply (expr_result_formula_at_ret_fvar_lookup_eq
          D x y my σ0);
          [exact HD|exact HyD|exact (Hclosed_x σ0 Hσ0)| |exact Hres|exact Hσ0].
	        change (x ∈ dom (storeA_restrict σ0 ({[x]} : aset) : gmap atom value)).
	        rewrite storeA_restrict_dom.
	        rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
	        apply elem_open_world_inter_singleton. exact Hxm.
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
               apply (storeA_restrict_lookup_some_2 _ _ _ _ H0look Hxm).
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               apply elem_of_union_l. exact Hxm.
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
        -- assert (HaA : a ∈ A).
           {
             apply elem_of_union in Ha as [HaA|HaY]; [exact HaA|].
             apply elem_of_singleton in HaY. subst a. contradiction.
           }
           assert (HaDom : a ∈ world_dom (m : WorldT)).
           { exact (HAm _ HaA). }
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
               apply (storeA_restrict_lookup_some_2 _ _ _ _ H0look HaDom).
             - exfalso.
               apply not_elem_of_dom in H0look.
               apply H0look.
               rewrite (wfworld_store_dom my σ0 Hσ0), Hdom_my.
               apply elem_of_union_l. exact HaDom.
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

Lemma res_restrict_singleton_exact_dom_subset
    (m : WfWorldT) X σ :
  dom (σ : StoreT) = X ->
  res_restrict m X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  X ⊆ world_dom (m : WorldT).
Proof.
  intros Hdomσ Hsingle a Ha.
  assert (Hdom_eq :
      world_dom (res_restrict m X : WorldT) = dom (σ : StoreT)).
  { rewrite Hsingle. reflexivity. }
  rewrite res_restrict_dom, Hdomσ in Hdom_eq.
  set_solver.
Qed.

Lemma res_fiber_from_projection_restrict_singleton
    (m mfib : WfWorldT) X σ :
  dom (σ : StoreT) = X ->
  res_fiber_from_projection m X σ mfib ->
  res_restrict mfib X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT).
Proof.
  intros Hdomσ Hproj.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom.
    rewrite (res_fiber_from_projection_world_dom m mfib X σ Hproj).
    destruct Hproj as [Hσproj _].
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσproj)
      as Hdom_proj.
    change (dom (σ : StoreT) = world_dom (res_restrict m X : WorldT))
      in Hdom_proj.
    rewrite res_restrict_dom in Hdom_proj.
    cbn [world_dom raw_world raw_worldA singleton_world singleton_worldA].
    symmetry. exact Hdom_proj.
  - intros τ. split.
    + intros [τ0 [Hτ0 Hτ]].
      pose proof (res_fiber_from_projection_store_restrict
        m mfib X σ τ0 Hproj Hτ0) as Hτ0σ.
      change (store_restrict τ0 (dom (σ : StoreT)) = σ) in Hτ0σ.
      rewrite Hdomσ in Hτ0σ.
      assert (τ = σ) as ->.
      { rewrite <- Hτ. exact Hτ0σ. }
      unfold singleton_world. cbn [raw_world raw_worldA singleton_worldA].
      reflexivity.
    + intros Hτ.
      unfold singleton_world in Hτ.
      cbn [raw_world raw_worldA singleton_worldA] in Hτ.
      rewrite Hτ.
      destruct Hproj as [[τ0 [Hτ0 Hτ0X]] Hfib].
      exists τ0. split.
      * destruct mfib as [wmfib Hwmfib].
        cbn [proj1_sig raw_world raw_worldA world_stores] in Hfib |- *.
        change (wmfib = rawA_fiber (m : WorldT) σ) in Hfib.
        rewrite Hfib. split; [exact Hτ0|].
        change (store_restrict τ0 (dom (σ : StoreT)) = σ).
        rewrite Hdomσ. exact Hτ0X.
      * exact Hτ0X.
Qed.

Lemma store_singleton_dom_value y (v : value) :
  dom ({[y := v]} : StoreT) = {[y]}.
Proof.
  change (dom ({[y := v]} : gmap atom value) = ({[y]} : aset)).
  apply dom_singleton_L.
Qed.

Lemma singleton_world_member_eq (σ τ : StoreT) :
  (singleton_world σ : WorldT) τ ->
  τ = σ.
Proof.
  unfold singleton_world.
  cbn [raw_world raw_worldA singleton_worldA].
  intros ->. reflexivity.
Qed.

Definition const_fresh_value_extension
    (X : aset) (y : atom) (v : value) (HyX : y ∉ X) : fiber_extension :=
  mk_fiber_extension X {[y]}
    (fun _ =>
      (exist _ (singleton_world ({[y := v]} : StoreT))
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorldT))
    ltac:(set_solver)
    ltac:(intros σ Hσ;
      cbn [world_dom raw_world raw_worldA singleton_world];
      apply store_singleton_dom_value)
    ltac:(intros σ Hσ; exists ({[y := v]} : StoreT);
      cbn [raw_world raw_worldA singleton_world];
      reflexivity).

Lemma res_extend_by_const_fresh_value_exact
    (m : WfWorldT) y v (Hy : y ∉ world_dom (m : WorldT)) :
  exists my,
    res_extend_by m
      (const_fresh_value_extension (world_dom (m : WorldT)) y v Hy) my /\
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my (world_dom (m : WorldT)) = m /\
    forall σ, (my : WorldT) σ -> σ !! y = Some v.
Proof.
  set (F := const_fresh_value_extension (world_dom (m : WorldT)) y v Hy).
  assert (Happ : extension_applicable F m).
  {
    constructor.
    - subst F. cbn [const_fresh_value_extension extA_in].
      reflexivity.
    - subst F. cbn [const_fresh_value_extension extA_out].
      set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [my Hext].
  exists my.
  split; [exact Hext|].
  split.
  - rewrite (res_extend_by_dom m F my Hext).
    subst F. reflexivity.
  - split; [exact (res_extend_by_restrict_base m F my Hext)|].
    intros σ Hσ.
    pose proof (resA_extend_by_store_iff m F my σ Hext) as Hiff.
    destruct (proj1 Hiff Hσ) as [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
    subst F.
    change (we =
      (exist _ (singleton_world ({[y := v]} : StoreT))
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorldT)) in Hrel.
    rewrite Hrel in Hσe.
    apply singleton_world_member_eq in Hσe. subst σe.
    rewrite (lookup_union_r (M:=gmap atom) (A:=value)
      σm ({[y := v]} : gmap atom value) y).
    + apply map_lookup_insert.
    + apply not_elem_of_dom.
      rewrite (wfworld_store_dom m σm Hσm).
      exact Hy.
Qed.

Lemma res_extend_by_const_fresh_value
    (m : WfWorldT) y v :
  y ∉ world_dom (m : WorldT) ->
  exists F my,
    ext_in F = world_dom (m : WorldT) /\
    ext_out F = {[y]} /\
    res_extend_by m F my /\
    world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} /\
    res_restrict my (world_dom (m : WorldT)) = m /\
    forall σ, (my : WorldT) σ -> σ !! y = Some v.
Proof.
  intros Hy.
  set (F := const_fresh_value_extension (world_dom (m : WorldT)) y v Hy).
  destruct (res_extend_by_const_fresh_value_exact m y v Hy)
    as [my [Hext [Hdom [Hbase Hlookup]]]].
  exists F, my.
  split; [subst F; reflexivity|].
  split; [subst F; reflexivity|].
  split; [exact Hext|].
  split; [exact Hdom|].
  split; [exact Hbase|exact Hlookup].
Qed.

Lemma res_yfiber_open_arg_base_subset
    (m my myfib : WfWorldT) y σy :
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_fiber_from_projection my {[y]} σy myfib ->
  res_subset (res_restrict myfib (world_dom (m : WorldT))) m.
Proof.
  intros Hy Hdom Hbase Hfib.
  split.
  - rewrite res_restrict_dom.
    rewrite (res_fiber_from_projection_world_dom my myfib {[y]} σy Hfib).
    rewrite Hdom. set_solver.
  - intros σ [σ0 [Hσ0 Hrestrict]].
    destruct Hfib as [_ Hraw].
    destruct myfib as [wmyfib Hwmyfib].
    cbn [proj1_sig raw_world raw_worldA world_stores] in Hraw, Hσ0.
    change (wmyfib = raw_fiber (my : WorldT) σy) in Hraw.
    rewrite Hraw in Hσ0.
    destruct Hσ0 as [Hσ0_my _].
    assert ((res_restrict my (world_dom (m : WorldT)) : WorldT) σ).
    { exists σ0. split; [exact Hσ0_my|exact Hrestrict]. }
    rewrite Hbase in H. exact H.
Qed.

Lemma res_yfiber_sub_const_fresh_extension_concrete
    (m my myfib : WfWorldT) y v
    (Hy : y ∉ world_dom (m : WorldT)) :
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_fiber_from_projection my {[y]} ({[y := v]} : StoreT) myfib ->
  exists myconst,
    res_extend_by m
      (const_fresh_value_extension (world_dom (m : WorldT)) y v Hy)
      myconst /\
    res_subset myfib myconst.
Proof.
  intros Hdom Hbase Hfib.
  destruct (res_extend_by_const_fresh_value_exact m y v Hy)
    as [myconst [Hext [Hdom_const [Hbase_const Hy_const]]]].
  exists myconst. split; [exact Hext|].
  split.
  - change (world_dom (myfib : WorldT) = world_dom (myconst : WorldT)).
    rewrite (res_fiber_from_projection_world_dom my myfib {[y]}
      ({[y := v]} : StoreT) Hfib).
    rewrite Hdom. symmetry. exact Hdom_const.
  - intros τ Hτ.
    pose proof Hfib as Hfib_full.
    destruct Hfib as [_ Hraw].
    assert (Hτ_my : (my : WorldT) τ).
    {
      change ((myfib : WorldT) = raw_fiber (my : WorldT)
        ({[y := v]} : StoreT)) in Hraw.
      destruct myfib as [wmyfib Hwmyfib].
      cbn [proj1_sig raw_world raw_worldA world_stores] in Hraw, Hτ.
      rewrite Hraw in Hτ.
      exact (proj1 Hτ).
    }
    pose proof (res_fiber_from_projection_restrict_singleton
      my myfib {[y]} ({[y := v]} : StoreT)
      (store_singleton_dom_value y v) Hfib_full) as Hsingle_y.
    pose proof (res_restrict_singleton_store_eq
      myfib ({[y]} : aset) ({[y := v]} : StoreT) τ Hsingle_y Hτ)
      as Hτ_y.
    set (τbase := store_restrict τ (world_dom (m : WorldT))).
    assert (Hτbase_m : (m : WorldT) τbase).
    {
      subst τbase.
      assert ((res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict τ (world_dom (m : WorldT)))).
      { exists τ. split; [exact Hτ_my|reflexivity]. }
      rewrite Hbase in H. exact H.
    }
    assert (Hyτbase : y ∉ dom (τbase : StoreT)).
    {
      subst τbase.
      intros Hyin.
      change (y ∈ dom (storeA_restrict τ (world_dom (m : WorldT)) : gmap atom value))
        in Hyin.
      apply elem_of_dom in Hyin as [vy Hylook].
      apply storeA_restrict_lookup_some in Hylook as [Hybase _].
      exact (Hy Hybase).
    }
    assert (Hτ_eq : τ = τbase ∪ ({[y := v]} : StoreT)).
    {
      assert (Hinsert : (τ : StoreT) = <[y := v]> (τbase : StoreT)).
      {
        eapply storeA_eq_insert_of_restrict_singleton
          with (X := world_dom (m : WorldT)).
        - rewrite (wfworld_store_dom myfib τ Hτ).
          rewrite (res_fiber_from_projection_world_dom my myfib {[y]}
            ({[y := v]} : StoreT) Hfib_full).
          rewrite Hdom. set_solver.
        - exact Hy.
        - subst τbase. reflexivity.
        - exact Hτ_y.
      }
      rewrite Hinsert.
      symmetry. apply storeA_union_singleton_insert_fresh. exact Hyτbase.
    }
    pose proof (resA_extend_by_store_iff
      m
      (const_fresh_value_extension (world_dom (m : WorldT)) y v Hy)
      myconst τ Hext) as Hiff.
    apply (proj2 Hiff).
    exists τbase,
      (exist _ (singleton_world ({[y := v]} : StoreT))
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorldT),
      ({[y := v]} : StoreT).
    split; [exact Hτbase_m|].
    split.
    + cbn [const_fresh_value_extension extA_rel].
      reflexivity.
    + split.
      * cbn [raw_world raw_worldA singleton_world]. reflexivity.
      * exact Hτ_eq.
Qed.

Lemma ty_denote_gas_persist_ret_fvar_intro_singleton
    gas Σ τ z σ (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ fv_cty τ ->
  dom (σ : StoreT) = fv_cty τ ∪ {[z]} ->
  res_restrict m (fv_cty τ ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas Σ τ (tret (vfvar z)) ->
  m ⊨ ty_denote_gas (S gas) Σ
    (CTPersist τ) (tret (vfvar z)).
Proof.
  intros HΣclosed Hzτ Hdomσ Hsingle Hden.
  pose proof (ty_denote_gas_guard_formula gas Σ τ
    (tret (vfvar z)) m Hden) as Hguard_src.
  assert (Hguard_tgt :
      m ⊨ ty_guard_formula
        (relevant_env Σ (CTPersist τ) (tret (vfvar z)))
        (CTPersist τ) (tret (vfvar z))).
  { apply ty_guard_to_persist. exact Hguard_src. }
  eapply res_models_and_intro_from_models; [exact Hguard_tgt|].
  assert (Hscope_full :
      formula_scoped_in_world m
        (ty_denote_gas (S gas) Σ (CTPersist τ) (tret (vfvar z)))).
  {
    unfold formula_scoped_in_world.
    eapply ty_denote_gas_scope_of_guard.
    - reflexivity.
    - exact Hguard_tgt.
  }
  cbn [ty_denote_gas] in Hscope_full.
  pose proof (formula_scoped_and_r _ _ _ Hscope_full) as Hscope_forall.
  eapply res_models_forall_rev_intro; [exact Hscope_forall|].
  set (Dres := dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))).
  exists (world_dom (m : WorldT) ∪ lvars_fv (dom Σ) ∪
    lvars_fv Dres ∪ fv_cty τ ∪ {[z]}).
  intros y Hy my Hdom_my Hbase_my.
  rewrite formula_open_impl.
  eapply res_models_impl_intro.
  {
    rewrite <- formula_open_impl.
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope_forall.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - rewrite Hdom_my. apply elem_of_union_r. apply elem_of_singleton.
      reflexivity.
  }
  intros Hres.
  cbn [formula_open] in Hres.
  subst Dres.
  rewrite formula_open_expr_result_formula_at_shift0 in Hres.
  2:{ apply lvars_shift_from_lc. apply relevant_env_closed. exact HΣclosed. }
  2:{ rewrite lvars_shift_from_fv. clear -Hy. set_solver. }
  2:{ apply lc_ret_iff_value. constructor. }
  2:{ cbn [fv_tm fv_value]. clear -Hy. set_solver. }
  rewrite (lvars_shift_from_lc_eq 0
    (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))))
    in Hres
    by (apply relevant_env_closed; exact HΣclosed).
  rewrite relevant_env_persist_eq in Hres.
  pose proof (ty_guard_formula_context_wf _ _ _ _ Hguard_src) as Hwf_src.
  pose proof (ty_guard_formula_basic_world _ _ _ _ Hguard_src) as Hworld_src.
  pose proof Hworld_src as Hworld_src_info.
  apply basic_world_formula_models_iff in Hworld_src_info
    as [_ [Hrel_world _]].
  pose proof Hwf_src as Hwf_src_info.
  apply context_ty_wf_formula_models_iff in Hwf_src_info
    as [HlcD_src [_ [HτD_src Hbasic_cty_src]]].
  assert (Hlcτ_src : lc_context_ty τ).
  {
    unfold lc_context_ty.
    eapply (context_ty_lvars_at_lc 0
      (dom (relevant_env Σ τ (tret (vfvar z)))) τ);
      eauto.
  }
  assert (HtmD_ret_src :
      tm_lvars (tret (vfvar z)) ⊆ dom (relevant_env Σ τ (tret (vfvar z)))).
  {
    eapply ty_denote_gas_tm_lvars_relevant_env_dom. exact Hden.
  }
	  assert (Hzdom : z ∈ world_dom (m : WorldT)).
	  {
	    pose proof (res_restrict_singleton_exact_dom_subset
	      m (fv_cty τ ∪ {[z]}) σ Hdomσ Hsingle) as Hsub.
	    apply Hsub. apply elem_of_union_r. apply elem_of_singleton.
	    reflexivity.
	  }
	  assert (HA_sub : fv_cty τ ⊆ world_dom (m : WorldT)).
	  {
	    pose proof (res_restrict_singleton_exact_dom_subset
	      m (fv_cty τ ∪ {[z]}) σ Hdomσ Hsingle) as Hsub.
	    intros a Ha. apply Hsub. apply elem_of_union_l. exact Ha.
  }
  assert (Hy_m : y ∉ world_dom (m : WorldT)).
  { clear -Hy. set_solver. }
  assert (Hyτ : y ∉ fv_cty τ).
  { clear -Hy. set_solver. }
  assert (Hclosed_z_m : wfworld_closed_on ({[z]} : aset) m).
  {
    change ({[z]} : aset) with (fv_tm (tret (vfvar z))).
    eapply denot_ty_lvar_guard_wfworld_closed_on_term.
    exact Hguard_src.
  }
  assert (Hclosed_z_my : wfworld_closed_on ({[z]} : aset) my).
  {
    eapply wfworld_closed_on_le.
    - intros a Ha. apply elem_of_singleton in Ha. subst a. exact Hzdom.
    - rewrite <- Hbase_my. apply res_restrict_le.
    - exact Hclosed_z_m.
  }
  assert (HDmy : lvars_fv
      (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z))))
      ⊆ world_dom (my : WorldT)).
  {
    intros a Ha.
    rewrite relevant_env_persist_eq in Ha.
    rewrite Hdom_my.
    apply elem_of_union_l.
    apply Hrel_world. exact Ha.
  }
  assert (HtmD_result :
      tm_lvars (tret (vfvar z)) ⊆
        dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))).
  { rewrite relevant_env_persist_eq. exact HtmD_ret_src. }
  assert (HyD_result :
      LVFree y ∉ dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))).
  {
    eapply basic_world_formula_free_notin_dom.
    - eapply ty_guard_formula_basic_world. exact Hguard_tgt.
    - exact Hy_m.
  }
  assert (Hyfresh_result :
      y ∉ world_dom (m : WorldT) ∪ fv_cty τ ∪
        lvars_fv (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z))))).
  {
    intros Hyfresh.
    apply elem_of_union in Hyfresh as [Hyfresh|HyDfv].
    - apply elem_of_union in Hyfresh as [Hyworld|Hyτbad].
      + exact (Hy_m Hyworld).
      + exact (Hyτ Hyτbad).
    - apply HyD_result. rewrite lvars_fv_elem in HyDfv. exact HyDfv.
  }
  pose proof (res_restrict_singleton_push_ret_fvar_result
    (fv_cty τ)
    (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z))))
    z y m my σ
    HA_sub Hzdom Hyfresh_result Hzτ HtmD_result Hres
    Hclosed_z_my Hdom_my Hbase_my Hsingle)
    as [σy [Hdomσy Hsingle_y]].
  assert (Hinner_insert :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τ]> Σ) τ (tret (vfvar y))).
  {
    eapply (ty_denote_gas_result_alias_at
      gas (<[LVFree y := erase_ty τ]> Σ) τ (tret (vfvar z)) y
      (dom (relevant_env Σ (CTPersist τ) (tret (vfvar z)))) my).
    - apply lty_env_closed_insert_free. exact HΣclosed.
    - apply relevant_env_closed. exact HΣclosed.
    - rewrite relevant_env_persist_eq. exact HtmD_ret_src.
    - rewrite relevant_env_persist_eq. exact HτD_src.
    - exact HyD_result.
    - exact HDmy.
    - apply map_lookup_insert.
    - exact Hres.
    - rewrite (ty_denote_gas_insert_fresh_lty_env_eq
        gas Σ τ (tret (vfvar z)) y (erase_ty τ)).
      2:{
        intros HyΣ.
        assert (HyΣfv : y ∈ lvars_fv (dom Σ)).
        { apply lvars_fv_elem. exact HyΣ. }
        apply Hy.
        clear -HyΣfv. set_solver.
      }
      2:{
        intros Hy_lvar.
        apply Hyτ.
        rewrite <- context_ty_lvars_fv.
        apply lvars_fv_elem. exact Hy_lvar.
      }
	      2:{
	        cbn [fv_tm fv_value].
	        intros Hyz. apply elem_of_singleton in Hyz. subst y.
	        exact (Hy_m Hzdom).
	      }
      eapply (res_models_kripke m my).
      + rewrite <- Hbase_my. apply res_restrict_le.
      + exact Hden.
  }
  assert (Hinner_norm :
      my ⊨ ty_denote_gas gas
        (<[LVFree y := erase_ty τ]>
          (relevant_env Σ τ (tret (vfvar z))))
        τ (tret (vfvar y))).
  {
    eapply res_models_ty_denote_gas_env_agree_on.
    - reflexivity.
    - symmetry. apply insert_relevant_env_ret_fvar_restrict_eq.
      + clear -Hy. set_solver.
      + exact Hzτ.
    - exact Hinner_insert.
  }
  rewrite formula_open_persist.
  rewrite formula_open_ty_denote_gas_singleton.
  2:{
    rewrite typed_lty_env_bind_lvars_fv_dom.
    intros HyD.
    apply Hy_m.
    apply Hrel_world.
    apply lvars_fv_elem.
    rewrite relevant_env_persist_eq in HyD.
    apply lvars_fv_elem in HyD.
    exact HyD.
  }
	  2:{
	    cbn [fv_tm fv_value].
	    apply not_elem_of_empty.
	  }
  2:{
    rewrite cty_shift_fv.
    exact Hyτ.
  }
  rewrite cty_open_shift_from_lc_fresh.
  2:{ exact Hlcτ_src. }
  2:{ exact Hyτ. }
  rewrite typed_lty_env_bind_open_current.
  2:{ exact HyD_result. }
  2:{ apply relevant_env_closed. exact HΣclosed. }
  change (erase_ty (CTPersist τ)) with (erase_ty τ).
  rewrite relevant_env_persist_eq.
  eapply (ty_denote_gas_ret_fvar_persist_body_intro_singleton
    gas (<[LVFree y := erase_ty τ]>
      (relevant_env Σ τ (tret (vfvar z)))) τ y σy my).
  - exact Hdomσy.
  - exact Hsingle_y.
  - exact Hinner_norm.
Qed.


Lemma ty_denote_gas_persist_over_ret_fvar_intro_singleton
    gas Σ b φ z σ (m : WfWorldT) :
  lty_env_closed Σ ->
  z ∉ qual_dom φ ->
  dom (σ : StoreT) = fv_cty (CTOver b φ) ∪ {[z]} ->
  res_restrict m (fv_cty (CTOver b φ) ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote_gas gas Σ (CTOver b φ) (tret (vfvar z)) ->
  m ⊨ ty_denote_gas (S gas) Σ
    (CTPersist (CTOver b φ)) (tret (vfvar z)).
Proof.
  intros HΣclosed Hzφ Hdomσ Hsingle Hden.
  eapply ty_denote_gas_persist_ret_fvar_intro_singleton.
  - exact HΣclosed.
  - unfold fv_cty, context_ty_lvars.
    cbn [context_ty_lvars_at].
    rewrite lvars_fv_lvars_at_depth.
    exact Hzφ.
  - exact Hdomσ.
  - exact Hsingle.
  - exact Hden.
Qed.

Lemma ty_denote_persist_ret_fvar_intro_singleton
    (Δ : gmap atom ty) τ z σ (m : WfWorldT) :
  z ∉ fv_cty τ ->
  dom (σ : StoreT) = fv_cty τ ∪ {[z]} ->
  res_restrict m (fv_cty τ ∪ {[z]}) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  m ⊨ ty_denote Δ τ (tret (vfvar z)) ->
  m ⊨ ty_denote Δ (CTPersist τ) (tret (vfvar z)).
Proof.
  intros Hzτ Hdomσ Hsingle Hden.
  unfold ty_denote in *.
  cbn [cty_depth].
  eapply ty_denote_gas_persist_ret_fvar_intro_singleton; eauto.
  apply atom_store_to_lvar_store_closed.
Qed.

End TypePersist.
