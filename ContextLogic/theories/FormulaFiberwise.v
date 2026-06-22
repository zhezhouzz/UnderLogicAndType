(** * Fiberwise aggregation for formulas *)

From ContextLogic Require Import
  FormulaSemantics FormulaConnectives FormulaConnectivesHigher.
From ContextAlgebra Require Import
  ResourceInterface ResourceCompat ResourceCore ResourceAlgebra.

Section FormulaFiberwise.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (Store (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition fiberwise_joinable_on (X : aset) (P : FormulaT) : Prop :=
  forall m,
    (forall σ mfib,
       res_fiber_from_projection m X σ mfib ->
       mfib ⊨ P) ->
    m ⊨ P.

Definition fiberwise_joinable (P : FormulaT) : Prop :=
  forall X, fiberwise_joinable_on X P.

Local Lemma res_fiber_from_projection_of_store_any
    (m : WfWorldT) (X : aset) (σ : StoreT) :
  (m : WorldT) σ ->
  exists mfib,
    res_fiber_from_projection m X (store_restrict σ X) mfib /\
    (mfib : WorldT) σ.
Proof.
  intros Hσ.
  set (σX := store_restrict σ X).
  assert (HdomσX : dom (σX : StoreT) = world_dom (m : WorldT) ∩ X).
  {
    subst σX.
    change (dom (storeA_restrict σ X : gmap atom V) =
      world_dom (m : WorldT) ∩ X).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m σ Hσ).
    reflexivity.
  }
  assert (Hne :
      exists σ0,
        (m : WorldT) σ0 /\
        storeA_restrict σ0 (dom (σX : StoreT)) = σX).
  {
    exists σ. split; [exact Hσ|].
    subst σX.
    rewrite HdomσX.
    apply storeA_map_eq. intros a.
    rewrite !storeA_restrict_lookup.
    destruct (decide (a ∈ world_dom (m : WorldT) ∩ X)) as [Ha|Ha].
    + destruct (decide (a ∈ X)) as [_|Hbad]; [reflexivity|set_solver].
    + destruct (decide (a ∈ X)) as [HaX|_]; [|reflexivity].
      assert (Haσ : a ∉ dom (σ : StoreT)).
      {
        change (a ∉ dom (σ : gmap atom V)).
        rewrite (wfworld_store_dom m σ Hσ).
        set_solver.
      }
      change (a ∉ dom (σ : gmap atom V)) in Haσ.
      apply not_elem_of_dom_1 in Haσ.
      symmetry. exact Haσ.
  }
  exists (resA_fiber m σX Hne).
  split.
  - split.
    + exists σ. split; [exact Hσ|reflexivity].
    + reflexivity.
  - cbn [raw_world raw_worldA world_stores rawA_fiber].
    split; [exact Hσ|].
    change (storeA_restrict σ (dom (σX : StoreT)) = σX).
    subst σX.
    rewrite HdomσX.
    apply storeA_map_eq. intros a.
    rewrite !storeA_restrict_lookup.
    destruct (decide (a ∈ world_dom (m : WorldT) ∩ X)) as [Ha|Ha].
    + destruct (decide (a ∈ X)) as [_|Hbad]; [reflexivity|set_solver].
    + destruct (decide (a ∈ X)) as [HaX|_]; [|reflexivity].
      assert (Haσ : a ∉ dom (σ : StoreT)).
      {
        change (a ∉ dom (σ : gmap atom V)).
        rewrite (wfworld_store_dom m σ Hσ).
        set_solver.
      }
      change (a ∉ dom (σ : gmap atom V)) in Haσ.
      apply not_elem_of_dom_1 in Haσ.
      symmetry. exact Haσ.
Qed.

Local Lemma res_fiber_from_projection_world_dom
    (m mfib : WfWorldT) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  world_dom (mfib : WorldT) = world_dom (m : WorldT).
Proof.
  intros [_ Hfib].
  pose proof (f_equal world_dom Hfib) as Hdom.
  cbn [raw_fiber rawA_fiber world_dom worldA_dom] in Hdom.
  exact Hdom.
Qed.

Local Lemma res_fiber_from_projection_store_restrict_input
    (m mfib : WfWorldT) (X : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : WorldT) τ ->
  store_restrict τ X = σ.
Proof.
  intros Hproj Hτ.
  pose proof (res_fiber_from_projection_store_source
    m mfib X σ τ Hproj Hτ) as Hτm.
  pose proof (res_fiber_from_projection_store_restrict
    m mfib X σ τ Hproj Hτ) as Hτdom.
  change ((store_restrict τ (dom (σ : StoreT)) : StoreT) = σ) in Hτdom.
  pose proof (wfworld_store_dom m τ Hτm) as Hdomτ.
  change (dom (τ : StoreT) = world_dom (m : WorldT)) in Hdomτ.
  destruct Hproj as [Hσproj _].
  pose proof (wfworld_store_dom (res_restrict m X) σ Hσproj)
    as Hdomσ.
  change (dom (σ : StoreT) =
    world_dom (res_restrict m X : WorldT)) in Hdomσ.
  rewrite res_restrict_dom in Hdomσ.
  apply storeA_map_eq. intros a.
  rewrite storeA_restrict_lookup.
  destruct (decide (a ∈ X)) as [HaX|HaX].
  - destruct (decide (a ∈ dom (σ : StoreT))) as [Haσ|Haσ].
    + change (a ∈ dom (σ : gmap atom V)) in Haσ.
      apply elem_of_dom in Haσ as [v Hσa].
      assert (Hτa : τ !! a = Some v).
      {
        assert ((store_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
          Some v) as Hlook.
        { rewrite Hτdom. exact Hσa. }
        apply storeA_restrict_lookup_some in Hlook as [_ Hτa].
        exact Hτa.
      }
      transitivity (Some v); [exact Hτa|symmetry; exact Hσa].
    + assert (Haτ : a ∉ dom (τ : StoreT)).
      {
        rewrite Hdomτ.
        intros Ham. apply Haσ.
        change (a ∈ dom (σ : StoreT)).
        rewrite Hdomσ. simpl. set_solver.
      }
      change (a ∉ dom (τ : gmap atom V)) in Haτ.
      apply not_elem_of_dom in Haτ.
      transitivity (@None V); [exact Haτ|].
      symmetry. apply not_elem_of_dom.
      change (a ∉ dom (σ : gmap atom V)) in Haσ. exact Haσ.
  - destruct (σ !! a) as [v|] eqn:Hσa; [|symmetry; exact Hσa].
    exfalso.
    assert (Haσ : a ∈ dom (σ : StoreT)).
    { change (a ∈ dom (σ : gmap atom V)).
      apply elem_of_dom. exists v. exact Hσa. }
    rewrite Hdomσ in Haσ. simpl in Haσ.
    set_solver.
Qed.

Local Lemma lstore_in_lworld_on_lift_res_subset
    (D : lvset) (m n : WfWorldT)
    (Hlc : lc_lvars D)
    (Hsubm : lvars_fv D ⊆ world_dom (m : WorldT))
    (Hsubn : lvars_fv D ⊆ world_dom (n : WorldT))
    (s : LStoreOn (V := V) D) :
  res_subset m n ->
  lstore_in_lworld_on s (lworld_on_lift D m Hlc Hsubm) ->
  lstore_in_lworld_on s (lworld_on_lift D n Hlc Hsubn).
Proof.
  intros [_ Hstores] Hmem.
  unfold lstore_in_lworld_on, lworld_on_lift in *.
  cbn [lw lraw_world raw_worldA worldA_stores] in *.
  destruct Hmem as [σl [Hσl Hrestrict]].
  exists σl. split; [|exact Hrestrict].
  destruct Hσl as [τ [Hτ Hτeq]].
  exists τ. split; [|exact Hτeq].
  destruct Hτ as [σ [Hσ Hσeq]].
  exists σ. split; [|exact Hσeq].
  apply Hstores. exact Hσ.
Qed.

Local Lemma res_fiber_from_projection_subset_of_fixed
    (m mfib_small mfib_big : WfWorldT)
    (Xbig Xsmall : aset) (σbig σsmall : StoreT) :
  dom (σbig : StoreT) ⊆ dom (σsmall : StoreT) ->
  store_restrict σsmall (dom (σbig : StoreT)) = σbig ->
  res_fiber_from_projection m Xbig σbig mfib_big ->
  res_fiber_from_projection m Xsmall σsmall mfib_small ->
  res_subset mfib_small mfib_big.
Proof.
  intros Hdom Hrestrict Hbig Hsmall.
  split.
  - change (world_dom (mfib_small : WorldT) =
      world_dom (mfib_big : WorldT)).
    rewrite (res_fiber_from_projection_world_dom m mfib_small Xsmall
      σsmall Hsmall).
    rewrite (res_fiber_from_projection_world_dom m mfib_big Xbig
      σbig Hbig).
    reflexivity.
  - intros τ Hτ.
    destruct Hbig as [_ Hbig_eq].
    change ((mfib_big : WorldT) τ).
    change ((mfib_big : WorldT) = raw_fiber (m : WorldT) σbig)
      in Hbig_eq.
    rewrite Hbig_eq.
    split.
    + eapply res_fiber_from_projection_store_source; eauto.
      + pose proof (res_fiber_from_projection_store_restrict
          m mfib_small Xsmall σsmall τ Hsmall Hτ) as Hτsmall.
      assert (Hτsmall_full :
          (storeA_restrict τ (dom (σsmall : gmap atom V)) : gmap atom V) =
          storeA_restrict σsmall (dom (σsmall : gmap atom V))).
      {
        change ((storeA_restrict τ (dom (σsmall : StoreT)) : StoreT) =
          σsmall) in Hτsmall.
        change ((storeA_restrict τ (dom (σsmall : StoreT)) : StoreT) =
          storeA_restrict σsmall (dom (σsmall : StoreT))).
        rewrite Hτsmall.
        symmetry. apply storeA_restrict_idemp_eq. reflexivity.
      }
      transitivity (store_restrict σsmall (dom (σbig : StoreT))).
      * eapply storeA_restrict_eq_mono; [exact Hdom|exact Hτsmall_full].
      * exact Hrestrict.
Qed.

Local Lemma res_fiber_from_projection_self_of_fixed
    (mfib : WfWorldT) (X : aset) (σ : StoreT) :
  (exists τ, (mfib : WorldT) τ /\
    store_restrict τ X = σ) ->
  (forall τ, (mfib : WorldT) τ ->
    store_restrict τ (dom (σ : StoreT)) = σ) ->
  res_fiber_from_projection mfib X σ mfib.
Proof.
  intros Hnonempty Hfixed.
  split.
  - exact Hnonempty.
  - apply world_ext.
    + reflexivity.
    + intros τ. split.
      * intros Hτ. split; [exact Hτ|apply Hfixed; exact Hτ].
      * intros [Hτ _]. exact Hτ.
Qed.

Local Lemma res_fiber_from_projection_lift_inner
    (m mfibD mfibDX : WfWorldT)
    (D X : aset) (σD σX : StoreT) :
  res_fiber_from_projection m D σD mfibD ->
  res_fiber_from_projection mfibD X σX mfibDX ->
  exists mfibX,
    res_fiber_from_projection m X σX mfibX /\
    res_fiber_from_projection mfibX D σD mfibDX.
Proof.
  intros HprojD HprojX.
  pose proof (res_fiber_from_projection_world_dom
    mfibD mfibDX X σX HprojX) as HdomDX.
  destruct HprojX as [HσX HfibX].
  destruct HσX as [τ0 [Hτ0D Hτ0X]].
  pose proof (res_fiber_from_projection_store_source
    m mfibD D σD τ0 HprojD Hτ0D) as Hτ0m.
  assert (HσX_m :
      exists τ, (m : WorldT) τ /\
        store_restrict τ X = σX).
  { exists τ0. split; [exact Hτ0m|exact Hτ0X]. }
  assert (Hτ0Xraw :
      store_restrict τ0 (dom (σX : StoreT)) = σX).
  {
    apply storeA_map_eq. intros a.
    rewrite storeA_restrict_lookup.
    destruct (decide (a ∈ dom (σX : StoreT))) as [HaσX|HaσX].
    - change (a ∈ dom (σX : gmap atom V)) in HaσX.
      apply elem_of_dom in HaσX as [v Hv].
      rewrite <- Hτ0X in Hv.
      apply storeA_restrict_lookup_some in Hv as [HaX Hτ0a].
      assert (HσXa : σX !! a = Some v).
      {
        rewrite <- Hτ0X.
        apply storeA_restrict_lookup_some_2; [exact Hτ0a|exact HaX].
      }
      transitivity (Some v); [exact Hτ0a|symmetry; exact HσXa].
    - destruct (decide (a ∈ X)) as [HaX|HaX].
      + destruct (τ0 !! a) as [v|] eqn:Hτ0a.
        2:{
          symmetry. apply not_elem_of_dom.
          change (a ∉ dom (σX : gmap atom V)) in HaσX.
          exact HaσX.
        }
        exfalso. apply HaσX.
        change (a ∈ dom (σX : gmap atom V)).
        apply elem_of_dom. exists v.
        rewrite <- Hτ0X.
        apply storeA_restrict_lookup_some_2; [exact Hτ0a|exact HaX].
      + symmetry.
        rewrite <- Hτ0X.
        apply storeA_restrict_lookup_none_r. exact HaX.
  }
  assert (HσX_raw :
      exists τ, (m : WorldT) τ /\
        store_restrict τ (dom (σX : StoreT)) = σX).
  { exists τ0. split; [exact Hτ0m|exact Hτ0Xraw]. }
  set (mfibX := resA_fiber m σX HσX_raw : WfWorldT).
  exists mfibX.
  split.
  { split; [exact HσX_m|reflexivity]. }
  split.
  - exists τ0. split.
    + cbn [mfibX raw_world raw_worldA world_stores rawA_fiber].
      split; [exact Hτ0m|exact Hτ0Xraw].
    + eapply res_fiber_from_projection_store_restrict_input; eauto.
  - pose proof HprojD as HprojD_full.
    destruct HprojD as [_ HfibD].
    assert (HmfibX_dom :
        world_dom (mfibX : WorldT) = world_dom (m : WorldT)).
    {
      unfold mfibX.
      cbn [raw_world raw_worldA world_dom worldA_dom rawA_fiber].
      reflexivity.
    }
    assert (HmfibDX_dom :
        world_dom (mfibDX : WorldT) = world_dom (m : WorldT)).
    {
      transitivity (world_dom (mfibD : WorldT)).
      - exact HdomDX.
      - symmetry.
        pose proof (f_equal world_dom HfibD) as HdomD.
        cbn [raw_fiber rawA_fiber world_dom worldA_dom] in HdomD.
        symmetry. exact HdomD.
    }
    apply world_ext.
    + transitivity (world_dom (m : WorldT)).
      * exact HmfibDX_dom.
      * symmetry.
        change (world_dom (rawA_fiber (mfibX : WorldT) σD) =
          world_dom (m : WorldT)).
        cbn [raw_fiber rawA_fiber world_dom worldA_dom].
        exact HmfibX_dom.
    + intros τ. split.
      * intros Hτ.
        change (mfibDX τ) in Hτ.
        pose proof (f_equal (fun w : WorldT => w τ) HfibX) as Hτeq.
        cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores]
          in Hτeq.
        pose proof (eq_rect _ (fun P : Prop => P) Hτ _ Hτeq) as Hτ'.
        destruct Hτ' as [HτD HτX].
        split.
        -- cbn [mfibX raw_fiber rawA_fiber raw_world raw_worldA world_stores].
           split.
           ++ eapply res_fiber_from_projection_store_source; eauto.
           ++ exact HτX.
        -- eapply res_fiber_from_projection_store_restrict; eauto.
      * intros [HτX HτD].
        change (mfibDX τ).
        pose proof (f_equal (fun w : WorldT => w τ) HfibX) as Hτeq.
        cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores]
          in Hτeq.
        refine (eq_rect _ (fun P : Prop => P) _ _ (eq_sym Hτeq)).
        cbn [mfibX raw_fiber rawA_fiber raw_world raw_worldA world_stores]
          in HτX.
        cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores].
    destruct HτX as [Hτm HτX].
    split.
        -- change (mfibD τ).
           pose proof (f_equal (fun w : WorldT => w τ) HfibD) as HτDeq.
           cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores]
             in HτDeq.
           refine (eq_rect _ (fun P : Prop => P) _ _ (eq_sym HτDeq)).
           split; [exact Hτm|exact HτD].
        -- exact HτX.
Qed.

Local Lemma store_restrict_drop_open
    (τ : StoreT) (X D : aset) (y : atom) :
  y ∉ X ->
  dom (τ : StoreT) = D ∪ {[y]} ->
  store_restrict (store_restrict τ D : StoreT) X =
  store_restrict τ X.
Proof.
  intros HyX Hdom.
  change (storeA_restrict (storeA_restrict τ D) X =
    storeA_restrict τ X).
  rewrite storeA_restrict_restrict.
  apply storeA_map_eq. intros a.
  rewrite !storeA_restrict_lookup.
  destruct (decide (a ∈ X)) as [HaX|HaX].
  2:{
    destruct (decide (a ∈ D ∩ X)) as [HaDX|_]; [set_solver|].
    reflexivity.
  }
  destruct (decide (a ∈ D)) as [HaD|HaD].
  {
    destruct (decide (a ∈ D ∩ X)) as [_|HaDX]; [reflexivity|set_solver].
  }
  assert (Hnotdom : a ∉ dom (τ : StoreT)).
  {
    rewrite Hdom. intros Ha.
    apply elem_of_union in Ha as [HaD'|Hay].
    - exact (HaD HaD').
    - apply elem_of_singleton in Hay. subst a. contradiction.
  }
  destruct (decide (a ∈ D ∩ X)) as [HaDX|_]; [set_solver|].
  symmetry. apply not_elem_of_dom_1. exact Hnotdom.
Qed.

Local Lemma res_restrict_open_world_eq
    (m my : WfWorldT) X y :
  y ∉ X ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_restrict my X = res_restrict m X.
Proof.
  intros HyX Hdom Hrestrict.
  apply wfworld_ext. apply world_ext.
  - rewrite !res_restrict_dom, Hdom.
    apply set_eq. intros a. set_solver.
  - intros τ. split.
    + intros [τy [Hτy Hτ]].
      assert ((res_restrict my (world_dom (m : WorldT)) : WorldT)
          (store_restrict τy (world_dom (m : WorldT)))) as Hτm.
      { exists τy. split; [exact Hτy|reflexivity]. }
      rewrite Hrestrict in Hτm.
      exists (store_restrict τy (world_dom (m : WorldT))).
      split; [exact Hτm|].
      rewrite <- Hτ.
      eapply store_restrict_drop_open; eauto.
      rewrite <- Hdom.
      apply wfworld_store_dom with (w := my). exact Hτy.
    + intros [τm [Hτm Hτ]].
      assert ((res_restrict my (world_dom (m : WorldT)) : WorldT) τm)
        as Hτm_restrict.
      { rewrite Hrestrict. exact Hτm. }
      destruct Hτm_restrict as [τy [Hτy Hτy_restrict]].
      exists τy. split; [exact Hτy|].
      rewrite <- Hτ. rewrite <- Hτy_restrict.
      symmetry.
      eapply store_restrict_drop_open; eauto.
      rewrite <- Hdom.
      apply wfworld_store_dom with (w := my). exact Hτy.
Qed.

Lemma res_fiber_from_projection_restrict_open_world
    (m my myfib : WfWorldT) X σ y :
  y ∉ X ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_fiber_from_projection my X σ myfib ->
  res_fiber_from_projection m X σ
    (res_restrict myfib (world_dom (m : WorldT))).
Proof.
  intros HyX Hdom Hrestrict Hproj.
  split.
  - change ((res_restrict m X : WorldT) σ).
    rewrite <- (res_restrict_open_world_eq m my X y HyX Hdom Hrestrict).
    exact (proj1 Hproj).
  - apply world_ext.
    + transitivity (world_dom (m : WorldT)).
      * rewrite res_restrict_dom.
        rewrite (res_fiber_from_projection_world_dom
          my myfib X σ Hproj).
        rewrite Hdom. apply set_eq. intros a. set_solver.
      * cbn [raw_fiber rawA_fiber world_dom worldA_dom].
        reflexivity.
    + intros τ. split.
      * intros [τy [Hτy Hτ]].
        destruct Hproj as [Hσproj Hfib].
        pose proof (f_equal (fun w : WorldT => w τy) Hfib) as Hτyeq.
        cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores]
          in Hτyeq.
        pose proof (eq_rect _ (fun P : Prop => P) Hτy _ Hτyeq)
          as [Hτy_my Hτy_fixed].
        split.
        -- assert ((res_restrict my (world_dom (m : WorldT)) : WorldT) τ)
             as Hτm.
           { exists τy. split; [exact Hτy_my|exact Hτ]. }
           rewrite Hrestrict in Hτm. exact Hτm.
        -- rewrite <- Hτ.
           assert (Hdomσ : dom (σ : StoreT) ⊆ world_dom (m : WorldT)).
           {
             pose proof (wfworld_store_dom (res_restrict my X)
               σ Hσproj) as Hdomσ.
             change (dom (σ : StoreT) =
               world_dom (res_restrict my X : WorldT)) in Hdomσ.
             rewrite res_restrict_dom, Hdom in Hdomσ.
             rewrite Hdomσ. intros a Ha. set_solver.
           }
           rewrite storeA_restrict_restrict.
           replace (world_dom (m : WorldT) ∩ dom (σ : StoreT))
             with (dom (σ : StoreT)) by set_solver.
           exact Hτy_fixed.
      * intros [Hτm Hτfixed].
        destruct Hproj as [Hσproj Hfib].
        assert ((res_restrict my (world_dom (m : WorldT)) : WorldT) τ)
          as Hτm_restrict.
        { rewrite Hrestrict. exact Hτm. }
        destruct Hτm_restrict as [τy [Hτy_my Hτy_restrict]].
        exists τy. split.
        -- pose proof (f_equal (fun w : WorldT => w τy) Hfib) as Hτyeq.
           cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores]
             in Hτyeq.
           refine (eq_rect _ (fun P : Prop => P) _ _ (eq_sym Hτyeq)).
           split; [exact Hτy_my|].
           assert (Hdomσ : dom (σ : StoreT) ⊆ world_dom (m : WorldT)).
           {
             pose proof (wfworld_store_dom (res_restrict my X)
               σ Hσproj) as Hdomσ.
             change (dom (σ : StoreT) =
               world_dom (res_restrict my X : WorldT)) in Hdomσ.
             rewrite res_restrict_dom, Hdom in Hdomσ.
             rewrite Hdomσ. intros a Ha. set_solver.
           }
           transitivity (store_restrict τ (dom (σ : StoreT))).
           ++ eapply storeA_restrict_eq_mono; [exact Hdomσ|].
              transitivity τ; [exact Hτy_restrict|].
              symmetry. apply storeA_restrict_idemp_eq.
              apply wfworld_store_dom with (w := m). exact Hτm.
           ++ exact Hτfixed.
        -- exact Hτy_restrict.
Qed.

Lemma res_fiber_open_world_shape
    (m my myfib : WfWorldT) X σ y :
  y ∉ X ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  res_fiber_from_projection my X σ myfib ->
  world_dom (myfib : WorldT) =
    world_dom
      (res_restrict myfib (world_dom (m : WorldT)) : WorldT) ∪ {[y]} /\
  res_restrict myfib
    (world_dom
      (res_restrict myfib (world_dom (m : WorldT)) : WorldT)) =
    res_restrict myfib (world_dom (m : WorldT)).
Proof.
  intros _ Hym Hdom _ Hproj.
  pose proof (res_fiber_from_projection_world_dom
    my myfib X σ Hproj) as Hfibdom.
  assert (Hrestrict_dom :
      world_dom
        (res_restrict myfib (world_dom (m : WorldT)) : WorldT) =
      world_dom (m : WorldT)).
  {
    rewrite res_restrict_dom, Hfibdom, Hdom.
    apply set_eq. intros a. set_solver.
  }
  split.
  - rewrite Hfibdom, Hrestrict_dom, Hdom. reflexivity.
  - rewrite Hrestrict_dom. reflexivity.
Qed.

Lemma fiberwise_joinable_on_true X :
  fiberwise_joinable_on X FTrue.
Proof.
  intros m _.
  unfold res_models. cbn [formula_measure res_models_fuel].
  split; [unfold formula_scoped_in_world; rewrite formula_fv_true; set_solver|].
  exact I.
Qed.

Lemma fiberwise_joinable_true :
  fiberwise_joinable FTrue.
Proof. intros X. apply fiberwise_joinable_on_true. Qed.

Lemma fiberwise_joinable_on_false X :
  fiberwise_joinable_on X FFalse.
Proof.
  intros m Hfib.
  destruct (world_wf m) as [[σ Hσ] _].
  destruct (res_fiber_from_projection_of_store_any m X σ Hσ)
    as [mfib [Hproj _]].
  pose proof (Hfib (store_restrict σ X) mfib Hproj) as Hfalse.
  unfold res_models in Hfalse.
  cbn [formula_measure res_models_fuel] in Hfalse.
  tauto.
Qed.

Lemma fiberwise_joinable_false :
  fiberwise_joinable FFalse.
Proof. intros X. apply fiberwise_joinable_on_false. Qed.

Lemma fiberwise_joinable_on_atom X q :
  fiberwise_joinable_on X (FAtom q).
Proof.
  destruct q as [D P].
  intros m Hfib.
  unfold res_models. cbn [formula_measure res_models_fuel qualifier_exact_denote].
  assert (Hscope : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    destruct (world_wf m) as [[σ0 Hσ0] _].
    destruct (res_fiber_from_projection_of_store_any m X σ0 Hσ0)
      as [mfib0 [Hproj0 _]].
    pose proof (Hfib (store_restrict σ0 X) mfib0 Hproj0) as Hatom0.
    pose proof (res_models_fuel_scoped
      (formula_measure (FAtom (tqual D P))) mfib0
      (FAtom (tqual D P)) Hatom0) as Hscoped0.
    unfold formula_scoped_in_world in Hscoped0.
    rewrite formula_fv_atom in Hscoped0.
    cbn [qual_vars] in Hscoped0.
    rewrite (res_fiber_from_projection_world_dom m mfib0 X
      (store_restrict σ0 X) Hproj0) in Hscoped0.
    exact Hscoped0.
  }
  assert (Hlc : lc_lvars D).
  {
    destruct (world_wf m) as [[σ0 Hσ0] _].
    destruct (res_fiber_from_projection_of_store_any m X σ0 Hσ0)
      as [mfib0 [Hproj0 _]].
    pose proof (Hfib (store_restrict σ0 X) mfib0 Hproj0) as Hatom0.
    cbn [res_models formula_measure res_models_fuel qualifier_exact_denote]
      in Hatom0.
    destruct Hatom0 as [_ [Hlc0 _]].
    exact Hlc0.
  }
  split.
  { unfold formula_scoped_in_world. rewrite formula_fv_atom.
    cbn [qual_vars]. exact Hscope. }
  exists Hlc, Hscope. intros s.
  split.
  - intros HPs.
    destruct (world_wf m) as [[σ0 Hσ0] _].
    destruct (res_fiber_from_projection_of_store_any m X σ0 Hσ0)
      as [mfib0 [Hproj0 _]].
    pose proof (Hfib (store_restrict σ0 X) mfib0 Hproj0) as Hatom0.
    cbn [res_models formula_measure res_models_fuel qualifier_exact_denote]
      in Hatom0.
    destruct Hatom0 as [_ [Hlc0 [Hsub0 Hiff0]]].
    pose proof (proj1 (Hiff0 s) HPs) as Hmem0.
    change (lstore_in_lworld_on s (lworld_on_lift D m Hlc0 Hscope)).
    eapply (lstore_in_lworld_on_lift_res_subset D mfib0 m Hlc0 Hsub0 Hscope s).
    + apply res_subset_fiber_source with
        (X := X) (σ := store_restrict σ0 X).
      exact Hproj0.
    + exact Hmem0.
  - intros Hmem.
    unfold lstore_in_lworld_on, lworld_on_lift in Hmem.
    cbn [lw lraw_world raw_worldA worldA_stores] in Hmem.
    destruct Hmem as [σl [[τ [Hτres Hτeq]] Hrestrict_l]].
    destruct Hτres as [σ [Hσ Hσeq]].
    destruct (res_fiber_from_projection_of_store_any m X σ Hσ)
      as [mfib [Hproj Hσfib]].
    pose proof (Hfib (store_restrict σ X) mfib Hproj) as Hatom.
    cbn [res_models formula_measure res_models_fuel qualifier_exact_denote]
      in Hatom.
    destruct Hatom as [_ [Hlc_f [Hsub_f Hiff_f]]].
    apply (proj2 (Hiff_f s)).
    unfold lstore_in_lworld_on, lworld_on_lift.
    cbn [lw lraw_world raw_worldA worldA_stores].
    exists σl. split; [|exact Hrestrict_l].
    exists τ. split; [|exact Hτeq].
    exists σ. split; [exact Hσfib|exact Hσeq].
Qed.

Lemma fiberwise_joinable_atom q :
  fiberwise_joinable (FAtom q).
Proof. intros X. apply fiberwise_joinable_on_atom. Qed.

Lemma fiberwise_joinable_on_and X P Q :
  fiberwise_joinable_on X P ->
  fiberwise_joinable_on X Q ->
  fiberwise_joinable_on X (FAnd P Q).
Proof.
  intros HP HQ m Hfib.
  apply res_models_and_intro_from_models.
  - apply HP. intros σ mfib Hproj.
    apply res_models_and_elim_l with (ψ := Q).
    exact (Hfib σ mfib Hproj).
  - apply HQ. intros σ mfib Hproj.
    apply res_models_and_elim_r with (φ := P).
    exact (Hfib σ mfib Hproj).
Qed.

Lemma fiberwise_joinable_and P Q :
  fiberwise_joinable P ->
  fiberwise_joinable Q ->
  fiberwise_joinable (FAnd P Q).
Proof.
  intros HP HQ X.
  apply fiberwise_joinable_on_and; [apply HP|apply HQ].
Qed.

Lemma fiberwise_joinable_on_fibvars X D P :
  X ∩ formula_fv P ⊆ lvars_fv D ->
  (forall σ, fiberwise_joinable_on X (formula_msubst_store σ P)) ->
  fiberwise_joinable_on X (FFibVars D P).
Proof.
  intros _ Hbody m HfibX.
  eapply res_models_FFibVars_intro.
  - destruct (world_wf m) as [[τ Hτ] _].
    destruct (res_fiber_from_projection_of_store_any m X τ Hτ)
      as [mfib [Hproj _]].
    pose proof (HfibX (store_restrict τ X) mfib Hproj) as Hfib.
    pose proof (res_models_scoped _ _ Hfib) as Hscope.
    unfold formula_scoped_in_world in Hscope |- *.
    rewrite (res_fiber_from_projection_world_dom m mfib X
      (store_restrict τ X) Hproj) in Hscope.
    exact Hscope.
  - destruct (world_wf m) as [[τ Hτ] _].
    destruct (res_fiber_from_projection_of_store_any m X τ Hτ)
      as [mfib [Hproj _]].
    pose proof (HfibX (store_restrict τ X) mfib Hproj) as Hfib.
    apply res_models_FFibVars_iff in Hfib as [_ [Hlc _]].
    exact Hlc.
  - intros σD mfibD HprojD.
    apply (Hbody σD).
    intros σX mfibDX HprojX.
    destruct (res_fiber_from_projection_lift_inner
      m mfibD mfibDX (lvars_fv D) X σD σX HprojD HprojX)
      as [mfibX [HprojXm HprojDX]].
    pose proof (HfibX σX mfibX HprojXm) as Hfib.
    apply res_models_FFibVars_iff in Hfib as [_ [_ Hinner]].
    exact (Hinner σD mfibDX HprojDX).
Qed.

Lemma fiberwise_joinable_on_fibvars_over_atom X D q :
  X ∩ formula_fv (FOver (FAtom q)) ⊆ lvars_fv D ->
  (forall σ,
    fiberwise_joinable_on X
      (formula_msubst_store σ (FOver (FAtom q)))) ->
  fiberwise_joinable_on X (FFibVars D (FOver (FAtom q))).
Proof.
  intros HXD Hbody.
  eapply fiberwise_joinable_on_fibvars; eauto.
Qed.

Lemma fiberwise_joinable_on_fibvars_under_atom X D q :
  X ∩ formula_fv (FUnder (FAtom q)) ⊆ lvars_fv D ->
  (forall σ,
    fiberwise_joinable_on X
      (formula_msubst_store σ (FUnder (FAtom q)))) ->
  fiberwise_joinable_on X (FFibVars D (FUnder (FAtom q))).
Proof.
  intros HXD Hbody.
  eapply fiberwise_joinable_on_fibvars; eauto.
Qed.

Lemma fiberwise_joinable_on_forall X P :
  (exists L : aset, forall y,
     y ∉ L ->
     fiberwise_joinable_on X (formula_open 0 y P)) ->
  fiberwise_joinable_on X (FForall P).
Proof.
  intros [L Hopen] m Hfib.
  assert (Hscope : formula_scoped_in_world m (FForall P)).
  {
    destruct (world_wf m) as [[τ Hτ] _].
    destruct (res_fiber_from_projection_of_store_any m X τ Hτ)
      as [mfib [Hproj _]].
    pose proof (Hfib (store_restrict τ X) mfib Hproj) as Hforall.
    pose proof (res_models_scoped _ _ Hforall) as Hscope_fib.
    unfold formula_scoped_in_world in Hscope_fib |- *.
    rewrite (res_fiber_from_projection_world_dom m mfib X
      (store_restrict τ X) Hproj) in Hscope_fib.
    exact Hscope_fib.
  }
  eapply res_models_forall_rev_intro; [exact Hscope|].
  exists (L ∪ X ∪ world_dom (m : WorldT) ∪ formula_fv P).
  intros y Hy my Hdom Hrestrict.
  assert (HyL : y ∉ L) by set_solver.
  assert (HyX : y ∉ X) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  specialize (Hopen y HyL).
  apply Hopen.
  intros σ myfib Hproj_my.
  set (mfib := res_restrict myfib (world_dom (m : WorldT))).
  assert (Hproj_m : res_fiber_from_projection m X σ mfib).
  {
    unfold mfib.
    eapply res_fiber_from_projection_restrict_open_world; eauto.
  }
  pose proof (Hfib σ mfib Hproj_m) as Hforall_mfib.
  destruct (res_fiber_open_world_shape m my myfib X σ y
    HyX Hym Hdom Hrestrict Hproj_my) as [Hdom_fib Hrestrict_fib].
  eapply res_models_forall_open_named_fresh; [exact Hforall_mfib| | |].
  - unfold mfib. rewrite res_restrict_dom.
    rewrite (res_fiber_from_projection_world_dom my myfib X σ Hproj_my).
    rewrite Hdom. set_solver.
  - exact Hdom_fib.
  - exact Hrestrict_fib.
Qed.

Lemma fiberwise_joinable_forall P :
  (exists L : aset, forall y,
     y ∉ L ->
     fiberwise_joinable (formula_open 0 y P)) ->
  fiberwise_joinable (FForall P).
Proof.
  intros [L Hopen] X.
  apply fiberwise_joinable_on_forall.
  exists L. intros y Hy. apply Hopen. exact Hy.
Qed.

Local Lemma fibvars_atom_refinement_data
    (D : lvset) (q : qualifier (V := V))
    (X : aset) (m mfibD : WfWorldT) (σD τ : StoreT) :
  formula_fv (FFibVars D (FOver (FAtom q))) ⊆ X ->
  formula_scoped_in_world m (FFibVars D (FOver (FAtom q))) ->
  res_fiber_from_projection m (lvars_fv D) σD mfibD ->
  (mfibD : WorldT) τ ->
  exists mfibX,
    res_fiber_from_projection m X (store_restrict τ X) mfibX /\
    (mfibX : WorldT) τ /\
    res_subset mfibX mfibD /\
    res_fiber_from_projection mfibX (lvars_fv D) σD mfibX.
Proof.
  intros HfvX Hscope HprojD HτD.
  pose proof (res_fiber_from_projection_store_source
    m mfibD (lvars_fv D) σD τ HprojD HτD) as Hτm.
  destruct (res_fiber_from_projection_of_store_any m X τ Hτm)
    as [mfibX [HprojX HτX]].
  exists mfibX.
  split; [exact HprojX|].
  split; [exact HτX|].
  assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
  {
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_fibvars in Hscope.
    intros a Ha. apply Hscope. apply elem_of_union_l. exact Ha.
  }
  assert (HdomσD : dom (σD : StoreT) = lvars_fv D).
  {
    destruct HprojD as [HσDproj _].
    pose proof (wfworld_store_dom (res_restrict m (lvars_fv D))
      σD HσDproj) as Hdom.
    change (dom (σD : StoreT) =
      world_dom (res_restrict m (lvars_fv D) : WorldT)) in Hdom.
    rewrite Hdom, res_restrict_dom.
    apply set_eq. intros a. split.
    - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    - intros Ha. apply elem_of_intersection. split; [apply HDm; exact Ha|exact Ha].
  }
  assert (HdomσX : dom (store_restrict τ X : StoreT) =
      world_dom (m : WorldT) ∩ X).
  {
    change (dom (storeA_restrict τ X : gmap atom V) =
      world_dom (m : WorldT) ∩ X).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m τ Hτm).
    reflexivity.
  }
  assert (Hdom_sub :
      dom (σD : StoreT) ⊆ dom (store_restrict τ X : StoreT)).
  {
    intros a Ha.
    rewrite HdomσX.
    apply elem_of_intersection. split.
    - apply HDm. rewrite <- HdomσD. exact Ha.
    - apply HfvX.
      rewrite formula_fv_fibvars.
      apply elem_of_union_l. rewrite <- HdomσD. exact Ha.
  }
  assert (HτD_restrict :
      store_restrict τ (dom (σD : StoreT)) = σD).
  { eapply res_fiber_from_projection_store_restrict; eauto. }
  assert (HσX_D :
      store_restrict (store_restrict τ X : StoreT) (dom (σD : StoreT)) =
      σD).
  {
    pose proof (res_fiber_from_projection_store_restrict
      m mfibX X (store_restrict τ X) τ HprojX HτX) as HτX_restrict.
    assert (HτX_full :
        (storeA_restrict τ (dom (store_restrict τ X : gmap atom V))
          : gmap atom V) =
        storeA_restrict (store_restrict τ X : StoreT)
          (dom (store_restrict τ X : gmap atom V))).
    {
      change ((storeA_restrict τ (dom (store_restrict τ X : StoreT))
        : StoreT) = store_restrict τ X) in HτX_restrict.
      change ((storeA_restrict τ (dom (store_restrict τ X : StoreT))
        : StoreT) =
        store_restrict (store_restrict τ X : StoreT)
          (dom (store_restrict τ X : StoreT))).
      rewrite HτX_restrict.
      symmetry. apply storeA_restrict_idemp_eq. reflexivity.
    }
    transitivity (store_restrict τ (dom (σD : StoreT))).
    - symmetry. eapply storeA_restrict_eq_mono.
      + exact Hdom_sub.
      + exact HτX_full.
    - exact HτD_restrict.
  }
  split.
  - eapply res_fiber_from_projection_subset_of_fixed;
      [exact Hdom_sub|exact HσX_D|exact HprojD|exact HprojX].
  - eapply res_fiber_from_projection_self_of_fixed.
    + exists τ. split; [exact HτX|].
      rewrite <- HdomσD. exact HτD_restrict.
    + intros ρ HρX.
      assert (HρD : (mfibD : WorldT) ρ).
      {
        eapply (proj2 (res_fiber_from_projection_subset_of_fixed
          m mfibX mfibD (lvars_fv D) X σD (store_restrict τ X)
          Hdom_sub HσX_D HprojD HprojX)).
        exact HρX.
      }
      eapply res_fiber_from_projection_store_restrict; eauto.
Qed.

End FormulaFiberwise.
