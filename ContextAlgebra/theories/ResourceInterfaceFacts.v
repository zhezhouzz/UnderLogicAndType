From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra ResourceExtension ResourceInterfaceCore.
From Stdlib Require Import Logic.ProofIrrelevance.

(** * Atom-keyed resource interface facts *)

Section ResourceInterface.

Context {V : Type} `{ValueSig V}.

Local Notation StoreT := (gmap atom V) (only parsing).
Local Notation World := (@World V).
Local Notation WfWorld := (@WfWorld V).
Local Notation LWorld := (@LWorld V).
Local Notation LWfWorld := (@LWfWorld V).

Lemma world_ext (m1 m2 : World) :
  world_dom m1 = world_dom m2 →
  (∀ σ, m1 σ ↔ m2 σ) →
  m1 = m2.
Proof. apply worldA_ext. Qed.

Lemma wfworld_ext (w1 w2 : WfWorld) :
  (w1 : World) = (w2 : World) →
  w1 = w2.
Proof. apply wfworldA_ext. Qed.

Lemma wfworld_store_dom (w : WfWorld) (σ : StoreT) :
  w σ → dom σ = world_dom (w : World).
Proof. apply wfworldA_store_dom. Qed.

Lemma wfworld_eq_by_dom_stores (m n : WfWorld) :
  world_dom (m : World) = world_dom (n : World) ->
  (forall σ, (m : World) σ <-> (n : World) σ) ->
  m = n.
Proof.
  intros Hdom Hstores.
  apply wfworld_ext. apply world_ext; assumption.
Qed.

Lemma raw_le_dom (m1 m2 : World) :
  raw_le m1 m2 →
  world_dom m1 ⊆ world_dom m2.
Proof. apply rawA_le_dom. Qed.

Lemma raw_le_refl (w : WfWorld) :
  raw_le w w.
Proof. apply rawA_le_refl. exact (world_wf w). Qed.

Lemma res_subset_refl (w : WfWorld) : res_subset w w.
Proof. apply resA_subset_refl. Qed.

Lemma raw_compat_unit_r (m : World) : world_compat m raw_unit.
Proof. apply rawA_compat_unit_r. Qed.

Lemma wf_singleton_world (σ : StoreT) : wf_world (singleton_world σ).
Proof. apply wf_singleton_worldA. Qed.

Lemma res_atom_swap_singleton_world x y (σ : StoreT) :
  res_atom_swap x y
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) =
  (exist _ (singleton_world (storeA_swap x y σ))
    (wf_singleton_world (storeA_swap x y σ)) : WfWorld).
Proof.
  apply wfworld_ext. apply world_ext.
  - rewrite world_dom_res_atom_swap.
    unfold singleton_world. cbn [worldA_dom singleton_worldA].
    change (set_swap x y (dom (σ : StoreT)) =
      dom (storeA_swap x y σ : StoreT)).
    rewrite storeA_swap_dom. reflexivity.
  - intros τ. split.
    + intros [σ0 [Hσ0 Hτ]]. destruct Hσ0. destruct Hτ. reflexivity.
    + intros ->. exists σ. split; reflexivity.
Qed.

Lemma res_fiber_from_projection_empty_store_dom
    (m mfib : WfWorld) (σ : StoreT) :
  res_fiber_from_projection m ∅ σ mfib ->
  dom (σ : StoreT) = ∅.
Proof.
  intros [Hproj _].
  pose proof (wfworld_store_dom (res_restrict m ∅) σ Hproj) as Hdom.
  change (dom (σ : StoreT) = world_dom (res_restrict m ∅ : World)) in Hdom.
  simpl in Hdom. set_solver.
Qed.

Lemma res_fiber_from_projection_store_dom_subset
    (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  dom (σ : StoreT) ⊆ X.
Proof.
  intros [Hproj _] a Ha.
  pose proof (wfworld_store_dom (res_restrict m X) σ Hproj) as Hdom.
  change (dom (σ : StoreT) = world_dom (res_restrict m X : World)) in Hdom.
  rewrite Hdom in Ha. simpl in Ha.
  set_solver.
Qed.

Lemma res_fiber_from_projection_store_source
    (m mfib : WfWorld) (X : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  (m : World) τ.
Proof.
  intros [_ Hfib] Hτ.
  destruct mfib as [wmfib Hwfib].
  cbn [raw_world raw_worldA world_stores] in Hτ, Hfib.
  change (wmfib = rawA_fiber (m : World) σ) in Hfib.
  change (wmfib τ) in Hτ.
  rewrite Hfib in Hτ.
  exact (proj1 Hτ).
Qed.

Lemma res_fiber_from_projection_store_restrict
    (m mfib : WfWorld) (X : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  store_restrict τ (dom (σ : StoreT)) = σ.
Proof.
  intros [Hproj Hfib] Hτ.
  destruct mfib as [wmfib Hwfib].
  cbn [raw_world raw_worldA world_stores] in Hτ, Hfib.
  change (wmfib = rawA_fiber (m : World) σ) in Hfib.
  change (wmfib τ) in Hτ.
  rewrite Hfib in Hτ.
  destruct Hτ as [_ Hτ].
  exact Hτ.
Qed.

Lemma res_fiber_from_projection_world_dom
    (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  world_dom (mfib : World) = world_dom (m : World).
Proof.
  intros [_ Hfib].
  pose proof (f_equal world_dom Hfib) as Hdom.
  cbn [raw_fiber rawA_fiber world_dom worldA_dom] in Hdom.
  exact Hdom.
Qed.

Lemma res_fiber_from_projection_fresh_eq
    (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  X ## world_dom (m : World) ->
  res_fiber_from_projection m X σ mfib ->
  mfib = m.
Proof.
  intros Hdisj Hfib.
  apply wfworld_ext. apply world_ext.
  - rewrite (res_fiber_from_projection_world_dom m mfib X σ Hfib).
    reflexivity.
  - intros τ. split.
    + intros Hτ.
      eapply res_fiber_from_projection_store_source; eauto.
    + intros Hτ.
      destruct Hfib as [Hσproj Hfib_eq].
      change ((mfib : World) = raw_fiber (m : World) σ) in Hfib_eq.
      rewrite Hfib_eq.
      split; [exact Hτ|].
      assert (Hdomσ : dom (σ : StoreT) = ∅).
      {
        pose proof (wfworld_store_dom (res_restrict m X) σ Hσproj)
          as Hdom.
        change (dom (σ : StoreT) =
          world_dom (res_restrict m X : World)) in Hdom.
        rewrite Hdom.
        change (world_dom (res_restrict m X : World))
          with (world_dom (m : World) ∩ X).
        clear -Hdisj. set_solver.
      }
      change (storeA_restrict τ (dom (σ : StoreT)) = (σ : StoreT)).
      rewrite Hdomσ.
      rewrite storeA_restrict_empty_set.
      symmetry.
      apply map_empty. intros a.
      apply not_elem_of_dom.
      change (a ∉ dom (σ : StoreT)).
      rewrite Hdomσ. set_solver.
Qed.

Lemma res_fiber_from_projection_store_restrict_input
    (m mfib : WfWorld) (X : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  store_restrict τ X = σ.
Proof.
  intros Hproj Hτ.
  pose proof (res_fiber_from_projection_store_source
    m mfib X σ τ Hproj Hτ) as Hτm.
  pose proof (res_fiber_from_projection_store_restrict
    m mfib X σ τ Hproj Hτ) as Hτdom.
  change ((store_restrict τ (dom (σ : StoreT)) : StoreT) = σ) in Hτdom.
  pose proof (wfworld_store_dom m τ Hτm) as Hdomτ.
  change (dom (τ : StoreT) = world_dom (m : World)) in Hdomτ.
  destruct Hproj as [Hσproj _].
  pose proof (wfworld_store_dom (res_restrict m X) σ Hσproj)
    as Hdomσ.
  change (dom (σ : StoreT) =
    world_dom (res_restrict m X : World)) in Hdomσ.
  simpl in Hdomσ.
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
  - destruct (σ !! a) as [v|] eqn:Hσa; [|reflexivity].
    exfalso.
    assert (Haσ : a ∈ dom (σ : StoreT)).
    { change (a ∈ dom (σ : gmap atom V)).
      apply elem_of_dom. exists v. exact Hσa. }
    rewrite Hdomσ in Haσ. simpl in Haσ.
    set_solver.
Qed.

Lemma res_fiber_from_projection_of_store_any_domain
    (m : WfWorld) (X : aset) (σ : StoreT) :
  (m : World) σ ->
  exists mfib,
    res_fiber_from_projection m X (store_restrict σ X) mfib /\
    (mfib : World) σ.
Proof.
  intros Hσ.
  set (σX := store_restrict σ X).
  assert (HdomσX : dom (σX : StoreT) = world_dom (m : World) ∩ X).
  {
    subst σX.
    change (dom (storeA_restrict σ X : gmap atom V) =
      world_dom (m : World) ∩ X).
    rewrite storeA_restrict_dom.
    rewrite (wfworld_store_dom m σ Hσ).
    reflexivity.
  }
  assert (Hne :
      exists σ0,
        (m : World) σ0 /\
        storeA_restrict σ0 (dom (σX : StoreT)) = σX).
  {
    exists σ. split; [exact Hσ|].
    subst σX.
    rewrite HdomσX.
    apply storeA_map_eq. intros a.
    rewrite !storeA_restrict_lookup.
    destruct (decide (a ∈ world_dom (m : World) ∩ X)) as [Ha|Ha].
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
    destruct (decide (a ∈ world_dom (m : World) ∩ X)) as [Ha|Ha].
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

Lemma res_fiber_from_projection_store_restrict_substore
    (m mfib : WfWorld) (X Y : aset) (σ τ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  (mfib : World) τ ->
  store_restrict τ (dom (store_restrict σ Y : StoreT)) =
    store_restrict σ Y.
Proof.
  intros Hproj Hτ.
  pose proof (res_fiber_from_projection_store_restrict
    m mfib X σ τ Hproj Hτ) as Hfixed.
  apply storeA_map_eq. intros a.
  rewrite !storeA_restrict_lookup.
  destruct (decide (a ∈ dom (store_restrict σ Y : StoreT))) as [Ha|Ha].
  - apply elem_of_dom in Ha as [v Hv].
    apply storeA_restrict_lookup_some in Hv as [HaY Hσa].
    assert (Hτa : τ !! a = Some v).
    {
      assert (Hτrestrict :
        (store_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
        Some v).
      { rewrite Hfixed. exact Hσa. }
      apply storeA_restrict_lookup_some in Hτrestrict as [_ Hτa].
      exact Hτa.
    }
    rewrite decide_True by exact HaY.
    rewrite Hσa. exact Hτa.
  - destruct (decide (a ∈ Y)) as [HaY|HaY]; [|reflexivity].
    destruct (σ !! a) as [v|] eqn:Hσa; [|reflexivity].
    exfalso. apply Ha. apply elem_of_dom. exists v.
    apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσa HaY).
Qed.

Lemma res_fiber_from_projection_drop_fixed_domain
    (m mfib : WfWorld) (Y : aset) (σ σfix : StoreT) :
  (forall τ, (m : World) τ ->
    store_restrict τ (dom (σfix : StoreT)) = σfix) ->
  res_fiber_from_projection m Y σ mfib ->
  res_fiber_from_projection m
    (Y ∖ dom (σfix : StoreT))
    (store_restrict σ (Y ∖ dom (σfix : StoreT))) mfib.
Proof.
  intros Hfixed [Hproj Hfib].
  destruct Hproj as [τ0 [Hτ0 Hτ0Y]].
  split.
  - exists τ0. split; [exact Hτ0|].
    rewrite <- Hτ0Y.
    rewrite storeA_restrict_restrict.
    replace (Y ∩ (Y ∖ dom (σfix : StoreT)))
      with (Y ∖ dom (σfix : StoreT)) by set_solver.
    reflexivity.
  - destruct mfib as [wmfib Hwfib].
    cbn [proj1_sig] in Hfib |- *.
    change (wmfib = rawA_fiber (m : World) σ) in Hfib.
    change (wmfib =
      rawA_fiber (m : World)
        (store_restrict σ (Y ∖ dom (σfix : StoreT)))).
    rewrite Hfib.
    apply world_ext.
    + reflexivity.
    + intros τ. cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores].
      split.
      * intros [Hτ HτY]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        rewrite !storeA_restrict_lookup.
        destruct (decide
          (a ∈ dom (storeA_restrict σ (Y ∖ dom (σfix : StoreT)) :
            gmap atom V)))
          as [Haσres|Haσres].
        -- destruct (decide (a ∈ Y ∖ dom (σfix : StoreT))) as [HaYfix|Hbad].
           2:{
             exfalso. apply Hbad.
             pose proof Haσres as Haσres_dom.
             rewrite storeA_restrict_dom in Haσres_dom.
             set_solver.
           }
           pose proof Haσres as Haσres_dom.
           rewrite storeA_restrict_dom in Haσres_dom.
           assert (Haσ : a ∈ dom (σ : StoreT)) by set_solver.
           destruct (σ !! a) as [va|] eqn:Hσa.
           2:{ apply not_elem_of_dom in Hσa. contradiction. }
           assert (Hτa : τ !! a = Some va).
           {
             assert ((storeA_restrict τ (dom (σ : StoreT)) : StoreT) !! a =
               Some va) as Hrt.
             { rewrite HτY. exact Hσa. }
             apply storeA_restrict_lookup_some in Hrt as [_ Hrt].
             exact Hrt.
           }
           exact Hτa.
        -- destruct (decide (a ∈ Y ∖ dom (σfix : StoreT))) as [HaYfix|_];
             [|reflexivity].
           assert (Haσnone : σ !! a = None).
           {
             apply not_elem_of_dom.
             intros Haσ.
             apply Haσres.
             rewrite storeA_restrict_dom.
             set_solver.
           }
           symmetry. exact Haσnone.
      * intros [Hτ Hτres]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        destruct (decide (a ∈ dom (σ : StoreT))) as [Haσ|Haσ].
        2:{
          rewrite storeA_restrict_lookup_none_r by exact Haσ.
          apply not_elem_of_dom in Haσ. symmetry. exact Haσ.
        }
        rewrite storeA_restrict_lookup.
        destruct (decide (a ∈ dom (σ : StoreT))) as [_|Hbad];
          [|contradiction].
        pose proof (wfworld_store_dom m τ0 Hτ0) as Hdomτ0.
        change (dom (τ0 : StoreT) = world_dom (m : World)) in Hdomτ0.
        assert (HaY : a ∈ Y).
        {
          rewrite <- Hτ0Y in Haσ.
          rewrite storeA_restrict_dom, Hdomτ0 in Haσ.
          set_solver.
        }
        destruct (decide (a ∈ dom (σfix : StoreT))) as [Hafix|Hafix].
        -- assert (Hτfix : τ !! a = σfix !! a).
           {
             rewrite <- (Hfixed τ Hτ).
             symmetry.
             change ((storeA_restrict τ (dom (σfix : StoreT)) : StoreT) !! a =
               τ !! a).
             destruct (τ !! a) as [va|] eqn:Hτa.
	             - apply (storeA_restrict_lookup_some_2 _ _ _ _ Hτa Hafix).
             - apply storeA_restrict_lookup_none_l. exact Hτa.
           }
           assert (Hτ0fix : τ0 !! a = σfix !! a).
           {
             rewrite <- (Hfixed τ0 Hτ0).
             symmetry.
             change ((storeA_restrict τ0 (dom (σfix : StoreT)) : StoreT) !! a =
               τ0 !! a).
             destruct (τ0 !! a) as [va|] eqn:Hτ0a.
	             - apply (storeA_restrict_lookup_some_2 _ _ _ _ Hτ0a Hafix).
             - apply storeA_restrict_lookup_none_l. exact Hτ0a.
           }
           transitivity (σfix !! a); [exact Hτfix|].
           transitivity (τ0 !! a); [symmetry; exact Hτ0fix|].
           rewrite <- Hτ0Y.
           rewrite storeA_restrict_lookup.
           destruct (decide (a ∈ Y)) as [_|Hbad]; [reflexivity|contradiction].
        -- assert (HaYfix : a ∈ Y ∖ dom (σfix : StoreT)) by set_solver.
           assert (Haσres :
             a ∈ dom (storeA_restrict σ (Y ∖ dom (σfix : StoreT)) :
               gmap atom V)).
           { rewrite storeA_restrict_dom. set_solver. }
           transitivity
             ((storeA_restrict τ
               (dom (storeA_restrict σ (Y ∖ dom (σfix : StoreT)) :
                 gmap atom V)) : StoreT) !! a).
           ++ symmetry.
              destruct (τ !! a) as [va|] eqn:Hτa.
	              ** apply (storeA_restrict_lookup_some_2 _ _ _ _ Hτa Haσres).
              ** apply storeA_restrict_lookup_none_l. exact Hτa.
           ++ rewrite Hτres.
              destruct (σ !! a) as [va|] eqn:Hσa.
	              ** apply (storeA_restrict_lookup_some_2 _ _ _ _ Hσa HaYfix).
              ** apply storeA_restrict_lookup_none_l. exact Hσa.
Qed.

Lemma res_fiber_from_projection_add_fixed_domain
    (m mfib : WfWorld) (Y : aset) (σres σfix : StoreT) :
  (forall τ, (m : World) τ ->
    store_restrict τ (dom (σfix : StoreT)) = σfix) ->
  res_fiber_from_projection m
    (Y ∖ dom (σfix : StoreT)) σres mfib ->
  res_fiber_from_projection m Y
    (store_restrict σfix Y ∪ σres) mfib.
Proof.
  intros Hfixed Hres.
  pose proof (res_fiber_from_projection_store_dom_subset
    m mfib (Y ∖ dom (σfix : StoreT)) σres Hres) as Hres_dom.
  destruct Hres as [[τ0 [Hτ0 Hτ0res]] Hfib].
  split.
  - exists τ0. split; [exact Hτ0|].
    apply storeA_map_eq. intros a.
    rewrite storeA_restrict_lookup.
    destruct (decide (a ∈ Y)) as [HaY|HaY].
    + destruct (decide (a ∈ dom (σfix : StoreT))) as [Hafix|Hafix].
      * assert (Hτ0fix_a : τ0 !! a = σfix !! a).
        {
          apply elem_of_dom in Hafix as [va Hva].
          assert (Hlook :
              (store_restrict τ0 (dom (σfix : StoreT)) : StoreT) !! a =
              Some va).
          { rewrite Hfixed by exact Hτ0. exact Hva. }
          apply storeA_restrict_lookup_some in Hlook as [_ Hτ0a].
          change ((τ0 : gmap atom V) !! a =
            (σfix : gmap atom V) !! a).
          exact (eq_trans Hτ0a (eq_sym Hva)).
        }
        assert (Hafix_dom : a ∈ dom (σfix : StoreT)) by exact Hafix.
        apply elem_of_dom in Hafix as [va Hva].
        transitivity (Some va).
        -- change ((τ0 : gmap atom V) !! a = Some va).
           rewrite Hτ0fix_a. exact Hva.
        -- symmetry.
	           transitivity ((store_restrict σfix Y : StoreT) !! a).
		           ++ apply lookup_union_l.
		              apply not_elem_of_dom.
		              intros Hares.
		              pose proof (Hres_dom a Hares) as HaresYfix.
		              apply elem_of_difference in HaresYfix as [_ Hanotfix].
		              exact (Hanotfix Hafix_dom).
	           ++ assert (HfixY :
	                (store_restrict σfix Y : StoreT) !! a = Some va).
		              { eapply (storeA_restrict_lookup_some_2 _ _ _ _ Hva HaY). }
	              exact HfixY.
      * assert (Hτ0res_a : τ0 !! a = σres !! a).
        {
          destruct (σres !! a) as [va|] eqn:Hresa.
          - assert (Hlook :
                (store_restrict τ0 (Y ∖ dom (σfix : StoreT)) : StoreT) !! a =
                Some va).
	            { rewrite Hτ0res. exact Hresa. }
	            apply storeA_restrict_lookup_some in Hlook as [_ Hτ0a].
	            exact Hτ0a.
	          - assert (Hlook :
	                (store_restrict τ0 (Y ∖ dom (σfix : StoreT)) : StoreT) !! a =
	                None).
	            { rewrite Hτ0res. exact Hresa. }
	            destruct (τ0 !! a) as [va|] eqn:Hτ0a; [|reflexivity].
	            exfalso.
	            assert (Hsome :
	                (store_restrict τ0 (Y ∖ dom (σfix : StoreT)) : StoreT)
                  !! a = Some va).
	            {
	              eapply storeA_restrict_lookup_some_2;
	                [exact Hτ0a|set_solver].
	            }
	            rewrite Hlook in Hsome. discriminate.
        }
	        transitivity (σres !! a); [exact Hτ0res_a|].
	        symmetry.
	        apply lookup_union_r.
	        apply storeA_restrict_lookup_none_l.
	        apply not_elem_of_dom. exact Hafix.
    + symmetry.
      apply map_lookup_union_None. split.
      * apply storeA_restrict_lookup_none_r. exact HaY.
      * apply not_elem_of_dom.
        intros Hares. apply Hres_dom in Hares. set_solver.
  - destruct mfib as [wmfib Hwfib].
    cbn [proj1_sig] in Hfib |- *.
    change (wmfib = rawA_fiber (m : World) σres) in Hfib.
    change (wmfib =
      rawA_fiber (m : World) (store_restrict σfix Y ∪ σres)).
    rewrite Hfib.
    apply world_ext.
    + reflexivity.
    + intros τ. cbn [raw_fiber rawA_fiber raw_world raw_worldA world_stores].
      split.
      * intros [Hτ Hτres]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        destruct (decide
          (a ∈ dom (store_restrict σfix Y ∪ σres : StoreT))) as [Hafull|Hafull].
	        -- rewrite storeA_restrict_lookup.
	           destruct (decide (a ∈ dom (store_restrict σfix Y ∪ σres : StoreT)))
	             as [_|Hbad]; [|contradiction].
	           destruct ((store_restrict σfix Y : StoreT) !! a) as [vfix|] eqn:Hfixlook.
	           ++ pose proof Hfixlook as Hfixlook_some.
	              apply storeA_restrict_lookup_some in Hfixlook_some
	                as [HaYfix Hσfixa].
	              assert (Hτfix_a : τ !! a = Some vfix).
	              {
	                assert (Hlook :
	                    (store_restrict τ (dom (σfix : StoreT)) : StoreT) !! a =
	                    Some vfix).
	                { rewrite Hfixed by exact Hτ. exact Hσfixa. }
	                apply storeA_restrict_lookup_some in Hlook as [_ Hτa].
	                exact Hτa.
	              }
	              transitivity (Some vfix); [exact Hτfix_a|].
	              symmetry.
	              transitivity ((store_restrict σfix Y : StoreT) !! a).
	              ** apply lookup_union_l.
	                 apply not_elem_of_dom.
	                 intros Hares.
	                 pose proof (Hres_dom a Hares) as HaresYfix.
	                 apply elem_of_difference in HaresYfix as [_ Hanotfix].
	                 apply Hanotfix. eapply elem_of_dom_2. exact Hσfixa.
	              ** exact Hfixlook.
	           ++ pose proof Hafull as Hafull_dom.
	              assert (Hares : a ∈ dom (σres : StoreT)).
	              {
	                destruct (σres !! a) as [vres|] eqn:Hreslook.
	                - eapply elem_of_dom_2. exact Hreslook.
	                - exfalso.
	                  assert (Hunion_none :
	                    (store_restrict σfix Y ∪ σres : StoreT) !! a = None).
	                  {
	                    apply map_lookup_union_None. split; assumption.
	                  }
	                  apply not_elem_of_dom in Hunion_none.
	                  exact (Hunion_none Hafull_dom).
	              }
	              assert (Hτres_a : τ !! a = σres !! a).
	              {
	                destruct (σres !! a) as [vres|] eqn:Hreslook.
	                - assert (Hlook :
	                    (store_restrict τ (dom (σres : StoreT)) : StoreT) !! a =
	                    Some vres).
	                  { rewrite Hτres. exact Hreslook. }
	                  apply storeA_restrict_lookup_some in Hlook as [_ Hτa].
	                  exact Hτa.
	                - exfalso. apply not_elem_of_dom in Hreslook.
	                  contradiction.
	              }
	              transitivity (σres !! a); [exact Hτres_a|].
	              symmetry.
	              apply lookup_union_r.
	              exact Hfixlook.
        -- rewrite storeA_restrict_lookup_none_r by exact Hafull.
           apply not_elem_of_dom in Hafull. symmetry. exact Hafull.
      * intros [Hτ Hτfull]. split; [exact Hτ|].
        apply storeA_map_eq. intros a.
        destruct (decide (a ∈ dom (σres : StoreT))) as [Hares|Hares].
        -- rewrite storeA_restrict_lookup.
           destruct (decide (a ∈ dom (σres : StoreT))) as [_|Hbad];
             [|contradiction].
	           pose proof Hares as HaresY.
	           apply Hres_dom in HaresY.
	           assert (Hanotfix : a ∉ dom (σfix : StoreT)) by set_solver.
	           apply elem_of_dom in Hares as [vres Hreslook].
	           assert (Hleft_none : (store_restrict σfix Y : StoreT) !! a = None).
	           {
	             apply storeA_restrict_lookup_none_l.
	             apply not_elem_of_dom. exact Hanotfix.
	           }
	           assert (Hfull_lookup :
	             (store_restrict σfix Y ∪ σres : StoreT) !! a = Some vres).
	           {
	             transitivity (σres !! a).
	             - apply lookup_union_r. exact Hleft_none.
	             - exact Hreslook.
	           }
	           assert (Hτa : τ !! a = Some vres).
	           {
	             assert (Hrestrict :
	               (store_restrict τ
	                 (dom (store_restrict σfix Y ∪ σres : StoreT)) : StoreT)
	               !! a = Some vres).
	             { rewrite Hτfull. exact Hfull_lookup. }
	             apply storeA_restrict_lookup_some in Hrestrict as [_ Hτa].
	             exact Hτa.
	           }
	           change ((τ : gmap atom V) !! a = (σres : gmap atom V) !! a).
	           rewrite Hτa, Hreslook. reflexivity.
        -- rewrite storeA_restrict_lookup_none_r by exact Hares.
           apply not_elem_of_dom in Hares. symmetry. exact Hares.
Qed.

Lemma res_subset_fiber_source
    (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  res_subset mfib m.
Proof.
  intros Hfib.
  split.
  - destruct Hfib as [_ Hfib_eq].
    change ((mfib : World) = raw_fiber (m : World) σ) in Hfib_eq.
    pose proof (f_equal world_dom Hfib_eq) as Hdom.
    change (world_dom (mfib : World) = world_dom (m : World)) in Hdom.
    exact Hdom.
  - intros τ Hτ.
    eapply res_fiber_from_projection_store_source; eauto.
Qed.

Lemma res_fiber_from_projection_of_store
    (m : WfWorld) (X : aset) (σ : StoreT) :
  X ⊆ world_dom (m : World) ->
  (m : World) σ ->
  exists mfib,
    res_fiber_from_projection m X (store_restrict σ X) mfib /\
    (mfib : World) σ.
Proof.
  intros HX Hσ.
  set (σX := store_restrict σ X).
  assert (HdomσX : dom (σX : StoreT) = X).
  {
    subst σX.
    change (dom (storeA_restrict σ X : gmap atom V) = X).
    rewrite (storeA_restrict_dom σ X).
    rewrite (wfworld_store_dom m σ Hσ).
    apply set_eq. intros a. split.
    - intros Ha. apply elem_of_intersection in Ha as [_ Ha]. exact Ha.
    - intros Ha. apply elem_of_intersection. split; [apply HX|]; exact Ha.
  }
  assert (Hne :
      exists σ0,
        (m : World) σ0 /\
        storeA_restrict σ0 (dom (σX : StoreT)) = σX).
  {
    exists σ. split; [exact Hσ|].
    rewrite HdomσX. reflexivity.
  }
  exists (resA_fiber m σX Hne).
  split.
  - split.
    + exists σ. split; [exact Hσ|reflexivity].
    + reflexivity.
  - cbn [raw_world raw_worldA world_stores rawA_fiber].
    split; [exact Hσ|].
    change (storeA_restrict σ (dom (σX : StoreT)) = σX).
    rewrite HdomσX.
    subst σX. reflexivity.
Qed.

Lemma res_fiber_from_projection_atom_swap
    x y (m mfib : WfWorld) (X : aset) (σ : StoreT) :
  res_fiber_from_projection m X σ mfib ->
  res_fiber_from_projection
    (res_atom_swap x y m) (set_swap x y X)
    (storeA_swap x y σ) (res_atom_swap x y mfib).
Proof.
  intros [Hproj Hfib]. split.
  - destruct Hproj as [σ0 [Hσ0 Hrestrict]]. subst σ.
    exists (storeA_swap x y σ0). split.
    + exists σ0. split; [exact Hσ0 | reflexivity].
    + apply storeA_restrict_swap.
  - apply world_ext.
    + pose proof (f_equal world_dom Hfib) as Hdomfib.
      simpl in Hdomfib.
      change (world_dom (mfib : World) = world_dom (m : World)) in Hdomfib.
      change (set_swap x y (world_dom (mfib : World)) =
        set_swap x y (world_dom (m : World))).
      rewrite Hdomfib. reflexivity.
    + intros τ. simpl. split.
      * intros [τ0 [Hmfib Hτ]].
        subst τ.
        rewrite Hfib in Hmfib.
        destruct Hmfib as [Hm Hrestrict].
        split.
        -- exists τ0. split; [exact Hm | reflexivity].
        -- rewrite storeA_swap_dom.
           change (storeA_restrict (storeA_swap x y τ0)
             (set_swap x y (dom σ)) = storeA_swap x y σ).
           rewrite storeA_restrict_swap.
           rewrite Hrestrict. reflexivity.
      * intros [[τ0 [Hm Hτ]] Hrestrict].
        subst τ.
        exists τ0. split.
        -- rewrite Hfib. split; [exact Hm |].
           rewrite storeA_swap_dom in Hrestrict.
           change (storeA_restrict (storeA_swap x y τ0)
             (set_swap x y (dom σ)) = storeA_swap x y σ) in Hrestrict.
           rewrite storeA_restrict_swap in Hrestrict.
           apply (f_equal (storeA_swap x y)) in Hrestrict.
           rewrite !storeA_swap_involutive in Hrestrict.
           exact Hrestrict.
        -- reflexivity.
Qed.



(** * Concrete resource key action and order interface lemmas *)




Lemma res_restrict_restrict_eq (w : WfWorld) (X Y : aset) :
  res_restrict (res_restrict w X) Y =
  res_restrict w (X ∩ Y).
Proof. apply resA_restrict_restrict_eq. Qed.

Lemma res_restrict_dom (w : WfWorld) (X : aset) :
  world_dom (res_restrict w X : World) = world_dom (w : World) ∩ X.
Proof. reflexivity. Qed.

Lemma opened_world_dom_contains_slot
    (m my : WfWorld) y :
  world_dom (my : World) = world_dom (m : World) ∪ {[y]} ->
  y ∈ world_dom (my : World).
Proof.
  intros Hdom.
  rewrite Hdom. apply elem_of_union_r. apply elem_of_singleton_2.
  reflexivity.
Qed.

Lemma singleton_subset_world_dom (m : WfWorld) z :
  z ∈ world_dom (m : World) ->
  ({[z]} : aset) ⊆ world_dom (m : World).
Proof.
  intros Hzm a Ha. apply elem_of_singleton in Ha. subst a. exact Hzm.
Qed.

Lemma fvar_in_singleton_restrict_dom
    (m my : WfWorld) (σ : StoreT) x y :
  x ∈ world_dom (m : World) ->
  (my : World) σ ->
  world_dom (my : World) = world_dom (m : World) ∪ {[y]} ->
  x ∈ dom (storeA_restrict σ ({[x]} : aset) : gmap atom V).
Proof.
  intros Hxm Hσ Hdom.
  rewrite storeA_restrict_dom.
  rewrite (wfworld_store_dom my σ Hσ), Hdom.
  apply elem_of_intersection. split.
  - apply elem_of_union_l. exact Hxm.
  - apply elem_of_singleton. reflexivity.
Qed.

Lemma res_restrict_le (w : WfWorld) (X : aset) :
  res_restrict w X ⊑ w.
Proof. apply resA_restrict_le. Qed.

Lemma res_restrict_mono (w : WfWorld) (X Y : aset) :
  X ⊆ Y →
  res_restrict w X ⊑ res_restrict w Y.
Proof. apply resA_restrict_mono. Qed.

Lemma res_restrict_eq_of_le (m n : WfWorld) :
  m ⊑ n →
  res_restrict n (world_dom (m : World)) = m.
Proof. apply resA_restrict_eq_of_le. Qed.

Lemma res_le_of_restrict_eq (m n p : WfWorld) :
  m ⊑ n ->
  res_restrict p (world_dom (n : World)) = n ->
  m ⊑ p.
Proof.
  intros Hmn Hnp.
  assert (Hn_p : n ⊑ p).
  {
    rewrite <- Hnp. apply res_restrict_le.
  }
  etransitivity; eauto.
Qed.

Lemma res_le_of_projection_eq (m p : WfWorld) :
  res_restrict p (world_dom (m : World)) = m ->
  m ⊑ p.
Proof.
  intros Hproj.
  eapply res_le_of_restrict_eq; [apply raw_le_refl|exact Hproj].
Qed.

Lemma res_le_store_lift
    (m n : WfWorld) (σ : StoreT) :
  m ⊑ n ->
  (m : World) σ ->
  exists σn,
    (n : World) σn /\
    store_restrict σn (world_dom (m : World)) = σ.
Proof.
  intros Hle Hσ.
  pose proof (res_restrict_eq_of_le m n Hle) as Hrestrict.
  assert (Hσrestrict :
      (res_restrict n (world_dom (m : World)) : World) σ).
  { rewrite Hrestrict. exact Hσ. }
  cbn [res_restrict raw_world raw_worldA world_stores] in Hσrestrict.
  destruct Hσrestrict as [σn [Hσn Hσn_restrict]].
  exists σn. split; [exact Hσn|exact Hσn_restrict].
Qed.

Lemma res_restrict_self_dom (m : WfWorld) (X : aset) :
  res_restrict m (world_dom (res_restrict m X : World)) =
  res_restrict m X.
Proof.
  apply res_restrict_eq_of_le. apply res_restrict_le.
Qed.

Lemma res_restrict_delete_notin (m : WfWorld) x :
  x ∉ world_dom
    (res_restrict m (world_dom (m : World) ∖ {[x]}) : World).
Proof.
  rewrite res_restrict_dom. better_set_solver.
Qed.

Lemma res_restrict_delete_insert_dom (m : WfWorld) x :
  x ∈ world_dom (m : World) ->
  world_dom (m : World) =
    world_dom
      (res_restrict m (world_dom (m : World) ∖ {[x]}) : World) ∪ {[x]}.
Proof.
  intros Hx.
  rewrite res_restrict_dom.
  replace (world_dom (m : World) ∩
    (world_dom (m : World) ∖ {[x]}))
    with (world_dom (m : World) ∖ {[x]}) by better_set_solver.
  apply set_eq. intros z. split.
  - intros Hz.
    destruct (decide (z = x)) as [->|Hzx].
    + apply elem_of_union_r. apply elem_of_singleton. reflexivity.
    + apply elem_of_union_l. apply elem_of_difference. split; [exact Hz|].
      intros Hzsingle. apply elem_of_singleton in Hzsingle. congruence.
  - intros Hz.
    apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_difference in Hz as [Hz _]. exact Hz.
    + apply elem_of_singleton in Hz. subst z. exact Hx.
Qed.

Lemma res_restrict_le_eq (m n : WfWorld) (X : aset) :
  m ⊑ n →
  X ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X.
Proof. apply resA_restrict_le_eq. Qed.

Lemma res_restrict_eq_subset
    (m n : WfWorld) (X Y : aset) :
  Y ⊆ X →
  res_restrict m X = res_restrict n X →
  res_restrict m Y = res_restrict n Y.
Proof. apply resA_restrict_eq_subset. Qed.

Lemma res_fiber_from_projection_transport_on
    (m n nfib : WfWorld) (σ : StoreT) (D X : aset) :
  D ⊆ X →
  D ⊆ world_dom (m : World) →
  res_restrict m X = res_restrict n X →
  res_fiber_from_projection n D σ nfib →
  ∃ mfib,
    res_fiber_from_projection m D σ mfib ∧
    res_restrict mfib X = res_restrict nfib X.
Proof. apply resA_fiber_from_projection_transport_on. Qed.

Lemma world_compat_le_r (w m n : WfWorld) :
  m ⊑ n →
  world_compat w n →
  world_compat w m.
Proof. apply worldA_compat_le_r. Qed.

Lemma world_compat_restrict_l_full_r (n m : WfWorld) (S X : aset) :
  X ⊆ S →
  world_compat n (res_restrict m S) →
  world_compat (res_restrict n X) m.
Proof. apply worldA_compat_restrict_l_full_r. Qed.

Lemma world_compat_of_disjoint_dom (m n : WfWorld) :
  world_dom (m : World) ## world_dom (n : World) →
  world_compat m n.
Proof.
  intros Hdisj.
  apply disj_dom_worldA_compat.
  set_solver.
Qed.

Lemma world_compat_restrict_overlap
    (n m : WfWorld) (X Y S : aset) :
  X ∩ Y ⊆ S ->
  world_compat n (res_restrict m S) ->
  world_compat (res_restrict n X) (res_restrict m Y).
Proof. apply worldA_compat_restrict_overlap. Qed.

Definition res_pullback_subset_projection (n p : WfWorld)
    (Hsub : res_subset p (res_restrict n (world_dom (p : World)))) : WfWorld :=
  resA_pullback_subset_projection n p Hsub.

Lemma res_pullback_subset_projection_restrict (n p : WfWorld) Hsub :
  res_restrict (res_pullback_subset_projection n p Hsub)
    (world_dom (p : World)) = p.
Proof. apply resA_pullback_subset_projection_restrict. Qed.

Lemma res_pullback_subset_projection_subset (n p : WfWorld) Hsub :
  res_subset (res_pullback_subset_projection n p Hsub) n.
Proof. apply resA_pullback_subset_projection_subset. Qed.

Lemma res_sum_pullback_subset_projection_full
    (n n1 n2 : WfWorld) (Hdef : raw_sum_defined n1 n2) :
  res_sum n1 n2 Hdef ⊑ n →
  ∃ (Hsub1 : res_subset n1 (res_restrict n (world_dom (n1 : World))))
    (Hsub2 : res_subset n2 (res_restrict n (world_dom (n2 : World))))
    (Hdef_full : raw_sum_defined
      (res_pullback_subset_projection n n1 Hsub1)
      (res_pullback_subset_projection n n2 Hsub2)),
    res_sum
      (res_pullback_subset_projection n n1 Hsub1)
      (res_pullback_subset_projection n n2 Hsub2)
      Hdef_full ⊑ n.
Proof. apply resA_sum_pullback_subset_projection_full. Qed.

Lemma res_product_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hc : world_compat w1 w2) (Hc' : world_compat w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_product w1 w2 Hc ⊑ res_product w1' w2' Hc'.
Proof. apply resA_product_le_mono. Qed.

Lemma res_product_dom (w1 w2 : WfWorld)
    (Hc : world_compat w1 w2) :
  world_dom (res_product w1 w2 Hc : World) =
  world_dom (w1 : World) ∪ world_dom (w2 : World).
Proof. reflexivity. Qed.

Lemma res_product_restrict_singleton_delete_dom
    (marg mframe : WfWorld) x
    (Hc : world_compat (res_restrict marg ({[x]} : aset))
      (res_restrict mframe (world_dom (mframe : World) ∖ {[x]}))) :
  x ∈ world_dom (marg : World) ->
  world_dom
    (res_product (res_restrict marg ({[x]} : aset))
      (res_restrict mframe (world_dom (mframe : World) ∖ {[x]})) Hc
      : World) =
    world_dom
      (res_restrict mframe (world_dom (mframe : World) ∖ {[x]}) : World) ∪
      {[x]}.
Proof.
  intros Hx.
  rewrite !res_restrict_dom.
  change ((world_dom (marg : World) ∩ {[x]}) ∪
    (world_dom (mframe : World) ∩ (world_dom (mframe : World) ∖ {[x]})) =
    (world_dom (mframe : World) ∩ (world_dom (mframe : World) ∖ {[x]})) ∪
      {[x]}).
  assert (Hsingle :
      world_dom (marg : World) ∩ ({[x]} : aset) = ({[x]} : aset)).
  {
    apply set_eq. intros z. split.
    - intros Hz. apply elem_of_intersection in Hz as [_ Hz]. exact Hz.
    - intros Hz. apply elem_of_intersection. split; [|exact Hz].
      apply elem_of_singleton in Hz. subst z. exact Hx.
  }
  rewrite Hsingle.
  apply set_eq. intros z. split.
  - intros Hz. apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_union_r. exact Hz.
    + apply elem_of_union_l. exact Hz.
  - intros Hz. apply elem_of_union in Hz as [Hz|Hz].
    + apply elem_of_union_r. exact Hz.
    + apply elem_of_union_l. exact Hz.
Qed.

Lemma res_subset_lift_under_projection_on
    (m n mu : WfWorld) (X : aset) :
  res_restrict m X = res_restrict n X →
  res_subset mu m →
  ∃ nu : WfWorld,
    res_subset nu n ∧ res_restrict mu X ⊑ nu.
Proof. apply resA_subset_lift_under_projection_on. Qed.

Lemma res_subset_lift_over_projection_on
    (m n mo : WfWorld) (X : aset) :
  res_restrict m X = res_restrict n X →
  res_subset m mo →
  ∃ no : WfWorld,
    res_subset n no ∧ res_restrict mo X ⊑ no.
Proof. apply resA_subset_lift_over_projection_on. Qed.

Lemma res_product_restrict_wand_le
    (n m : WfWorld) (S X Y : aset)
    (Hc_small : world_compat (res_restrict n X) m)
    (Hc : world_compat n (res_restrict m S)) :
  Y ⊆ S →
  Y ⊆ world_dom (m : World) →
  res_restrict (res_product (res_restrict n X) m Hc_small) Y ⊑
  res_product n (res_restrict m S) Hc.
Proof. apply resA_product_restrict_wand_le. Qed.

Lemma res_product_restrict_frame_common_eq
    (n m : WfWorld) (X S C Y : aset)
    (Hc_common : world_compat (res_restrict n X) (res_restrict m C))
    (Hc_tgt : world_compat n (res_restrict m S)) :
  S ⊆ C ->
  Y ⊆ (X ∩ world_dom (n : World)) ∪
        (S ∩ world_dom (m : World)) ->
  res_restrict
    (res_product (res_restrict n X) (res_restrict m C) Hc_common)
    Y =
    res_restrict (res_product n (res_restrict m S) Hc_tgt) Y.
Proof. apply resA_product_restrict_frame_common_eq. Qed.

Lemma res_product_restrict_frame_r_eq
    (n m : WfWorld) (S Y : aset)
    (Hc : world_compat n m)
    (HcS : world_compat n (res_restrict m S)) :
  S ⊆ world_dom (m : World) ->
  Y ⊆ world_dom (n : World) ∪ S ->
  res_restrict (res_product n (res_restrict m S) HcS) Y =
  res_restrict (res_product n m Hc) Y.
Proof.
  intros HSm HY.
  set (X := world_dom (n : World)).
  set (C := world_dom (m : World)).
  assert (Hn_full : res_restrict n X = n).
  { subst X. apply res_restrict_eq_of_le. apply raw_le_refl. }
  assert (Hm_full : res_restrict m C = m).
  { subst C. apply res_restrict_eq_of_le. apply raw_le_refl. }
  assert (Hc_common :
      world_compat (res_restrict n X) (res_restrict m C)).
  { rewrite Hn_full, Hm_full. exact Hc. }
  pose proof (res_product_restrict_frame_common_eq
    n m X S C Y Hc_common HcS ltac:(subst C; exact HSm))
    as Heq.
  assert (HY' : Y ⊆ (X ∩ world_dom (n : World)) ∪
                  (S ∩ world_dom (m : World))).
  {
    subst X. intros z Hz.
	    pose proof (HY z Hz) as HzNS.
	    apply elem_of_union in HzNS as [HzN|HzS].
	    - apply elem_of_union_l. set_solver.
	    - apply elem_of_union_r. apply elem_of_intersection.
	      split; [exact HzS|apply HSm; exact HzS].
	  }
	  specialize (Heq HY').
	  assert (Hcommon_full :
	      res_product (res_restrict n X) (res_restrict m C) Hc_common =
	      res_product n m Hc).
	  {
	    assert (Hc_nC : world_compat n (res_restrict m C)).
	    { eapply world_compat_le_r; [apply res_restrict_le|exact Hc]. }
	    transitivity (res_product n (res_restrict m C) Hc_nC).
	    - eapply res_product_l_eq. exact Hn_full.
	    - eapply res_product_r_eq. exact Hm_full.
	  }
  rewrite Hcommon_full in Heq.
  symmetry. exact Heq.
Qed.

Lemma res_product_restrict_same_le
    (m m1 m2 : WfWorld) (X : aset)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  ∃ HcX : world_compat (res_restrict m1 X) (res_restrict m2 X),
    res_product (res_restrict m1 X) (res_restrict m2 X) HcX
      ⊑ res_restrict m X.
Proof. apply resA_product_restrict_same_le. Qed.

Lemma res_sum_le_mono (w1 w2 w1' w2' : WfWorld)
    (Hdef : raw_sum_defined w1 w2) (Hdef' : raw_sum_defined w1' w2') :
  w1 ⊑ w1' → w2 ⊑ w2' →
  res_sum w1 w2 Hdef ⊑ res_sum w1' w2' Hdef'.
Proof. apply resA_sum_le_mono. Qed.

Lemma res_sum_restrict_same_le
    (m m1 m2 : WfWorld) (X : aset)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  ∃ HdefX : raw_sum_defined (res_restrict m1 X) (res_restrict m2 X),
    res_sum (res_restrict m1 X) (res_restrict m2 X) HdefX
      ⊑ res_restrict m X.
Proof. apply resA_sum_restrict_same_le. Qed.

Lemma res_product_unit_r_eq_any (w : WfWorld) (Hc : world_compat w res_unit) :
  res_product w res_unit Hc = w.
Proof. apply resA_product_unit_r_eq_any. Qed.

Lemma res_product_comm_eq (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  ∃ Hc' : world_compat w2 w1,
    res_product w1 w2 Hc = res_product w2 w1 Hc'.
Proof. apply resA_product_comm_eq. Qed.

Lemma res_product_le_l (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w1 ⊑ res_product w1 w2 Hc.
Proof. apply resA_le_product_l. Qed.

Lemma res_product_le_r (w1 w2 : WfWorld) (Hc : world_compat w1 w2) :
  w2 ⊑ res_product w1 w2 Hc.
Proof. apply resA_le_product_r. Qed.

Lemma singleton_projection_compat
    (m : WfWorld) (X : aset) (σ : StoreT) :
  dom (σ : StoreT) = X ->
  res_restrict m X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) ->
  world_compat
    (singleton_world σ)
    (m : World).
Proof.
  intros Hdomσ Hrestrict σ1 σ2 Hσ1 Hσ2.
  simpl in Hσ1. subst σ1.
  assert ((res_restrict m X : World) (storeA_restrict σ2 X)) as Hproj.
  {
    cbn [raw_world raw_worldA world_stores resA_restrict].
    exists σ2. split; [exact Hσ2|reflexivity].
  }
  rewrite Hrestrict in Hproj.
  simpl in Hproj.
  pose proof Hproj as Hrestrictσ2.
  rewrite <- Hrestrictσ2.
  unfold storeA_compat, map_compat.
  intros k v1 v2 H1 H2.
  apply storeA_restrict_lookup_some in H1 as [_ H1].
  congruence.
Qed.

Lemma res_restrict_singleton_world
    (σ : StoreT) X :
  res_restrict
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) X =
  (exist _ (singleton_world (store_restrict σ X))
    (wf_singleton_world (store_restrict σ X)) : WfWorld).
Proof.
  apply wfworld_ext. apply world_ext.
  - change (world_dom (res_restrict
        (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) X
        : World) =
      dom (store_restrict σ X : StoreT)).
    rewrite res_restrict_dom.
    change (world_dom
      ((exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld)
        : World)) with (dom (σ : StoreT)).
    symmetry. apply storeA_restrict_dom.
  - intros σ'. split.
    + intros [σ0 [Hσ0 Hσ']].
      simpl in Hσ0. subst σ0 σ'.
      simpl.
      reflexivity.
    + intros Hσ'.
      simpl in Hσ'. subst σ'.
      exists σ. split; [reflexivity|reflexivity].
Qed.

Lemma res_product_singleton_projection_eq
    (m : WfWorld) (X : aset) (σ : StoreT)
    (Hc : world_compat (singleton_world σ) (m : World)) :
  dom (σ : StoreT) = X ->
  res_restrict m X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) ->
  res_product
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld)
    m Hc = m.
Proof.
  intros Hdomσ Hrestrict.
  assert (HXsub : X ⊆ world_dom (m : World)).
  {
    pose proof (f_equal (fun w : WfWorld => world_dom (w : World))
      Hrestrict) as Hdom.
    change (world_dom (res_restrict m X : World) =
      world_dom
        ((exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld)
          : World)) in Hdom.
    rewrite res_restrict_dom in Hdom.
    unfold singleton_world in Hdom.
    cbn [world_dom raw_world raw_worldA world_dom worldA_dom singleton_worldA] in Hdom.
    set_solver.
  }
  apply wfworld_ext. apply world_ext.
  - rewrite res_product_dom.
    cbn [world_dom raw_world raw_worldA world_dom worldA_dom singleton_world].
    set_solver.
  - intros τ. split.
    + intros [σ1 [σ2 [Hσ1 [Hσ2 [Hcomp Hτ]]]]].
      simpl in Hσ1. subst σ1.
      assert ((res_restrict m X : World) (storeA_restrict σ2 X)) as Hproj.
      {
        cbn [raw_world raw_worldA world_stores resA_restrict].
        exists σ2. split; [exact Hσ2|reflexivity].
      }
      rewrite Hrestrict in Hproj.
      simpl in Hproj.
      pose proof Hproj as Hσ2X.
      subst τ.
      rewrite <- Hσ2X.
      rewrite storeA_union_absorb_r.
      * exact Hσ2.
      * unfold storeA_compat, map_compat.
        intros k v1 v2 H1 H2.
        apply storeA_restrict_lookup_some in H1 as [_ H1].
        congruence.
      * rewrite storeA_restrict_dom. set_solver.
    + intros Hτ.
      exists σ, τ. repeat split; try assumption.
      * apply Hc; [constructor|exact Hτ].
      * rewrite storeA_union_absorb_r.
        -- reflexivity.
        -- apply Hc; [constructor|exact Hτ].
        -- rewrite Hdomσ.
           rewrite (wfworld_store_dom m τ Hτ).
           apply HXsub.
Qed.

Lemma res_sum_comm_eq (w1 w2 : WfWorld) (Hdef : raw_sum_defined w1 w2) :
  ∃ Hdef' : raw_sum_defined w2 w1,
    res_sum w1 w2 Hdef = res_sum w2 w1 Hdef'.
Proof. apply resA_sum_comm_eq. Qed.

Lemma res_product_assoc_eq (w1 w2 w3 : WfWorld)
    (H12 : world_compat w1 w2)
    (H123 : world_compat (res_product w1 w2 H12) w3) :
  ∃ (H23 : world_compat w2 w3)
    (H1_23 : world_compat w1 (res_product w2 w3 H23)),
    res_product (res_product w1 w2 H12) w3 H123 =
    res_product w1 (res_product w2 w3 H23) H1_23.
Proof. apply resA_product_assoc_eq. Qed.

Lemma res_sum_assoc_eq (w1 w2 w3 : WfWorld)
    (H12 : raw_sum_defined w1 w2)
    (H123 : raw_sum_defined (res_sum w1 w2 H12) w3) :
  ∃ (H23 : raw_sum_defined w2 w3)
    (H1_23 : raw_sum_defined w1 (res_sum w2 w3 H23)),
    res_sum (res_sum w1 w2 H12) w3 H123 =
    res_sum w1 (res_sum w2 w3 H23) H1_23.
Proof. apply resA_sum_assoc_eq. Qed.

Lemma res_product_restrict_binder_arg_compat_dom
    (m n marg : WfWorld) (C X A : aset)
    (Hc_tgt : world_compat marg n) :
  res_restrict m C = res_restrict n C ->
  C ⊆ world_dom (m : World) ->
  A ## world_dom (m : World) ->
  A ## world_dom (n : World) ->
  world_dom (res_product marg n Hc_tgt : World) =
    world_dom (n : World) ∪ A ->
  X ⊆ C ∪ A ->
  A ⊆ X ->
  exists Hc_src : world_compat (res_restrict marg X) m,
    world_dom (res_product (res_restrict marg X) m Hc_src : World) =
      world_dom (m : World) ∪ A.
Proof.
  intros Hmn HCm HAm HAn Hdom_tgt HXC HAX.
  assert (HA_marg : A ⊆ world_dom (marg : World)).
  {
    intros a Ha.
    assert (Ha_prod : a ∈ world_dom (res_product marg n Hc_tgt : World)).
    { rewrite Hdom_tgt. set_solver. }
    change (a ∈ world_dom (marg : World) ∪ world_dom (n : World))
      in Ha_prod.
    set_solver.
  }
  assert (Hc_marg_nC : world_compat marg (res_restrict n C)).
  { eapply world_compat_le_r; [apply res_restrict_le|exact Hc_tgt]. }
  assert (Hc_marg_mC : world_compat marg (res_restrict m C)).
  { rewrite <- (eq_sym Hmn). exact Hc_marg_nC. }
  assert (Hc_src : world_compat (res_restrict marg X) m).
  {
    assert (Hc_tmp :
        world_compat (res_restrict marg X)
          (res_restrict m (world_dom (m : World)))).
    {
      eapply world_compat_restrict_overlap
        with (S := C) (n := marg) (m := m).
      - intros z Hz.
        apply elem_of_intersection in Hz as [HzX Hzm].
        assert (HzCA : z ∈ C ∪ A) by set_solver.
        apply elem_of_union in HzCA as [HzC|HzA]; [exact HzC|].
        exfalso.
        eapply elem_of_disjoint; [exact HAm|exact HzA|exact Hzm].
      - exact Hc_marg_mC.
    }
    rewrite (res_restrict_eq_of_le m m (raw_le_refl m)) in Hc_tmp.
    exact Hc_tmp.
  }
  exists Hc_src.
  apply set_eq. intros z. split; intros Hz.
  - change (z ∈ world_dom (res_restrict marg X : World) ∪
      world_dom (m : World)) in Hz.
    apply elem_of_union in Hz as [Hz|Hz]; [|set_solver].
    change (z ∈ world_dom (marg : World) ∩ X) in Hz.
    apply elem_of_intersection in Hz as [_ HzX].
	    assert (HzCA : z ∈ C ∪ A) by set_solver.
	    apply elem_of_union in HzCA as [HzC|HzA].
	    + apply elem_of_union_l. apply HCm. exact HzC.
	    + apply elem_of_union_r. exact HzA.
  - change (z ∈ world_dom (res_restrict marg X : World) ∪
      world_dom (m : World)).
	    apply elem_of_union in Hz as [Hzm|HzA].
	    + apply elem_of_union_r. exact Hzm.
	    + apply elem_of_union_l. change (z ∈ world_dom (marg : World) ∩ X).
      apply elem_of_intersection. split.
      * apply HA_marg. exact HzA.
      * apply HAX. exact HzA.
Qed.

Lemma res_product_restrict_binder_arg_projection
    (m n marg : WfWorld) (C X A Y : aset)
    (Hc_tgt : world_compat marg n) :
  res_restrict m C = res_restrict n C ->
  C ⊆ world_dom (m : World) ->
  A ## world_dom (m : World) ->
  A ## world_dom (n : World) ->
  world_dom (res_product marg n Hc_tgt : World) =
    world_dom (n : World) ∪ A ->
  X ⊆ C ∪ A ->
  A ⊆ X ->
  Y ⊆ C ∪ A ->
  exists Hc_src : world_compat (res_restrict marg X) m,
    world_dom (res_product (res_restrict marg X) m Hc_src : World) =
      world_dom (m : World) ∪ A /\
    res_restrict (res_product (res_restrict marg X) m Hc_src) Y =
    res_restrict (res_product marg n Hc_tgt) Y.
Proof.
  intros Hmn HCm HAm HAn Hdom_tgt HXC HAX HYC.
  destruct (res_product_restrict_binder_arg_compat_dom
    m n marg C X A Hc_tgt Hmn HCm HAm HAn Hdom_tgt HXC HAX)
    as [Hc_src Hdom_src].
  exists Hc_src. split; [exact Hdom_src|].
  assert (HA_marg : A ⊆ world_dom (marg : World)).
  {
    intros a Ha.
    assert (Ha_prod : a ∈ world_dom (res_product marg n Hc_tgt : World)).
    { rewrite Hdom_tgt. set_solver. }
    change (a ∈ world_dom (marg : World) ∪ world_dom (n : World))
      in Ha_prod.
    set_solver.
  }
  assert (HCn : C ⊆ world_dom (n : World)).
  {
    pose proof (f_equal (fun w : WfWorld => world_dom (w : World)) Hmn)
      as HdomC.
    cbn [world_dom raw_world raw_worldA res_restrict] in HdomC.
    set_solver.
  }
  assert (Hc_marg_nC : world_compat marg (res_restrict n C)).
  { eapply world_compat_le_r; [apply res_restrict_le|exact Hc_tgt]. }
  assert (Hc_marg_mC : world_compat marg (res_restrict m C)).
  { rewrite Hmn. exact Hc_marg_nC. }
  assert (Hc_common_m :
      world_compat (res_restrict marg X) (res_restrict m C)).
  {
    eapply world_compat_restrict_overlap
      with (S := C) (n := marg) (m := m).
    - set_solver.
    - exact Hc_marg_mC.
  }
	  assert (Hsrc_to_common :
	      res_restrict (res_product (res_restrict marg X) m Hc_src) Y =
	      res_restrict
	        (res_product (res_restrict marg X) (res_restrict m C)
	          Hc_common_m) Y).
	  {
    symmetry.
	    eapply res_product_restrict_frame_r_eq.
    - exact HCm.
    - intros z HzY.
      assert (HzCA : z ∈ C ∪ A) by set_solver.
      apply elem_of_union in HzCA as [HzC|HzA].
      + apply elem_of_union_r. exact HzC.
      + apply elem_of_union_l.
        change (z ∈ world_dom (marg : World) ∩ X).
        apply elem_of_intersection. split.
        * apply HA_marg. exact HzA.
        * apply HAX. exact HzA.
  }
	  assert (Hcommon_eq :
	      res_restrict
	        (res_product (res_restrict marg X) (res_restrict m C)
	          Hc_common_m) Y =
	      res_restrict (res_product marg (res_restrict n C) Hc_marg_nC) Y).
	  {
    assert (Hc_common_n :
        world_compat (res_restrict marg X) (res_restrict n C)).
    {
      eapply world_compat_restrict_overlap
        with (S := C) (n := marg) (m := n).
      - set_solver.
      - exact Hc_marg_nC.
    }
    assert (Hmn_prod :
        res_product (res_restrict marg X) (res_restrict m C)
          Hc_common_m =
        res_product (res_restrict marg X) (res_restrict n C)
          Hc_common_n).
    { eapply res_product_r_eq. exact Hmn. }
    rewrite Hmn_prod.
    eapply res_product_restrict_frame_common_eq
      with (S := C) (C := C).
    - set_solver.
    - intros z HzY.
      assert (HzCA : z ∈ C ∪ A) by set_solver.
      apply elem_of_union in HzCA as [HzC|HzA].
      + apply elem_of_union_r. apply elem_of_intersection.
        split; [exact HzC|apply HCn; exact HzC].
	      + apply elem_of_union_l. apply elem_of_intersection.
	        split.
	        * apply HAX. exact HzA.
	        * apply HA_marg. exact HzA.
	  }
  assert (Htgt_common_to_full :
      res_restrict (res_product marg (res_restrict n C) Hc_marg_nC) Y =
      res_restrict (res_product marg n Hc_tgt) Y).
  {
    eapply res_product_restrict_frame_r_eq.
    - exact HCn.
    - intros z HzY.
      assert (HzCA : z ∈ C ∪ A) by set_solver.
      apply elem_of_union in HzCA as [HzC|HzA].
      + apply elem_of_union_r. exact HzC.
      + apply elem_of_union_l. apply HA_marg. exact HzA.
  }
  rewrite Hsrc_to_common, Hcommon_eq, Htgt_common_to_full.
  reflexivity.
Qed.



(** * Concrete resource extension interface lemmas *)




Local Notation "m '#>' F '~~>' n" := (res_extend_by m F n)
  (at level 70, F at next level, n at next level).

Lemma res_extend_by_restrict_base (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  res_restrict n (world_dom m) = m.
Proof. apply resA_extend_by_restrict_base. Qed.

Lemma res_extend_by_dom (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  world_dom (n : World) = world_dom (m : World) ∪ extA_out F.
Proof. apply resA_extend_by_dom. Qed.

Lemma res_extend_by_le (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  m ⊑ n.
Proof. apply resA_extend_by_le. Qed.

Lemma res_extend_by_le_mono
    (m n mx nx : WfWorld) (F : fiber_extension) :
  m ⊑ n ->
  m #> F ~~> mx ->
  n #> F ~~> nx ->
  mx ⊑ nx.
Proof. apply resA_extend_by_le_mono. Qed.

Lemma res_extend_by_sum
    (m1 m2 m1x m2x : WfWorld) (F : fiber_extension)
    (Hdef : raw_sum_defined (m1 : World) (m2 : World)) :
  m1 #> F ~~> m1x ->
  m2 #> F ~~> m2x ->
  exists Hdefx : raw_sum_defined (m1x : World) (m2x : World),
    res_sum m1 m2 Hdef #> F ~~>
      res_sum m1x m2x Hdefx.
Proof. apply resA_extend_by_sum. Qed.

Lemma res_extend_by_applicable (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  extension_applicable F m.
Proof. apply resA_extend_by_applicable. Qed.

Lemma res_extend_by_input_dom (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  extA_in F ⊆ world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_in _ _ Happ).
Qed.

Lemma res_extend_by_output_fresh (m : WfWorld) (F : fiber_extension) (n : WfWorld) :
  m #> F ~~> n →
  extA_out F ## world_dom (m : World).
Proof.
  intros Hext.
  pose proof (res_extend_by_applicable m F n Hext) as Happ.
  exact (extA_app_out _ _ Happ).
Qed.

Lemma res_extend_rel_store_dom
    (m mx : WfWorld) (F : fiber_extension)
    (σm : StoreT) (we : WfWorld) (σe : StoreT) :
  res_extend_by m F mx ->
  (m : World) σm ->
  extA_rel F (store_restrict σm (extA_in F)) we ->
  (we : World) σe ->
  dom (σe : StoreT) = extA_out F.
Proof.
  intros Hext Hσm HFrel Hσe.
  eapply (extA_output_store_dom_from_base m F σm we σe); eauto.
  exact (resA_extend_by_applicable _ _ _ Hext).
Qed.

Lemma res_restrict_singleton_store_eq
    (m : WfWorld) X (σX σ : StoreT) :
  res_restrict m X =
    (exist _ (singleton_world σX) (wf_singleton_world σX) : WfWorld) ->
  (m : World) σ ->
  store_restrict σ X = σX.
Proof.
  intros Hsingle Hσ.
  assert (Hrestrict : (resA_restrict m X : World) (store_restrict σ X)).
  { exists σ. split; [exact Hσ|reflexivity]. }
  replace (resA_restrict m X)
    with (exist _ (singleton_world σX) (wf_singleton_world σX) : WfWorld)
    in Hrestrict by exact (eq_sym Hsingle).
  cbn [raw_world raw_worldA singleton_world] in Hrestrict.
  exact Hrestrict.
Qed.

Lemma res_restrict_singleton_exact_dom_subset
    (m : WfWorld) X σ :
  dom (σ : StoreT) = X ->
  res_restrict m X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld) ->
  X ⊆ world_dom (m : World).
Proof.
  intros Hdomσ Hsingle a Ha.
  assert (Hdom_eq :
      world_dom (res_restrict m X : World) = dom (σ : StoreT)).
  { rewrite Hsingle. reflexivity. }
  rewrite res_restrict_dom, Hdomσ in Hdom_eq.
  set_solver.
Qed.

Lemma res_fiber_from_projection_restrict_singleton
    (m mfib : WfWorld) X σ :
  dom (σ : StoreT) = X ->
  res_fiber_from_projection m X σ mfib ->
  res_restrict mfib X =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorld).
Proof.
  intros Hdomσ Hproj.
  apply wfworld_ext. apply world_ext.
  - rewrite res_restrict_dom.
    rewrite (res_fiber_from_projection_world_dom m mfib X σ Hproj).
    destruct Hproj as [Hσproj _].
    pose proof (wfworld_store_dom (res_restrict m X) σ Hσproj)
      as Hdom_proj.
    change (dom (σ : StoreT) = world_dom (res_restrict m X : World))
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
        change (wmfib = rawA_fiber (m : World) σ) in Hfib.
        rewrite Hfib. split; [exact Hτ0|].
        change (store_restrict τ0 (dom (σ : StoreT)) = σ).
        rewrite Hdomσ. exact Hτ0X.
      * exact Hτ0X.
Qed.

Lemma y_fiber_store_dom
    y σy (m mfib : WfWorld) :
  y ∈ world_dom (m : World) ->
  res_fiber_from_projection m {[y]} σy mfib ->
  dom (σy : StoreT) = {[y]}.
Proof.
  intros Hy_world Hproj.
  destruct Hproj as [Hσproj _].
  pose proof (wfworld_store_dom (res_restrict m {[y]}) σy Hσproj)
    as Hdom.
  change (dom (σy : StoreT) =
    world_dom (res_restrict m {[y]} : World)) in Hdom.
  rewrite res_restrict_dom in Hdom.
  rewrite Hdom. set_solver.
Qed.

Lemma y_fiber_restrict_singleton
    y σy (m mfib : WfWorld) :
  y ∈ world_dom (m : World) ->
  res_fiber_from_projection m {[y]} σy mfib ->
  res_restrict mfib {[y]} =
    (exist _ (singleton_world σy) (wf_singleton_world σy) : WfWorld).
Proof.
  intros Hy_world Hproj.
  apply (res_fiber_from_projection_restrict_singleton m mfib {[y]} σy).
  - apply y_fiber_store_dom with (m := m) (mfib := mfib); assumption.
  - exact Hproj.
Qed.

Lemma store_singleton_dom_value y (v : V) :
  dom ({[y := v]} : StoreT) = {[y]}.
Proof.
  change (dom ({[y := v]} : gmap atom V) = ({[y]} : aset)).
  apply dom_singleton_L.
Qed.

Lemma singleton_world_member_eq (σ τ : StoreT) :
  (singleton_world σ : World) τ ->
  τ = σ.
Proof.
  unfold singleton_world.
  cbn [raw_world raw_worldA singleton_worldA].
  intros ->. reflexivity.
Qed.

Lemma res_extend_by_singleton_output_in_world
    (m mx : WfWorld) F x :
  res_extend_by m F mx ->
  extA_out F = {[x]} ->
  x ∈ world_dom (mx : World).
Proof.
  intros Hext Hout.
  pose proof (res_extend_by_dom m F mx Hext) as Hdom.
  change (world_dom (mx : World) =
    world_dom (m : World) ∪ extA_out F) in Hdom.
  rewrite Hdom, Hout.
  set_solver.
Qed.

Lemma res_extend_by_singleton_output_open_world
    (m mx : WfWorld) F x :
  res_extend_by m F mx ->
  extA_out F = {[x]} ->
  world_dom (mx : World) = world_dom (m : World) ∪ {[x]} /\
  res_restrict mx (world_dom (m : World)) = m.
Proof.
  intros Hext Hout.
  split.
  - pose proof (res_extend_by_dom m F mx Hext) as Hdom.
    change (world_dom (mx : World) =
      world_dom (m : World) ∪ extA_out F) in Hdom.
    rewrite Hdom, Hout. reflexivity.
  - exact (res_extend_by_restrict_base m F mx Hext).
Qed.

Lemma res_extend_by_singleton_output_notin_base_store
    (m mx : WfWorld) F x (σ : StoreT) :
  res_extend_by m F mx ->
  extA_out F = {[x]} ->
  (m : World) σ ->
  x ∉ dom (σ : StoreT).
Proof.
  intros Hext Hout Hσ.
  pose proof (res_extend_by_output_fresh m F mx Hext) as Hfresh.
  change (extA_out F ## world_dom (m : World)) in Hfresh.
  pose proof (wfworldA_store_dom m σ Hσ) as Hdomσ.
  change (dom (σ : StoreT) = world_dom (m : World)) in Hdomσ.
  rewrite Hdomσ.
  rewrite Hout in Hfresh.
  set_solver.
Qed.

Lemma res_extend_by_exists (m : WfWorld) (F : fiber_extension) :
  extension_applicable F m →
  ∃ n, m #> F ~~> n.
Proof. apply resA_extend_by_exists. Qed.

Definition const_fresh_value_extension
    (X : aset) (y : atom) (v : V) (HyX : y ∉ X) : fiber_extension :=
  mk_fiber_extensionA X {[y]}
    (fun _ w =>
      w =
        (exist _ (singleton_world ({[y := v]} : StoreT))
          (wf_singleton_world ({[y := v]} : StoreT)) : WfWorld))
    ltac:(set_solver)
    ltac:(intros σ w Hσ ->;
      cbn [world_dom raw_world raw_worldA singleton_world];
      apply store_singleton_dom_value)
    ltac:(intros σ Hσ;
      exists (exist _ (singleton_world ({[y := v]} : StoreT))
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorld);
      exists ({[y := v]} : StoreT);
      cbn [raw_world raw_worldA singleton_world];
      split; reflexivity)
    ltac:(intros σ w1 w2 σe _ -> ->; reflexivity).

Lemma res_extend_by_const_fresh_value_exact
    (m : WfWorld) y v (Hy : y ∉ world_dom (m : World)) :
  exists my,
    res_extend_by m
      (const_fresh_value_extension (world_dom (m : World)) y v Hy) my /\
    world_dom (my : World) = world_dom (m : World) ∪ {[y]} /\
    res_restrict my (world_dom (m : World)) = m /\
    forall σ, (my : World) σ -> σ !! y = Some v.
Proof.
  set (F := const_fresh_value_extension (world_dom (m : World)) y v Hy).
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
        (wf_singleton_world ({[y := v]} : StoreT)) : WfWorld)) in Hrel.
    rewrite Hrel in Hσe.
    apply singleton_world_member_eq in Hσe. subst σe.
    rewrite (lookup_union_r (M:=gmap atom) (A:=V)
      σm ({[y := v]} : gmap atom V) y).
    + apply map_lookup_insert.
    + apply not_elem_of_dom.
      rewrite (wfworld_store_dom m σm Hσm).
      exact Hy.
Qed.

Lemma res_extend_by_const_fresh_value
    (m : WfWorld) y v :
  y ∉ world_dom (m : World) ->
  exists F my,
    extA_in F = world_dom (m : World) /\
    extA_out F = {[y]} /\
    res_extend_by m F my /\
    world_dom (my : World) = world_dom (m : World) ∪ {[y]} /\
    res_restrict my (world_dom (m : World)) = m /\
    forall σ, (my : World) σ -> σ !! y = Some v.
Proof.
  intros Hy.
  set (F := const_fresh_value_extension (world_dom (m : World)) y v Hy).
  destruct (res_extend_by_const_fresh_value_exact m y v Hy)
    as [my [Hext [Hdom [Hbase Hlookup]]]].
  exists F, my.
  split; [subst F; reflexivity|].
  split; [subst F; reflexivity|].
  split; [exact Hext|].
  split; [exact Hdom|].
  split; [exact Hbase|exact Hlookup].
Qed.

Lemma res_extend_by_projection_eq
    (m n : WfWorld) (F : fiber_extension) (my ny : WfWorld) :
  res_restrict m (extA_in F) = res_restrict n (extA_in F) →
  m #> F ~~> my →
  n #> F ~~> ny →
  res_restrict my (extA_in F ∪ extA_out F) =
  res_restrict ny (extA_in F ∪ extA_out F).
Proof. apply resA_extend_by_projection_eq. Qed.

Lemma res_extend_by_product_frame_r
    (m1 m1x m2 : WfWorld) (F : fiber_extension)
    (Hc : world_compat m1 m2) :
  m1 #> F ~~> m1x ->
  extA_out F ## world_dom (m2 : World) ->
  exists Hcx : world_compat m1x m2,
    res_product m1 m2 Hc #> F ~~>
      res_product m1x m2 Hcx.
Proof. apply resA_extend_by_product_frame_r. Qed.

Lemma res_extend_by_product_frame_l
    (m1 m1x m2 : WfWorld) (F : fiber_extension)
    (Hc : world_compat m2 m1) :
  m1 #> F ~~> m1x ->
  extA_out F ## world_dom (m2 : World) ->
  exists Hcx : world_compat m2 m1x,
    res_product m2 m1 Hc #> F ~~>
      res_product m2 m1x Hcx.
Proof. apply resA_extend_by_product_frame_l. Qed.

End ResourceInterface.

Notation "r '↾ᵣ' X" := (res_restrict r X)
  (at level 20, no associativity,
   format "r  ↾ᵣ  X", only printing).
Notation "m1 '⊑ᵣ' m2" := (raw_le m1 m2)
  (at level 70, no associativity,
   format "m1  ⊑ᵣ  m2", only printing).
Notation "m1 '##ᵣ' m2" := (world_compat m1 m2)
  (at level 70, no associativity,
   format "m1  ##ᵣ  m2", only printing).
Notation "m1 '×ᵣ[' Hc ']' m2" := (res_product m1 m2 Hc)
  (at level 40, Hc at level 200, left associativity,
   format "m1  ×ᵣ[ Hc ]  m2", only printing).
Notation "m1 '+ᵣ[' Hdef ']' m2" := (res_sum m1 m2 Hdef)
  (at level 50, Hdef at level 200, left associativity,
   format "m1  +ᵣ[ Hdef ]  m2", only printing).
