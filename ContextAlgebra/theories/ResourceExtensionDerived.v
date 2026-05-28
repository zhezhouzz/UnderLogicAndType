From ContextBase Require Import Prelude LogicVar.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
  ResourceAlgebraBase ResourceAlgebraOrder ResourceAlgebraPullback ResourceAlgebraSum ResourceAlgebraLaws ResourceExtensionCore ResourceExtensionEquiv.

(** * Derived extension lemmas

    This file is intentionally after the core extension files.  Long legacy proofs
    that are really extension arguments should land here, not in the basic
    resource files.  During the definition-migration phase these are named
    review points. *)

Section ResourceExtensionDerivedA.

Context {K : Type} `{Countable K} .
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (gmap K V) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).

Lemma resA_extend_by_sum_pullback
    (m : WfWorldAT) F (n n1 n2 : WfWorldAT)
    (Hdef : rawA_sum_defined (n1 : WorldAT) (n2 : WorldAT)) :
  resA_extend_by m F n →
  fiber_extensionA_functional_on m F →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (n1 : WorldAT) →
  worldA_dom (m : WorldAT) ⊆ worldA_dom (n2 : WorldAT) →
  resA_sum n1 n2 Hdef ⊑ n →
  ∃ (m1 m2 : WfWorldAT) (Hdefm : rawA_sum_defined m1 m2)
    (n1' n2' : WfWorldAT),
    worldA_dom (m1 : WorldAT) = worldA_dom (m : WorldAT) ∧
    worldA_dom (m2 : WorldAT) = worldA_dom (m : WorldAT) ∧
    resA_subset m1 m ∧
    resA_subset m2 m ∧
    resA_sum m1 m2 Hdefm ⊑ m ∧
    resA_extend_by m1 F n1' ∧
    n1 ⊑ n1' ∧
    resA_extend_by m2 F n2' ∧
    n2 ⊑ n2'.
Proof.
  intros Hext Hfun Hdom_m_n1 Hdom_m_n2 Hsum_le.
  set (X := worldA_dom (m : WorldAT)).
  set (m1 := resA_restrict n1 X).
  set (m2 := resA_restrict n2 X).
  assert (Hdom_m1 : worldA_dom (m1 : WorldAT) = X).
  { subst m1 X. simpl. set_solver. }
  assert (Hdom_m2 : worldA_dom (m2 : WorldAT) = X).
  { subst m2 X. simpl. set_solver. }
  assert (Hsub_m1_m : resA_subset m1 m).
  {
    subst m1 X.
    split.
    - simpl. set_solver.
    - intros σ Hσ.
      rewrite <- (resA_extend_by_restrict_base m F n Hext).
      simpl in Hσ |- *.
      destruct Hσ as [σ1 [Hσ1 Hrestrict1]].
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
      assert ((resA_sum n1 n2 Hdef : WorldAT) σ1) as Hsumσ1.
      { simpl. left. exact Hσ1. }
      rewrite Hsum_le in Hsumσ1. simpl in Hsumσ1.
      destruct Hsumσ1 as [σn [Hσn Hrestrict_sum]].
      exists σn. split; [exact Hσn |].
      rewrite <- Hrestrict1, <- Hrestrict_sum.
      rewrite storeA_restrict_restrict.
      f_equal.
      pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
      simpl in Hdom_sum_n.
      rewrite Hdef in Hdom_sum_n.
      set_solver.
  }
  assert (Hsub_m2_m : resA_subset m2 m).
  {
    subst m2 X.
    split.
    - simpl. set_solver.
    - intros σ Hσ.
      rewrite <- (resA_extend_by_restrict_base m F n Hext).
      simpl in Hσ |- *.
      destruct Hσ as [σ2 [Hσ2 Hrestrict2]].
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
      assert ((resA_sum n1 n2 Hdef : WorldAT) σ2) as Hsumσ2.
      { simpl. right. exact Hσ2. }
      rewrite Hsum_le in Hsumσ2. simpl in Hsumσ2.
      destruct Hsumσ2 as [σn [Hσn Hrestrict_sum]].
      exists σn. split; [exact Hσn |].
      rewrite <- Hrestrict2, <- Hrestrict_sum.
      rewrite storeA_restrict_restrict.
      f_equal.
      pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
      simpl in Hdom_sum_n.
      set_solver.
  }
  assert (Hsub_m1_n : resA_subset m1 (resA_restrict n X)).
  {
    subst X. rewrite (resA_extend_by_restrict_base m F n Hext).
    exact Hsub_m1_m.
  }
  assert (Hsub_m2_n : resA_subset m2 (resA_restrict n X)).
  {
    subst X. rewrite (resA_extend_by_restrict_base m F n Hext).
    exact Hsub_m2_m.
  }
  set (n1' := resA_slice_restrict n X m1 Hsub_m1_n).
  set (n2' := resA_slice_restrict n X m2 Hsub_m2_n).
  assert (Hm1ext : resA_extend_by m1 F n1').
  {
    subst n1' X.
    eapply resA_extend_by_slice_restrict_base; eauto.
  }
  assert (Hm2ext : resA_extend_by m2 F n2').
  {
    subst n2' X.
    eapply resA_extend_by_slice_restrict_base; eauto.
  }
  assert (Hdefm : rawA_sum_defined (m1 : WorldAT) (m2 : WorldAT)).
  { unfold rawA_sum_defined. rewrite Hdom_m1, Hdom_m2. reflexivity. }
  exists m1, m2, Hdefm, n1', n2'.
  split; [subst X; exact Hdom_m1 |].
  split; [subst X; exact Hdom_m2 |].
  split; [exact Hsub_m1_m |].
  split; [exact Hsub_m2_m |].
  refine (conj _ (conj Hm1ext (conj _ (conj Hm2ext _)))).
  - subst m1 m2 X.
    rewrite (resA_restrict_sum n1 n2 (worldA_dom (m : WorldAT)) Hdef Hdefm).
    pose proof (resA_restrict_le_mono (resA_sum n1 n2 Hdef) n
      (worldA_dom (m : WorldAT)) Hsum_le) as Hle_restrict.
    rewrite (resA_extend_by_restrict_base m F n Hext) in Hle_restrict.
    exact Hle_restrict.
  - subst n1'. unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
    apply worldA_ext.
    + simpl.
      pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
      simpl in Hdom_sum_n. set_solver.
    + intros σ. simpl. split.
      * intros Hσ1.
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ) as Hsumσ.
        { simpl. left. exact Hσ1. }
        rewrite Hsum_le in Hsumσ. simpl in Hsumσ.
        destruct Hsumσ as [σn [Hσn Hrestrict]].
        exists σn. split; [| exact Hrestrict].
        split; [exact Hσn |].
        subst m1. simpl.
        exists σ. split; [exact Hσ1 |].
        rewrite <- Hrestrict.
        rewrite storeA_restrict_restrict.
        replace (worldA_dom (n1 : WorldAT) ∩ X) with X by set_solver.
        reflexivity.
      * intros [σn [[Hσn Hσm1] Hrestrict]].
        subst m1. simpl in Hσm1.
        destruct Hσm1 as [σ1 [Hσ1 Hσ1_proj]].
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ1) as Hsumσ1.
        { simpl. left. exact Hσ1. }
        rewrite Hsum_le in Hsumσ1. simpl in Hsumσ1.
        destruct Hsumσ1 as [σn1 [Hσn1 Hrestrict1]].
        apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσn.
        apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσn1.
        destruct Hσn as [σm [we [σe [Hσm [HFrel [Hσe Hσn_eq]]]]]].
        destruct Hσn1 as [σm1 [we1 [σe1 [Hσm1 [HFrel1 [Hσe1 Hσn1_eq]]]]]].
        subst σn σn1.
        assert (Hbase :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σe) X = σm).
        {
          subst X.
          exact (resA_extend_store_restrict_base m F σm we σe
            (resA_extend_by_applicable _ _ _ Hext) Hσm HFrel Hσe).
        }
        assert (Hbase1 :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm1 σe1) X = σm1).
        {
          subst X.
          exact (resA_extend_store_restrict_base m F σm1 we1 σe1
            (resA_extend_by_applicable _ _ _ Hext) Hσm1 HFrel1 Hσe1).
        }
        assert (Hσm1_eq : σm1 = σm).
        {
          rewrite <- Hbase1.
          replace (@storeA_restrict V K _ _ (@union (gmap K V) _ σm1 σe1) X)
            with (@storeA_restrict V K _ _ σ1 X).
          2:{
            rewrite <- Hrestrict1.
            rewrite storeA_restrict_restrict.
            replace (worldA_dom (resA_sum n1 n2 Hdef : WorldAT) ∩ X)
              with X by (simpl; set_solver).
            reflexivity.
          }
          rewrite Hσ1_proj.
          exact Hbase.
        }
        subst σm1.
        pose proof (fiber_extensionA_functional_outputs_eq m F σm we1 we σe1 σe
          (resA_extend_by_applicable _ _ _ Hext) Hfun Hσm HFrel1 HFrel Hσe1 Hσe)
          as Heq_fiber.
        subst σe1.
        rewrite Hrestrict1 in Hrestrict.
        subst σ.
        exact Hσ1.
  - subst n2'. unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
    apply worldA_ext.
    + simpl.
      pose proof (rawA_le_dom _ _ Hsum_le) as Hdom_sum_n.
      simpl in Hdom_sum_n |- *. rewrite <- Hdef. set_solver.
    + intros σ. simpl. split.
      * intros Hσ2.
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ) as Hsumσ.
        { simpl. right. exact Hσ2. }
        rewrite Hsum_le in Hsumσ. simpl in Hsumσ.
        destruct Hsumσ as [σn [Hσn Hrestrict]].
        exists σn. split.
        2:{ rewrite <- Hdef. exact Hrestrict. }
        split; [exact Hσn |].
        subst m2. simpl.
        exists σ. split; [exact Hσ2 |].
        rewrite <- Hrestrict.
        rewrite storeA_restrict_restrict.
        replace (worldA_dom (n1 : WorldAT) ∩ X) with X by set_solver.
        reflexivity.
      * intros [σn [[Hσn Hσm2] Hrestrict]].
        subst m2. simpl in Hσm2.
        destruct Hσm2 as [σ2 [Hσ2 Hσ2_proj]].
        unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hsum_le.
        assert ((resA_sum n1 n2 Hdef : WorldAT) σ2) as Hsumσ2.
        { simpl. right. exact Hσ2. }
        rewrite Hsum_le in Hsumσ2. simpl in Hsumσ2.
        destruct Hsumσ2 as [σn2 [Hσn2 Hrestrict2]].
        apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσn.
        apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσn2.
        destruct Hσn as [σm [we [σe [Hσm [HFrel [Hσe Hσn_eq]]]]]].
        destruct Hσn2 as [σm2 [we2 [σe2 [Hσm2 [HFrel2 [Hσe2 Hσn2_eq]]]]]].
        subst σn σn2.
        assert (Hbase :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σe) X = σm).
        {
          subst X.
          exact (resA_extend_store_restrict_base m F σm we σe
            (resA_extend_by_applicable _ _ _ Hext) Hσm HFrel Hσe).
        }
        assert (Hbase2 :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm2 σe2) X = σm2).
        {
          subst X.
          exact (resA_extend_store_restrict_base m F σm2 we2 σe2
            (resA_extend_by_applicable _ _ _ Hext) Hσm2 HFrel2 Hσe2).
        }
        assert (Hσm2_eq : σm2 = σm).
        {
          rewrite <- Hbase2.
          replace (@storeA_restrict V K _ _ (@union (gmap K V) _ σm2 σe2) X)
            with (@storeA_restrict V K _ _ σ2 X).
          2:{
            rewrite <- Hrestrict2.
            rewrite storeA_restrict_restrict.
            replace (worldA_dom (resA_sum n1 n2 Hdef : WorldAT) ∩ X)
              with X by (simpl; rewrite Hdef; set_solver).
            reflexivity.
          }
          rewrite Hσ2_proj.
          exact Hbase.
        }
        subst σm2.
        pose proof (fiber_extensionA_functional_outputs_eq m F σm we2 we σe2 σe
          (resA_extend_by_applicable _ _ _ Hext) Hfun Hσm HFrel2 HFrel Hσe2 Hσe)
          as Heq_fiber.
        subst σe2.
        assert (Hrestrict2' :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σe)
            (worldA_dom (n2 : WorldAT)) = σ2).
        {
          rewrite <- Hdef. exact Hrestrict2.
        }
        rewrite Hrestrict2' in Hrestrict.
        subst σ.
        exact Hσ2.
Qed.

Lemma resA_one_point_extension_pushout
    (m n my : WfWorldAT) (y : K) :
  m ⊑ n →
  y ∉ worldA_dom (n : WorldAT) →
  worldA_dom (my : WorldAT) = worldA_dom (m : WorldAT) ∪ {[y]} →
  resA_restrict my (worldA_dom (m : WorldAT)) = m →
  ∃ ny : WfWorldAT,
    worldA_dom (ny : WorldAT) = worldA_dom (n : WorldAT) ∪ {[y]} ∧
    resA_restrict ny (worldA_dom (n : WorldAT)) = n ∧
    my ⊑ ny.
Proof.
  intros Hmn Hy_n Hdom_my Hrestr_my.
  pose proof (rawA_le_dom m n Hmn) as Hdom_m_n.
  pose (raw_ny := ({|
    worldA_dom := worldA_dom (n : WorldAT) ∪ {[y]};
    worldA_stores := λ τ,
      ∃ σn σy,
        (n : WorldAT) σn ∧
        (my : WorldAT) σy ∧
        @storeA_restrict V K _ _ σn (worldA_dom (m : WorldAT)) =
          @storeA_restrict V K _ _ σy (worldA_dom (m : WorldAT)) ∧
        τ = @union (gmap K V) _ σn
          (@storeA_restrict V K _ _ σy ({[y]} : gset K))
  |} : WorldAT)).
  assert (Hwf_ny : wf_worldA raw_ny).
  {
    constructor.
    - destruct (wfA_ne _ (worldA_wf my)) as [σy Hσy].
      assert (Hm_proj :
          (m : WorldAT) (@storeA_restrict V K _ _ σy (worldA_dom (m : WorldAT)))).
      {
        assert (Hraw : rawA_restrict my (worldA_dom (m : WorldAT))
            (@storeA_restrict V K _ _ σy (worldA_dom (m : WorldAT)))).
        { exists σy. split; [exact Hσy | reflexivity]. }
        assert (Heq : rawA_restrict my (worldA_dom (m : WorldAT)) = (m : WorldAT)).
        {
          change ((resA_restrict my (worldA_dom (m : WorldAT)) : WorldAT) =
            (m : WorldAT)).
          rewrite Hrestr_my. reflexivity.
        }
        rewrite Heq in Hraw. exact Hraw.
      }
      unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hmn.
      rewrite Hmn in Hm_proj. simpl in Hm_proj.
      destruct Hm_proj as [σn [Hσn Hrestrict]].
      exists (@union (gmap K V) _ (σn : gmap K V)
        (@storeA_restrict V K _ _ σy ({[y]} : gset K) : gmap K V)).
      simpl. exists σn, σy. repeat split; eauto.
      replace (worldA_dom (n : WorldAT) ∩ worldA_dom (m : WorldAT))
        with (worldA_dom (m : WorldAT)) in Hrestrict by set_solver.
      exact Hrestrict.
    - intros τ [σn [σy [Hσn [Hσy [Hagree ->]]]]].
      pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
      pose proof (wfworldA_store_dom my σy Hσy) as Hdomσy.
      change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
      change (dom (σy : gmap K V) = worldA_dom (my : WorldAT)) in Hdomσy.
      assert (Hcompat :
          @storeA_compat V K _ _ σn (@storeA_restrict V K _ _ σy ({[y]} : gset K))).
      {
        apply storeA_disj_dom_compat.
        apply set_eq. intros z. split.
        - intros Hz.
          apply elem_of_intersection in Hz as [Hzn Hzy].
          change (z ∈ (dom (σn : gmap K V) : gset K)) in Hzn.
          change (z ∈ (dom (@storeA_restrict V K _ _ σy ({[y]} : gset K) : gmap K V) : gset K)) in Hzy.
          pose proof (storeA_restrict_dom σy ({[y]} : gset K)) as Hdom_restr.
          change (dom (@storeA_restrict V K _ _ σy ({[y]} : gset K) : gmap K V) =
            dom (σy : gmap K V) ∩ ({[y]} : gset K)) in Hdom_restr.
          rewrite Hdom_restr in Hzy.
          rewrite Hdomσn in Hzn.
          apply elem_of_intersection in Hzy as [Hzy Hy].
          change (z ∈ (dom (σy : gmap K V) : gset K)) in Hzy.
          rewrite Hdomσy, Hdom_my in Hzy. set_solver.
        - intros Hz. apply elem_of_empty in Hz. contradiction.
      }
      change (dom (@union (gmap K V) _ (σn : gmap K V)
        (@storeA_restrict V K _ _ σy ({[y]} : gset K) : gmap K V)) =
        worldA_dom (n : WorldAT) ∪ {[y]}).
      rewrite (storeA_union_dom σn
        (@storeA_restrict V K _ _ σy ({[y]} : gset K)) Hcompat).
      pose proof (storeA_restrict_dom σy ({[y]} : gset K)) as Hdom_restr.
      change (dom (@storeA_restrict V K _ _ σy ({[y]} : gset K) : gmap K V) =
        dom (σy : gmap K V) ∩ ({[y]} : gset K)) in Hdom_restr.
      rewrite Hdom_restr. rewrite Hdomσn.
      apply set_eq. intros z. split.
      * intros Hz.
        apply elem_of_union in Hz as [Hz|Hz]; [set_solver |].
        apply elem_of_intersection in Hz as [Hzy Hy].
        change (z ∈ (dom (σy : gmap K V) : gset K)) in Hzy.
        rewrite Hdomσy, Hdom_my in Hzy. set_solver.
      * intros Hz.
        apply elem_of_union.
        destruct (decide (z ∈ worldA_dom (n : WorldAT))) as [Hzn|Hzn].
        -- left. exact Hzn.
        -- right. apply elem_of_intersection. split.
           ++ change (z ∈ (dom (σy : gmap K V) : gset K)).
              rewrite Hdomσy, Hdom_my. set_solver.
           ++ set_solver.
  }
  exists (exist _ raw_ny Hwf_ny). split.
  - reflexivity.
  - split.
    + apply wfworldA_ext. apply worldA_ext.
      * simpl. set_solver.
      * intros τ. simpl. split.
        -- intros [τny [[σn [σy [Hσn [Hσy [Hagree ->]]]]] Hrestrict]].
           rewrite (storeA_restrict_union_piece_l
             σn (@storeA_restrict V K _ _ σy ({[y]} : gset K))
             (worldA_dom (n : WorldAT)) ({[y]} : gset K)) in Hrestrict.
           ++ subst τ. exact Hσn.
           ++ apply storeA_compat_restrict_singleton_fresh.
              pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
              change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
              change (y ∉ (dom (σn : gmap K V) : gset K)).
              rewrite Hdomσn. exact Hy_n.
           ++ pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
              change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
              intros z Hz. change (z ∈ (dom (σn : gmap K V) : gset K)) in Hz.
              rewrite Hdomσn in Hz. exact Hz.
           ++ apply storeA_restrict_dom_subset.
           ++ set_solver.
        -- intros Hτn.
           assert (Hm_proj :
               (m : WorldAT) (@storeA_restrict V K _ _ τ (worldA_dom (m : WorldAT)))).
           {
             unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hmn.
             rewrite Hmn at 1. simpl. exists τ. split; [exact Hτn | reflexivity].
           }
           assert (Hraw_my :
               rawA_restrict my (worldA_dom (m : WorldAT))
                 (@storeA_restrict V K _ _ τ (worldA_dom (m : WorldAT)))).
           {
             assert (Heq : rawA_restrict my (worldA_dom (m : WorldAT)) = (m : WorldAT)).
             {
               change ((resA_restrict my (worldA_dom (m : WorldAT)) : WorldAT) =
                 (m : WorldAT)).
               rewrite Hrestr_my. reflexivity.
             }
             rewrite Heq. exact Hm_proj.
           }
           simpl in Hraw_my.
           destruct Hraw_my as [σy [Hσy Hσy_restrict]].
           exists (@union (gmap K V) _ (τ : gmap K V)
             (@storeA_restrict V K _ _ σy ({[y]} : gset K) : gmap K V)).
           split.
           ++ simpl. exists τ, σy. repeat split; eauto.
           ++ apply (storeA_restrict_union_piece_l
                τ (@storeA_restrict V K _ _ σy ({[y]} : gset K))
                (worldA_dom (n : WorldAT)) ({[y]} : gset K)).
              ** apply storeA_compat_restrict_singleton_fresh.
                 pose proof (wfworldA_store_dom n τ Hτn) as Hdomτ.
                 change (dom (τ : gmap K V) = worldA_dom (n : WorldAT)) in Hdomτ.
                 change (y ∉ (dom (τ : gmap K V) : gset K)).
                 rewrite Hdomτ. exact Hy_n.
              ** pose proof (wfworldA_store_dom n τ Hτn) as Hdomτ.
                 change (dom (τ : gmap K V) = worldA_dom (n : WorldAT)) in Hdomτ.
                 intros z Hz. change (z ∈ (dom (τ : gmap K V) : gset K)) in Hz.
                 rewrite Hdomτ in Hz. exact Hz.
              ** apply storeA_restrict_dom_subset.
              ** set_solver.
    + unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le.
      apply worldA_ext.
      * simpl. rewrite Hdom_my. set_solver.
      * intros τ. simpl. split.
        -- intros Hτmy.
           assert (Hm_proj :
               (m : WorldAT) (@storeA_restrict V K _ _ τ (worldA_dom (m : WorldAT)))).
           {
             assert (Hraw : rawA_restrict my (worldA_dom (m : WorldAT))
                 (@storeA_restrict V K _ _ τ (worldA_dom (m : WorldAT)))).
             { exists τ. split; [exact Hτmy | reflexivity]. }
             assert (Heq : rawA_restrict my (worldA_dom (m : WorldAT)) = (m : WorldAT)).
             {
               change ((resA_restrict my (worldA_dom (m : WorldAT)) : WorldAT) =
                 (m : WorldAT)).
               rewrite Hrestr_my. reflexivity.
             }
             rewrite Heq in Hraw. exact Hraw.
           }
           unfold sqsubseteq, wf_worldA_sqsubseteq, resA_le, rawA_le in Hmn.
           rewrite Hmn in Hm_proj. simpl in Hm_proj.
           destruct Hm_proj as [σn [Hσn Hrestrict]].
           exists (@union (gmap K V) _ (σn : gmap K V)
             (@storeA_restrict V K _ _ τ ({[y]} : gset K) : gmap K V)).
           split.
           ++ simpl. exists σn, τ. repeat split; eauto.
              replace (worldA_dom (n : WorldAT) ∩ worldA_dom (m : WorldAT))
                with (worldA_dom (m : WorldAT)) in Hrestrict by set_solver.
              exact Hrestrict.
           ++ pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
              pose proof (wfworldA_store_dom my τ Hτmy) as Hdomτ.
              change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
              change (dom (τ : gmap K V) = worldA_dom (my : WorldAT)) in Hdomτ.
              change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
              change (dom (τ : gmap K V) = worldA_dom (my : WorldAT)) in Hdomτ.
              rewrite Hdom_my.
              apply storeA_restrict_union_base_singleton.
              ** intros z Hz. change (z ∈ (dom (σn : gmap K V) : gset K)).
                 rewrite Hdomσn. apply Hdom_m_n. exact Hz.
              ** change ((dom (τ : gmap K V) : gset K) =
                   worldA_dom (m : WorldAT) ∪ {[y]}).
                 rewrite Hdomτ, Hdom_my. reflexivity.
              ** change (y ∉ (dom (σn : gmap K V) : gset K)).
                 rewrite Hdomσn. exact Hy_n.
              ** replace (worldA_dom (n : WorldAT) ∩ worldA_dom (m : WorldAT))
                   with (worldA_dom (m : WorldAT)) in Hrestrict by set_solver.
                 exact Hrestrict.
        -- intros [τny [[σn [σy [Hσn [Hσy [Hagree ->]]]]] Hrestrict]].
           rewrite Hdom_my in Hrestrict.
           replace ((worldA_dom (n : WorldAT) ∪ {[y]}) ∩
             (worldA_dom (m : WorldAT) ∪ {[y]}))
             with (worldA_dom (m : WorldAT) ∪ {[y]}) in Hrestrict by set_solver.
           change (@storeA_restrict V K _ _
             (@union (gmap K V) _ σn (@storeA_restrict V K _ _ σy ({[y]} : gset K)))
             (worldA_dom (m : WorldAT) ∪ {[y]}) = τ) in Hrestrict.
           assert (Hglue :
             @storeA_restrict V K _ _
               (@union (gmap K V) _ σn (@storeA_restrict V K _ _ σy ({[y]} : gset K)))
               (worldA_dom (m : WorldAT) ∪ {[y]}) = σy).
           {
             apply storeA_restrict_union_base_singleton.
             - pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
               change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
               intros z Hz. change (z ∈ (dom (σn : gmap K V) : gset K)).
               rewrite Hdomσn. apply Hdom_m_n. exact Hz.
             - pose proof (wfworldA_store_dom my σy Hσy) as Hdomσy.
               change (dom (σy : gmap K V) = worldA_dom (my : WorldAT)) in Hdomσy.
               change ((dom (σy : gmap K V) : gset K) =
                 worldA_dom (m : WorldAT) ∪ {[y]}).
               rewrite Hdomσy, Hdom_my. reflexivity.
             - pose proof (wfworldA_store_dom n σn Hσn) as Hdomσn.
               change (dom (σn : gmap K V) = worldA_dom (n : WorldAT)) in Hdomσn.
               change (y ∉ (dom (σn : gmap K V) : gset K)).
               rewrite Hdomσn. exact Hy_n.
             - exact Hagree.
           }
           rewrite Hglue in Hrestrict. subst τ. exact Hσy.
Qed.

End ResourceExtensionDerivedA.
