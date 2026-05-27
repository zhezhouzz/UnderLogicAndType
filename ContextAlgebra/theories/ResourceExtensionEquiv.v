(** * Fiber extension equivalence and commuting lemmas *)

From ContextPrelude Require Import Prelude Store.
From ContextAlgebra Require Import ResourceCore ResourceKeyAction ResourceRestrict
  ResourceAlgebra ResourceExtensionCore.

Section ResourceExtensionA.

Context {K : Type} `{Countable K} `{!SwapKey K}.
Context {V : Type} `{ValueSig V}.

Local Notation StoreAT := (@StoreA V K _ _) (only parsing).
Local Notation WorldAT := (@WorldA K _ _ V) (only parsing).
Local Notation WfWorldAT := (@WfWorldA K _ _ V) (only parsing).
Local Notation fiber_extensionA := (@fiber_extensionA K _ _ V).

Local Notation "m '#>' F '~~A>' n" := (resA_extend_by m F n)
  (at level 70, F at next level, n at next level).

Lemma fiber_extensionA_functional_outputs_eq
    (m : WfWorldAT) (F : fiber_extensionA)
    (σ : StoreAT) (w1 w2 : WfWorldAT) (σe1 σe2 : StoreAT) :
  extension_applicableA F m →
  fiber_extensionA_functional_on m F →
  (m : WorldAT) σ →
  extA_rel F (@storeA_restrict V K _ _ σ (extA_in F)) w1 →
  extA_rel F (@storeA_restrict V K _ _ σ (extA_in F)) w2 →
  (w1 : WorldAT) σe1 →
  (w2 : WorldAT) σe2 →
  σe1 = σe2.
Proof.
  intros Happ Hfun Hσ Hw1 Hw2 Hσe1 Hσe2.
  assert (Hproj_dom :
      dom (@storeA_restrict V K _ _ σ (extA_in F)) = extA_in F)
    by (eapply extA_projection_dom; eauto).
  pose proof (proj1 (extA_rel_extensional F
    (@storeA_restrict V K _ _ σ (extA_in F)) w1 w2 σe1
    Hproj_dom Hw1 Hw2) Hσe1) as Hσe1_w2.
  eapply Hfun; eauto.
Qed.

Lemma resA_extend_by_output_unique
    (m : WfWorldAT) (F G : fiber_extensionA) (n : WfWorldAT) :
  m #> F ~~A> n →
  m #> G ~~A> n →
  extA_out F = extA_out G.
Proof.
  intros HF HG.
  pose proof (resA_extend_by_dom _ _ _ HF) as HFdom.
  pose proof (resA_extend_by_dom _ _ _ HG) as HGdom.
  pose proof (extA_app_out _ _ (resA_extend_by_applicable _ _ _ HF)) as HFfresh.
  pose proof (extA_app_out _ _ (resA_extend_by_applicable _ _ _ HG)) as HGfresh.
  set_solver.
Qed.

Lemma resA_extend_by_fiber_equiv_on
    (m : WfWorldAT) (F G : fiber_extensionA) (n : WfWorldAT) :
  extA_in F = extA_in G →
  m #> F ~~A> n →
  m #> G ~~A> n →
  fiber_extensionA_equiv_on m F G.
Proof.
  intros Hin HF HG. split; [exact Hin |].
  assert (Hdir :
    forall A B,
      extA_in A = extA_in B ->
      m #> A ~~A> n ->
      m #> B ~~A> n ->
      forall σ wA wB σe,
        (m : WorldAT) σ ->
        extA_rel A (@storeA_restrict V K _ _ σ (extA_in A)) wA ->
        extA_rel B (@storeA_restrict V K _ _ σ (extA_in B)) wB ->
        (wA : WorldAT) σe ->
        (wB : WorldAT) σe).
  {
    intros A B HAB HA HB σ wA wB σe Hσ HArel HBrel HAe.
    pose proof (resA_extend_by_applicable _ _ _ HA) as HAppA.
    pose proof (resA_extend_by_applicable _ _ _ HB) as HAppB.
    pose proof (resA_extend_store_compat m A σ wA σe HAppA Hσ HArel HAe)
      as HcompatA.
    assert (Hn : (n : WorldAT) (@union (gmap K V) _ σ σe)).
    {
      apply (proj2 (resA_extend_by_store_iff m A n
        (@union (gmap K V) _ σ σe) HA)).
      exists σ, wA, σe. repeat split; eauto.
    }
    apply (proj1 (resA_extend_by_store_iff m B n
      (@union (gmap K V) _ σ σe) HB)) in Hn.
    destruct Hn as [σB [wBe [σBe [HσB [HBwe [HBe Heq]]]]]].
    pose proof (resA_extend_store_compat m B σB wBe σBe HAppB HσB HBwe HBe)
      as HcompatB.
    assert (Hdomσ : dom (σ : gmap K V) = worldA_dom (m : WorldAT)).
    { exact (wfworldA_store_dom m σ Hσ). }
    assert (HdomσB : dom (σB : gmap K V) = worldA_dom (m : WorldAT)).
    { exact (wfworldA_store_dom m σB HσB). }
    assert (HprojA :
        dom (@storeA_restrict V K _ _ σ (extA_in A)) = extA_in A)
      by (eapply extA_projection_dom; eauto).
    assert (HprojB :
        dom (@storeA_restrict V K _ _ σB (extA_in B)) = extA_in B)
      by (eapply extA_projection_dom; eauto).
    assert (Hdomσe : dom (σe : gmap K V) = extA_out A).
    {
      pose proof (wfworldA_store_dom wA σe HAe) as Hdom_wA.
      change (dom (σe : gmap K V) = worldA_dom (wA : WorldAT)) in Hdom_wA.
      rewrite Hdom_wA. eapply extA_rel_dom; eauto.
    }
    assert (HdomσBe : dom (σBe : gmap K V) = extA_out B).
    {
      pose proof (wfworldA_store_dom wBe σBe HBe) as Hdom_wBe.
      change (dom (σBe : gmap K V) = worldA_dom (wBe : WorldAT)) in Hdom_wBe.
      rewrite Hdom_wBe. eapply extA_rel_dom; eauto.
    }
    pose proof (resA_extend_by_output_unique m A B n HA HB) as Hout.
    assert (HbaseA :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σ σe)
          (worldA_dom (m : WorldAT)) = σ).
    {
      apply (storeA_restrict_union_piece_l σ σe
        (worldA_dom (m : WorldAT)) (extA_out A)); eauto.
      - change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite Hdomσ. reflexivity.
      - change (dom (σe : gmap K V) ⊆ extA_out A).
        rewrite Hdomσe. reflexivity.
      - pose proof (extA_app_out _ _ HAppA). set_solver.
    }
    assert (HbaseB :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σB σBe)
          (worldA_dom (m : WorldAT)) = σB).
    {
      apply (storeA_restrict_union_piece_l σB σBe
        (worldA_dom (m : WorldAT)) (extA_out B)); eauto.
      - change (dom (σB : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite HdomσB. reflexivity.
      - change (dom (σBe : gmap K V) ⊆ extA_out B).
        rewrite HdomσBe. reflexivity.
      - pose proof (extA_app_out _ _ HAppB). set_solver.
    }
    assert (HσB_eq : σB = σ).
    {
      rewrite <- Heq in HbaseB.
      rewrite HbaseA in HbaseB. symmetry. exact HbaseB.
    }
    subst σB.
    assert (HextraA :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σ σe) (extA_out A) = σe).
    {
      apply (storeA_restrict_union_piece_r σ σe
        (worldA_dom (m : WorldAT)) (extA_out A)); eauto.
      - change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite Hdomσ. reflexivity.
      - change (dom (σe : gmap K V) ⊆ extA_out A).
        rewrite Hdomσe. reflexivity.
      - pose proof (extA_app_out _ _ HAppA). set_solver.
    }
    assert (HextraB :
        @storeA_restrict V K _ _ (@union (gmap K V) _ σ σBe) (extA_out B) = σBe).
    {
      apply (storeA_restrict_union_piece_r σ σBe
        (worldA_dom (m : WorldAT)) (extA_out B)); eauto.
      - change (dom (σ : gmap K V) ⊆ worldA_dom (m : WorldAT)).
        rewrite Hdomσ. reflexivity.
      - change (dom (σBe : gmap K V) ⊆ extA_out B).
        rewrite HdomσBe. reflexivity.
      - pose proof (extA_app_out _ _ HAppB). set_solver.
    }
    assert (HσBe_eq : σBe = σe).
    {
      rewrite <- Heq in HextraB.
      rewrite <- Hout in HextraB.
      rewrite HextraA in HextraB. symmetry. exact HextraB.
    }
    subst σBe.
    replace (@storeA_restrict V K _ _ σ (extA_in A))
      with (@storeA_restrict V K _ _ σ (extA_in B)) in HBwe
      by (rewrite HAB; reflexivity).
    replace (@storeA_restrict V K _ _ σ (extA_in A))
      with (@storeA_restrict V K _ _ σ (extA_in B)) in HBrel
      by (rewrite HAB; reflexivity).
    apply (proj1 (extA_rel_extensional B
      (@storeA_restrict V K _ _ σ (extA_in B)) wBe wB σe
      HprojB HBwe HBrel)).
    exact HBe.
  }
  intros σ wF wG σe Hσ HFrel HGrel. split.
  - eapply Hdir; eauto.
  - intros HGe.
    eapply Hdir with (A := G) (B := F) (σ := σ) (wA := wG) (wB := wF); eauto;
      symmetry; exact Hin.
Qed.

Lemma resA_extend_by_commute
    (m : WfWorldAT) (F G : fiber_extensionA)
    (mF mG mFG mGF : WfWorldAT) :
  m #> F ~~A> mF →
  m #> G ~~A> mG →
  mF #> G ~~A> mFG →
  mG #> F ~~A> mGF →
  mFG = mGF.
Proof.
  intros HF HG HFG HGF.
  pose proof (resA_extend_by_dom _ _ _ HF) as Hdom_mF.
  pose proof (resA_extend_by_dom _ _ _ HG) as Hdom_mG.
  pose proof (resA_extend_by_applicable _ _ _ HF) as HAppF_m.
  pose proof (resA_extend_by_applicable _ _ _ HG) as HAppG_m.
  pose proof (resA_extend_by_applicable _ _ _ HFG) as HAppG_mF.
  pose proof (resA_extend_by_applicable _ _ _ HGF) as HAppF_mG.
  pose proof (extA_app_out _ _ HAppF_m) as HFfresh_m.
  pose proof (extA_app_out _ _ HAppG_m) as HGfresh_m.
  pose proof (extA_app_out _ _ HAppG_mF) as HGfresh_mF.
  pose proof (extA_app_out _ _ HAppF_mG) as HFfresh_mG.
  assert (HFGfresh : extA_out F ## extA_out G) by set_solver.
  assert (HGFfresh : extA_out G ## extA_out F) by set_solver.
  apply wfworldA_ext. apply worldA_ext.
  - rewrite (resA_extend_by_dom _ _ _ HFG).
    rewrite (resA_extend_by_dom _ _ _ HGF).
    rewrite Hdom_mF, Hdom_mG. set_solver.
  - intros σ. split.
    + intros Hσ.
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ HGF)).
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HFG)) in Hσ.
      destruct Hσ as [σmF [wG [σge [HmFσ [HGrel [HGstore ->]]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HF)) in HmFσ.
      destruct HmFσ as [σm [wF [σfe [Hmσ [HFrel [HFstore ->]]]]]].
      pose proof (resA_extend_store_compat m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as HcompatF.
      pose proof (extA_output_store_dom_from_base m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as Hdomσfe.
      assert (HprojG :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σfe) (extA_in G) =
          @storeA_restrict V K _ _ σm (extA_in G)).
      {
        exact (resA_extend_store_restrict_other_input m F G σm wF σfe
          HAppF_m HAppG_m Hmσ HFrel HFstore).
      }
      rewrite HprojG in HGrel.
      pose proof (resA_extend_store_compat m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as HcompatG.
      pose proof (extA_output_store_dom_from_base m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as Hdomσge.
      exists (@union (gmap K V) _ (σm : gmap K V) (σge : gmap K V)), wF, σfe.
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ HG)).
        exists σm, wG, σge. repeat split; eauto.
      * split.
        -- assert (HprojF :
             @storeA_restrict V K _ _
               (@union (gmap K V) _ σm σge) (extA_in F) =
             @storeA_restrict V K _ _ σm (extA_in F)).
           {
             exact (resA_extend_store_restrict_other_input m G F σm wG σge
               HAppG_m HAppF_m Hmσ HGrel HGstore).
           }
           rewrite HprojF. exact HFrel.
        -- split; [exact HFstore |].
           assert (Hcompat_extra : @storeA_compat V K _ _ σfe σge).
           {
             apply storeA_disj_dom_compat.
             change (dom (σfe : gmap K V) ∩ dom (σge : gmap K V) = ∅).
             rewrite Hdomσfe, Hdomσge. set_solver.
           }
           apply storeA_union_swap_right. exact Hcompat_extra.
    + intros Hσ.
      apply (proj2 (resA_extend_by_store_iff _ _ _ _ HFG)).
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HGF)) in Hσ.
      destruct Hσ as [σmG [wF [σfe [HmGσ [HFrel [HFstore ->]]]]]].
      apply (proj1 (resA_extend_by_store_iff _ _ _ _ HG)) in HmGσ.
      destruct HmGσ as [σm [wG [σge [Hmσ [HGrel [HGstore ->]]]]]].
      pose proof (resA_extend_store_compat m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as HcompatG.
      pose proof (extA_output_store_dom_from_base m G σm wG σge
        HAppG_m Hmσ HGrel HGstore) as Hdomσge.
      assert (HprojF :
          @storeA_restrict V K _ _ (@union (gmap K V) _ σm σge) (extA_in F) =
          @storeA_restrict V K _ _ σm (extA_in F)).
      {
        exact (resA_extend_store_restrict_other_input m G F σm wG σge
          HAppG_m HAppF_m Hmσ HGrel HGstore).
      }
      rewrite HprojF in HFrel.
      pose proof (resA_extend_store_compat m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as HcompatF.
      pose proof (extA_output_store_dom_from_base m F σm wF σfe
        HAppF_m Hmσ HFrel HFstore) as Hdomσfe.
      exists (@union (gmap K V) _ (σm : gmap K V) (σfe : gmap K V)), wG, σge.
      split.
      * apply (proj2 (resA_extend_by_store_iff _ _ _ _ HF)).
        exists σm, wF, σfe. repeat split; eauto.
      * split.
        -- assert (HprojG :
             @storeA_restrict V K _ _
               (@union (gmap K V) _ σm σfe) (extA_in G) =
             @storeA_restrict V K _ _ σm (extA_in G)).
           {
             exact (resA_extend_store_restrict_other_input m F G σm wF σfe
               HAppF_m HAppG_m Hmσ HFrel HFstore).
           }
           rewrite HprojG. exact HGrel.
        -- split; [exact HGstore |].
           assert (Hcompat_extra : @storeA_compat V K _ _ σge σfe).
           {
             apply storeA_disj_dom_compat.
             change (dom (σge : gmap K V) ∩ dom (σfe : gmap K V) = ∅).
             rewrite Hdomσge, Hdomσfe. set_solver.
           }
           apply storeA_union_swap_right. exact Hcompat_extra.
Qed.

End ResourceExtensionA.
