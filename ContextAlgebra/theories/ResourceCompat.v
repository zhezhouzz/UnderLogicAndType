From ContextBase Require Import Prelude LogicVar BaseTactics.
From ContextStore Require Import Store.
From ContextAlgebra Require Import ResourceCore ResourceAlgebra ResourceExtension ResourceInterface.
From Stdlib Require Import Logic.Classical Logic.ClassicalEpsilon Logic.ProofIrrelevance.

(** * Resource extension compatibility helpers

    The core extension interface is relation-shaped: a fiber extension relates
    an input projection to one or more extension worlds.  This file packages
    the common compatibility/projection facts used by higher layers. *)


Section ResourceCompat.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FiberExtensionT := (fiber_extension (V := V)) (only parsing).
Local Notation StoreT := (gmap atom V) (only parsing).

Definition ext_in (F : FiberExtensionT) : aset := extA_in F.
Definition ext_out (F : FiberExtensionT) : aset := extA_out F.
Definition ext_rel (F : FiberExtensionT) : StoreT -> WfWorldT -> Prop :=
  extA_rel F.

Definition mk_fiber_extension_rel
    (X Y : aset) (R : StoreT -> WfWorldT -> Prop)
    (Hdisj : X ## Y)
    (Hdom : forall σ w, dom σ = X -> R σ w -> world_dom (w : WorldT) = Y)
    (Hne : forall σ, dom σ = X -> exists w σe, R σ w /\ (w : WorldT) σe)
    (Hext : forall σ w1 w2 σe,
      dom σ = X -> R σ w1 -> R σ w2 ->
      ((w1 : WorldT) σe <-> (w2 : WorldT) σe))
    : FiberExtensionT :=
  mk_fiber_extensionA X Y R Hdisj Hdom Hne Hext.

Definition mk_fiber_extension
    (X Y : aset) (f : StoreT -> WfWorldT)
    (Hdisj : X ## Y)
    (Hdom : forall σ, dom σ = X -> world_dom (f σ : WorldT) = Y)
    (Hne : forall σ, dom σ = X -> exists σe, (f σ : WorldT) σe)
    : FiberExtensionT :=
  mk_fiber_extension_rel X Y
    (fun σ w => w = f σ)
    Hdisj
    ltac:(intros σ w Hσ ->; apply Hdom; exact Hσ)
    ltac:(intros σ Hσ; destruct (Hne σ Hσ) as [σe Hσe];
      exists (f σ), σe; split; [reflexivity | exact Hσe])
    ltac:(intros σ w1 w2 σe _ -> ->; reflexivity).

Definition fiber_extension_atom_swap
    (x y : atom) (F : FiberExtensionT) : FiberExtensionT.
Proof.
  refine (mk_fiber_extension_rel
    (set_swap x y (ext_in F))
    (set_swap x y (ext_out F))
    (fun σ w =>
      exists σ0 w0,
        ext_rel F σ0 w0 /\
        σ = storeA_swap x y σ0 /\
        w = res_atom_swap x y w0)
    _ _ _ _).
  - pose proof (extA_disjoint F) as Hdisj.
    intros z HzIn HzOut.
    rewrite set_swap_elem in HzIn.
    rewrite set_swap_elem in HzOut.
    exact (Hdisj _ HzIn HzOut).
  - intros σ w Hσdom [σ0 [w0 [HF [-> ->]]]].
    change (world_dom (res_atom_swap x y w0 : WorldT) =
      set_swap x y (ext_out F)).
    rewrite world_dom_res_atom_swap.
    change (set_swap x y (world_dom (w0 : WorldT)) =
      set_swap x y (ext_out F)).
    assert (Hσ0dom : dom (σ0 : StoreT) = ext_in F).
    {
      rewrite storeA_swap_dom in Hσdom.
      rewrite <- (set_swap_involutive x y (dom (σ0 : StoreT))).
      rewrite Hσdom.
      rewrite set_swap_involutive.
      reflexivity.
    }
    pose proof (extA_rel_dom F σ0 w0) as Hdom_w0.
    change (dom σ0 = ext_in F ->
      ext_rel F σ0 w0 ->
      world_dom (w0 : WorldT) = ext_out F) in Hdom_w0.
    rewrite (Hdom_w0 Hσ0dom HF). reflexivity.
  - intros σ Hσdom.
    set (σ0 := storeA_swap x y σ).
    assert (Hσ0dom : dom (σ0 : StoreT) = ext_in F).
    {
      unfold σ0.
      rewrite storeA_swap_dom.
      rewrite Hσdom.
      rewrite set_swap_involutive.
      reflexivity.
    }
    destruct (extA_rel_nonempty F σ0 Hσ0dom) as [w0 [σe [HF Hσe]]].
    exists (res_atom_swap x y w0), (storeA_swap x y σe).
    split.
    + exists σ0, w0. repeat split; eauto.
      unfold σ0. symmetry. apply storeA_swap_involutive.
    + exists σe. split; [exact Hσe | reflexivity].
  - intros σ w1 w2 σe Hσdom
      [σ1 [w01 [HF1 [Hσ1eq ->]]]]
      [σ2 [w02 [HF2 [Hσ2eq ->]]]].
    assert (Hσ1dom : dom (σ1 : StoreT) = ext_in F).
    {
      rewrite Hσ1eq in Hσdom.
      rewrite storeA_swap_dom in Hσdom.
      rewrite <- (set_swap_involutive x y (dom (σ1 : StoreT))).
      rewrite Hσdom.
      rewrite set_swap_involutive.
      reflexivity.
    }
    assert (Hσ12 : σ1 = σ2).
    {
      assert (Hsw : storeA_swap x y σ1 = storeA_swap x y σ2)
        by congruence.
      rewrite <- (storeA_swap_involutive x y σ1).
      rewrite Hsw.
      apply storeA_swap_involutive.
    }
    subst σ2.
    split.
    + intros [τ [Hτ Hτeq]].
      pose proof (proj1 (extA_rel_extensional F σ1 w01 w02 τ
        Hσ1dom HF1 HF2) Hτ) as Hτ2.
      exists τ. split; [exact Hτ2 | exact Hτeq].
    + intros [τ [Hτ Hτeq]].
      pose proof (proj2 (extA_rel_extensional F σ1 w01 w02 τ
        Hσ1dom HF1 HF2) Hτ) as Hτ1.
      exists τ. split; [exact Hτ1 | exact Hτeq].
Defined.

Lemma res_extend_by_atom_swap
    (x y : atom) (m n : WfWorldT) (F : FiberExtensionT) :
  res_extend_by m F n ->
  res_extend_by (res_atom_swap x y m) (fiber_extension_atom_swap x y F)
    (res_atom_swap x y n).
Proof.
  intros Hext.
  pose proof (resA_extend_by_applicable _ _ _ Hext) as Happ.
  split.
  - constructor.
    + cbn [fiber_extension_atom_swap mk_fiber_extension_rel extA_in].
      rewrite world_dom_res_atom_swap.
      pose proof (extA_app_in _ _ Happ) as Hin.
      intros z Hz.
      change (z ∈ set_swap x y (ext_in F)) in Hz.
      change (z ∈ set_swap x y (world_dom (m : WorldT))).
      rewrite set_swap_elem in Hz |- *.
      apply Hin. exact Hz.
    + cbn [fiber_extension_atom_swap mk_fiber_extension_rel extA_out].
      rewrite world_dom_res_atom_swap.
      pose proof (extA_app_out _ _ Happ) as Hout.
      intros z HzOut HzDom.
      change (z ∈ set_swap x y (ext_out F)) in HzOut.
      change (z ∈ set_swap x y (world_dom (m : WorldT))) in HzDom.
      rewrite set_swap_elem in HzOut.
      rewrite set_swap_elem in HzDom.
      exact (Hout _ HzOut HzDom).
  - split.
    + cbn [fiber_extension_atom_swap mk_fiber_extension_rel extA_out].
      rewrite !world_dom_res_atom_swap.
      pose proof (resA_extend_by_dom _ _ _ Hext) as Hdom_n.
      change (world_dom (n : WorldT) =
        world_dom (m : WorldT) ∪ ext_out F) in Hdom_n.
      change (set_swap x y (world_dom (n : WorldT)) =
        set_swap x y (world_dom (m : WorldT)) ∪
        set_swap x y (ext_out F)).
      rewrite Hdom_n.
      rewrite set_swap_union. reflexivity.
    + intros σ. split.
      * intros [σn [Hσn Hσeq]]. subst σ.
        apply (proj1 (resA_extend_by_store_iff _ _ _ _ Hext)) in Hσn.
        destruct Hσn as [σm [we [σe [Hσm [HF [Hσe Hunion]]]]]].
        subst σn.
        exists (storeA_swap x y σm),
          (res_atom_swap x y we),
          (storeA_swap x y σe).
        repeat split.
        -- exists σm. split; [exact Hσm | reflexivity].
        -- exists (storeA_restrict σm (ext_in F)), we.
           repeat split.
           ++ exact HF.
           ++ change (storeA_restrict (storeA_swap x y σm)
                (set_swap x y (ext_in F)) =
                storeA_swap x y (storeA_restrict σm (ext_in F))).
              apply storeA_restrict_swap.
        -- exists σe. split; [exact Hσe | reflexivity].
        -- apply storeA_swap_union.
      * intros Hsw.
        destruct Hsw as [σm_sw [we_sw [σe_sw
          [Hσm_sw [HF_sw [Hσe_sw Hunion]]]]]].
        destruct Hσm_sw as [σm [Hσm Hσm_sw]].
        destruct HF_sw as [σin [we [HF [Hσin_sw Hwe_sw]]]].
        subst we_sw.
        destruct Hσe_sw as [σe [Hσe Hσe_sw]].
        subst σm_sw σe_sw.
        assert (Hσin_eq : σin = storeA_restrict σm (ext_in F)).
        {
          rewrite <- (storeA_swap_involutive x y σin).
          rewrite <- Hσin_sw.
          change (storeA_swap x y
            (storeA_restrict (storeA_swap x y σm)
              (set_swap x y (ext_in F))) =
            storeA_restrict σm (ext_in F)).
          rewrite storeA_restrict_swap.
          apply storeA_swap_involutive.
        }
        subst σin.
        exists (@union (gmap atom V) _ σm σe). split.
        -- apply (proj2 (resA_extend_by_store_iff _ _ _ _ Hext)).
           exists σm, we, σe. repeat split; eauto.
        -- subst σ.
           apply storeA_swap_union.
Qed.

Definition mk_forall_extension
    (X : aset) (y : atom) (f : StoreT -> WfWorldT)
    (Hfresh : y ∉ X)
    (Hdom : forall σ, dom σ = X -> world_dom (f σ : WorldT) = {[y]})
    (Hne : forall σ, dom σ = X -> exists σy, (f σ : WorldT) σy)
    : FiberExtensionT :=
  mk_fiber_extension X {[y]} f ltac:(set_solver) Hdom Hne.

Definition forall_extension_shape (X : aset) (y : atom) (F : FiberExtensionT) : Prop :=
  ext_in F = X /\ ext_out F = {[y]}.

Definition one_point_projected_output_raw
    (my : WfWorldT) (X : aset) (y : atom) (σX : StoreT) : WorldT :=
  @mk_worldA atom _ _ V {[y]}
    (fun σy =>
      (exists σmy : StoreT,
        (my : WorldT) σmy /\
        store_restrict σmy X = σX /\
        σy = store_restrict σmy {[y]}) \/
      ((forall σmy : StoreT,
          (my : WorldT) σmy ->
          store_restrict σmy X <> σX) /\
        σy = ({[y := inhabitant]} : StoreT))).

Definition one_point_projected_output
    (m my : WfWorldT) (X : aset) (y : atom) (σX : StoreT)
    (Hy : y ∉ world_dom (m : WorldT))
    (Hdom_my : world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]})
    : WfWorldT.
Proof.
  refine (exist _ (one_point_projected_output_raw my X y σX) _).
  split.
  - destruct (classic (exists σmy : StoreT,
      (my : WorldT) σmy /\ store_restrict σmy X = σX))
      as [[σmy [Hmy Hproj]]|Hnone].
    + exists (store_restrict σmy {[y]}). left.
      exists σmy. repeat split; eauto.
    + exists ({[y := inhabitant]} : StoreT). right.
      split; [|reflexivity].
      intros σmy Hmy Hproj. apply Hnone. exists σmy. split; assumption.
  - intros σy Hσy.
    destruct Hσy as [[σmy [Hmy [_ ->]]]|[_ ->]].
    + replace (dom (store_restrict σmy {[y]} : StoreT))
        with (dom (σmy : gmap atom V) ∩ {[y]}).
      pose proof (wfworld_store_dom my σmy Hmy) as Hσmy_dom.
      change (dom (σmy : gmap atom V) = world_dom (my : WorldT))
        in Hσmy_dom.
      rewrite Hσmy_dom, Hdom_my.
      apply set_eq. intros z. set_solver.
      symmetry.
      change (dom (store_restrict σmy {[y]} : gmap atom V) =
        dom (σmy : gmap atom V) ∩ {[y]}).
      apply storeA_restrict_dom.
    + change (dom ({[y := inhabitant]} : gmap atom V) = {[y]}).
      apply set_eq. intros z. apply dom_singleton.
Defined.

Definition one_point_projected_extension
    (m my : WfWorldT) (X : aset) (y : atom)
    (Hy : y ∉ world_dom (m : WorldT))
    (Hdisj : X ## {[y]})
    (Hdom_my : world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]})
    : FiberExtensionT :=
  mk_fiber_extension X {[y]}
    (fun σX => one_point_projected_output m my X y σX Hy Hdom_my)
    Hdisj
    ltac:(intros; reflexivity)
    ltac:(intros σX _; destruct
      (world_wf (one_point_projected_output m my X y σX Hy Hdom_my))
      as [Hne _]; exact Hne).

Lemma one_point_projected_extension_projection_eq
    (m my : WfWorldT) (X : aset) (y : atom)
    (Hy : y ∉ world_dom (m : WorldT))
    (Hdisj : X ## {[y]})
    (Hdom_my : world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]})
    (Hrestrict : res_restrict my (world_dom (m : WorldT)) = m) :
  X ⊆ world_dom (m : WorldT) ->
  forall n : WfWorldT,
    res_extend_by m
      (one_point_projected_extension m my X y Hy Hdisj Hdom_my)
      n ->
    res_restrict n (X ∪ {[y]}) = res_restrict my (X ∪ {[y]}).
Proof.
  intros HXm n Hext.
  apply wfworld_ext. apply world_ext.
  - simpl.
    pose proof (res_extend_by_dom m
      (one_point_projected_extension m my X y Hy Hdisj Hdom_my) n Hext)
      as Hdom_n.
    change (world_dom (n : WorldT) ∩ (X ∪ {[y]}) =
      world_dom (my : WorldT) ∩ (X ∪ {[y]})).
    transitivity ((world_dom (m : WorldT) ∪ {[y]}) ∩ (X ∪ {[y]})).
    + rewrite Hdom_n. reflexivity.
    + rewrite Hdom_my. reflexivity.
  - intros σ. split.
    + intros [σn [Hσn Hrestrict_n]].
      destruct Hext as [_ [_ Hstores]].
      apply (proj1 (Hstores σn)) in Hσn.
      destruct Hσn as [σm [we [σe [Hσm [Hrel [Hσe ->]]]]]].
      simpl in Hrel. subst we.
      simpl in Hσe.
      destruct Hσe as [[σmy [Hσmy [HprojX ->]]]|[Hnone ->]].
      * exists σmy. split; [exact Hσmy |].
        rewrite <- Hrestrict_n.
        symmetry.
        apply storeA_restrict_union_base_project.
        -- pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
           change (X ⊆ dom (σm : gmap atom V)). set_solver.
        -- transitivity (world_dom (my : WorldT)).
           ++ apply (wfworld_store_dom my); exact Hσmy.
           ++ rewrite Hdom_my.
              pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
              set_solver.
        -- pose proof (wfworld_store_dom m σm Hσm) as Hdomσm.
           change (y ∉ dom (σm : gmap atom V)). set_solver.
        -- exact HprojX.
      * exfalso.
        rewrite <- Hrestrict in Hσm.
        destruct Hσm as [σmy [Hσmy Hproj_m]].
        eapply Hnone; [exact Hσmy |].
        rewrite <- Hproj_m.
        symmetry. apply storeA_restrict_twice_subset. exact HXm.
    + intros [σmy [Hσmy Hrestrict_my]].
      destruct Hext as [_ [_ Hstores]].
      set (σm := store_restrict σmy (world_dom (m : WorldT)) : StoreT).
      assert (Hσm : (m : WorldT) σm).
      {
        rewrite <- Hrestrict.
        exists σmy. split; [exact Hσmy | reflexivity].
      }
      set (σe := store_restrict σmy {[y]} : StoreT).
      assert (Hrel :
          (one_point_projected_output m my X y
            (store_restrict σm X) Hy Hdom_my : WorldT) σe).
      {
        left. exists σmy. repeat split; eauto.
        subst σm.
        symmetry. apply storeA_restrict_twice_subset. exact HXm.
      }
      assert (Hσn : (n : WorldT) (σm ∪ σe)).
      {
        apply (proj2 (Hstores (σm ∪ σe))).
        exists σm,
          (one_point_projected_output m my X y
            (store_restrict σm X) Hy Hdom_my),
          σe.
        repeat split; eauto.
      }
      exists (σm ∪ σe). split; [exact Hσn |].
      rewrite <- Hrestrict_my.
      subst σm σe.
      apply storeA_restrict_union_base_project.
      * change (X ⊆ dom (store_restrict σmy (world_dom (m : WorldT)) : gmap atom V)).
        rewrite storeA_restrict_dom.
        assert (Hdomσmy :
            dom (σmy : gmap atom V) = world_dom (m : WorldT) ∪ {[y]}).
        {
          transitivity (world_dom (my : WorldT)).
          - apply (wfworld_store_dom my); exact Hσmy.
          - exact Hdom_my.
        }
        rewrite Hdomσmy. set_solver.
      * assert (Hdomσmy :
            dom (σmy : gmap atom V) = world_dom (m : WorldT) ∪ {[y]}).
        {
          transitivity (world_dom (my : WorldT)).
          - apply (wfworld_store_dom my); exact Hσmy.
          - exact Hdom_my.
        }
        change (dom (σmy : gmap atom V) =
          dom (store_restrict σmy (world_dom (m : WorldT)) : gmap atom V) ∪
          {[y]}).
        rewrite storeA_restrict_dom, Hdomσmy.
        apply set_eq. intros z. set_solver.
      * change (y ∉ dom (store_restrict σmy (world_dom (m : WorldT)) : gmap atom V)).
        rewrite storeA_restrict_dom.
        assert (Hdomσmy :
            dom (σmy : gmap atom V) = world_dom (m : WorldT) ∪ {[y]}).
        {
          transitivity (world_dom (my : WorldT)).
          - apply (wfworld_store_dom my); exact Hσmy.
          - exact Hdom_my.
        }
        rewrite Hdomσmy. set_solver.
      * rewrite storeA_restrict_twice_subset by exact HXm.
        reflexivity.
Qed.

Lemma one_point_ext_by_projection
    (m my : WfWorldT) (X : aset) (y : atom)
    (Hy : y ∉ world_dom (m : WorldT))
    (Hdisj : X ## {[y]})
    (Hdom_my : world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]})
    (Hrestrict : res_restrict my (world_dom (m : WorldT)) = m) :
  X ⊆ world_dom (m : WorldT) ->
  exists n : WfWorldT,
    res_extend_by m
      (one_point_projected_extension m my X y Hy Hdisj Hdom_my)
      n /\
    res_restrict n (X ∪ {[y]}) = res_restrict my (X ∪ {[y]}).
Proof.
  intros HXm.
  set (F := one_point_projected_extension m my X y Hy Hdisj Hdom_my).
  assert (Happ : extension_applicable F m).
  {
    constructor.
    - subst F. simpl. exact HXm.
    - subst F. simpl. set_solver.
  }
  destruct (res_extend_by_exists m F Happ) as [n Hext].
  exists n. split; [exact Hext |].
  subst F.
  eapply one_point_projected_extension_projection_eq; eauto.
Qed.

Lemma forall_extension_from_world_dom_projection
    (m my : WfWorldT) (X : aset) (y : atom) :
  X ⊆ world_dom (m : WorldT) ->
  y ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  exists (F : FiberExtensionT) (n : WfWorldT),
    ext_in F = X /\
    ext_out F = {[y]} /\
    res_extend_by m F n /\
    res_restrict n (X ∪ {[y]}) = res_restrict my (X ∪ {[y]}).
Proof.
  intros HXm Hy Hdom_my Hrestrict.
  assert (Hdisj : X ## {[y]}) by set_solver.
  destruct (one_point_ext_by_projection
    m my X y Hy Hdisj Hdom_my Hrestrict HXm) as [n [Hext Hproj]].
  exists (one_point_projected_extension m my X y Hy Hdisj Hdom_my), n.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact Hext | exact Hproj].
Qed.

Lemma res_restrict_delete_extend_self (m : WfWorldT) x :
  x ∈ world_dom (m : WorldT) ->
  exists F : FiberExtensionT,
    ext_in F = world_dom (m : WorldT) ∖ {[x]} /\
    ext_out F = {[x]} /\
    res_extend_by
      (res_restrict m (world_dom (m : WorldT) ∖ {[x]})) F m.
Proof.
  intros Hx.
  set (m0 := res_restrict m (world_dom (m : WorldT) ∖ {[x]})).
  assert (Hx0 : x ∉ world_dom (m0 : WorldT)).
  { subst m0. apply res_restrict_delete_notin. }
  assert (Hdom_m : world_dom (m : WorldT) =
      world_dom (m0 : WorldT) ∪ {[x]}).
  { subst m0. apply res_restrict_delete_insert_dom. exact Hx. }
  assert (Hrestrict_m : res_restrict m (world_dom (m0 : WorldT)) = m0).
  { subst m0. apply res_restrict_self_dom. }
  assert (Hdisj : world_dom (m0 : WorldT) ## {[x]}) by set_solver.
  set (F := one_point_projected_extension
    m0 m (world_dom (m0 : WorldT)) x Hx0 Hdisj Hdom_m).
  assert (Happ : extension_applicable F m0).
  {
    constructor.
    - subst F. simpl. set_solver.
    - subst F. simpl. set_solver.
  }
  destruct (res_extend_by_exists m0 F Happ) as [n Hext].
  pose proof (one_point_projected_extension_projection_eq
    m0 m (world_dom (m0 : WorldT)) x Hx0 Hdisj Hdom_m
    Hrestrict_m ltac:(set_solver) n Hext) as Hproj.
  assert (Hn_dom : world_dom (n : WorldT) = world_dom (m : WorldT)).
  {
    pose proof (res_extend_by_dom m0 F n Hext) as Hdom_n.
    subst F. simpl in Hdom_n.
    rewrite Hdom_n. symmetry. exact Hdom_m.
  }
  assert (Hn_eq : n = m).
  {
    transitivity (res_restrict n (world_dom (m : WorldT))).
    - symmetry. rewrite <- Hn_dom.
      apply res_restrict_eq_of_le. apply raw_le_refl.
    - rewrite <- Hdom_m in Hproj.
      rewrite Hproj.
      apply res_restrict_eq_of_le. apply raw_le_refl.
  }
  subst n.
  exists F. split.
  - subst F. simpl. set_solver.
  - split; [subst F; reflexivity|exact Hext].
Qed.

Local Lemma ext_rel_exists (F : FiberExtensionT) σ :
  dom σ = ext_in F ->
  exists w, ext_rel F σ w.
Proof.
  intros Hdom.
  destruct (extA_rel_nonempty F σ Hdom) as [w [σe [Hrel _]]].
  exists w. exact Hrel.
Qed.

Definition ext_fun (F : FiberExtensionT) (σ : StoreT) : WfWorldT.
Proof.
  destruct (decide (dom σ = ext_in F)) as [Hdom|_].
  - exact (proj1_sig (constructive_indefinite_description _
      (ext_rel_exists F σ Hdom))).
  - exact res_unit.
Defined.

Definition fiber_extension_input_widen
    (F : FiberExtensionT) (X' : aset)
    (Hin : ext_in F ⊆ X')
    (Hdisj : X' ## ext_out F) : FiberExtensionT :=
  mk_fiber_extension_rel X' (ext_out F)
    (fun σ w => ext_rel F (store_restrict σ (ext_in F)) w)
    Hdisj
    ltac:(intros σ w Hσ Hrel;
      eapply extA_rel_dom; [| exact Hrel];
      change (dom (store_restrict σ (ext_in F) : gmap atom V) = ext_in F);
      rewrite storeA_restrict_dom; set_solver)
    ltac:(intros σ Hσ;
      eapply extA_rel_nonempty;
      change (dom (store_restrict σ (ext_in F) : gmap atom V) = ext_in F);
      rewrite storeA_restrict_dom; set_solver)
    ltac:(intros σ w1 w2 σe Hσ Hrel1 Hrel2;
      eapply extA_rel_extensional; [| exact Hrel1 | exact Hrel2];
      change (dom (store_restrict σ (ext_in F) : gmap atom V) = ext_in F);
      rewrite storeA_restrict_dom; set_solver).

Record fiber_extension_input_widen_to
    (F F' : FiberExtensionT) : Prop := {
  input_widen_in : ext_in F ⊆ ext_in F';
  input_widen_out : ext_out F' = ext_out F;
  input_widen_rel :
    forall σ w,
      dom σ = ext_in F' ->
      (ext_rel F' σ w <->
       ext_rel F (store_restrict σ (ext_in F)) w);
}.

Local Lemma input_widen_projection_eq
    (m : WfWorldT) F F' σ :
  fiber_extension_input_widen_to F F' ->
  ext_in F' ⊆ world_dom (m : WorldT) ->
  (m : WorldT) σ ->
  store_restrict (store_restrict σ (ext_in F')) (ext_in F) =
  store_restrict σ (ext_in F).
Proof.
  intros Hwid Hin' Hσ.
  rewrite storeA_restrict_twice_subset; [reflexivity |].
  exact (input_widen_in _ _ Hwid).
Qed.

End ResourceCompat.

Notation "F '~>i' F'" := (fiber_extension_input_widen_to F F')
  (at level 70).
