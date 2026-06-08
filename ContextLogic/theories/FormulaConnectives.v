(** * ContextLogic.FormulaConnectives

    Derived proof principles for Context Logic connectives. *)

From ContextLogic Require Import FormulaAtom FormulaSemantics.
From ContextAlgebra Require Import ResourceInterface ResourceCompat.
From ContextBase Require Import LogicVarOpenEnv.
From Stdlib Require Import Lia Logic.ProofIrrelevance.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for the store-free formula semantics.  This file
    keeps only statements that still describe useful structure under the new
    dependent-lqual and extension-based forall definitions. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation StoreT := (Store (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma formula_scoped_atom_swap_iff
    (m : WfWorldT) (φ : FormulaT) x y :
  formula_scoped_in_world (res_atom_swap x y m) (formula_atom_swap x y φ) <->
  formula_scoped_in_world m φ.
Proof.
  unfold formula_scoped_in_world.
  rewrite formula_fv_atom_swap, world_dom_res_atom_swap.
  split.
  - intros Hsub z Hz.
    specialize (Hsub (swap x y z)).
    rewrite !set_swap_elem in Hsub.
    rewrite !swap_involutive in Hsub.
    exact (Hsub Hz).
  - intros Hsub z Hz.
    rewrite !set_swap_elem in *.
    apply Hsub. exact Hz.
Qed.

Lemma res_models_fuel_atom_swap
    gas (m : WfWorldT) (φ : FormulaT) x y :
  res_models_fuel gas (res_atom_swap x y m) (formula_atom_swap x y φ) <->
  res_models_fuel gas m φ.
Proof.
  assert (Hstrong :
    forall n (ψ : FormulaT) (fuel : nat) (m0 : WfWorldT),
      formula_measure ψ <= n ->
      res_models_fuel fuel (res_atom_swap x y m0) (formula_atom_swap x y ψ) <->
      res_models_fuel fuel m0 ψ).
  {
    induction n as [|n IHn].
    { intros ψ fuel m0 Hn.
      pose proof (formula_measure_pos ψ). lia. }
    intros ψ fuel m0 Hn.
    destruct fuel as [|gas']; simpl.
    { split; intros Hfalse; exact Hfalse. }
    split.
    - intros [Hscope Hbody].
      split.
      { apply (proj1 (formula_scoped_atom_swap_iff m0 ψ x y)).
        exact Hscope. }
      destruct ψ; cbn [formula_atom_swap] in Hbody.
      + exact I.
      + exact Hbody.
      + apply (proj1 (qualifier_exact_denote_atom_swap x y a m0)).
        exact Hbody.
      + destruct Hbody as [Hp Hq]. split.
        * exact (proj1 (IHn ψ1 gas' m0 ltac:(simpl in Hn; lia)) Hp).
        * exact (proj1 (IHn ψ2 gas' m0 ltac:(simpl in Hn; lia)) Hq).
      + destruct Hbody as [Hp|Hq].
        * left. exact (proj1 (IHn ψ1 gas' m0 ltac:(simpl in Hn; lia)) Hp).
        * right. exact (proj1 (IHn ψ2 gas' m0 ltac:(simpl in Hn; lia)) Hq).
      + intros m1 Hle Hp.
        pose proof (proj2 (IHn ψ1 gas' m1 ltac:(simpl in Hn; lia)) Hp)
          as Hp_sw.
        pose proof (Hbody (res_atom_swap x y m1)
          (raw_le_atom_swap x y m0 m1 Hle) Hp_sw) as Hq_sw.
        exact (proj1 (IHn ψ2 gas' m1 ltac:(simpl in Hn; lia)) Hq_sw).
      + destruct Hbody as [m1 [m2 [Hc [Hle [Hp Hq]]]]].
        pose proof (world_compat_atom_swap x y m1 m2 Hc) as Hc_sw.
        exists (res_atom_swap x y m1), (res_atom_swap x y m2), Hc_sw.
        split.
        * pose proof (raw_le_atom_swap x y
            (res_product m1 m2 Hc) (res_atom_swap x y m0) Hle) as Hle_sw.
          rewrite (res_product_atom_swap_eq x y m1 m2 Hc Hc_sw).
          rewrite res_atom_swap_involutive in Hle_sw.
          exact Hle_sw.
        * split.
          -- apply (proj1 (IHn ψ1 gas' (res_atom_swap x y m1)
               ltac:(simpl in Hn; lia))).
             rewrite res_atom_swap_involutive. exact Hp.
          -- apply (proj1 (IHn ψ2 gas' (res_atom_swap x y m2)
               ltac:(simpl in Hn; lia))).
             rewrite res_atom_swap_involutive. exact Hq.
      + destruct Hbody as [L Hwand].
        exists (L ∪ {[x]} ∪ {[y]}).
        intros η narg Hc Hbind Hfresh Hdom Harg.
        pose proof (Hbind) as [Hinj _].
        assert (Hηxy : open_env_atoms η ## ({[x]} ∪ {[y]})) by set_solver.
        pose proof (world_compat_atom_swap x y narg m0 Hc) as Hc_sw.
        assert (Hdom_sw :
            world_dom (res_product (res_atom_swap x y narg)
              (res_atom_swap x y m0) Hc_sw : WorldT) =
            world_dom (res_atom_swap x y m0 : WorldT) ∪ open_env_atoms η).
        {
          apply set_eq. intros z.
          change (world_dom (res_product narg m0 Hc : WorldT) =
            world_dom (m0 : WorldT) ∪ open_env_atoms η) in Hdom.
          change (z ∈ world_dom (res_atom_swap x y narg : WorldT) ∪
                    world_dom (res_atom_swap x y m0 : WorldT) <->
                  z ∈ world_dom (res_atom_swap x y m0 : WorldT) ∪
                    open_env_atoms η).
          rewrite !world_dom_res_atom_swap.
          rewrite !elem_of_union.
          rewrite !set_swap_elem.
          assert (Hηfresh : swap x y z ∈ open_env_atoms η <-> z ∈ open_env_atoms η).
          {
            split; intros Hzη.
            - destruct (decide (z = x)) as [->|Hzx].
              { rewrite swap_l in Hzη.
                exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy y);
                  [exact Hzη | set_solver]. }
              destruct (decide (z = y)) as [->|Hzy].
              { rewrite swap_r in Hzη.
                exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy x);
                  [exact Hzη | set_solver]. }
              rewrite swap_fresh in Hzη by congruence. exact Hzη.
            - destruct (decide (z = x)) as [->|Hzx].
              { exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy x);
                  [exact Hzη | set_solver]. }
              destruct (decide (z = y)) as [->|Hzy].
              { exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy y);
                  [exact Hzη | set_solver]. }
              rewrite swap_fresh by congruence. exact Hzη.
          }
          split.
          -- intros Hzdom.
             assert (Hzprod :
                 swap x y z ∈ world_dom (res_product narg m0 Hc : WorldT)).
             {
               change (swap x y z ∈
                 world_dom (narg : WorldT) ∪ world_dom (m0 : WorldT)).
               apply elem_of_union. exact Hzdom.
             }
             rewrite Hdom in Hzprod.
             apply elem_of_union in Hzprod.
             destruct Hzprod as [Hzm | Hzη].
             ++ left. exact Hzm.
             ++ right. apply Hηfresh. exact Hzη.
          -- intros Hzdom.
             assert (Hzprod :
                 swap x y z ∈ world_dom (m0 : WorldT) ∪ open_env_atoms η).
             {
               apply elem_of_union.
               destruct Hzdom as [Hzm | Hzη].
               - left. exact Hzm.
               - right. apply Hηfresh. exact Hzη.
             }
             rewrite <- Hdom in Hzprod.
             change (swap x y z ∈
               world_dom (narg : WorldT) ∪ world_dom (m0 : WorldT)) in Hzprod.
             apply elem_of_union in Hzprod.
             exact Hzprod.
        }
        assert (Harg_sw :
            res_models_fuel gas' (res_atom_swap x y narg)
              (formula_open_env η (formula_atom_swap x y ψ1))).
        {
          rewrite <- formula_atom_swap_open_env_fresh by assumption.
          exact (proj2 (IHn (formula_open_env η ψ1) gas' narg
            ltac:(rewrite formula_open_env_preserves_measure; simpl in Hn; lia))
            Harg).
        }
        pose proof (Hwand η (res_atom_swap x y narg) Hc_sw
          Hbind ltac:(set_solver) Hdom_sw Harg_sw) as Hres_sw.
        rewrite <- formula_atom_swap_open_env_fresh in Hres_sw by assumption.
        rewrite (res_product_atom_swap_eq x y narg m0 Hc Hc_sw) in Hres_sw.
        exact (proj1 (IHn (formula_open_env η ψ2) gas'
          (res_product narg m0 Hc)
          ltac:(rewrite formula_open_env_preserves_measure; simpl in Hn; lia))
          Hres_sw).
      + destruct Hbody as [m1 [m2 [Hdef [Hle [Hp Hq]]]]].
        pose proof (raw_sum_defined_atom_swap x y m1 m2 Hdef) as Hdef_sw.
        exists (res_atom_swap x y m1), (res_atom_swap x y m2), Hdef_sw.
        split.
        * pose proof (raw_le_atom_swap x y
            (res_sum m1 m2 Hdef) (res_atom_swap x y m0) Hle) as Hle_sw.
          rewrite (res_sum_atom_swap_eq x y m1 m2 Hdef Hdef_sw).
          rewrite res_atom_swap_involutive in Hle_sw.
          exact Hle_sw.
        * split.
          -- apply (proj1 (IHn ψ1 gas' (res_atom_swap x y m1)
               ltac:(simpl in Hn; lia))).
             rewrite res_atom_swap_involutive. exact Hp.
          -- apply (proj1 (IHn ψ2 gas' (res_atom_swap x y m2)
               ltac:(simpl in Hn; lia))).
             rewrite res_atom_swap_involutive. exact Hq.
      + destruct Hbody as [L Hforall].
        exists (L ∪ {[x]} ∪ {[y]}).
        intros z Hz F HFin HFout mz Hext.
        assert (Hzxy : z <> x /\ z <> y) by set_solver.
        pose proof (res_extend_by_atom_swap x y m0 mz F Hext) as Hext_sw.
        assert (HFin_sw :
            ext_in (fiber_extension_atom_swap x y F) =
            formula_fv (formula_atom_swap x y ψ)).
        {
          change (set_swap x y (ext_in F) =
            formula_fv (formula_atom_swap x y ψ)).
          rewrite HFin, formula_fv_atom_swap. reflexivity.
        }
        assert (HFout_sw :
            ext_out (fiber_extension_atom_swap x y F) = {[z]}).
        {
          change (set_swap x y (ext_out F) = {[z]}).
          rewrite HFout.
          apply set_swap_fresh; set_solver.
        }
        pose proof (Hforall z ltac:(set_solver)
          (fiber_extension_atom_swap x y F) HFin_sw HFout_sw
          (res_atom_swap x y mz) Hext_sw) as Hbody_sw.
        assert (Hopen :
            formula_open 0 z (formula_atom_swap x y ψ) =
            formula_atom_swap x y (formula_open 0 z ψ)).
        {
          rewrite <- (formula_atom_swap_open_conjugate 0 x y z ψ).
          rewrite swap_fresh by set_solver. reflexivity.
        }
        rewrite Hopen in Hbody_sw.
        exact (proj1 (IHn (formula_open 0 z ψ) gas' mz
          ltac:(rewrite formula_open_preserves_measure; simpl in Hn; lia))
          Hbody_sw).
      + destruct Hbody as [m1 [Hsub Hm1]].
        exists (res_atom_swap x y m1). split.
        * pose proof (res_subset_atom_swap x y (res_atom_swap x y m0) m1 Hsub)
            as Hsub_sw.
          rewrite res_atom_swap_involutive in Hsub_sw. exact Hsub_sw.
        * apply (proj1 (IHn ψ gas' (res_atom_swap x y m1)
            ltac:(simpl in Hn; lia))).
          rewrite res_atom_swap_involutive. exact Hm1.
      + destruct Hbody as [m1 [Hsub Hm1]].
        exists (res_atom_swap x y m1). split.
        * pose proof (res_subset_atom_swap x y m1 (res_atom_swap x y m0) Hsub)
            as Hsub_sw.
          rewrite res_atom_swap_involutive in Hsub_sw. exact Hsub_sw.
        * apply (proj1 (IHn ψ gas' (res_atom_swap x y m1)
            ltac:(simpl in Hn; lia))).
          rewrite res_atom_swap_involutive. exact Hm1.
      + destruct Hbody as [Hlc Hfib].
        split.
        * apply lc_lvars_no_bv.
          pose proof (proj1 (lc_lvars_no_bv _) Hlc) as Hbv_sw.
          rewrite lvars_bv_swap in Hbv_sw. exact Hbv_sw.
        * intros σ mfib Hproj.
          pose proof (res_fiber_from_projection_atom_swap x y m0 mfib
            (lvars_fv D) σ Hproj) as Hproj_sw.
          rewrite <- lvars_fv_swap in Hproj_sw.
          pose proof (Hfib (storeA_swap x y σ) (res_atom_swap x y mfib)
            Hproj_sw) as Hfib_sw.
          rewrite <- formula_atom_swap_msubst_store in Hfib_sw.
          exact (proj1 (IHn (formula_msubst_store σ ψ) gas' mfib
            ltac:(rewrite formula_msubst_store_preserves_measure; simpl in Hn; lia))
            Hfib_sw).
    - intros [Hscope Hbody].
      split.
      { apply (proj2 (formula_scoped_atom_swap_iff m0 ψ x y)).
        exact Hscope. }
      destruct ψ; cbn [formula_atom_swap]; cbn [formula_atom_swap] in Hbody.
      + exact I.
      + exact Hbody.
      + apply (proj2 (qualifier_exact_denote_atom_swap x y a m0)).
        exact Hbody.
      + destruct Hbody as [Hp Hq]. split.
        * exact (proj2 (IHn ψ1 gas' m0 ltac:(simpl in Hn; lia)) Hp).
        * exact (proj2 (IHn ψ2 gas' m0 ltac:(simpl in Hn; lia)) Hq).
      + destruct Hbody as [Hp|Hq].
        * left. exact (proj2 (IHn ψ1 gas' m0 ltac:(simpl in Hn; lia)) Hp).
        * right. exact (proj2 (IHn ψ2 gas' m0 ltac:(simpl in Hn; lia)) Hq).
      + intros m1 Hle Hp.
        pose proof (raw_le_atom_swap x y
          (res_atom_swap x y m0) m1 Hle) as Hle_orig.
        rewrite res_atom_swap_involutive in Hle_orig.
        pose proof (proj1 (IHn ψ1 gas' (res_atom_swap x y m1)
          ltac:(simpl in Hn; lia))
          ltac:(rewrite res_atom_swap_involutive; exact Hp)) as Hp_orig.
        pose proof (Hbody (res_atom_swap x y m1) Hle_orig Hp_orig) as Hq_orig.
        rewrite <- (res_atom_swap_involutive x y m1).
        exact (proj2 (IHn ψ2 gas' (res_atom_swap x y m1)
          ltac:(simpl in Hn; lia)) Hq_orig).
      + destruct Hbody as [m1 [m2 [Hc [Hle [Hp Hq]]]]].
        pose proof (world_compat_atom_swap x y m1 m2 Hc) as Hc_sw.
        exists (res_atom_swap x y m1), (res_atom_swap x y m2), Hc_sw.
        split.
        * pose proof (raw_le_atom_swap x y
            (res_product m1 m2 Hc) m0 Hle) as Hle_sw.
          rewrite (res_product_atom_swap_eq x y m1 m2 Hc Hc_sw).
          exact Hle_sw.
        * split.
          -- exact (proj2 (IHn ψ1 gas' m1 ltac:(simpl in Hn; lia)) Hp).
          -- exact (proj2 (IHn ψ2 gas' m2 ltac:(simpl in Hn; lia)) Hq).
      + destruct Hbody as [L Hwand].
        exists (L ∪ {[x]} ∪ {[y]}).
        intros η narg Hc Hbind Hfresh Hdom Harg.
        pose proof (Hbind) as [Hinj _].
        assert (Hηxy : open_env_atoms η ## ({[x]} ∪ {[y]})) by set_solver.
        pose proof (world_compat_atom_swap x y narg (res_atom_swap x y m0) Hc)
          as Hc_orig.
        rewrite res_atom_swap_involutive in Hc_orig.
        assert (Hdom_orig :
            world_dom (res_product (res_atom_swap x y narg) m0 Hc_orig : WorldT) =
            world_dom (m0 : WorldT) ∪ open_env_atoms η).
        {
          apply set_eq. intros z.
          change (world_dom (res_product narg (res_atom_swap x y m0) Hc : WorldT) =
            world_dom (res_atom_swap x y m0 : WorldT) ∪ open_env_atoms η) in Hdom.
          change (z ∈ world_dom (res_atom_swap x y narg : WorldT) ∪
                    world_dom (m0 : WorldT) <->
                  z ∈ world_dom (m0 : WorldT) ∪ open_env_atoms η).
          rewrite world_dom_res_atom_swap, elem_of_union, set_swap_elem.
          assert (Hηfresh : swap x y z ∈ open_env_atoms η <-> z ∈ open_env_atoms η).
          {
            split; intros Hzη.
            - destruct (decide (z = x)) as [->|Hzx].
              { rewrite swap_l in Hzη.
                exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy y);
                  [exact Hzη | set_solver]. }
              destruct (decide (z = y)) as [->|Hzy].
              { rewrite swap_r in Hzη.
                exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy x);
                  [exact Hzη | set_solver]. }
              rewrite swap_fresh in Hzη by congruence. exact Hzη.
            - destruct (decide (z = x)) as [->|Hzx].
              { exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy x);
                  [exact Hzη | set_solver]. }
              destruct (decide (z = y)) as [->|Hzy].
              { exfalso. apply (proj1 (elem_of_disjoint _ _) Hηxy y);
                  [exact Hzη | set_solver]. }
              rewrite swap_fresh by congruence. exact Hzη.
          }
          split.
          - intros Hzdom.
            assert (Hzprod :
                swap x y z ∈ world_dom (res_product narg
                  (res_atom_swap x y m0) Hc : WorldT)).
            {
              change (swap x y z ∈
                world_dom (narg : WorldT) ∪
                world_dom (res_atom_swap x y m0 : WorldT)).
              apply elem_of_union.
              destruct Hzdom as [Hzn | Hzm].
              + left. exact Hzn.
              + right. rewrite world_dom_res_atom_swap, set_swap_elem.
                rewrite swap_involutive. exact Hzm.
            }
            rewrite Hdom in Hzprod.
            apply elem_of_union in Hzprod.
            destruct Hzprod as [Hzm | Hzη].
            + apply elem_of_union. left.
              rewrite world_dom_res_atom_swap, set_swap_elem in Hzm.
              rewrite swap_involutive in Hzm. exact Hzm.
            + apply elem_of_union. right. apply Hηfresh. exact Hzη.
          - intros Hzdom.
            assert (Hzprod :
                swap x y z ∈ world_dom (res_atom_swap x y m0 : WorldT) ∪
                  open_env_atoms η).
            {
              apply elem_of_union.
              apply elem_of_union in Hzdom.
              destruct Hzdom as [Hzm | Hzη].
              - left. rewrite world_dom_res_atom_swap, set_swap_elem.
                rewrite swap_involutive. exact Hzm.
              - right. apply Hηfresh. exact Hzη.
            }
            rewrite <- Hdom in Hzprod.
            change (swap x y z ∈
              world_dom (narg : WorldT) ∪
              world_dom (res_atom_swap x y m0 : WorldT)) in Hzprod.
            rewrite world_dom_res_atom_swap, elem_of_union, set_swap_elem in Hzprod.
            destruct Hzprod as [Hzn | Hzm].
            + left. exact Hzn.
            + right. rewrite swap_involutive in Hzm. exact Hzm.
        }
        assert (Harg_orig :
            res_models_fuel gas' (res_atom_swap x y narg)
              (formula_open_env η ψ1)).
        {
          apply (proj1 (IHn (formula_open_env η ψ1) gas'
            (res_atom_swap x y narg)
            ltac:(rewrite formula_open_env_preserves_measure; simpl in Hn; lia))).
          rewrite res_atom_swap_involutive.
          rewrite formula_atom_swap_open_env_fresh; eauto.
        }
        pose proof (Hwand η (res_atom_swap x y narg) Hc_orig
          Hbind ltac:(set_solver) Hdom_orig Harg_orig) as Hres_orig.
        pose proof (proj2 (IHn (formula_open_env η ψ2) gas'
          (res_product (res_atom_swap x y narg) m0 Hc_orig)
          ltac:(rewrite formula_open_env_preserves_measure; simpl in Hn; lia))
          Hres_orig) as Hres_sw.
        rewrite <- formula_atom_swap_open_env_fresh by assumption.
        pose proof (world_compat_atom_swap x y (res_atom_swap x y narg) m0
          Hc_orig) as Hc_back.
        assert (Hprod_eq :
            res_product narg (res_atom_swap x y m0) Hc =
            res_atom_swap x y
              (res_product (res_atom_swap x y narg) m0 Hc_orig)).
        {
          transitivity (res_product
            (res_atom_swap x y (res_atom_swap x y narg))
            (res_atom_swap x y m0) Hc_back).
          - eapply res_product_l_eq.
            symmetry. apply res_atom_swap_involutive.
          - rewrite <- (res_product_atom_swap_eq x y
              (res_atom_swap x y narg) m0 Hc_orig Hc_back).
            reflexivity.
        }
        rewrite Hprod_eq.
        exact Hres_sw.
      + destruct Hbody as [m1 [m2 [Hdef [Hle [Hp Hq]]]]].
        pose proof (raw_sum_defined_atom_swap x y m1 m2 Hdef) as Hdef_sw.
        exists (res_atom_swap x y m1), (res_atom_swap x y m2), Hdef_sw.
        split.
        * pose proof (raw_le_atom_swap x y
            (res_sum m1 m2 Hdef) m0 Hle) as Hle_sw.
          rewrite (res_sum_atom_swap_eq x y m1 m2 Hdef Hdef_sw).
          exact Hle_sw.
        * split.
          -- exact (proj2 (IHn ψ1 gas' m1 ltac:(simpl in Hn; lia)) Hp).
          -- exact (proj2 (IHn ψ2 gas' m2 ltac:(simpl in Hn; lia)) Hq).
      + destruct Hbody as [L Hforall].
        exists (L ∪ {[x]} ∪ {[y]}).
        intros z Hz F HFin HFout mz Hext.
        assert (Hzxy : z <> x /\ z <> y) by set_solver.
        pose proof (res_extend_by_atom_swap x y (res_atom_swap x y m0) mz F Hext)
          as Hext_sw0.
        rewrite res_atom_swap_involutive in Hext_sw0.
        assert (HFin_sw :
            ext_in (fiber_extension_atom_swap x y F) = formula_fv ψ).
        {
          change (set_swap x y (ext_in F) = formula_fv ψ).
          rewrite HFin, formula_fv_atom_swap, set_swap_involutive.
          reflexivity.
        }
        assert (HFout_sw :
            ext_out (fiber_extension_atom_swap x y F) = {[z]}).
        {
          change (set_swap x y (ext_out F) = {[z]}).
          rewrite HFout.
          apply set_swap_fresh; set_solver.
        }
        pose proof (Hforall z ltac:(set_solver)
          (fiber_extension_atom_swap x y F) HFin_sw HFout_sw
          (res_atom_swap x y mz) Hext_sw0) as Hbody_orig.
        assert (Hopen :
            formula_open 0 z (formula_atom_swap x y ψ) =
            formula_atom_swap x y (formula_open 0 z ψ)).
        {
          rewrite <- (formula_atom_swap_open_conjugate 0 x y z ψ).
          rewrite swap_fresh by set_solver. reflexivity.
        }
        rewrite Hopen.
        apply (proj1 (IHn (formula_atom_swap x y (formula_open 0 z ψ))
          gas' mz
          ltac:(rewrite formula_atom_swap_preserves_measure;
            rewrite formula_open_preserves_measure; simpl in Hn; lia))).
        rewrite formula_atom_swap_involutive. exact Hbody_orig.
      + destruct Hbody as [m1 [Hsub Hm1]].
        exists (res_atom_swap x y m1). split.
        * exact (res_subset_atom_swap x y m0 m1 Hsub).
        * exact (proj2 (IHn ψ gas' m1 ltac:(simpl in Hn; lia)) Hm1).
      + destruct Hbody as [m1 [Hsub Hm1]].
        exists (res_atom_swap x y m1). split.
        * exact (res_subset_atom_swap x y m1 m0 Hsub).
        * exact (proj2 (IHn ψ gas' m1 ltac:(simpl in Hn; lia)) Hm1).
      + destruct Hbody as [Hlc Hfib].
        split.
        * apply lc_lvars_no_bv.
          rewrite lvars_bv_swap.
          exact (proj1 (lc_lvars_no_bv _) Hlc).
        * intros σ mfib Hproj.
	          pose proof (res_fiber_from_projection_atom_swap x y
	            (res_atom_swap x y m0) mfib (lvars_fv (lvars_swap x y D)) σ Hproj)
	            as Hproj_sw0.
	          rewrite res_atom_swap_involutive in Hproj_sw0.
	          rewrite lvars_fv_swap in Hproj_sw0.
	          rewrite set_swap_involutive in Hproj_sw0.
	          pose proof (Hfib (storeA_swap x y σ) (res_atom_swap x y mfib)
	            Hproj_sw0) as Hfib_orig.
	          rewrite <- (res_atom_swap_involutive x y mfib).
	          rewrite <- (storeA_swap_involutive x y σ).
	          rewrite <- formula_atom_swap_msubst_store.
	          exact (proj2 (IHn
	            (formula_msubst_store (storeA_swap x y σ) ψ) gas'
	            (res_atom_swap x y mfib)
	            ltac:(rewrite formula_msubst_store_preserves_measure; simpl in Hn; lia))
	            Hfib_orig).
  }
  exact (Hstrong (formula_measure φ) φ gas m ltac:(lia)).
Qed.

Lemma res_models_atom_swap (m : WfWorldT) (φ : FormulaT) x y :
  res_atom_swap x y m ⊨ formula_atom_swap x y φ <-> m ⊨ φ.
Proof.
  unfold res_models.
  rewrite formula_atom_swap_preserves_measure.
  apply res_models_fuel_atom_swap.
Qed.

Lemma res_models_from_restrict_extension_on_fv
    (m n : WfWorldT) (X : aset) (φ : FormulaT) :
  formula_fv φ ⊆ X ->
  formula_fv φ ⊆ world_dom (m : WorldT) ->
  res_restrict m X ⊑ n ->
  n ⊨ φ ->
  m ⊨ φ.
Proof.
  intros HfvX Hfvm Hle Hn.
  eapply res_models_fuel_projection with (m := n); [| exact Hn].
  transitivity (res_restrict (res_restrict m X) (formula_fv φ)).
  - symmetry. eapply res_restrict_le_eq.
    + exact Hle.
    + set_solver.
  - rewrite res_restrict_restrict_eq.
    replace (X ∩ formula_fv φ) with (formula_fv φ) by set_solver.
    reflexivity.
Qed.

Lemma res_models_and_intro_from_models (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ FAnd φ ψ.
Proof.
  intros Hφ Hψ.
  eapply res_models_and_intro; [| exact Hφ | exact Hψ].
  apply (proj2 (formula_scoped_and_iff m φ ψ)).
  split; eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_and_iff (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FAnd φ ψ ↔ m ⊨ φ ∧ m ⊨ ψ.
Proof.
  split.
  - intros Hand. split.
    + eapply res_models_and_elim_l; exact Hand.
    + eapply res_models_and_elim_r; exact Hand.
  - intros [Hφ Hψ]. eapply res_models_and_intro_from_models; eauto.
Qed.

Lemma res_models_or_iff (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FOr φ ψ) ->
  m ⊨ FOr φ ψ ↔ m ⊨ φ ∨ m ⊨ ψ.
Proof.
  intros Hscope.
  split.
  - unfold res_models. simpl.
    intros [_ [Hφ|Hψ]].
    + left. eapply res_models_fuel_irrel; [| | exact Hφ]; lia.
    + right. eapply res_models_fuel_irrel; [| | exact Hψ]; lia.
  - intros [Hφ|Hψ].
    + eapply res_models_or_intro_l; [exact Hscope | exact Hφ].
    + eapply res_models_or_intro_r; [exact Hscope | exact Hψ].
Qed.

Lemma res_models_or_intro_l_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ φ →
  formula_fv ψ ⊆ world_dom (m : WorldT) →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφ Hψscope.
  eapply res_models_or_intro_l; [| exact Hφ].
  apply (proj2 (formula_scoped_or_iff m φ ψ)).
  split; [eapply res_models_fuel_scoped; eauto | exact Hψscope].
Qed.

Lemma res_models_or_intro_r_from_model (m : WfWorldT) (φ ψ : FormulaT) :
  formula_fv φ ⊆ world_dom (m : WorldT) →
  m ⊨ ψ →
  m ⊨ FOr φ ψ.
Proof.
  intros Hφscope Hψ.
  eapply res_models_or_intro_r; [| exact Hψ].
  apply (proj2 (formula_scoped_or_iff m φ ψ)).
  split; [exact Hφscope | eapply res_models_fuel_scoped; eauto].
Qed.

Lemma formula_scoped_star_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  formula_scoped_in_world m (FStar φ ψ).
Proof.
  intros Hle Hφ Hψ.
  pose proof (res_models_scoped m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_scoped m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in *.
  rewrite formula_fv_star.
  pose proof (raw_le_dom (res_product m1 m2 Hc : WorldT) (m : WorldT) Hle)
    as Hdom.
  intros z Hz. apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom.
    change (world_dom (res_product m1 m2 Hc : WorldT))
      with (world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT)).
    set_solver.
  - apply Hdom.
    change (world_dom (res_product m1 m2 Hc : WorldT))
      with (world_dom (m1 : WorldT) ∪ world_dom (m2 : WorldT)).
    set_solver.
Qed.

Lemma res_models_star_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hc : world_compat m1 m2) :
  res_product m1 m2 Hc ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FStar φ ψ.
Proof.
  intros Hle Hφ Hψ. unfold res_models. simpl.
  split; [eapply formula_scoped_star_from_models; eauto |].
  exists m1, m2, Hc. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_star_iff (m : WfWorldT) (φ ψ : FormulaT) :
  (m ⊨ FStar φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hc : world_compat m1 m2),
      res_product m1 m2 Hc ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hc [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hc. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hc [Hle [Hφ Hψ]]]]].
    eapply res_models_star_intro; eauto.
Qed.

Lemma formula_scoped_plus_from_models
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  formula_scoped_in_world m (FPlus φ ψ).
Proof.
  intros Hle Hφ Hψ.
  pose proof (res_models_scoped m1 φ Hφ) as Hscopeφ.
  pose proof (res_models_scoped m2 ψ Hψ) as Hscopeψ.
  unfold formula_scoped_in_world in *.
  rewrite formula_fv_plus.
  pose proof (raw_le_dom (res_sum m1 m2 Hdef : WorldT) (m : WorldT) Hle)
    as Hdom.
  change (world_dom (m1 : WorldT) = world_dom (m2 : WorldT)) in Hdef.
  change (world_dom (m1 : WorldT) ⊆ world_dom (m : WorldT)) in Hdom.
  intros z Hz. apply elem_of_union in Hz as [Hz | Hz].
  - apply Hdom. exact (Hscopeφ z Hz).
  - apply Hdom. rewrite Hdef. exact (Hscopeψ z Hz).
Qed.

Lemma res_models_plus_intro
    (m m1 m2 : WfWorldT) (φ ψ : FormulaT)
    (Hdef : raw_sum_defined m1 m2) :
  res_sum m1 m2 Hdef ⊑ m →
  m1 ⊨ φ →
  m2 ⊨ ψ →
  m ⊨ FPlus φ ψ.
Proof.
  intros Hle Hφ Hψ. unfold res_models. simpl.
  split; [eapply formula_scoped_plus_from_models; eauto |].
  exists m1, m2, Hdef. split; [exact Hle |]. split.
  - models_fuel_irrel Hφ.
  - models_fuel_irrel Hψ.
Qed.

Lemma res_models_plus_iff (m : WfWorldT) (φ ψ : FormulaT) :
  (m ⊨ FPlus φ ψ ↔
    ∃ (m1 m2 : WfWorldT) (Hdef : raw_sum_defined m1 m2),
      res_sum m1 m2 Hdef ⊑ m ∧
      m1 ⊨ φ ∧ m2 ⊨ ψ).
Proof.
  split.
  - unfold res_models. simpl.
    intros [_ [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]]].
    exists m1, m2, Hdef. repeat split; eauto;
      unfold res_models; models_fuel_irrel_auto.
  - intros [m1 [m2 [Hdef [Hle [Hφ Hψ]]]]].
    eapply res_models_plus_intro; eauto.
Qed.

Lemma res_models_over_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FOver φ) →
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_over_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FOver φ.
Proof.
  intros Hφ.
  eapply res_models_over_intro_same; [| exact Hφ].
  apply (proj2 (formula_scoped_over_iff m φ)).
  eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_under_intro_same (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FUnder φ) →
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hφ. split; [exact Hscope |].
  exists m. split; [apply res_subset_refl |].
  models_fuel_irrel Hφ.
Qed.

Lemma res_models_under_intro_same_from_model (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ →
  m ⊨ FUnder φ.
Proof.
  intros Hφ.
  eapply res_models_under_intro_same; [| exact Hφ].
  apply (proj2 (formula_scoped_under_iff m φ)).
  eapply res_models_fuel_scoped; eauto.
Qed.

Lemma res_models_FFibVars_intro (m : WfWorldT) (D : lvset) (φ : FormulaT) :
	  formula_scoped_in_world m (FFibVars D φ) →
	  lc_lvars D →
	  (∀ (σ : Store (V := V)) (mfib : WfWorldT),
	    res_fiber_from_projection m (lvars_fv D) σ mfib →
	    mfib ⊨ formula_msubst_store σ φ) →
	  m ⊨ FFibVars D φ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hlc Hfib. split; [exact Hscope |].
  split; [exact Hlc |].
	  intros σ mfib Hproj.
	  specialize (Hfib σ mfib Hproj).
	  models_fuel_irrel Hfib.
Qed.

Lemma res_models_FFibVars_iff (m : WfWorldT) (D : lvset) (φ : FormulaT) :
  m ⊨ FFibVars D φ <->
  formula_scoped_in_world m (FFibVars D φ) /\
  lc_lvars D /\
  forall (σ : Store (V := V)) (mfib : WfWorldT),
    res_fiber_from_projection m (lvars_fv D) σ mfib ->
    mfib ⊨ formula_msubst_store σ φ.
Proof.
  unfold res_models. cbn [formula_measure res_models_fuel].
  split.
  - intros [Hscope [Hlc Hfib]].
    split; [exact Hscope|].
    split; [exact Hlc|].
    intros σ mfib Hproj.
    unfold res_models.
    specialize (Hfib σ mfib Hproj).
    models_fuel_irrel Hfib.
  - intros [Hscope [Hlc Hfib]].
    split; [exact Hscope|].
    split; [exact Hlc|].
    intros σ mfib Hproj.
    specialize (Hfib σ mfib Hproj).
    models_fuel_irrel Hfib.
Qed.

Lemma res_models_FAtom_store_holds (m : WfWorldT) q :
  m ⊨ FAtom q ->
  forall σ, (m : WorldT) σ -> qualifier_holds_store q σ.
Proof.
  destruct q as [D P].
  intros Hatom σ Hσ.
  unfold res_models in Hatom.
  cbn [formula_measure res_models_fuel qualifier_exact_denote] in Hatom.
  destruct Hatom as [_ [Hlc [Hsub Hiff]]].
  unfold qualifier_holds_store.
  cbn [qual_lvars qual_prop].
  assert (Hsubσ : lvars_fv D ⊆ dom (σ : Store (V := V))).
  {
    intros x Hx.
    change (x ∈ dom (σ : gmap atom V)).
    rewrite (wfworld_store_dom m σ Hσ).
    exact (Hsub x Hx).
  }
  exists Hlc, Hsubσ.
  apply (proj2 (Hiff (lstore_on_lift_store D σ Hlc Hsubσ))).
  apply lstore_in_lworld_on_lift_store_of_world. exact Hσ.
Qed.

Lemma res_models_FFiberAtom_fibers_iff (m : WfWorldT) q :
  m ⊨ FFiberAtom q <->
  formula_scoped_in_world m (FFiberAtom q) /\
  lc_lvars (qual_vars q) /\
  forall (σ : Store (V := V)) (mfib : WfWorldT),
    res_fiber_from_projection m (qual_dom q) σ mfib ->
    mfib ⊨ FAtom (qual_msubst_store σ q).
Proof.
  unfold FFiberAtom, res_models. cbn [formula_measure res_models_fuel].
  split.
  - intros [Hscope [Hlc Hfib]].
    split; [exact Hscope|].
    split; [exact Hlc|].
    exact Hfib.
  - intros [Hscope [Hlc Hfib]].
    split; [exact Hscope|].
    split; [exact Hlc|].
    exact Hfib.
Qed.

Lemma res_fiber_from_projection_lookup_eq
    (m mfib : WfWorldT) (X : aset) (σproj τ : Store (V := V)) x :
  res_fiber_from_projection m X σproj mfib ->
  (mfib : WorldT) τ ->
  x ∈ dom (σproj : Store (V := V)) ->
  (τ : gmap atom V) !! x = (σproj : gmap atom V) !! x.
Proof.
  intros Hproj Hτ Hx.
  destruct Hproj as [_ Hfib_eq].
  change ((mfib : WorldT) = raw_fiber (m : WorldT) σproj) in Hfib_eq.
  rewrite Hfib_eq in Hτ.
  destruct Hτ as [_ Hτproj].
  pose proof (f_equal (fun st => (st : Store (V := V)) !! x) Hτproj)
    as Hlook.
  change (store_restrict τ (dom (σproj : Store (V := V))) !! x =
    σproj !! x) in Hlook.
  assert (Hrestrict :
    store_restrict τ (dom (σproj : Store (V := V))) !! x =
    (τ : gmap atom V) !! x).
  {
    change ((storeA_restrict τ (dom (σproj : Store (V := V))) : gmap atom V)
      !! x = (τ : gmap atom V) !! x).
    rewrite (storeA_restrict_lookup (K := atom)
      (τ : gmap atom V) (dom (σproj : Store (V := V))) x).
    destruct (decide (x ∈ dom (σproj : Store (V := V)))) as [_|Hnot].
    - reflexivity.
    - contradiction.
  }
  rewrite <- Hrestrict.
  exact Hlook.
Qed.

Lemma res_models_FFiberAtom_store_iff (m : WfWorldT) q :
  m ⊨ FFiberAtom q <->
  formula_scoped_in_world m (FFiberAtom q) /\
  forall σ, (m : WorldT) σ -> qualifier_holds_store q σ.
Proof.
  destruct q as [D P].
  rewrite res_models_FFiberAtom_fibers_iff.
  cbn [qual_vars qual_dom qualifier_holds_store qual_msubst_store
    qual_mlsubst].
  split.
  - intros [Hscope [Hlc Hfib]].
    split; [exact Hscope|].
    intros σ Hσ.
    assert (HDm : lvars_fv D ⊆ world_dom (m : WorldT)).
    {
      unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_fiber_atom in Hscope.
      cbn [qual_dom qual_vars qual_lvars] in Hscope.
      exact Hscope.
    }
    assert (HDσ : lvars_fv D ⊆ dom (σ : Store (V := V))).
    {
      intros x Hx.
      change (x ∈ dom (σ : gmap atom V)).
      rewrite (wfworld_store_dom m σ Hσ).
      exact (HDm x Hx).
    }
    destruct (res_fiber_from_projection_of_store m (lvars_fv D) σ HDm Hσ)
      as [mfib [Hproj Hσfib]].
    pose proof (Hfib (store_restrict σ (lvars_fv D)) mfib Hproj)
      as Hatom.
    unfold res_models in Hatom.
    cbn [formula_measure res_models_fuel qualifier_exact_denote
      qual_msubst_store qual_mlsubst] in Hatom.
    destruct Hatom as [_ Hatom].
    set (ρ := atom_store_to_lvar_store (store_restrict σ (lvars_fv D))
      : LStore (V := V)) in *.
    assert (Hρdom : dom (ρ : gmap logic_var V) =
      lvars_of_atoms (lvars_fv D)).
    {
      subst ρ.
      rewrite atom_store_to_lvar_store_dom.
      rewrite storeA_restrict_dom.
      rewrite (wfworld_store_dom m σ Hσ).
      replace (world_dom (m : WorldT) ∩ lvars_fv D) with (lvars_fv D)
        by better_set_solver.
      reflexivity.
    }
    assert (HDempty : D ∖ dom (ρ : gmap logic_var V) = ∅).
    {
      subst ρ.
      apply lvars_closed_difference_atom_store_to_lvar_store_empty.
      - exact Hlc.
      - apply set_eq. intros x.
        split.
        + intros Hx.
          eapply storeA_restrict_dom_subset; exact Hx.
        + intros Hx.
          change (x ∈ dom (store_restrict σ (lvars_fv D) : gmap atom V)).
          rewrite elem_of_dom.
          destruct ((σ : gmap atom V) !! x) as [v|] eqn:Hv.
          * exists v. apply storeA_restrict_lookup_some_2; assumption.
          * exfalso.
            apply not_elem_of_dom in Hv.
            apply Hv.
            change (x ∈ dom (σ : gmap atom V)).
            rewrite (wfworld_store_dom m σ Hσ). exact (HDm x Hx).
    }
    destruct Hatom as [Hlc_empty [Hsub_empty Hholds]].
    assert (Hempty_sub :
      lvars_fv (D ∖ dom (ρ : gmap logic_var V)) ⊆ dom (σ : Store (V := V))).
    { rewrite HDempty, lvars_fv_empty. intros x Hx. set_solver. }
    set (sempty :=
      lstore_on_lift_store (D ∖ dom (ρ : gmap logic_var V)) σ
        Hlc_empty Hempty_sub).
    assert (Hmem_empty :
      lstore_in_lworld_on sempty
        (lworld_on_lift (D ∖ dom (ρ : gmap logic_var V)) mfib
          Hlc_empty Hsub_empty)).
    { apply lstore_in_lworld_on_lift_store_of_world. exact Hσfib. }
    pose proof (proj2 (Hholds sempty) Hmem_empty) as HPback.
    exists Hlc, HDσ.
    enough (lstore_on_mlsubst_back D ρ sempty =
      lstore_on_lift_store D σ Hlc HDσ) as Heq.
    { rewrite <- Heq. exact HPback. }
    apply lstore_on_mlsubst_back_full_lift; [|exact HDempty].
    subst ρ.
    rewrite lstore_lift_free_restrict_fv_lvars_eq. reflexivity.
  - intros [Hscope Hstores].
    split; [exact Hscope|].
    assert (HlcD : lc_lvars D).
    {
      destruct (world_wf m) as [[σ Hσ] _].
      destruct (Hstores σ Hσ) as [HlcD _].
      exact HlcD.
    }
    split; [exact HlcD|].
    intros σproj mfib Hproj.
    unfold res_models.
    cbn [formula_measure res_models_fuel qualifier_exact_denote
      qual_msubst_store qual_mlsubst].
    set (ρ := atom_store_to_lvar_store σproj : LStore (V := V)).
    assert (Hσproj_dom : dom (σproj : Store (V := V)) = lvars_fv D).
    {
      destruct Hproj as [Hproj_src _].
      pose proof (wfworld_store_dom (res_restrict m (lvars_fv D))
        σproj Hproj_src) as Hdom.
      change (dom (σproj : Store (V := V)) = lvars_fv D).
      transitivity (world_dom (res_restrict m (lvars_fv D) : WorldT)).
      { exact Hdom. }
      apply set_eq. intros x.
      rewrite res_restrict_dom.
      rewrite elem_of_intersection.
      split; [tauto|].
      intros Hx.
      split; [|exact Hx].
      unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_fiber_atom in Hscope.
      cbn [qual_dom qual_vars qual_lvars] in Hscope.
      exact (Hscope x Hx).
    }
    assert (HDempty : D ∖ dom (ρ : gmap logic_var V) = ∅).
    {
      subst ρ.
      apply lvars_closed_difference_atom_store_to_lvar_store_empty;
        assumption.
    }
    split.
    {
      unfold formula_scoped_in_world. rewrite formula_fv_atom.
      cbn [qual_dom qual_vars qual_lvars].
      rewrite HDempty, lvars_fv_empty.
      intros x Hx. set_solver.
    }
    assert (Hlc_empty : lc_lvars (D ∖ dom (ρ : gmap logic_var V))).
    { rewrite HDempty. intros v Hv. set_solver. }
    assert (Hsub_empty :
      lvars_fv (D ∖ dom (ρ : gmap logic_var V)) ⊆ world_dom (mfib : WorldT)).
    { rewrite HDempty, lvars_fv_empty. intros x Hx. set_solver. }
    exists Hlc_empty, Hsub_empty.
    intros s.
    split.
    + intros _.
      unfold lstore_in_lworld_on, lworld_on_lift.
      cbn [lw lraw_world].
      destruct (world_wf mfib) as [[τ Hτ] _].
      exists (lstore_lift_free (store_restrict τ (lvars_fv (D ∖ dom (ρ : gmap logic_var V))))).
      split.
      * exists (store_restrict τ (lvars_fv (D ∖ dom (ρ : gmap logic_var V)))).
        split.
        -- exists τ. split; [exact Hτ|reflexivity].
        -- reflexivity.
      * apply storeA_map_eq. intros v.
        transitivity (@None V).
        -- apply storeA_restrict_lookup_none_r.
           rewrite HDempty. set_solver.
        -- symmetry. apply not_elem_of_dom.
           change (v ∉ dom (lso_store s : LStore (V := V))).
           rewrite (lso_dom s), HDempty. set_solver.
    + intros _.
      destruct (world_wf mfib) as [[τ Hτ] _].
      pose proof (res_fiber_from_projection_store_source m mfib
        (lvars_fv D) σproj τ Hproj Hτ) as Hτm.
      specialize (Hstores τ Hτm) as [Hlcτ [Hsubτ HP]].
      enough (lstore_on_mlsubst_back D ρ s =
        lstore_on_lift_store D τ Hlcτ Hsubτ) as Heq.
      { rewrite Heq. exact HP. }
      apply lstore_on_mlsubst_back_full_lift; [|exact HDempty].
      subst ρ.
      apply storeA_map_eq. intros v.
      rewrite !storeA_restrict_lookup.
      destruct (decide (v ∈ D)) as [HvD|HvD]; [|reflexivity].
      destruct v as [k|x].
      * exfalso. exact (HlcD (LVBound k) HvD).
      * rewrite atom_store_to_lvar_store_lookup_free.
        rewrite lstore_lift_free_lookup_free.
        symmetry.
        apply res_fiber_from_projection_lookup_eq with
          (m := m) (mfib := mfib) (X := lvars_fv D) (σproj := σproj);
          [exact Hproj|exact Hτ|].
        rewrite Hσproj_dom. apply lvars_fv_elem. exact HvD.
Qed.

End FormulaConnectives.

Ltac normalize_models_ands_in H :=
  repeat rewrite res_models_and_iff in H.

Ltac normalize_models_ands_goal :=
  repeat rewrite res_models_and_iff.

Ltac destruct_models_formula_hyps :=
  repeat match goal with
  | H : res_models _ (FAnd _ _) |- _ =>
      rewrite res_models_and_iff in H; destruct H
  | H : res_models _ _ /\ _ |- _ =>
      destruct H
  | H : _ /\ res_models _ _ |- _ =>
      destruct H
  end.

Ltac split_models_formula_goal :=
  repeat match goal with
  | |- res_models _ (FAnd _ _) =>
      rewrite res_models_and_iff; split
  | |- res_models _ _ /\ _ =>
      split
  | |- _ /\ res_models _ _ =>
      split
  end.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for implication formulas. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_impl_future_iff_local (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  ((∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hφscope Hψscope. split.
  - intros Hfuture Hφ. eapply Hfuture; [reflexivity | exact Hφ].
  - intros Hlocal m' Hle Hφ.
    assert (Hφ_base : m ⊨ φ).
    {
      pose proof (res_models_minimal_on (world_dom (m : WorldT)) m' φ)
        as Hminimal.
      assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
      { exact Hφscope. }
      specialize (Hminimal Hfv).
      rewrite (res_restrict_eq_of_le m m' Hle) in Hminimal.
      apply (proj1 Hminimal). exact Hφ.
    }
    eapply res_models_kripke; [exact Hle |].
    eauto.
Qed.

Lemma models_impl_future_iff_of_scope
    (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  ((∀ m', m ⊑ m' →
      m' ⊨ φ →
      m' ⊨ ψ) ↔
   (m ⊨ φ → m ⊨ ψ)).
Proof.
  intros Hscope.
  eapply res_models_impl_future_iff_local;
    apply (proj1 (formula_scoped_impl_iff m φ ψ)) in Hscope;
    tauto.
Qed.

Lemma res_models_impl_intro_future (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (∀ m', m ⊑ m' →
     m' ⊨ φ →
     m' ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope Hfuture. split; [exact Hscope |].
  intros m' Hle Hφ.
  assert (Hφ_model : m' ⊨ φ).
  { unfold res_models. models_fuel_irrel Hφ. }
  pose proof (Hfuture m' Hle Hφ_model) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_impl_intro (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m (FImpl φ ψ) →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hscope Hlocal.
  eapply res_models_impl_intro_future; [exact Hscope |].
  apply (proj2 (models_impl_future_iff_of_scope
    m φ ψ Hscope)).
  exact Hlocal.
Qed.

Lemma res_models_impl_intro_scoped (m : WfWorldT) (φ ψ : FormulaT) :
  formula_scoped_in_world m φ →
  formula_scoped_in_world m ψ →
  (m ⊨ φ → m ⊨ ψ) →
  m ⊨ FImpl φ ψ.
Proof.
  intros Hφscope Hψscope Hlocal.
  eapply res_models_impl_intro.
  - apply (proj2 (formula_scoped_impl_iff m φ ψ)).
    split; assumption.
  - exact Hlocal.
Qed.

Lemma res_models_impl_elim_future (m n : WfWorldT) (φ ψ : FormulaT) :
  m ⊑ n →
  m ⊨ FImpl φ ψ →
  n ⊨ φ →
  n ⊨ ψ.
Proof.
  intros Hle Himpl Hφ.
  unfold res_models in Himpl.
  simpl in Himpl. destruct Himpl as [_ Himpl].
  assert (Hφ_fuel :
      res_models_fuel (formula_measure φ + formula_measure ψ) n φ).
  { models_fuel_irrel Hφ. }
  pose proof (Himpl n Hle Hφ_fuel) as Hψ.
  unfold res_models. models_fuel_irrel Hψ.
Qed.

Lemma res_models_impl_elim (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FImpl φ ψ →
  m ⊨ φ →
  m ⊨ ψ.
Proof.
  intros Himpl Hφ.
  eapply res_models_impl_elim_future; [reflexivity | exact Himpl | exact Hφ].
Qed.

Lemma res_models_impl2_intro
    (m : WfWorldT) (φ ψ χ : FormulaT) :
  formula_scoped_in_world m (FImpl φ (FImpl ψ χ)) →
  (m ⊨ φ → m ⊨ ψ → m ⊨ χ) →
  m ⊨ FImpl φ (FImpl ψ χ).
Proof.
  intros Hscope Hlocal.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ.
  eapply res_models_impl_intro.
  - eapply formula_scoped_impl_r. exact Hscope.
  - intros Hψ. exact (Hlocal Hφ Hψ).
Qed.

Lemma res_models_impl2_elim
    (m : WfWorldT) (φ ψ χ : FormulaT) :
  m ⊨ FImpl φ (FImpl ψ χ) →
  m ⊨ φ →
  m ⊨ ψ →
  m ⊨ χ.
Proof.
  intros Himpl Hφ Hψ.
  eapply res_models_impl_elim; [| exact Hψ].
  eapply res_models_impl_elim; eauto.
Qed.

Lemma res_models_impl_map
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 ψ2) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ1 → m ⊨ ψ2) →
  m ⊨ FImpl φ1 ψ1 →
  m ⊨ FImpl φ2 ψ2.
Proof.
  intros Hscope Hφ Hψ Himpl.
  eapply res_models_impl_intro; [exact Hscope |].
  intros Hφ2.
  apply Hψ.
  eapply res_models_impl_elim; [exact Himpl |].
  apply Hφ. exact Hφ2.
Qed.

Lemma res_models_impl2_map
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 χ1 χ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 (FImpl ψ2 χ2)) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ2 → m ⊨ ψ1) →
  (m ⊨ χ1 → m ⊨ χ2) →
  m ⊨ FImpl φ1 (FImpl ψ1 χ1) →
  m ⊨ FImpl φ2 (FImpl ψ2 χ2).
Proof.
  intros Hscope Hφ Hψ Hχ Himpl.
  eapply res_models_impl2_intro; [exact Hscope |].
  intros Hφ2 Hψ2.
  apply Hχ.
  eapply res_models_impl2_elim; [exact Himpl | |].
  - apply Hφ. exact Hφ2.
  - apply Hψ. exact Hψ2.
Qed.

Lemma res_models_impl2_map_dep
    (m : WfWorldT)
    (φ1 φ2 ψ1 ψ2 χ1 χ2 : FormulaT) :
  formula_scoped_in_world m (FImpl φ2 (FImpl ψ2 χ2)) →
  (m ⊨ φ2 → m ⊨ φ1) →
  (m ⊨ ψ2 → m ⊨ ψ1) →
  (m ⊨ φ2 → m ⊨ ψ2 → m ⊨ χ1 → m ⊨ χ2) →
  m ⊨ FImpl φ1 (FImpl ψ1 χ1) →
  m ⊨ FImpl φ2 (FImpl ψ2 χ2).
Proof.
  intros Hscope Hφ Hψ Hχ Himpl.
  eapply res_models_impl2_intro; [exact Hscope |].
  intros Hφ2 Hψ2.
  eapply Hχ; [exact Hφ2 | exact Hψ2 |].
  eapply res_models_impl2_elim; [exact Himpl | |].
  - apply Hφ. exact Hφ2.
  - apply Hψ. exact Hψ2.
Qed.

End FormulaConnectives.

Ltac use_models_impl H Hout :=
  lazymatch type of H with
  | res_models ?m (FImpl ?p ?q) =>
      let Harg := fresh "Harg" in
      assert (Harg : res_models m p);
      [ | pose proof (res_models_impl_elim m p q H Harg) as Hout;
          clear Harg ]
  | res_models ?m (formula_open ?k ?x (FImpl ?p ?q)) =>
      rewrite formula_open_impl in H;
      use_models_impl H Hout
  end.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for binder-aware wand formulas. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Lemma res_models_fbwand_intro (m : WfWorldT) d (φ ψ : FormulaT) :
  formula_scoped_in_world m (FBWand d φ ψ) →
  (exists L : aset,
    ∀ η (m' : WfWorldT)
      (Hc : world_compat m' m),
      open_env_binds d η →
      open_env_atoms η ## L →
      world_dom (res_product m' m Hc : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η →
      m' ⊨ formula_open_env η φ →
      res_product m' m Hc ⊨ formula_open_env η ψ) →
  m ⊨ FBWand d φ ψ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hwand]. split; [exact Hscope |].
  exists L.
  intros η m' Hc Hbind Hfresh Hdom Hφ.
  assert (Hφ_model : m' ⊨ formula_open_env η φ).
  { unfold res_models. models_fuel_irrel Hφ. }
  pose proof (Hwand η m' Hc Hbind Hfresh Hdom Hφ_model) as Hψ.
  models_fuel_irrel Hψ.
Qed.

Lemma res_models_fbwand_rev
    (m : WfWorldT) d
    (φ ψ : FormulaT) :
  m ⊨ FBWand d φ ψ ->
  exists L : aset,
    forall (η : gmap nat atom) (m' : WfWorldT)
      (Hc : world_compat m' m),
      open_env_binds d η ->
      open_env_atoms η ## L ->
      world_dom (res_product m' m Hc : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η ->
      m' ⊨ formula_open_env η φ ->
      res_product m' m Hc ⊨ formula_open_env η ψ.
Proof.
  unfold res_models. simpl. intros [_ [L Hwand]].
  exists L.
  intros η m' Hc Hbind Hfresh Hdom Hφ.
  assert (Hφ_fuel :
      res_models_fuel (formula_measure φ + formula_measure ψ) m'
        (formula_open_env η φ)).
  { models_fuel_irrel Hφ. }
  pose proof (Hwand η m' Hc Hbind Hfresh Hdom Hφ_fuel) as Hψ.
  models_fuel_irrel Hψ.
Qed.

(** Reviewer-facing sanity theorem.

    [FBWand] has product-domain semantics: the semantic clause only invokes the
    body when the product of the argument resource and closure resource
    introduces exactly the atoms opened for the binder block.  Reviewers may
    reasonably ask how this relates to the ordinary BI wand rule.  The theorem
    below records that a well-formed [FBWand] supports the usual BI-style use:
    any compatible argument resource that provides the opened binder atoms and
    satisfies the opened antecedent entails the opened consequent on the product
    world.

    This theorem is intentionally not used by type denotation, minimality, or
    Fundamental.  It is metatheory explaining the binder-aware connective, so do
    not delete it as an apparently unused wrapper during cleanup. *)
Theorem res_models_fbwand_bi_of_wf
    (m : WfWorldT) d (φ ψ : FormulaT) :
  formula_wf (FBWand d φ ψ) ->
  m ⊨ FBWand d φ ψ ->
  exists L : aset,
    forall (η : gmap nat atom) (n : WfWorldT)
      (Hc : world_compat n m),
      open_env_binds d η ->
      open_env_atoms η ## L ->
      open_env_atoms η ⊆ world_dom (n : WorldT) ->
      n ⊨ formula_open_env η φ ->
      res_product n m Hc ⊨ formula_open_env η ψ.
Proof.
  intros Hwf Hmodel.
  destruct Hwf as [_ [_ _]].
  pose proof (res_models_scoped _ _ Hmodel) as Hscope.
  pose proof (res_models_fbwand_rev _ _ _ _ Hmodel) as [L Hwand].
  exists (L ∪ world_dom (m : WorldT)).
  intros η n Hc Hbind Hfresh Hηn Hφ.
  set (A := open_env_atoms η).
  set (X := world_dom (m : WorldT) ∪ A).
  assert (Hfresh_L : A ## L) by (subst A; set_solver).
  assert (HφX : formula_fv (formula_open_env η φ) ⊆ X).
  {
    subst X A.
    pose proof (formula_open_env_fv_subset η φ) as Hopen.
    assert (Hφm : formula_fv φ ⊆ world_dom (m : WorldT)).
    {
      intros z Hz. apply Hscope.
      rewrite formula_fv_fbwand.
      rewrite (formula_lvars_at_fv d φ), (formula_lvars_at_fv d ψ).
      set_solver.
    }
    set_solver.
  }
  assert (Hc_small : world_compat (res_restrict n X) m).
  {
    assert (Hc_full : world_compat n (res_restrict m (world_dom (m : WorldT)))).
    {
      rewrite (res_restrict_eq_of_le m m (raw_le_refl m)).
      exact Hc.
    }
    pose proof (world_compat_restrict_overlap n m X (world_dom (m : WorldT))
      (world_dom (m : WorldT)) ltac:(set_solver) Hc_full) as Htmp.
    rewrite (res_restrict_eq_of_le m m (raw_le_refl m)) in Htmp.
    exact Htmp.
  }
  assert (Hdom_small :
      world_dom (res_product (res_restrict n X) m Hc_small : WorldT) =
        world_dom (m : WorldT) ∪ A).
  {
    apply set_eq. intros z.
    change (z ∈ world_dom (res_restrict n X : WorldT) ∪
      world_dom (m : WorldT) ↔
      z ∈ world_dom (m : WorldT) ∪ A).
    rewrite res_restrict_dom.
    subst X A. set_solver.
  }
  assert (Hφ_small :
      res_restrict n X ⊨ formula_open_env η φ).
  {
    apply (proj1 (res_models_minimal_on X n
      (formula_open_env η φ) HφX)).
    exact Hφ.
  }
  pose proof (Hwand η (res_restrict n X) Hc_small
    Hbind Hfresh_L Hdom_small Hφ_small) as Hψ_small.
  eapply res_models_kripke; [| exact Hψ_small].
  eapply res_product_le_mono.
  - apply res_restrict_le.
  - apply raw_le_refl.
Qed.

Lemma res_models_fbwand_open_one_named_fresh
    (m n : WfWorldT) x (φ ψ : FormulaT)
    (Hc : world_compat n m) :
  m ⊨ FBWand 1 φ ψ ->
  x ∉ world_dom (m : WorldT) ->
  world_dom (res_product n m Hc : WorldT) =
    world_dom (m : WorldT) ∪ {[x]} ->
  n ⊨ formula_open 0 x φ ->
  res_product n m Hc ⊨ formula_open 0 x ψ.
Proof.
  intros Hwand Hxm Hdom Harg.
  destruct (res_models_fbwand_rev m 1 φ ψ Hwand) as [L Hrev].
  pose proof (res_models_scoped m (FBWand 1 φ ψ) Hwand) as Hscope.
  pose proof (formula_scoped_fbwand_l m 1 φ ψ Hscope) as Hscope_arg.
  pose proof (formula_scoped_fbwand_r m 1 φ ψ Hscope) as Hscope_res.
  set (y := fresh_for
    (L ∪ world_dom (res_product n m Hc : WorldT) ∪
      formula_fv φ ∪ formula_fv ψ ∪ {[x]})).
  pose proof (fresh_for_not_in
    (L ∪ world_dom (res_product n m Hc : WorldT) ∪
      formula_fv φ ∪ formula_fv ψ ∪ {[x]})) as Hyfresh.
  assert (HyL : y ∉ L) by better_set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)).
  { intros Hy. apply Hyfresh. rewrite Hdom. better_set_solver. }
  assert (Hyprod : y ∉ world_dom (res_product n m Hc : WorldT))
    by better_set_solver.
  assert (Hxfv_arg : x ∉ formula_fv φ).
  { intros Hbad. exact (Hxm (Hscope_arg x Hbad)). }
  assert (Hyfv_arg : y ∉ formula_fv φ) by better_set_solver.
  assert (Hxfv_res : x ∉ formula_fv ψ).
  { intros Hbad. exact (Hxm (Hscope_res x Hbad)). }
  assert (Hyfv_res : y ∉ formula_fv ψ) by better_set_solver.
  set (η := <[0 := y]> (∅ : gmap nat atom)).
  assert (Hbind : open_env_binds 1 η).
  {
    unfold open_env_binds. split.
    { unfold η. apply open_env_values_inj_singleton. }
    intros k. destruct k as [|k].
    { unfold η. rewrite lookup_insert.
      split; [intros _; eexists; reflexivity | intros _; lia]. }
    unfold η. rewrite lookup_insert_ne by lia. rewrite lookup_empty.
    split; [lia | intros [? Hnone]; inversion Hnone].
  }
  assert (Hatoms : open_env_atoms η = {[y]}).
  {
    unfold η. rewrite open_env_atoms_insert by apply lookup_empty.
    rewrite open_env_atoms_empty. better_set_solver.
  }
  pose proof (world_compat_atom_swap x y n m Hc) as Hc_sw0.
  assert (Hm_sw : res_atom_swap x y m = m).
  { apply res_atom_swap_fresh; assumption. }
  assert (Hc_sw : world_compat (res_atom_swap x y n) m).
  { rewrite <- Hm_sw. exact Hc_sw0. }
  assert (Hprod_sw :
      res_product (res_atom_swap x y n) m Hc_sw =
      res_atom_swap x y (res_product n m Hc)).
  {
    transitivity (res_product (res_atom_swap x y n)
      (res_atom_swap x y m) Hc_sw0).
    - eapply res_product_r_eq. symmetry. exact Hm_sw.
    - apply res_product_atom_swap_eq.
  }
  assert (Hdom_sw :
      world_dom (res_product (res_atom_swap x y n) m Hc_sw : WorldT) =
        world_dom (m : WorldT) ∪ open_env_atoms η).
  {
    rewrite Hprod_sw, world_dom_res_atom_swap, Hdom, Hatoms.
    rewrite set_swap_union.
    rewrite set_swap_fresh by (exact Hxm || exact Hym).
    rewrite set_swap_singleton, swap_l. reflexivity.
  }
  assert (Harg_sw :
      res_atom_swap x y n ⊨ formula_open_env η φ).
  {
    unfold η. rewrite formula_open_env_singleton.
    rewrite <- (formula_atom_swap_open_fresh x y φ)
      by (exact Hxfv_arg || exact Hyfv_arg).
    exact (proj2 (res_models_atom_swap n (formula_open 0 x φ) x y) Harg).
  }
  pose proof (Hrev η (res_atom_swap x y n) Hc_sw Hbind
    ltac:(rewrite Hatoms; better_set_solver) Hdom_sw Harg_sw) as Hres_sw.
  unfold η in Hres_sw. rewrite formula_open_env_singleton in Hres_sw.
  apply (proj1 (res_models_atom_swap (res_product n m Hc)
    (formula_open 0 x ψ) x y)).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv_res || exact Hyfv_res).
  rewrite <- Hprod_sw. exact Hres_sw.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectives

    Derived proof principles for forall under the extension-based formula
    semantics. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WorldT := (World (V := V)) (only parsing).
Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).
Local Notation "m ⊨ φ" := (res_models m φ)
  (at level 70, format "m  ⊨  φ").

Definition res_extend_by_input_widened_to
    (m : WfWorldT) (F : fiber_extension) (X : aset) (my : WfWorldT) : Prop :=
  ∃ Fwide : fiber_extension,
    F ~>i Fwide ∧
    ext_in Fwide = X ∧
    res_extend_by m Fwide my.

Lemma res_models_forall_intro (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (∃ L : aset,
    ∀ y : atom, y ∉ L →
    ∀ F : fiber_extension,
      ext_in F = formula_fv φ →
      ext_out F = {[y]} →
      ∀ my : WfWorldT,
        res_extend_by m F my →
        my ⊨ formula_open 0 y φ) →
  m ⊨ FForall φ.
Proof.
  unfold res_models.
  simpl. intros Hscope [L Hforall]. split; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  pose proof (Hforall y Hy F HFin HFout my Hext) as Hbody.
  models_fuel_irrel Hbody.
Qed.

Lemma res_models_forall_iff (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) →
  (m ⊨ FForall φ ↔
    ∃ L : aset,
      ∀ y : atom, y ∉ L →
      ∀ F : fiber_extension,
        ext_in F = formula_fv φ →
        ext_out F = {[y]} →
        ∀ my : WfWorldT,
          res_extend_by m F my →
          my ⊨ formula_open 0 y φ).
Proof.
  intros Hscope. split.
  - unfold res_models. simpl.
    intros [_ [L Hforall]]. exists L.
    intros y Hy F HFin HFout my Hext.
    specialize (Hforall y Hy F HFin HFout my Hext).
    unfold res_models. models_fuel_irrel Hforall.
  - intros Hforall.
    eapply res_models_forall_intro; eauto.
Qed.

Lemma res_models_forall_rev
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FForall φ ->
  exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ.
Proof.
  intros Hforall.
  pose proof (res_models_scoped m (FForall φ) Hforall) as Hscope.
  pose proof (proj1 (res_models_forall_iff m φ Hscope) Hforall)
    as [L Hbody].
  exists (L ∪ world_dom (m : WorldT)).
  intros y Hy my Hdom Hrestrict.
  assert (HyL : y ∉ L) by set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)) by set_solver.
  assert (Hfv : formula_fv φ ⊆ world_dom (m : WorldT)).
  { eapply formula_scoped_forall_body. exact Hscope. }
  destruct (forall_extension_from_world_dom_projection
    m my (formula_fv φ) y Hfv Hym Hdom Hrestrict)
    as [F [n [HFin [HFout [Hext Hproj]]]]].
  pose proof (Hbody y HyL F HFin HFout n Hext) as Hn.
  assert (Hopen_fv :
      formula_fv (formula_open 0 y φ) ⊆ formula_fv φ ∪ {[y]}).
  { apply formula_open_fv_subset. }
  apply (proj2 (res_models_minimal_on (formula_fv φ ∪ {[y]}) my
    (formula_open 0 y φ) Hopen_fv)).
  rewrite <- Hproj.
  apply (proj1 (res_models_minimal_on (formula_fv φ ∪ {[y]}) n
    (formula_open 0 y φ) Hopen_fv)).
  exact Hn.
Qed.

Lemma res_models_forall_open_named_fresh
    (m my : WfWorldT) x φ :
  m ⊨ FForall φ ->
  x ∉ world_dom (m : WorldT) ->
  world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[x]} ->
  res_restrict my (world_dom (m : WorldT)) = m ->
  my ⊨ formula_open 0 x φ.
Proof.
  intros Hforall Hx Hdom Hrestrict.
  destruct (res_models_forall_rev m φ Hforall) as [L Hrev].
  pose proof (res_models_scoped m (FForall φ) Hforall) as Hscope.
  pose proof (formula_scoped_forall_body m φ Hscope) as Hscope_body.
  set (y := fresh_for (L ∪ world_dom (my : WorldT) ∪ formula_fv φ ∪ {[x]})).
  pose proof (fresh_for_not_in
    (L ∪ world_dom (my : WorldT) ∪ formula_fv φ ∪ {[x]})) as Hyfresh.
  assert (HyL : y ∉ L) by better_set_solver.
  assert (Hym : y ∉ world_dom (m : WorldT)).
  { intros Hym.
    apply Hyfresh.
    rewrite Hdom.
    better_set_solver.
  }
  set (my_y := res_atom_swap x y my).
  assert (Hdom_y :
      world_dom (my_y : WorldT) = world_dom (m : WorldT) ∪ {[y]}).
  {
    unfold my_y.
    rewrite world_dom_res_atom_swap, Hdom, set_swap_union.
    rewrite set_swap_fresh by (exact Hx || exact Hym).
    rewrite set_swap_singleton, swap_l. reflexivity.
  }
  assert (Hrestrict_y : res_restrict my_y (world_dom (m : WorldT)) = m).
  {
    unfold my_y.
    rewrite <- (set_swap_fresh x y (world_dom (m : WorldT))) by
      (exact Hx || exact Hym).
    rewrite res_restrict_atom_swap, Hrestrict.
    apply res_atom_swap_fresh; [exact Hx | exact Hym].
  }
  pose proof (Hrev y HyL my_y Hdom_y Hrestrict_y) as Hbody_y.
  assert (Hxfv : x ∉ formula_fv φ).
  { intros Hbad. exact (Hx (Hscope_body x Hbad)). }
  assert (Hyfv : y ∉ formula_fv φ) by better_set_solver.
  apply (proj1 (res_models_atom_swap my (formula_open 0 x φ) x y)).
  rewrite formula_atom_swap_open_fresh by (exact Hxfv || exact Hyfv).
  exact Hbody_y.
Qed.

Lemma res_models_forall_rev_intro
    (m : WfWorldT) (φ : FormulaT) :
  formula_scoped_in_world m (FForall φ) ->
  (exists L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ) ->
  m ⊨ FForall φ.
Proof.
  intros Hscope [L Hfull].
  eapply res_models_forall_intro; [exact Hscope |].
  exists L. intros y Hy F HFin HFout my Hext.
  eapply Hfull; [exact Hy | |].
  - pose proof (res_extend_by_dom m F my Hext) as Hdom.
    unfold ext_out in HFout.
    rewrite Hdom, HFout. reflexivity.
  - eapply res_extend_by_restrict_base; exact Hext.
Qed.

Lemma res_models_forall_full_world_map
    (m : WfWorldT) (φ ψ : FormulaT) :
  (** This is the "full-world" view of [FForall].  The primitive semantics
      only asks extensions to read [formula_fv φ], but nested denotation
      transports often open a formula under several binders and then need to
      compare witnesses whose input domain is the whole current world.  The
      proof converts [FForall φ] to that full-world form with
      [res_models_forall_rev], maps the opened body there, and packages the
      result back with [res_models_forall_rev_intro].  This is intentionally
      independent of any [formula_fv φ = formula_fv ψ] side condition; the
      world-domain restriction/restrict-back hypotheses carry the alignment. *)
  formula_scoped_in_world m (FForall ψ) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        my ⊨ formula_open 0 y φ ->
        my ⊨ formula_open 0 y ψ) ->
  m ⊨ FForall φ ->
  m ⊨ FForall ψ.
Proof.
  intros Hscope [Lmap Hmap] Hforall.
  destruct (res_models_forall_rev m φ Hforall) as [Lsrc Hsrc].
  eapply res_models_forall_rev_intro; [exact Hscope |].
  exists (Lmap ∪ Lsrc).
  intros y Hy my Hdom Hrestrict.
  eapply Hmap.
  - set_solver.
  - exact Hdom.
  - exact Hrestrict.
  - eapply Hsrc.
    + set_solver.
    + exact Hdom.
    + exact Hrestrict.
Qed.

Lemma res_models_forall_full_world_impl2_map
    (m : WfWorldT)
    (A1 A2 B1 B2 C1 C2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 (FImpl B2 C2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B2 -> my ⊨ formula_open 0 y B1) /\
        (my ⊨ formula_open 0 y C1 -> my ⊨ formula_open 0 y C2)) ->
  m ⊨ FForall (FImpl A1 (FImpl B1 C1)) ->
  m ⊨ FForall (FImpl A2 (FImpl B2 C2)).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 (FImpl B2 C2)))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_impl in Hopened |- *.
  rewrite !formula_open_impl in Htarget_scope.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA [HB HC]].
  eapply res_models_impl2_map; [| exact HA | exact HB | exact HC | exact Hopened].
  exact Htarget_scope.
Qed.

Lemma res_models_forall_full_world_impl_map
    (m : WfWorldT)
    (A1 A2 B1 B2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 B2)) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B1 -> my ⊨ formula_open 0 y B2)) ->
  m ⊨ FForall (FImpl A1 B1) ->
  m ⊨ FForall (FImpl A2 B2).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 B2))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_impl in Hopened |- *.
  rewrite !formula_open_impl in Htarget_scope.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA HB].
  eapply res_models_impl_map; [| exact HA | exact HB | exact Hopened].
  exact Htarget_scope.
Qed.

Lemma res_models_forall_full_world_impl2_map_dep
    (m : WfWorldT)
    (A1 A2 B1 B2 C1 C2 : FormulaT) :
  formula_scoped_in_world m (FForall (FImpl A2 (FImpl B2 C2))) ->
  (∃ L : aset,
    forall y : atom, y ∉ L ->
      forall my : WfWorldT,
        world_dom (my : WorldT) = world_dom (m : WorldT) ∪ {[y]} ->
        res_restrict my (world_dom (m : WorldT)) = m ->
        (my ⊨ formula_open 0 y A2 -> my ⊨ formula_open 0 y A1) /\
        (my ⊨ formula_open 0 y B2 -> my ⊨ formula_open 0 y B1) /\
        (my ⊨ formula_open 0 y A2 ->
         my ⊨ formula_open 0 y B2 ->
         my ⊨ formula_open 0 y C1 ->
         my ⊨ formula_open 0 y C2)) ->
  m ⊨ FForall (FImpl A1 (FImpl B1 C1)) ->
  m ⊨ FForall (FImpl A2 (FImpl B2 C2)).
Proof.
  intros Hscope [L Hmap] Hforall.
  eapply res_models_forall_full_world_map; [exact Hscope | | exact Hforall].
  exists L.
  intros y Hy my Hdom Hrestrict Hopened.
  assert (Htarget_scope :
      formula_scoped_in_world my
        (formula_open 0 y (FImpl A2 (FImpl B2 C2)))).
  {
    eapply formula_scoped_forall_open_res_le.
    - exact Hscope.
    - rewrite <- Hrestrict. apply res_restrict_le.
    - rewrite Hdom. set_solver.
  }
  rewrite !formula_open_impl in Hopened |- *.
  rewrite !formula_open_impl in Htarget_scope.
  destruct (Hmap y Hy my Hdom Hrestrict) as [HA [HB HC]].
  eapply res_models_impl2_map_dep; [| exact HA | exact HB | exact HC | exact Hopened].
  exact Htarget_scope.
Qed.

End FormulaConnectives.

(** * ContextLogic.FormulaConnectives

    High-level algebraic properties of the store-free formula semantics. *)


Section FormulaConnectives.

Context {V : Type} `{ValueSig V}.

Local Notation WfWorldT := (WfWorld (V := V)) (only parsing).
Local Notation FormulaT := (Formula (V := V)) (only parsing).

Notation "φ ⊫ ψ" := (entails φ ψ)
  (at level 85, ψ at level 84, no associativity).

(** Over and under remain monotone.  Ordinary forall monotonicity is no longer
    exported as a separate lemma: the extension-form map lemmas are the useful
    interface under the new semantics. *)
Definition ext (φ : FormulaT) : WfWorldT → Prop :=
  λ m, res_models m φ.

Definition over_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m m'.

Definition under_closure (R : WfWorldT → Prop) : WfWorldT → Prop :=
  λ m', ∃ m, R m ∧ res_subset m' m.

End FormulaConnectives.
