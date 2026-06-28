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
	    + destruct Hbody as [σ [Hdomσ [Hrestrict Hp]]].
	        exists (storeA_swap x y σ). split.
	        * transitivity (set_swap x y (dom (σ : StoreT))).
	          -- apply storeA_swap_dom.
	          -- rewrite Hdomσ, formula_fv_atom_swap,
	               set_swap_involutive. reflexivity.
	        * split.
	          -- change (res_restrict (res_atom_swap x y m0)
	               (formula_fv (formula_atom_swap x y ψ)) =
	               (exist _ (singleton_world σ) (wf_singleton_world σ)
	                 : WfWorldT)) in Hrestrict.
	             rewrite formula_fv_atom_swap in Hrestrict.
	             rewrite res_restrict_atom_swap in Hrestrict.
	             apply (f_equal (res_atom_swap x y)) in Hrestrict.
	             rewrite res_atom_swap_involutive in Hrestrict.
	             rewrite res_atom_swap_singleton_world in Hrestrict.
	             exact Hrestrict.
	          -- apply (proj1 (IHn ψ gas'
	               (exist _ (singleton_world (storeA_swap x y σ))
	                 (wf_singleton_world (storeA_swap x y σ)) : WfWorldT)
	               ltac:(simpl in Hn; lia))).
	             rewrite res_atom_swap_singleton_world,
	               storeA_swap_involutive.
	             exact Hp.
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
	      + destruct Hbody as [σ [Hdomσ [Hrestrict Hp]]].
	        exists (storeA_swap x y σ). split.
	        * transitivity (set_swap x y (dom (σ : StoreT))).
	          -- apply storeA_swap_dom.
	          -- rewrite Hdomσ. symmetry. apply formula_fv_atom_swap.
	        * split.
	          -- rewrite formula_fv_atom_swap, res_restrict_atom_swap.
	             rewrite Hrestrict. apply res_atom_swap_singleton_world.
	          -- pose proof (proj2 (IHn ψ gas'
	               (exist _ (singleton_world σ) (wf_singleton_world σ)
	                 : WfWorldT) ltac:(simpl in Hn; lia)) Hp) as Hp_sw.
	             rewrite res_atom_swap_singleton_world in Hp_sw.
	             exact Hp_sw.
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

Lemma res_models_over_and_elim_l (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FOver (FAnd φ ψ) ->
  m ⊨ FOver φ.
Proof.
  intros Hover.
  unfold res_models in *.
  cbn [formula_measure res_models_fuel] in *.
  destruct Hover as [Hscope [mo [Hsub Hand]]].
  split.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_over, formula_fv_and in Hscope.
    rewrite formula_fv_over.
    intros x Hx. apply Hscope. set_solver.
  - exists mo. split; [exact Hsub|].
    apply res_models_and_elim_l with (ψ := ψ).
    unfold res_models. models_fuel_irrel Hand.
Qed.

Lemma res_models_under_and_elim_l (m : WfWorldT) (φ ψ : FormulaT) :
  m ⊨ FUnder (FAnd φ ψ) ->
  m ⊨ FUnder φ.
Proof.
  intros Hunder.
  unfold res_models in *.
  cbn [formula_measure res_models_fuel] in *.
  destruct Hunder as [Hscope [mo [Hsub Hand]]].
  split.
  - unfold formula_scoped_in_world in *.
    rewrite formula_fv_under, formula_fv_and in Hscope.
    rewrite formula_fv_under.
    intros x Hx. apply Hscope. set_solver.
  - exists mo. split; [exact Hsub|].
    apply res_models_and_elim_l with (ψ := ψ).
    unfold res_models. models_fuel_irrel Hand.
Qed.

Lemma formula_scoped_persist_from_singleton
    (m : WfWorldT) (φ : FormulaT) (σ : Store (V := V)) :
  dom (σ : Store (V := V)) = formula_fv φ ->
  res_restrict m (formula_fv φ) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  formula_scoped_in_world m (FPersist φ).
Proof.
  intros Hdomσ Hrestrict.
  unfold formula_scoped_in_world.
  rewrite formula_fv_persist.
  pose proof (f_equal (fun w : WfWorldT => world_dom (w : WorldT))
    Hrestrict) as Hdom_restrict.
  change (world_dom (res_restrict m (formula_fv φ) : WorldT) =
    world_dom ((exist _ (singleton_world σ) (wf_singleton_world σ)
      : WfWorldT) : WorldT)) in Hdom_restrict.
  rewrite res_restrict_dom in Hdom_restrict.
  change (world_dom ((exist _ (singleton_world σ) (wf_singleton_world σ)
    : WfWorldT) : WorldT)) with (dom (σ : Store (V := V))) in Hdom_restrict.
  rewrite Hdomσ in Hdom_restrict.
  set_solver.
Qed.

Lemma res_models_persist_intro
    (m : WfWorldT) (φ : FormulaT) (σ : Store (V := V)) :
  dom (σ : Store (V := V)) = formula_fv φ ->
  res_restrict m (formula_fv φ) =
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ->
  (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ⊨ φ ->
  m ⊨ FPersist φ.
Proof.
  intros Hdomσ Hrestrict Hφ.
  unfold res_models. cbn [formula_measure res_models_fuel].
  split.
  - eapply formula_scoped_persist_from_singleton; eauto.
  - exists σ. split; [exact Hdomσ|].
    split; [exact Hrestrict|].
    models_fuel_irrel Hφ.
Qed.

Lemma res_models_persist_iff (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FPersist φ <->
  exists σ : Store (V := V),
    dom (σ : Store (V := V)) = formula_fv φ /\
    res_restrict m (formula_fv φ) =
      (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) /\
    (exist _ (singleton_world σ) (wf_singleton_world σ) : WfWorldT) ⊨ φ.
Proof.
  split.
  - unfold res_models. cbn [formula_measure res_models_fuel].
    intros [_ [σ [Hdomσ [Hrestrict Hφ]]]].
    exists σ. split; [exact Hdomσ|].
    split; [exact Hrestrict|].
    unfold res_models. exact Hφ.
  - intros [σ [Hdomσ [Hrestrict Hφ]]].
    eapply res_models_persist_intro; eauto.
Qed.

Lemma res_models_persist_elim (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FPersist φ ->
  m ⊨ φ.
Proof.
  intros Hpersist.
  apply res_models_persist_iff in Hpersist as [σ [_ [Hrestrict Hφ]]].
  eapply res_models_kripke; [| exact Hφ].
  rewrite <- Hrestrict.
  apply res_restrict_le.
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

Lemma res_models_over_FAtom_store_holds (m : WfWorldT) q :
  m ⊨ FOver (FAtom q) ->
  forall σ, (m : WorldT) σ -> qualifier_holds_store q σ.
Proof.
  intros Hover σ Hσ.
  unfold res_models in Hover.
  cbn [formula_measure res_models_fuel] in Hover.
  destruct Hover as [_ [mo [Hsub Hatom]]].
  eapply res_models_FAtom_store_holds; [exact Hatom|].
  destruct Hsub as [Hdom Hstores].
  apply Hstores.
  exact Hσ.
Qed.

Lemma res_models_over_FAtom_intro_store_holds (m : WfWorldT) q :
  formula_scoped_in_world m (FOver (FAtom q)) ->
  (forall σ, (m : WorldT) σ -> qualifier_holds_store q σ) ->
  m ⊨ FOver (FAtom q).
Proof.
  intros Hscope Hholds.
  destruct (world_wf m) as [[σ0 Hσ0] Hdom].
  set (A := world_dom (m : WorldT)).
  assert (Hdom0 : dom (σ0 : StoreT) = A).
  { subst A. apply Hdom. exact Hσ0. }
  assert (Hholds0 : qualifier_holds_store q σ0).
  { apply Hholds. exact Hσ0. }
  set (mo := qualifier_saturated_world A q σ0 Hdom0 Hholds0).
  unfold res_models. cbn [formula_measure res_models_fuel].
  split; [exact Hscope|].
  exists mo. split.
  - split.
	    + subst mo A.
	      cbn [qualifier_saturated_world qualifier_saturated_raw_world
	        raw_world world_dom].
      reflexivity.
	    + intros σ Hσ.
	      subst mo A.
	      cbn [qualifier_saturated_world qualifier_saturated_raw_world
	        raw_world world_stores].
      split.
      * apply Hdom. exact Hσ.
      * apply Hholds. exact Hσ.
  - unfold res_models. cbn [formula_measure res_models_fuel].
    split.
    + unfold formula_scoped_in_world in Hscope |- *.
      rewrite formula_fv_over, formula_fv_atom in Hscope.
      rewrite formula_fv_atom.
	      subst mo A.
	      cbn [qualifier_saturated_world qualifier_saturated_raw_world
	        raw_world world_dom].
      exact Hscope.
    + apply qualifier_saturated_world_exact.
      unfold formula_scoped_in_world in Hscope.
      rewrite formula_fv_over, formula_fv_atom in Hscope.
      subst A. exact Hscope.
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

Lemma res_fiber_from_projection_empty_self (m : WfWorldT) :
  res_fiber_from_projection m ∅ (∅ : Store (V := V)) m.
Proof.
  split.
  - destruct (world_wf m) as [[σ Hσ] _].
    exists σ. split; [exact Hσ|].
    apply storeA_restrict_empty_set.
  - apply world_ext.
    + reflexivity.
    + intros σ. split.
      * intros Hσ. split; [exact Hσ|].
        apply storeA_restrict_empty_set.
      * intros [Hσ _]. exact Hσ.
Qed.

Lemma res_models_fibvars_empty_elim
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ FFibVars ∅ φ ->
  m ⊨ φ.
Proof.
  intros Hfib.
  unfold res_models in Hfib |- *.
  cbn [formula_measure res_models_fuel] in Hfib |- *.
  destruct Hfib as [_ [_ Hfib]].
  specialize (Hfib (∅ : Store (V := V)) m
    (res_fiber_from_projection_empty_self m)).
  rewrite formula_msubst_store_empty in Hfib by reflexivity.
  models_fuel_irrel Hfib.
Qed.

Lemma res_fiber_from_projection_empty_eq
    (m mfib : WfWorldT) (σ : Store (V := V)) :
  res_fiber_from_projection m ∅ σ mfib ->
  mfib = m.
Proof.
  intros Hfib.
  pose proof (res_fiber_from_projection_empty_store_dom m mfib σ Hfib)
    as Hσdom.
  apply wfworld_ext, world_ext.
  - destruct Hfib as [_ Hfib_eq].
    change ((mfib : WorldT) = raw_fiber (m : WorldT) σ) in Hfib_eq.
    rewrite Hfib_eq. reflexivity.
  - intros τ. split.
    + intros Hτ.
      eapply res_fiber_from_projection_store_source; eauto.
    + intros Hτ.
      destruct Hfib as [_ Hfib_eq].
      change ((mfib : WorldT) = raw_fiber (m : WorldT) σ) in Hfib_eq.
      rewrite Hfib_eq.
      split; [exact Hτ|].
      apply storeA_map_eq. intros a.
      rewrite storeA_restrict_lookup.
      destruct (decide (a ∈ dom (σ : Store (V := V)))) as [Ha|Ha].
      * rewrite decide_True by exact Ha.
        exfalso. pose proof Hσdom. set_solver.
      * rewrite decide_False by exact Ha.
        destruct (σ !! a) as [v|] eqn:Hσa; [|symmetry; exact Hσa].
        exfalso. apply Ha.
        change ((σ : gmap atom V) !! a = Some v) in Hσa.
        change (a ∈ dom (σ : gmap atom V)).
        by apply elem_of_dom_2 in Hσa.
Qed.

Lemma res_models_fibvars_empty_intro
    (m : WfWorldT) (φ : FormulaT) :
  m ⊨ φ ->
  m ⊨ FFibVars ∅ φ.
Proof.
  intros Hφ.
  eapply res_models_FFibVars_intro.
  - unfold formula_scoped_in_world.
    rewrite formula_fv_fibvars, lvars_fv_empty.
    eapply res_models_fuel_scoped in Hφ.
    unfold formula_scoped_in_world in Hφ. set_solver.
  - apply lc_lvars_no_bv. set_solver.
  - intros σ mfib Hfib.
    pose proof (res_fiber_from_projection_empty_store_dom m mfib σ Hfib)
      as Hσdom.
    rewrite (res_fiber_from_projection_empty_eq m mfib σ Hfib).
    replace σ with (∅ : Store (V := V)).
    + rewrite formula_msubst_store_empty by reflexivity. exact Hφ.
    + apply storeA_map_eq. intros a.
      rewrite lookup_empty.
      destruct (σ !! a) as [v|] eqn:Hσa; [|symmetry; exact Hσa].
      exfalso.
      change ((σ : gmap atom V) !! a = Some v) in Hσa.
      pose proof Hσa as Ha.
      apply elem_of_dom_2 in Ha.
      rewrite Hσdom in Ha. set_solver.
Qed.

Local Lemma store_restrict_fixed_union_piece_lvars
    (D : lvset) (X : aset) (σall σfix : Store (V := V)) :
  dom (σall : Store (V := V)) ⊆ lvars_fv D ->
  X ⊆ lvars_fv D ->
  store_restrict σall X = σfix ->
  σfix ∪ store_restrict σall (lvars_fv (D ∖ lvars_of_atoms X)) = σall.
Proof.
  intros Hall HX Hfix.
  rewrite lvars_fv_difference_atoms.
  assert (HσfixD : dom (σfix : Store (V := V)) ⊆ lvars_fv D).
  {
    rewrite <- Hfix.
    pose proof (storeA_restrict_dom_subset (σall : gmap atom V) X) as Hdom.
    change (dom (store_restrict σall X : Store (V := V)) ⊆ X) in Hdom.
    set_solver.
  }
  rewrite <- (storeA_restrict_idemp σfix (lvars_fv D) HσfixD) at 1.
  symmetry.
  eapply storeA_restrict_fixed_union_piece; eauto.
Qed.

Lemma res_models_fibvars_msubst_store_fixed
    (m : WfWorldT) (D : lvset) (φ : FormulaT) σfix :
  dom (σfix : Store (V := V)) ⊆ lvars_fv D ->
  (forall τ, (m : WorldT) τ ->
    store_restrict τ (dom (σfix : Store (V := V))) = σfix) ->
  m ⊨ FFibVars D φ <->
  m ⊨ formula_msubst_store σfix (FFibVars D φ).
Proof.
  intros HσD Hfixed.
  set (Xfix := dom (σfix : Store (V := V))) in *.
  rewrite formula_msubst_store_fibvars.
  rewrite res_models_FFibVars_iff.
  rewrite res_models_FFibVars_iff.
  split.
  - intros [Hscope [Hlc Hfib]].
    split.
	    {
	      unfold formula_scoped_in_world in *.
	      intros a Ha.
	      apply Hscope.
	      rewrite !formula_fv_fibvars in Ha |- *.
	      rewrite lvars_fv_difference_atoms in Ha.
	      apply elem_of_union in Ha as [Ha|Ha].
	      - apply elem_of_union_l. set_solver.
	      - apply elem_of_union_r.
	        apply formula_msubst_store_fv_subset in Ha. exact Ha.
	    }
    split.
    {
      intros v Hv.
      apply Hlc.
      set_solver.
    }
    intros σres mfib Hproj_res.
    rewrite formula_msubst_store_merge.
    2:{
      pose proof (res_fiber_from_projection_store_dom_subset
        m mfib (lvars_fv (D ∖ lvars_of_atoms (dom (σfix : Store (V := V)))))
        σres Hproj_res) as Hres_dom.
      rewrite lvars_fv_difference_atoms in Hres_dom.
      set_solver.
    }
    replace (σfix ∪ σres)
      with (store_restrict σfix (lvars_fv D) ∪ σres).
    2:{
      rewrite storeA_restrict_idemp; [reflexivity|exact HσD].
    }
    eapply Hfib.
    rewrite lvars_fv_difference_atoms in Hproj_res.
    eapply res_fiber_from_projection_add_fixed_domain; [exact Hfixed|].
    exact Hproj_res.
  - intros [Hscope [Hlc Hfib]].
    split.
    {
      unfold formula_scoped_in_world in *.
      intros a Ha.
      destruct (decide (a ∈ dom (σfix : Store (V := V)))) as [Haσ|Haσ].
	      - destruct (world_wf m) as [[τ Hτ] _].
	        rewrite <- (wfworld_store_dom m τ Hτ).
	        change (a ∈ dom (τ : gmap atom V)).
	        rewrite elem_of_dom.
	        change (a ∈ dom (σfix : gmap atom V)) in Haσ.
	        rewrite elem_of_dom in Haσ.
	        destruct Haσ as [v Hv].
	        exists v.
        assert (Hlook :
          (store_restrict τ (dom (σfix : Store (V := V))) :
            Store (V := V)) !! a = Some v).
        { rewrite Hfixed by exact Hτ. exact Hv. }
        apply storeA_restrict_lookup_some in Hlook as [_ Hτa].
        exact Hτa.
	      - apply Hscope.
	        rewrite formula_fv_fibvars.
	        rewrite formula_fv_fibvars in Ha.
	        rewrite lvars_fv_difference_atoms.
	        apply elem_of_union in Ha as [Ha|Ha].
	        + apply elem_of_union_l. set_solver.
	        + apply elem_of_union_r.
	          rewrite formula_msubst_store_fv. set_solver.
    }
	    split.
	    {
	      intros v Hv.
	      destruct v as [k|a]; [|exact I].
	      apply Hlc. better_set_solver.
	    }
    intros σall mfib Hproj_all.
    pose proof (res_fiber_from_projection_store_dom_subset
      m mfib (lvars_fv D) σall Hproj_all) as Hall_dom.
    pose proof (res_fiber_from_projection_drop_fixed_domain
      m mfib (lvars_fv D) σall σfix Hfixed Hproj_all) as Hproj_res.
    rewrite <- lvars_fv_difference_atoms in Hproj_res.
    specialize (Hfib _ _ Hproj_res).
	    rewrite formula_msubst_store_merge in Hfib.
	    2:{
	      pose proof (storeA_restrict_dom_subset
	        (σall : gmap atom V)
	        (lvars_fv (D ∖ lvars_of_atoms (dom (σfix : Store (V := V))))))
	        as Hres_dom.
	      change (dom (store_restrict σall
	        (lvars_fv (D ∖ lvars_of_atoms (dom (σfix : Store (V := V))))) :
	          Store (V := V)) ⊆
	        lvars_fv (D ∖ lvars_of_atoms (dom (σfix : Store (V := V)))))
	        in Hres_dom.
	      intros a Haσ Hares.
	      apply Hres_dom in Hares.
	      rewrite lvars_fv_difference_atoms in Hares.
	      apply elem_of_difference in Hares as [_ Ha_not].
	      exact (Ha_not Haσ).
	    }
	    replace (σfix ∪
	        store_restrict (σall : gmap atom V)
	          (lvars_fv (D ∖ lvars_of_atoms Xfix)))
	      with σall in Hfib.
    { exact Hfib. }
    symmetry.
	    assert (Hσall_fix :
	        store_restrict σall Xfix = σfix).
    {
      destruct Hproj_all as [[τ [Hτ HτY]] _].
      rewrite <- HτY.
	      rewrite storeA_restrict_restrict.
		      replace (lvars_fv D ∩ Xfix) with Xfix by set_solver.
      exact (Hfixed τ Hτ).
    }
	    apply store_restrict_fixed_union_piece_lvars; assumption.
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
