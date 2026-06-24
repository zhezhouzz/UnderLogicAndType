(** * Denotation.TypeEquivTLetFormula

    TLet reverse transport from an explicit result graph.

    The ordinary [tlet_intro_denotation] theorem consumes a standard
    [expr_result_extension_witness]/[res_extend_by] pair.  Match proofs often
    already have an explicit result graph world instead.  This file bridges the
    two presentations: build a canonical extension world from the graph, prove
    it agrees with the given world on the variables observed by the target
    denotation, then reuse the existing TLet reverse direction. *)

From Denotation Require Import Notation TypeDenote.
From Denotation Require Import
  TypeEquivCore
  TypeEquivTermResult
  TypeEquivTLet
  TypeEquivFiberBaseResult
  TypeEquivFiberBaseProjected
  DenotationSetMapFacts.
From CoreLang Require Import StrongNormalization.

Section TypeDenote.

Local Lemma ty_denote_gas_models_projection
    gas Σ τ e (m n : WfWorldT) S :
  formula_fv (ty_denote_gas gas Σ τ e) ⊆ S ->
  res_restrict m S = res_restrict n S ->
  m ⊨ ty_denote_gas gas Σ τ e ->
  n ⊨ ty_denote_gas gas Σ τ e.
Proof.
  intros Hfv Hproj Hm.
  eapply res_models_projection; [|exact Hm].
  eapply res_restrict_eq_subset; [exact Hfv|exact Hproj].
Qed.

Lemma result_graph_tlet_reverse_transport
    gas (Σ : lty_env) τ e1 e2 x D (m : WfWorldT) :
  lc_lvars D ->
  tm_lvars e1 ⊆ D ->
  LVFree x ∉ D ->
  lvars_fv D ⊆ world_dom (m : WorldT) ->
  x ∉ fv_tm e2 ->
  x ∉ fv_cty τ ->
  formula_fv (ty_denote_gas 0 Σ τ (e2 ^^ x)) ⊆ lvars_fv D ∪ {[x]} ->
  formula_fv (ty_denote_gas 0 Σ τ (tlete e1 e2)) ⊆ lvars_fv D ∪ {[x]} ->
  formula_fv (ty_denote_gas gas Σ τ (e2 ^^ x)) ⊆ lvars_fv D ∪ {[x]} ->
  formula_fv (ty_denote_gas gas Σ τ (tlete e1 e2)) ⊆ lvars_fv D ∪ {[x]} ->
  lc_tm e1 ->
  m ⊨ expr_result_formula_at D e1 (LVFree x) ->
  wfworld_closed_on (fv_tm e1)
    (res_restrict m (world_dom (m : WorldT) ∖ {[x]})) ->
  expr_total_on_atom_world e1
    (res_restrict m (world_dom (m : WorldT) ∖ {[x]})) ->
  m ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x) ->
  m ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2) ->
  m ⊨ ty_denote_gas gas Σ τ (tlete e1 e2) ->
  m ⊨ ty_denote_gas gas Σ τ (e2 ^^ x).
Proof.
  intros HlcD HeD HxD HDm Hxe2 Hxτ
    Hfv0_body Hfv0_tlet Hfvg_body Hfvg_tlet
    Hlc_e1 Hres Hclosed_e1_base_delete Htotal_e1_base_delete
    Hzero_body Hzero_tlet Hgas_tlet.
  set (S := lvars_fv D ∪ {[x]}).
  assert (Hx_e1 : x ∉ fv_tm e1).
  {
    intros Hx_e1.
    apply HxD. apply HeD.
    apply lvars_fv_elem. rewrite tm_lvars_fv. exact Hx_e1.
  }
  assert (Hx_m : x ∈ world_dom (m : WorldT)).
  {
    pose proof (res_models_scoped _ _ Hres) as Hscope.
    unfold formula_scoped_in_world in Hscope.
    rewrite formula_fv_expr_result_formula_at in Hscope.
    apply Hscope.
    apply elem_of_union_r.
    apply lvars_fv_elem.
    apply elem_of_union_r. apply elem_of_singleton.
    reflexivity.
  }
  set (mbase := res_restrict m (world_dom (m : WorldT) ∖ {[x]})).
  assert (Hdom_m :
      world_dom (m : WorldT) = world_dom (mbase : WorldT) ∪ {[x]}).
  { subst mbase. apply res_restrict_delete_insert_dom. exact Hx_m. }
  assert (Hrestrict_m : res_restrict m (world_dom (mbase : WorldT)) = mbase).
  { subst mbase. apply res_restrict_self_dom. }
	  assert (HD_base : lvars_fv D ⊆ world_dom (mbase : WorldT)).
	  {
	    subst mbase. rewrite res_restrict_dom.
	    intros a Ha.
	    assert (a <> x).
	    {
	      intros ->. apply HxD. apply lvars_fv_elem. exact Ha.
	    }
	    apply elem_of_intersection. split.
	    - exact (HDm _ Ha).
	    - apply elem_of_difference. split.
	      + exact (HDm _ Ha).
	      + intros Hx. apply H. apply elem_of_singleton in Hx. exact Hx.
	  }
  assert (Hx_base : x ∉ world_dom (mbase : WorldT)).
  { subst mbase. apply res_restrict_delete_notin. }
  assert (Htotal_e1_base :
      expr_total_on_atom_world e1 mbase).
  { subst mbase. exact Htotal_e1_base_delete. }
  assert (Hclosed_e1_base :
      wfworld_closed_on (fv_tm e1) mbase).
  { subst mbase. exact Hclosed_e1_base_delete. }
	  pose proof (expr_result_formula_at_refine_domain_projected
	    D D D e1 x mbase m
	    ltac:(intros lv Hlv; exact Hlv)
	    ltac:(intros lv Hlv; exact Hlv)
	    HlcD HeD HxD Hx_base
	    HD_base Hdom_m Hrestrict_m Htotal_e1_base Hres)
    as [mstd [Hdom_std [Hrestrict_std [Hres_std Hproj_std_m]]]].
  assert (Hzero_body_std :
      mstd ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x)).
  {
    eapply ty_denote_gas_models_projection.
    - exact Hfv0_body.
    - symmetry. exact Hproj_std_m.
    - exact Hzero_body.
  }
  assert (Hzero_tlet_std :
      mstd ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2)).
  {
    eapply ty_denote_gas_models_projection.
    - exact Hfv0_tlet.
    - symmetry. exact Hproj_std_m.
    - exact Hzero_tlet.
  }
  assert (Hgas_tlet_std :
      mstd ⊨ ty_denote_gas gas Σ τ (tlete e1 e2)).
  {
    eapply ty_denote_gas_models_projection.
    - exact Hfvg_tlet.
    - symmetry. exact Hproj_std_m.
    - exact Hgas_tlet.
  }
  assert (Hbody_std :
      mstd ⊨ ty_denote_gas gas Σ τ (e2 ^^ x)).
  {
    destruct (expr_result_extension_witness_exists e1 x Hx_e1)
      as [Fx HFx].
    assert (Happ : extension_applicable Fx mbase).
    {
      destruct HFx as [_ [Hin Hout] _].
      constructor.
      - change (ext_in Fx ⊆ world_dom (mbase : WorldT)).
        rewrite Hin.
        intros a Ha.
        apply HD_base.
        apply lvars_fv_elem. apply HeD.
        apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
	      - change (ext_out Fx ## world_dom (mbase : WorldT)).
	        rewrite Hout.
	        intros a HaX HaBase.
	        apply elem_of_singleton in HaX. subst a.
	        exact (Hx_base HaBase).
    }
    destruct (res_extend_by_exists mbase Fx Happ) as [mx Hext].
    denotation_regular.
    assert (Hres_mx_D :
        mx ⊨ expr_result_formula_at D e1 (LVFree x)).
    {
      eapply expr_result_formula_at_coarsen_domain.
      - intros lv Hlv. apply elem_of_union_l. exact Hlv.
      - exact HeD.
      - intros Hbad.
        apply elem_of_union in Hbad as [Hbad|Hbad].
        + exact (HxD Hbad).
        + apply Hx_e1.
          rewrite <- tm_lvars_fv. apply lvars_fv_elem. exact Hbad.
      - eapply expr_result_formula_at_of_result_extends.
        + exact HlcD.
        + exact Hlc_e1.
        + exact HD_base.
        + intros a Ha.
          apply HD_base.
          apply lvars_fv_elem. apply HeD.
          apply lvars_fv_elem. rewrite tm_lvars_fv. exact Ha.
	        + intros Hbad.
	          apply elem_of_union in Hbad as [Hbad|Hbad].
	          * apply HxD. apply lvars_fv_elem. exact Hbad.
	          * exact (Hx_e1 Hbad).
        + exact HFx.
        + exact Hext.
        + exact Htotal_e1_base.
        + exact Hclosed_e1_base.
    }
    assert (Hproj_mx_std :
        res_restrict mx S = res_restrict mstd S).
    {
      subst S.
      assert (HoutFx : ext_out Fx = {[x]}).
      { destruct HFx as [_ [_ Hout] _]. exact Hout. }
      eapply (expr_result_formula_at_projection_eq_of_domains
        D D D e1 x mbase mstd mx).
      - intros lv Hlv. exact Hlv.
      - intros lv Hlv. exact Hlv.
      - exact HeD.
      - exact HxD.
      - exact HD_base.
      - exact Hdom_std.
      - exact Hrestrict_std.
      - rewrite Hdom_ext.
        change (extA_out Fx) with (ext_out Fx).
        rewrite HoutFx. reflexivity.
      - exact Hbase_ext.
      - exact Hres_std.
      - exact Hres_mx_D.
    }
    assert (Hzero_body_mx :
        mx ⊨ ty_denote_gas 0 Σ τ (e2 ^^ x)).
    {
      eapply ty_denote_gas_models_projection.
      - exact Hfv0_body.
      - symmetry. exact Hproj_mx_std.
      - exact Hzero_body_std.
    }
    assert (Hzero_tlet_mx :
        mx ⊨ ty_denote_gas 0 Σ τ (tlete e1 e2)).
    {
      eapply ty_denote_gas_models_projection.
      - exact Hfv0_tlet.
      - symmetry. exact Hproj_mx_std.
      - exact Hzero_tlet_std.
    }
    assert (Hgas_tlet_mx :
        mx ⊨ ty_denote_gas gas Σ τ (tlete e1 e2)).
    {
      eapply ty_denote_gas_models_projection.
      - exact Hfvg_tlet.
      - symmetry. exact Hproj_mx_std.
      - exact Hgas_tlet_std.
    }
    pose proof (proj2 (tlet_intro_denotation gas Σ τ e1 e2 x Fx
      mbase mx Hxe2 Hxτ HFx Hext Hzero_body_mx Hzero_tlet_mx)
      Hgas_tlet_mx) as Hbody_mx.
    eapply ty_denote_gas_models_projection.
    - exact Hfvg_body.
    - exact Hproj_mx_std.
    - exact Hbody_mx.
  }
  eapply ty_denote_gas_models_projection.
  - exact Hfvg_body.
  - exact Hproj_std_m.
  - exact Hbody_std.
Qed.

End TypeDenote.
