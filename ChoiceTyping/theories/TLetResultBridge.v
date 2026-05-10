(** * ChoiceTyping.TLetResultBridge

    The high-risk expression-result bridge for [tlet].

    This file is intentionally placed after both [ResultWorldBridge] and
    [TLetGraph].  The general result-world facts do not depend on the
    proof-only tlet graph, while the tlet bridge does: its job is to show that
    the graph preserves the exact [X -> x -> ν] pairing needed by the body
    proof and by the whole-let result atom. *)

From CoreLang Require Import Instantiation InstantiationProps OperationalProps
  LocallyNamelessProps.
From ChoiceTyping Require Export ResultWorldBridge.
From ChoiceTyping Require Import TLetGraph.
From ChoiceType Require Import BasicStore LocallyNamelessProps.

Lemma nested_tlet_result_world_source_transport
    X e1 e2 x ν (m ntgt : WfWorld)
    Hfresh_m Hresult_m Hfreshx_ntgtX Hresult_ntgtX Hfreshν Hresult_body :
  X ⊆ world_dom (m : World) →
  m ⊑ ntgt →
  x ∉ X →
  ν ∉ X ∪ {[x]} →
  model_transport_on (X ∪ {[x]})
    (let_result_world_on X e1 x m Hfresh_m Hresult_m)
    (let_result_world_on (X ∪ {[x]}) (e2 ^^ x) ν
      (let_result_world_on X e1 x (res_restrict ntgt X)
        Hfreshx_ntgtX Hresult_ntgtX)
      Hfreshν Hresult_body).
Proof.
  intros HXm Hmn HxX HνXx.
  eapply model_transport_on_restrict_common.
  - pose proof (raw_le_dom (m : World) (ntgt : World) Hmn) as Hdommn.
    simpl. set_solver.
  - transitivity
      (let_result_world_on X e1 x (res_restrict ntgt X)
        Hfreshx_ntgtX Hresult_ntgtX).
    + apply let_result_world_on_restrict_input_le; assumption.
    + symmetry.
      assert (Hdom_base :
        world_dom (let_result_world_on X e1 x (res_restrict ntgt X)
          Hfreshx_ntgtX Hresult_ntgtX : World) = X ∪ {[x]}).
      {
        simpl.
        pose proof (raw_le_dom (m : World) (ntgt : World) Hmn) as Hdommn.
        set_solver.
      }
      transitivity (res_restrict
        (let_result_world_on (X ∪ {[x]}) (e2 ^^ x) ν
          (let_result_world_on X e1 x (res_restrict ntgt X)
            Hfreshx_ntgtX Hresult_ntgtX)
          Hfreshν Hresult_body)
        (world_dom
          (let_result_world_on X e1 x (res_restrict ntgt X)
            Hfreshx_ntgtX Hresult_ntgtX : World))).
      * f_equal. symmetry. exact Hdom_base.
      * exact (let_result_world_on_restrict
          (X ∪ {[x]}) (e2 ^^ x) ν
          (let_result_world_on X e1 x (res_restrict ntgt X)
            Hfreshx_ntgtX Hresult_ntgtX)
          Hfreshν Hresult_body).
Qed.

Lemma nested_tlet_result_world_target_transport
    X e1 e2 x ν (ntgt : WfWorld)
    Hfreshx Hresult1 Hfreshν Hresult2 :
  x ∉ X ∪ fv_tm e2 ∪ {[ν]} →
  fv_tm (tlete e1 e2) ⊆ X →
  ν ∉ X →
  X ⊆ world_dom (ntgt : World) →
  world_store_closed_on X ntgt →
  lc_tm (tlete e1 e2) →
  ntgt ⊨ FExprResultOn X (tlete e1 e2) ν →
  model_transport_on (X ∪ {[ν]})
    (let_result_world_on (X ∪ {[x]}) (e2 ^^ x) ν
      (let_result_world_on X e1 x (res_restrict ntgt X) Hfreshx Hresult1)
      Hfreshν Hresult2)
    ntgt.
Proof.
  intros Hx Hfv HνX HXntgt Hclosed Hlc Htarget.
  destruct (proj1 (lc_lete_iff_body e1 e2) Hlc) as [Hlce1 Hbodye2].
  pose proof (proj1 (FExprResultOn_iff_let_result_world_on
    X (tlete e1 e2) ν ntgt Hfv Hlc HνX HXntgt Hclosed) Htarget)
    as [Hfresh_tlet [Hresult_tlet Heq_tgt]].
  assert (Hνntgt : ν ∈ world_dom (ntgt : World)).
  {
    pose proof (FExprResultOn_scoped_dom X (tlete e1 e2) ν ntgt
      (res_models_with_store_fuel_scoped _ _ _ _ Htarget)) as Hscoped.
    set_solver.
  }
  eapply model_transport_on_restrict_common.
  - simpl. intros z Hz.
    apply elem_of_union in Hz as [HzX | Hzν].
    + apply elem_of_intersection. split; [set_solver | apply HXntgt; exact HzX].
    + apply elem_of_singleton in Hzν. subst z.
      apply elem_of_intersection. split; [set_solver | exact Hνntgt].
  - transitivity (let_result_world_on X (tlete e1 e2) ν
      (res_restrict ntgt X) Hfresh_tlet Hresult_tlet).
    + replace (X ∪ {[ν]}) with
        (world_dom (res_restrict ntgt X : World) ∪ {[ν]}).
      2:{ simpl. set_solver. }
      eapply let_result_world_on_tlete_decompose.
      * exact Hfv.
      * exact Hx.
      * exact Hfresh_tlet.
      * simpl. set_solver.
	      * intros σ Hσ.
	        eapply world_store_closed_on_restrict_store_restrict_closed_env.
	        -- exact Hclosed.
	        -- exact Hσ.
	      * intros σ Hσ.
	        eapply world_store_closed_on_restrict_store_restrict_lc_env.
	        -- exact Hclosed.
	        -- exact Hσ.
	      * intros σ vx Hσ Hsteps.
	        eapply (steps_closed_result_of_restrict_world X e1 ntgt σ vx).
	        -- exact HXntgt.
	        -- intros z Hz. apply Hfv. simpl. set_solver.
	        -- exact Hlce1.
	        -- exact Hclosed.
	        -- exact Hσ.
	        -- exact Hsteps.
	      * intros σ Hσ.
	        eapply body_tm_msubst_restrict_world.
	        -- exact Hbodye2.
	        -- exact Hclosed.
	        -- exact Hσ.
    + symmetry. exact Heq_tgt.
Qed.

Lemma nested_body_result_world_models_FExprResultOn
    X e1 e2 x ν (ntgt : WfWorld)
    Hfreshx Hresult1 Hfreshν Hresult2 :
  x ∉ X ∪ fv_tm e2 →
  fv_tm (tlete e1 e2) ⊆ X →
  ν ∉ X ∪ {[x]} →
  X ⊆ world_dom (ntgt : World) →
  world_store_closed_on X ntgt →
  lc_tm (tlete e1 e2) →
  let_result_world_on (X ∪ {[x]}) (e2 ^^ x) ν
    (let_result_world_on X e1 x (res_restrict ntgt X) Hfreshx Hresult1)
    Hfreshν Hresult2
    ⊨ FExprResultOn (X ∪ {[x]}) (e2 ^^ x) ν.
Proof.
  intros Hx Hfv HνXx HXntgt Hclosed Hlc.
  destruct (proj1 (lc_lete_iff_body e1 e2) Hlc) as [Hlce1 Hbodye2].
  apply let_result_world_on_models_FExprResultOn.
  - change (fv_tm (open_tm 0 (vfvar x) e2) ⊆ X ∪ {[x]}).
    pose proof (open_fv_tm e2 (vfvar x) 0) as Hopen.
    simpl in Hopen. set_solver.
  - apply body_open_tm; [exact Hbodye2 | constructor].
  - exact HνXx.
  - simpl. set_solver.
  - apply let_result_world_on_store_closed_on_insert.
    + assert (HxX : x ∉ X) by set_solver.
      exact HxX.
	    + eapply world_store_closed_on_restrict; [set_solver | exact Hclosed].
	    + intros σ vx Hσ Hsteps.
	      eapply (steps_closed_result_of_restrict_world X e1 ntgt σ vx).
	      * exact HXntgt.
	      * intros z Hz. apply Hfv. simpl. set_solver.
	      * exact Hlce1.
	      * exact Hclosed.
	      * exact Hσ.
	      * exact Hsteps.
Qed.

(** High-risk tlet expression-result bridge.

    This is the resource-level version of the operational identity
    [Results(let x = e1 in e2) = Results(e2[x := Results(e1)])].
    It is intentionally phrased as an [expr_result_model_bridge], so later type
    denotation transport can stay generic in [τ].

    Anti-slip rule: this proof must stay expression/resource-level.  It should
    use the tlet graph and exact expression-result worlds, but it must not
    inspect the final choice type or split into [CTOver]/[CTUnder] cases. *)
Lemma expr_result_model_bridge_tlete
    X e1 e2 x (m : WfWorld) Hfresh Hresult :
  x ∉ X ∪ fv_tm e2 →
  fv_tm (tlete e1 e2) ⊆ X →
  X ⊆ world_dom (m : World) →
  world_store_closed_on X m →
  lc_tm (tlete e1 e2) →
  (∀ n,
    m ⊑ n →
    X ⊆ world_dom (n : World) →
    (∀ σ, (n : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx) →
    ∀ Hfreshn Hresultn,
      expr_total_on (X ∪ {[x]}) (e2 ^^ x)
        (let_result_world_on X e1 x n Hfreshn Hresultn)) →
  expr_result_model_bridge
    (X ∪ {[x]}) (e2 ^^ x)
    X (tlete e1 e2)
    (let_result_world_on X e1 x m Hfresh Hresult)
    m.
Proof.
  intros Hx Hfv HXm Hclosed_m Hlc Hbody_total_future.
  unfold expr_result_model_bridge.
  intros ν ntgt Hνfresh Hsrc_aux_fresh Hνm Hmntgt Htarget.
  assert (HνX : ν ∉ X) by set_solver.
  assert (HxX : x ∉ X) by set_solver.
  assert (Hxe2 : x ∉ fv_tm e2) by set_solver.
  assert (Hxν : x ≠ ν) by set_solver.
  assert (HXntgt : X ⊆ world_dom (ntgt : World)).
  { pose proof (raw_le_dom (m : World) (ntgt : World) Hmntgt) as Hdom.
    set_solver. }
  assert (Hclosed_ntgt : world_store_closed_on X ntgt).
  {
    eapply (world_store_closed_on_le X m ntgt).
    - exact HXm.
    - exact Hmntgt.
    - exact Hclosed_m.
  }
  destruct (proj1 (lc_lete_iff_body e1 e2) Hlc) as [Hlce1 Hbodye2].

  pose proof (proj1 (FExprResultOn_iff_let_result_world_on
    X (tlete e1 e2) ν ntgt Hfv Hlc HνX HXntgt Hclosed_ntgt) Htarget)
    as [Hfresh_tlet [Hresult_tlet Heq_tgt]].

  set (ntgtX := res_restrict ntgt X).
  assert (Hfreshx_ntgt : x ∉ world_dom (ntgt : World)).
  {
    assert (Hxsrc : x ∈ (X ∪ {[x]}) ∖ X) by set_solver.
    unfold disjoint in Hsrc_aux_fresh.
    specialize (Hsrc_aux_fresh x).
    set_solver.
  }
  assert (Hfreshx_ntgtX : x ∉ world_dom (ntgtX : World)).
  { subst ntgtX. simpl. set_solver. }

  assert (Hresult_ntgt_e1 :
    ∀ σ, (ntgt : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx).
  {
    intros σ Hσ.
    assert (HσX : (ntgtX : World) (store_restrict σ X)).
    { subst ntgtX. exists σ. split; [exact Hσ | reflexivity]. }
    destruct (Hresult_tlet (store_restrict σ X) HσX) as [v Hsteps_tlet].
    rewrite store_restrict_restrict in Hsteps_tlet.
    replace (X ∩ X) with X in Hsteps_tlet by set_solver.
    change (subst_map (store_restrict σ X) (tlete e1 e2))
      with (m{store_restrict σ X} (tlete e1 e2)) in Hsteps_tlet.
    rewrite msubst_lete in Hsteps_tlet.
    destruct (reduction_lete
      (m{store_restrict σ X} e1) (m{store_restrict σ X} e2) v Hsteps_tlet)
      as [vx [Hsteps1 _]].
    exists vx. exact Hsteps1.
  }

  assert (Hresult_ntgtX_e1 :
    ∀ σ, (ntgtX : World) σ →
      ∃ vx, subst_map (store_restrict σ X) e1 →* tret vx).
  {
    intros σ Hσ.
    destruct (Hresult_tlet σ Hσ) as [v Hsteps_tlet].
    change (subst_map (store_restrict σ X) (tlete e1 e2))
      with (m{store_restrict σ X} (tlete e1 e2)) in Hsteps_tlet.
    rewrite msubst_lete in Hsteps_tlet.
    destruct (reduction_lete
      (m{store_restrict σ X} e1) (m{store_restrict σ X} e2) v Hsteps_tlet)
      as [vx [Hsteps1 _]].
    exists vx. exact Hsteps1.
  }

  set (w1 := let_result_world_on X e1 x ntgtX Hfreshx_ntgtX Hresult_ntgtX_e1).
  assert (Hfreshν_w1 : ν ∉ world_dom (w1 : World)).
  { subst w1 ntgtX. simpl. set_solver. }

  assert (Hbody_total_ntgt :
    expr_total_on (X ∪ {[x]}) (e2 ^^ x)
      (let_result_world_on X e1 x ntgt Hfreshx_ntgt Hresult_ntgt_e1)).
  { eapply Hbody_total_future; eauto. }

  assert (Hresult_body :
    ∀ σx, (w1 : World) σx →
      ∃ v, subst_map (store_restrict σx (X ∪ {[x]})) (e2 ^^ x) →* tret v).
  {
    intros σx Hσx.
    destruct (let_result_world_on_elim X e1 x ntgtX Hfreshx_ntgtX
      Hresult_ntgtX_e1 σx Hσx) as [σX [vx [HσX [Hsteps1 ->]]]].
    destruct HσX as [σ [Hσ Hσ_restrict]].
    pose proof (let_result_world_on_member X e1 x ntgt Hfreshx_ntgt
      Hresult_ntgt_e1 σ vx Hσ) as Hσx_ntgt.
    assert (Hsteps1_full : subst_map (store_restrict σ X) e1 →* tret vx).
    { rewrite <- Hσ_restrict in Hsteps1.
      rewrite store_restrict_restrict in Hsteps1.
      replace (X ∩ X) with X in Hsteps1 by set_solver.
      exact Hsteps1. }
    specialize (Hσx_ntgt Hsteps1_full).
    destruct Hbody_total_ntgt as [_ Htotal_body].
    destruct (Htotal_body (<[x := vx]> σ) Hσx_ntgt) as [v Hsteps_body].
    exists v.
    assert (HσX_proj :
      store_restrict (<[x := vx]> σX) (X ∪ {[x]}) = <[x := vx]> σX).
    {
      rewrite <- Hσ_restrict.
      rewrite store_restrict_insert_fresh_union.
      - rewrite store_restrict_restrict.
        replace (X ∩ X) with X by set_solver.
        reflexivity.
      - eapply store_lookup_none_of_dom.
        + rewrite store_restrict_dom.
          pose proof (wfworld_store_dom ntgt σ Hσ) as Hdomσ.
          set_solver.
        + set_solver.
      - exact HxX.
    }
    assert (Hσ_proj :
      store_restrict (<[x := vx]> σ) (X ∪ {[x]}) = <[x := vx]> σX).
    {
      rewrite store_restrict_insert_fresh_union.
      - rewrite Hσ_restrict. reflexivity.
      - eapply store_lookup_none_of_dom.
        + apply wfworld_store_dom. exact Hσ.
        + exact Hfreshx_ntgt.
      - exact HxX.
    }
    rewrite HσX_proj, <- Hσ_proj.
    exact Hsteps_body.
  }

  (** At this point the core paired-totality construction has been checked:
      the target whole-let exact result atom plus future body totality produces
      a body-result world over the projected let-result resource.  The remaining
      work is resource transport bookkeeping between this world, the source
      continuation scope, and the target [X ∪ {ν}] scope. *)
  set (nsrc := let_result_world_on (X ∪ {[x]}) (e2 ^^ x) ν w1 Hfreshν_w1 Hresult_body).
  exists nsrc.
  split.
  - subst nsrc w1 ntgtX.
    exact (nested_tlet_result_world_source_transport
      X e1 e2 x ν m ntgt Hfresh Hresult Hfreshx_ntgtX Hresult_ntgtX_e1
      Hfreshν_w1 Hresult_body HXm Hmntgt HxX ltac:(set_solver)).
  - split.
    + subst nsrc w1 ntgtX.
      exact (nested_body_result_world_models_FExprResultOn
        X e1 e2 x ν ntgt Hfreshx_ntgtX Hresult_ntgtX_e1
        Hfreshν_w1 Hresult_body Hx Hfv ltac:(set_solver) HXntgt
        Hclosed_ntgt Hlc).
    + subst nsrc w1 ntgtX.
      exact (nested_tlet_result_world_target_transport
        X e1 e2 x ν ntgt Hfreshx_ntgtX Hresult_ntgtX_e1
        Hfreshν_w1 Hresult_body ltac:(set_solver) Hfv HνX HXntgt
        Hclosed_ntgt Hlc Htarget).
Qed.
